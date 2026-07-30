//! Wraps exports so a panic escaping to JS rewinds `__stack_pointer`.
//!
//! Under `panic=unwind` the export shim catches the panic and rethrows it as a
//! `PanicError`, abandoning its own frame without running the epilogue that
//! rewinds the shadow stack. Each escaping panic leaks a frame until the stack
//! runs out and later calls trap. Saving at the export boundary rewinds the
//! whole abandoned chain, not just the outermost frame.
//!
//! Targets are the adapter-backed exports in `wit.exports`, a superset of the
//! shims that can actually unwind. Runtime intrinsics are left alone: JS
//! resolves those by searching for the export pointing at a known `FunctionId`
//! (`Context::export_name_of`), which repointing breaks.

use super::ExceptionHandlingVersion;
use crate::wasm_conventions;
use crate::wit::NonstandardWitSection;
use anyhow::Error;
use std::collections::HashMap;
use walrus::ir::*;
use walrus::{
    ExportItem, FunctionBuilder, FunctionId, FunctionKind, GlobalId, LocalId, Module, RefType,
    ValType,
};

/// Does nothing when the module cannot unwind out of an export, which includes
/// `panic=abort`: `catch_handler` has already made its escaping exceptions
/// terminal.
pub fn run(
    module: &mut Module,
    wit: &NonstandardWitSection,
    eh_version: ExceptionHandlingVersion,
) -> Result<(), Error> {
    if !eh_version.unwinds() {
        return Ok(());
    }

    // No shadow stack, nothing to rewind.
    let Some(sp) = wasm_conventions::get_stack_pointer(module) else {
        return Ok(());
    };

    // Keyed by function, not export: `wasm-ld` can merge two shims into one
    // function that ends up exported under both names.
    let mut wrappers: HashMap<FunctionId, FunctionId> = HashMap::new();

    for &(export_id, _) in &wit.exports {
        let ExportItem::Function(func_id) = module.exports.get(export_id).item else {
            continue;
        };
        // Imported functions have no frame of their own to leak.
        if !matches!(module.funcs.get(func_id).kind, FunctionKind::Local(_)) {
            continue;
        }

        let wrapper = *wrappers
            .entry(func_id)
            .or_insert_with(|| generate_wrapper(module, func_id, sp, eh_version.is_legacy()));

        module.exports.get_mut(export_id).item = ExportItem::Function(wrapper);
    }

    log::debug!("Export sp-restore created {} wrappers", wrappers.len());
    Ok(())
}

fn generate_wrapper(
    module: &mut Module,
    original: FunctionId,
    sp: GlobalId,
    legacy: bool,
) -> FunctionId {
    let ty = module.types.get(module.funcs.get(original).ty());
    let params = ty.params().to_vec();
    let results = ty.results().to_vec();

    let mut builder = FunctionBuilder::new(&mut module.types, &params, &results);
    if let Some(name) = module.funcs.get(original).name.as_deref() {
        builder.name(format!("{name} sp restore wrapper"));
    }

    let param_locals: Vec<LocalId> = params.iter().map(|ty| module.locals.add(*ty)).collect();

    // Follows the global's type: `i32` on wasm32, `i64` on memory64.
    let saved_sp = module.locals.add(module.globals.get(sp).ty);

    // Returning from inside the try keeps the results off the stack, so
    // neither the try nor the handler has to carry them.
    let try_body_id = builder.dangling_instr_seq(None).id();
    {
        let mut try_body = builder.instr_seq(try_body_id);
        for local in &param_locals {
            try_body.local_get(*local);
        }
        try_body.call(original);
        try_body.instr(Return {});
    }

    // Save the stack pointer; each handler restores it on the way out.
    let mut body = builder.func_body();
    body.global_get(sp);
    body.local_set(saved_sp);

    if legacy {
        emit_legacy_eh(&mut builder, sp, saved_sp, try_body_id);
    } else {
        emit_modern_eh(&mut builder, sp, saved_sp, try_body_id);
    }

    builder.finish(param_locals, &mut module.funcs)
}

/// Emit the modern (`try_table`) form:
///
/// ```wat
/// (block $catch_all (result exnref)
///   (try_table (catch_all_ref $catch_all) <try body>)
///   unreachable
/// )
/// local.get $saved_sp
/// global.set $__stack_pointer
/// throw_ref
/// ```
///
/// `global.set` pops only the saved pointer, leaving the `exnref` underneath
/// for `throw_ref`, so the exception needs no scratch local of its own.
fn emit_modern_eh(
    builder: &mut FunctionBuilder,
    sp: GlobalId,
    saved_sp: LocalId,
    try_body_id: InstrSeqId,
) {
    let exnref_block_ty: InstrSeqType = ValType::Ref(RefType::EXNREF).into();
    let catch_all_block_id = builder.dangling_instr_seq(exnref_block_ty).id();
    {
        let mut catch_all_block = builder.instr_seq(catch_all_block_id);
        catch_all_block.instr(TryTable {
            seq: try_body_id,
            catches: vec![TryTableCatch::CatchAllRef {
                label: catch_all_block_id,
            }],
        });
        catch_all_block.unreachable();
    }

    let mut body = builder.func_body();
    body.instr(Block {
        seq: catch_all_block_id,
    });
    body.local_get(saved_sp);
    body.global_set(sp);
    body.instr(ThrowRef {});
}

/// Emit the legacy (`try`/`catch_all`) form. Legacy EH has no `exnref`, so the
/// handler restores and rethrows in place.
fn emit_legacy_eh(
    builder: &mut FunctionBuilder,
    sp: GlobalId,
    saved_sp: LocalId,
    try_body_id: InstrSeqId,
) {
    let catch_all_handler_id = builder.dangling_instr_seq(None).id();
    {
        let mut catch_all_handler = builder.instr_seq(catch_all_handler_id);
        catch_all_handler.local_get(saved_sp);
        catch_all_handler.global_set(sp);
        catch_all_handler.instr(Rethrow { relative_depth: 0 });
    }

    let mut body = builder.func_body();
    body.instr(Try {
        seq: try_body_id,
        catches: vec![LegacyCatch::CatchAll {
            handler: catch_all_handler_id,
        }],
    });
    body.unreachable();
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::wit::AdapterId;
    use walrus::ModuleConfig;

    fn parse_wat(wat: &str) -> walrus::Module {
        let wasm = wat::parse_str(wat).unwrap();
        ModuleConfig::new()
            .generate_producers_section(false)
            .parse(&wasm)
            .unwrap()
    }

    /// Build a `wit` section claiming the named exports as adapter exports.
    fn wit_claiming(module: &walrus::Module, names: &[&str]) -> NonstandardWitSection {
        let mut wit = NonstandardWitSection::default();
        for (i, name) in names.iter().enumerate() {
            let export = module
                .exports
                .iter()
                .find(|e| e.name == *name)
                .unwrap_or_else(|| panic!("no export named `{name}`"));
            wit.exports.push((export.id(), AdapterId(i)));
        }
        wit
    }

    fn func_of(module: &walrus::Module, name: &str) -> FunctionId {
        match module.exports.iter().find(|e| e.name == name).unwrap().item {
            ExportItem::Function(f) => f,
            _ => panic!("`{name}` is not a function export"),
        }
    }

    /// `default()` already covers exceptions and memory64; legacy EH does not.
    fn validate(module: &mut walrus::Module, extra: wasmparser::WasmFeatures) {
        let features = wasmparser::WasmFeatures::default() | extra;
        wasmparser::Validator::new_with_features(features)
            .validate_all(&module.emit_wasm())
            .expect("transformed module should validate");
    }

    /// A module with a shadow stack, an adapter-backed export and an intrinsic
    /// export that must be left alone.
    const MODULE: &str = r#"
        (module
            (global $__stack_pointer (mut i32) (i32.const 1048576))
            (func $shim (param i32) (result i32) local.get 0)
            (func $__wbindgen_malloc (param i32) (result i32) local.get 0)
            (export "shim" (func $shim))
            (export "__wbindgen_malloc" (func $__wbindgen_malloc))
        )
    "#;

    #[test]
    fn wraps_adapter_exports_and_leaves_intrinsics_alone() {
        let mut module = parse_wat(MODULE);
        let shim = func_of(&module, "shim");
        let malloc = func_of(&module, "__wbindgen_malloc");
        let wit = wit_claiming(&module, &["shim"]);

        run(&mut module, &wit, ExceptionHandlingVersion::Modern).unwrap();

        let wrapped = func_of(&module, "shim");
        assert_ne!(wrapped, shim);
        assert_eq!(
            module.funcs.get(wrapped).name.as_deref(),
            Some("shim sp restore wrapper")
        );
        assert_eq!(module.funcs.get(wrapped).ty(), module.funcs.get(shim).ty());

        // Still reachable by its original `FunctionId`, and still exported once.
        assert_eq!(func_of(&module, "__wbindgen_malloc"), malloc);
        assert_eq!(
            module
                .exports
                .iter()
                .filter(|e| e.name == "__wbindgen_malloc")
                .count(),
            1
        );

        validate(&mut module, wasmparser::WasmFeatures::empty());
    }

    #[test]
    fn legacy_eh_wrapper_validates() {
        let mut module = parse_wat(MODULE);
        let wit = wit_claiming(&module, &["shim"]);

        run(&mut module, &wit, ExceptionHandlingVersion::Legacy).unwrap();

        validate(&mut module, wasmparser::WasmFeatures::LEGACY_EXCEPTIONS);
    }

    /// The `__stack_pointer` global is `i64` on memory64, so the scratch local
    /// has to follow it or the wrapper fails validation.
    #[test]
    fn memory64_stack_pointer_uses_an_i64_local() {
        let wat = r#"
            (module
                (memory i64 1)
                (global $__stack_pointer (mut i64) (i64.const 1048576))
                (func $shim (param i32) (result i32) local.get 0)
                (export "shim" (func $shim))
            )
        "#;
        let mut module = parse_wat(wat);
        let wit = wit_claiming(&module, &["shim"]);
        assert_eq!(
            module
                .locals
                .iter()
                .filter(|l| l.ty() == ValType::I64)
                .count(),
            0
        );

        run(&mut module, &wit, ExceptionHandlingVersion::Modern).unwrap();

        assert_eq!(
            module
                .locals
                .iter()
                .filter(|l| l.ty() == ValType::I64)
                .count(),
            1,
            "expected exactly one i64 scratch local for the stack pointer"
        );

        validate(&mut module, wasmparser::WasmFeatures::empty());
    }

    /// One function exported under two names gets one shared wrapper.
    #[test]
    fn shared_function_gets_one_wrapper() {
        let wat = r#"
            (module
                (global $__stack_pointer (mut i32) (i32.const 1048576))
                (func $shim (param i32) (result i32) local.get 0)
                (export "a" (func $shim))
                (export "b" (func $shim))
            )
        "#;
        let mut module = parse_wat(wat);
        let before = module.funcs.iter().count();
        let wit = wit_claiming(&module, &["a", "b"]);

        run(&mut module, &wit, ExceptionHandlingVersion::Modern).unwrap();

        assert_eq!(func_of(&module, "a"), func_of(&module, "b"));
        assert_eq!(module.funcs.iter().count(), before + 1);

        validate(&mut module, wasmparser::WasmFeatures::empty());
    }

    #[test]
    fn no_wrappers_without_unwinding() {
        for eh_version in [
            ExceptionHandlingVersion::None,
            ExceptionHandlingVersion::ModernButWithPanicAbort,
        ] {
            let mut module = parse_wat(MODULE);
            let shim = func_of(&module, "shim");
            let wit = wit_claiming(&module, &["shim"]);

            run(&mut module, &wit, eh_version).unwrap();

            assert_eq!(func_of(&module, "shim"), shim, "{eh_version:?}");
        }
    }

    #[test]
    fn no_wrappers_without_a_shadow_stack() {
        let wat = r#"
            (module
                (func $shim (param i32) (result i32) local.get 0)
                (export "shim" (func $shim))
            )
        "#;
        let mut module = parse_wat(wat);
        let shim = func_of(&module, "shim");
        let wit = wit_claiming(&module, &["shim"]);

        run(&mut module, &wit, ExceptionHandlingVersion::Modern).unwrap();

        assert_eq!(func_of(&module, "shim"), shim);
    }
}
