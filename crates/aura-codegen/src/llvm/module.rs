#[cfg(feature = "llvm-backend")]
use aura_runtime_host::runtime_function;
use aura_typecheck::CheckedModule;
#[cfg(feature = "llvm-backend")]
use aura_typecheck::Ty;
#[cfg(feature = "llvm-backend")]
use aura_typecheck::TyId;
#[cfg(feature = "llvm-backend")]
use std::collections::HashSet;
use std::path::Path;

use super::error::CodegenError;

#[cfg(feature = "llvm-backend")]
use super::expr::classify_expr_kind;
#[cfg(feature = "llvm-backend")]
use super::expr::lower_expr;
#[cfg(feature = "llvm-backend")]
use super::types::{classify_type, lower_basic_type};

#[cfg(feature = "llvm-backend")]
use inkwell::context::Context;
#[cfg(feature = "llvm-backend")]
use inkwell::targets::FileType;

#[cfg(feature = "llvm-backend")]
use super::{
    context::CodegenContext,
    function::{declare_function, declare_function_with_name, declare_global_stub},
};

#[cfg(feature = "llvm-backend")]
fn bind_function_params<'ctx, 'm>(
    cg: &CodegenContext<'ctx, 'm>,
    decl: &aura_typecheck::checked_ir::CheckedDecl,
    function: inkwell::values::FunctionValue<'ctx>,
) -> Result<(), CodegenError> {
    let Some(Ty::Func { params, .. }) = cg.checked.types.get(decl.ty) else {
        return Err(CodegenError::InvalidFunctionType(decl.name.clone()));
    };
    if decl.params.len() != params.len() {
        return Err(CodegenError::InvalidFunctionType(decl.name.clone()));
    }

    for (index, (param_name, param)) in decl.params.iter().zip(params.iter()).enumerate() {
        let Some(value) = function.get_nth_param(index as u32) else {
            return Err(CodegenError::InvalidFunctionType(decl.name.clone()));
        };
        let _value_ty = classify_type(&cg.checked.types, param.ty)?;
        let basic_ty = lower_basic_type(cg.context, &cg.checked.types, param.ty)?;
        let slot = cg
            .builder
            .build_alloca(basic_ty, &format!("param_{param_name}"))
            .map_err(|_| CodegenError::UnsupportedExpression("param"))?;
        cg.builder
            .build_store(slot, value)
            .map_err(|_| CodegenError::UnsupportedExpression("param"))?;
        cg.insert_local(
            param_name.clone(),
            super::context::LocalSlot {
                ptr: slot,
                ty: param.ty,
            },
        );
    }

    Ok(())
}

#[cfg(feature = "llvm-backend")]
fn is_runtime_builtin_wrapper(decl: &aura_typecheck::checked_ir::CheckedDecl) -> bool {
    match &decl.value {
        aura_typecheck::checked_ir::CheckedExpr::Ident(name) => runtime_function(name).is_some(),
        _ => false,
    }
}

#[cfg(feature = "llvm-backend")]
fn ensure_native_main_stub<'ctx, 'm>(cg: &CodegenContext<'ctx, 'm>) -> Result<(), CodegenError> {
    if cg.module.get_function("main").is_some() {
        return Ok(());
    }

    let fn_ty = cg.context.i32_type().fn_type(&[], false);
    let function = cg.module.add_function("main", fn_ty, None);
    let entry = cg.context.append_basic_block(function, "entry");
    cg.builder.position_at_end(entry);
    let zero = cg.context.i32_type().const_zero();
    cg.builder
        .build_return(Some(&zero))
        .map_err(|_| CodegenError::UnsupportedExpression("main_stub"))?;
    Ok(())
}

#[cfg(feature = "llvm-backend")]
fn find_main_decl<'m>(
    checked: &'m CheckedModule,
) -> Option<&'m aura_typecheck::checked_ir::CheckedDecl> {
    checked.ir.declarations.iter().find(|d| d.name == "main")
}

#[cfg(feature = "llvm-backend")]
fn is_void_ty(checked: &CheckedModule, ty: TyId) -> bool {
    matches!(checked.types.get(ty), Some(Ty::Void))
}

#[cfg(feature = "llvm-backend")]
fn build_native_main_wrapper<'ctx, 'm>(cg: &CodegenContext<'ctx, 'm>) -> Result<(), CodegenError> {
    let Some(main_decl) = find_main_decl(cg.checked) else {
        return ensure_native_main_stub(cg);
    };
    let Some(main_ty) = cg.checked.types.get(main_decl.ty) else {
        return Err(CodegenError::InvalidTypeId(main_decl.ty.0));
    };
    let Ty::Func { params, ret } = main_ty else {
        return Err(CodegenError::MainLowering(
            "`main` declaration is not a function".to_string(),
        ));
    };
    if !params.is_empty() {
        return Err(CodegenError::MainLowering(
            "`main` with parameters is not supported in native entrypoint lowering".to_string(),
        ));
    }

    let user_main_name = main_decl.link_name.as_str();
    let user_main = if let Some(existing) = cg.module.get_function(user_main_name) {
        existing
    } else {
        declare_function_with_name(cg, main_decl, user_main_name)?
    };

    let fn_ty = cg.context.i32_type().fn_type(&[], false);
    let entry_main = cg.module.add_function("main", fn_ty, None);
    let block = cg.context.append_basic_block(entry_main, "entry");
    cg.builder.position_at_end(block);
    let call = cg
        .builder
        .build_call(user_main, &[], "call_user_main")
        .map_err(|_| CodegenError::MainLowering("failed to call lowered `main`".to_string()))?;

    if is_void_ty(cg.checked, *ret) {
        let zero = cg.context.i32_type().const_zero();
        cg.builder
            .build_return(Some(&zero))
            .map_err(|_| CodegenError::MainLowering("failed to return success code".to_string()))?;
        return Ok(());
    }

    let _ = call;
    Err(CodegenError::MainLowering(
        "`main` return type must be `Void`".to_string(),
    ))
}

#[cfg(feature = "llvm-backend")]
pub fn emit_module_stub(
    module_name: &str,
    checked: &CheckedModule,
) -> Result<String, CodegenError> {
    let context = Context::create();
    let cg = CodegenContext::new(&context, module_name, checked);

    let function_names = checked
        .ir
        .declarations
        .iter()
        .filter_map(|decl| {
            let ty = checked.types.get(decl.ty)?;
            if matches!(ty, Ty::Func { .. }) && !decl.is_extern {
                return Some(decl.link_name.clone());
            }
            None
        })
        .collect::<HashSet<_>>();

    for decl in &checked.ir.declarations {
        if is_runtime_builtin_wrapper(decl) {
            continue;
        }
        let Some(ty) = checked.types.get(decl.ty) else {
            return Err(CodegenError::InvalidTypeId(decl.ty.0));
        };

        if matches!(ty, Ty::Func { .. }) {
            declare_function(&cg, decl)?;
        } else {
            declare_global_stub(&cg, decl)?;
        }
    }

    for decl in &checked.ir.declarations {
        if is_runtime_builtin_wrapper(decl) || decl.is_extern {
            continue;
        }
        if !function_names.contains(&decl.link_name) {
            continue;
        }

        let function = cg
            .module
            .get_function(&decl.link_name)
            .ok_or(CodegenError::InvalidFunctionType(decl.name.clone()))?;
        let entry = cg.context.append_basic_block(function, "entry");
        cg.builder.position_at_end(entry);
        cg.push_local_scope();
        bind_function_params(&cg, decl, function)?;

        let lowered = lower_expr(&cg, &decl.value)?;

        if function.get_type().get_return_type().is_some() {
            cg.builder.build_return(Some(&lowered)).map_err(|_| {
                CodegenError::UnsupportedExpression(classify_expr_kind(&decl.value))
            })?;
        } else {
            cg.builder.build_return(None).map_err(|_| {
                CodegenError::UnsupportedExpression(classify_expr_kind(&decl.value))
            })?;
        }
        cg.pop_local_scope();
    }

    Ok(cg.module.print_to_string().to_string())
}

#[cfg(feature = "llvm-backend")]
pub fn emit_object_file(
    module_name: &str,
    checked: &CheckedModule,
    out_path: &Path,
) -> Result<(), CodegenError> {
    emit_object_file_with_options(module_name, checked, out_path, true)
}

#[cfg(feature = "llvm-backend")]
pub fn emit_object_file_with_options(
    module_name: &str,
    checked: &CheckedModule,
    out_path: &Path,
    include_native_entry: bool,
) -> Result<(), CodegenError> {
    CodegenContext::initialize_native_target()?;
    let target_machine = CodegenContext::native_target_machine()
        .ok_or(CodegenError::NativeTargetMachineUnavailable)?;

    let context = Context::create();
    let cg = CodegenContext::new(&context, module_name, checked);

    let function_names = checked
        .ir
        .declarations
        .iter()
        .filter_map(|decl| {
            let ty = checked.types.get(decl.ty)?;
            if matches!(ty, Ty::Func { .. }) && !decl.is_extern {
                return Some(decl.link_name.clone());
            }
            None
        })
        .collect::<HashSet<_>>();

    for decl in &checked.ir.declarations {
        if is_runtime_builtin_wrapper(decl) {
            continue;
        }
        let Some(ty) = checked.types.get(decl.ty) else {
            return Err(CodegenError::InvalidTypeId(decl.ty.0));
        };

        if matches!(ty, Ty::Func { .. }) {
            declare_function(&cg, decl)?;
        } else {
            declare_global_stub(&cg, decl)?;
        }
    }

    for decl in &checked.ir.declarations {
        if is_runtime_builtin_wrapper(decl) || decl.is_extern {
            continue;
        }
        if !function_names.contains(&decl.link_name) {
            continue;
        }

        let function = cg
            .module
            .get_function(&decl.link_name)
            .ok_or(CodegenError::InvalidFunctionType(decl.name.clone()))?;
        let entry = cg.context.append_basic_block(function, "entry");
        cg.builder.position_at_end(entry);
        cg.push_local_scope();
        bind_function_params(&cg, decl, function)?;

        let lowered = lower_expr(&cg, &decl.value)?;

        if function.get_type().get_return_type().is_some() {
            cg.builder.build_return(Some(&lowered)).map_err(|_| {
                CodegenError::UnsupportedExpression(classify_expr_kind(&decl.value))
            })?;
        } else {
            cg.builder.build_return(None).map_err(|_| {
                CodegenError::UnsupportedExpression(classify_expr_kind(&decl.value))
            })?;
        }
        cg.pop_local_scope();
    }

    if include_native_entry {
        build_native_main_wrapper(&cg)?;
    }

    if let Err(msg) = cg.module.verify() {
        return Err(CodegenError::ModuleVerification(msg.to_string()));
    }

    target_machine
        .write_to_file(&cg.module, FileType::Object, out_path)
        .map_err(|e| CodegenError::ObjectEmit(e.to_string()))?;
    Ok(())
}

#[cfg(not(feature = "llvm-backend"))]
pub fn emit_object_file(
    _module_name: &str,
    _checked: &CheckedModule,
    _out_path: &Path,
) -> Result<(), CodegenError> {
    Err(CodegenError::BackendDisabled)
}

#[cfg(not(feature = "llvm-backend"))]
pub fn emit_object_file_with_options(
    _module_name: &str,
    _checked: &CheckedModule,
    _out_path: &Path,
    _include_native_entry: bool,
) -> Result<(), CodegenError> {
    Err(CodegenError::BackendDisabled)
}

#[cfg(not(feature = "llvm-backend"))]
pub fn emit_module_stub(
    _module_name: &str,
    _checked: &CheckedModule,
) -> Result<String, CodegenError> {
    Err(CodegenError::BackendDisabled)
}

#[cfg(test)]
mod tests {
    #[cfg(feature = "llvm-backend")]
    use aura_frontend::Parser;
    #[cfg(not(feature = "llvm-backend"))]
    use aura_frontend::Parser;
    #[cfg(not(feature = "llvm-backend"))]
    use aura_typecheck::check_module;
    #[cfg(feature = "llvm-backend")]
    use aura_typecheck::{CheckOptions, check_module, check_module_with_options};

    #[cfg(feature = "llvm-backend")]
    use super::CodegenError;
    #[cfg(not(feature = "llvm-backend"))]
    use super::emit_module_stub;

    #[cfg(not(feature = "llvm-backend"))]
    #[test]
    fn backend_disabled_without_feature() {
        let program = Parser::parse_source("def x = 1;").expect("parse");
        let checked = check_module(&program);
        let module = checked.module.expect("checked module");
        let err = emit_module_stub("test", &module).expect_err("backend disabled");
        assert_eq!(
            err.to_string(),
            "LLVM backend is disabled; enable feature `llvm-backend`"
        );
    }

    #[cfg(feature = "llvm-backend")]
    #[test]
    fn object_emission_supports_void_main_entrypoint() {
        let program = Parser::parse_source("def main() -> Void { () }").expect("parse");
        let checked = check_module(&program);
        let module = checked.module.expect("checked module");
        let out = std::env::temp_dir().join("aura-main-void.obj");
        super::emit_object_file("main_void", &module, &out).expect("emit object");
        assert!(out.exists());
        let _ = std::fs::remove_file(out);
    }

    #[cfg(feature = "llvm-backend")]
    #[test]
    fn object_emission_supports_local_assignment_before_exit() {
        let src = "defstub syscall_exit: Func[(code: Int), Never]; \
                   def main() -> Void { let exit_code = 0; exit_code = 0; syscall_exit(exit_code) }";
        let program = Parser::parse_source(src).expect("parse");
        let checked = check_module(&program);
        let module = checked.module.expect("checked module");
        let out = std::env::temp_dir().join("aura-main-local-assign.obj");
        super::emit_object_file("main_local_assign", &module, &out).expect("emit object");
        assert!(out.exists());
        let _ = std::fs::remove_file(out);
    }

    #[cfg(feature = "llvm-backend")]
    #[test]
    fn llvm_ir_supports_struct_field_assignment() {
        let src = "def main() -> Int { let p = (left = 1, right = 2); p.right = 3; p.right }";
        let program = Parser::parse_source(src).expect("parse");
        let checked = check_module(&program);
        let module = checked
            .module
            .unwrap_or_else(|| panic!("checked module: {:?}", checked.diagnostics));

        let ir = super::emit_module_stub("field_assign", &module).expect("emit ir");

        assert!(ir.contains("getelementptr"));
        assert!(ir.contains("store i32 3"));
        assert!(ir.contains("load i32"));
    }

    #[cfg(feature = "llvm-backend")]
    #[test]
    fn object_emission_supports_syscall_write_with_string_into() {
        let src = "defstub syscall_exit: Func[(code: Int), Never]; \
                   defstub syscall_write: Func[(fd: Int, bytes: Bytes), ISize]; \
                   defstub string_into: Func[(text: String), Bytes]; \
                   def main() -> Void { syscall_write(1, \"Hello, world!\".into()); syscall_exit(0) }";
        let program = Parser::parse_source(src).expect("parse");
        let checked = check_module(&program);
        let module = checked.module.expect("checked module");
        let out = std::env::temp_dir().join("aura-main-hello-world.obj");
        super::emit_object_file("main_hello_world", &module, &out).expect("emit object");
        assert!(out.exists());
        let _ = std::fs::remove_file(out);
    }

    #[cfg(feature = "llvm-backend")]
    #[test]
    fn llvm_ir_declares_runtime_bytes_and_write_symbols() {
        let src = "defstub syscall_exit: Func[(code: Int), Never]; \
                   defstub syscall_write: Func[(fd: Int, bytes: Bytes), ISize]; \
                   defstub string_into: Func[(text: String), Bytes]; \
                   def main() -> Void { syscall_write(1, \"Hello, world!\".into()); syscall_exit(0) }";
        let program = Parser::parse_source(src).expect("parse");
        let checked = check_module(&program);
        let module = checked.module.expect("checked module");

        let ir = super::emit_module_stub("main_hello_world", &module).expect("emit ir");

        assert!(ir.contains("declare i64 @syscall_write(i32, ptr)"));
        assert!(ir.contains("declare ptr @string_into(ptr)"));
        assert!(ir.contains("declare void @syscall_exit(i32)"));
        assert!(ir.contains("call ptr @string_into(ptr"));
        assert!(ir.contains("call i64 @syscall_write(i32 1, ptr"));
    }

    #[cfg(feature = "llvm-backend")]
    #[test]
    fn llvm_ir_declares_managed_memory_runtime_symbols() {
        let src = r#"
            def touch(reference: Ref[Int]) -> Int {
                reference.set(7);
                reference.get()
            }

            def main() -> Void {
                let alloc = RawAlloc[Int].new(2);
                let slice = alloc.slice();
                slice.set(0, 42);
                let value = slice.get(0);
                let reference = slice.ref_at(0);
                ()
            }
        "#;
        let program = Parser::parse_source(src).expect("parse");
        let checked = check_module(&program);
        let module = checked.module.expect("checked module");

        let ir = super::emit_module_stub("managed_memory", &module).expect("emit ir");

        assert!(ir.contains("declare ptr @raw_alloc_new(i64, i64, i64)"));
        assert!(ir.contains("declare ptr @raw_alloc_slice(ptr)"));
        assert!(ir.contains("declare i1 @slice_set(ptr, i64, ptr)"));
        assert!(ir.contains("declare i1 @slice_get(ptr, i64, ptr)"));
        assert!(ir.contains("declare ptr @slice_ref_at(ptr, i64)"));
        assert!(ir.contains("declare void @ref_set(ptr, ptr)"));
        assert!(ir.contains("declare void @ref_get(ptr, ptr)"));
        assert!(ir.contains("call ptr @raw_alloc_new(i64 2, i64 4, i64 4)"));
        assert!(ir.contains("call ptr @raw_alloc_slice(ptr"));
        assert!(ir.contains("call i1 @slice_set(ptr"));
        assert!(ir.contains("call i1 @slice_get(ptr"));
        assert!(ir.contains("call ptr @slice_ref_at(ptr"));
        assert!(ir.contains("call void @ref_set(ptr"));
        assert!(ir.contains("call void @ref_get(ptr"));
    }

    #[cfg(feature = "llvm-backend")]
    #[test]
    fn llvm_identifier_named_true_prefers_local_binding() {
        let src = "def echo(true: Int) -> Int { true }";
        let program = Parser::parse_source(src).expect("parse");
        let checked = check_module(&program);
        let module = checked.module.expect("checked module");

        let ir = super::emit_module_stub("true_shadow", &module).expect("emit ir");

        assert!(ir.contains("store i32 %0, ptr %param_true"));
        assert!(ir.contains("load i32, ptr %param_true"));
        assert!(!ir.contains("ret i1 true"));
    }

    #[cfg(feature = "llvm-backend")]
    #[test]
    fn non_void_main_is_rejected_before_codegen() {
        let src = "def main() -> Result[Void, UInt8] { .err(7) }";
        let program = Parser::parse_source(src).expect("parse");
        let checked = check_module_with_options(
            &program,
            CheckOptions {
                enforce_main_signature: false,
            },
        );
        let module = checked
            .module
            .expect("typechecking should allow Result main");
        let out = std::env::temp_dir().join("aura-non-void-main.obj");
        let err = super::emit_object_file("non_void_main", &module, &out)
            .expect_err("native entry lowering should reject non-Void main");

        assert!(matches!(err, CodegenError::MainLowering(_)));
        let _ = std::fs::remove_file(out);
    }

    #[cfg(feature = "llvm-backend")]
    #[test]
    fn object_emission_supports_generic_enum_methods_and_calls() {
        let src = r#"
            def ExitCode = enum(success, failure, custom: Int);

            def ExitCode.into(self: ExitCode) -> Int {
                .success -> 0,
                .failure -> 1,
                .custom(code) -> code,
            }

            def exit_code() -> ExitCode { .custom(100) }
            def main() -> Void { let code = exit_code(); code.into(); () }
        "#;
        let program = Parser::parse_source(src).expect("parse");
        let checked = check_module(&program);
        let module = checked.module.expect("checked module");
        let out = std::env::temp_dir().join("aura-enum-generic.obj");
        super::emit_object_file("enum_generic", &module, &out).expect("emit object");
        assert!(out.exists());
        let _ = std::fs::remove_file(out);
    }
}
