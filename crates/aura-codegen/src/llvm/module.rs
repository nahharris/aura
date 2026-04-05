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
use inkwell::context::Context;
#[cfg(feature = "llvm-backend")]
use inkwell::targets::FileType;

#[cfg(feature = "llvm-backend")]
use super::{
    context::CodegenContext,
    function::{declare_function, declare_function_with_name, declare_global_stub},
};

#[cfg(feature = "llvm-backend")]
fn is_runtime_builtin_wrapper(decl: &aura_typecheck::checked_ir::CheckedDecl) -> bool {
    match &decl.value {
        aura_typecheck::checked_ir::CheckedExpr::Ident(name) => name.starts_with("rt_"),
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
    checked
        .ir
        .declarations
        .iter()
        .find(|d| d.name == "main" || d.name == "aura_user_main")
}

#[cfg(feature = "llvm-backend")]
fn is_void_ty(checked: &CheckedModule, ty: TyId) -> bool {
    matches!(checked.types.get(ty), Some(Ty::Void))
}

#[cfg(feature = "llvm-backend")]
fn is_result_void_u8_ty(checked: &CheckedModule, ty: TyId) -> bool {
    let Some(Ty::Enum(variants)) = checked.types.get(ty) else {
        return false;
    };
    if variants.len() != 2 {
        return false;
    }
    if variants[0].0 != "ok" || variants[0].1.is_some() {
        return false;
    }
    if variants[1].0 != "err" {
        return false;
    }
    let Some(err_ty) = variants[1].1 else {
        return false;
    };
    matches!(checked.types.get(err_ty), Some(Ty::UInt8))
        || matches!(checked.types.get(err_ty), Some(Ty::Nominal(name)) if name == "UInt8")
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

    let user_main_name = "aura_user_main";
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
        .map_err(|_| CodegenError::MainLowering("failed to call `aura_user_main`".to_string()))?;

    if is_void_ty(cg.checked, *ret) {
        let zero = cg.context.i32_type().const_zero();
        cg.builder
            .build_return(Some(&zero))
            .map_err(|_| CodegenError::MainLowering("failed to return success code".to_string()))?;
        return Ok(());
    }

    if is_result_void_u8_ty(cg.checked, *ret) {
        let result = call.try_as_basic_value().left().ok_or_else(|| {
            CodegenError::MainLowering("`main` result value was not returned".to_string())
        })?;

        let exit_i32 = if result.is_int_value() {
            result.into_int_value()
        } else if result.is_pointer_value() {
            cg.context.i32_type().const_zero()
        } else {
            return Err(CodegenError::MainLowering(
                "`main` lowered to unsupported ABI return value".to_string(),
            ));
        };
        cg.builder.build_return(Some(&exit_i32)).map_err(|_| {
            CodegenError::MainLowering("failed to return Result exit code".to_string())
        })?;
        return Ok(());
    }

    Err(CodegenError::MainLowering(
        "`main` return type must be `Void` or `Result[Void, UInt8]`".to_string(),
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
            if matches!(ty, Ty::Func { .. }) {
                return Some(decl.name.clone());
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
            declare_function_with_name(&cg, decl, &decl.name)?;
        } else {
            declare_global_stub(&cg, decl)?;
        }
    }

    for decl in &checked.ir.declarations {
        if is_runtime_builtin_wrapper(decl) {
            continue;
        }
        if !function_names.contains(&decl.name) {
            continue;
        }

        let function = cg
            .module
            .get_function(&decl.name)
            .ok_or(CodegenError::InvalidFunctionType(decl.name.clone()))?;
        let entry = cg.context.append_basic_block(function, "entry");
        cg.builder.position_at_end(entry);

        let lowered = lower_expr(&cg, &decl.value)
            .map_err(|_| CodegenError::UnsupportedExpression(classify_expr_kind(&decl.value)))?;

        if function.get_type().get_return_type().is_some() {
            cg.builder.build_return(Some(&lowered)).map_err(|_| {
                CodegenError::UnsupportedExpression(classify_expr_kind(&decl.value))
            })?;
        } else {
            cg.builder.build_return(None).map_err(|_| {
                CodegenError::UnsupportedExpression(classify_expr_kind(&decl.value))
            })?;
        }
    }

    Ok(cg.module.print_to_string().to_string())
}

#[cfg(feature = "llvm-backend")]
pub fn emit_object_file(
    module_name: &str,
    checked: &CheckedModule,
    out_path: &Path,
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
            if matches!(ty, Ty::Func { .. }) {
                return Some(decl.name.clone());
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
        if !function_names.contains(&decl.name) {
            continue;
        }

        let function = cg
            .module
            .get_function(&decl.name)
            .ok_or(CodegenError::InvalidFunctionType(decl.name.clone()))?;
        let entry = cg.context.append_basic_block(function, "entry");
        cg.builder.position_at_end(entry);

        let lowered = lower_expr(&cg, &decl.value)
            .map_err(|_| CodegenError::UnsupportedExpression(classify_expr_kind(&decl.value)))?;

        if function.get_type().get_return_type().is_some() {
            cg.builder.build_return(Some(&lowered)).map_err(|_| {
                CodegenError::UnsupportedExpression(classify_expr_kind(&decl.value))
            })?;
        } else {
            cg.builder.build_return(None).map_err(|_| {
                CodegenError::UnsupportedExpression(classify_expr_kind(&decl.value))
            })?;
        }
    }

    build_native_main_wrapper(&cg)?;

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
    #[cfg(feature = "llvm-backend")]
    use aura_typecheck::check_module;
    #[cfg(not(feature = "llvm-backend"))]
    use aura_typecheck::check_module;

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
        let program = Parser::parse_source("def main() -> Void { .unit }").expect("parse");
        let checked = check_module(&program);
        let module = checked.module.expect("checked module");
        let out = std::env::temp_dir().join("aura-main-void.obj");
        super::emit_object_file("main_void", &module, &out).expect("emit object");
        assert!(out.exists());
        let _ = std::fs::remove_file(out);
    }

    #[cfg(feature = "llvm-backend")]
    #[test]
    fn object_emission_supports_result_void_u8_main_entrypoint() {
        let src = "def main() -> Result[Void, UInt8] { .err(7) }";
        let program = Parser::parse_source(src).expect("parse");
        let checked = check_module(&program);
        let module = checked.module.expect("checked module");
        let out = std::env::temp_dir().join("aura-main-result.obj");
        super::emit_object_file("main_result", &module, &out).expect("emit object");
        assert!(out.exists());
        let _ = std::fs::remove_file(out);
    }
}
