use aura_typecheck::checked_ir::CheckedDecl;

use super::error::CodegenError;

#[cfg(feature = "llvm-backend")]
use super::types::classify_function_type;

#[cfg(feature = "llvm-backend")]
use super::types::classify_type;

#[cfg(feature = "llvm-backend")]
use inkwell::module::Linkage;

#[cfg(feature = "llvm-backend")]
use inkwell::types::BasicType;

#[cfg(feature = "llvm-backend")]
use super::context::CodegenContext;

#[cfg(feature = "llvm-backend")]
pub fn declare_function<'ctx, 'm>(
    cg: &CodegenContext<'ctx, 'm>,
    decl: &CheckedDecl,
) -> Result<inkwell::values::FunctionValue<'ctx>, CodegenError> {
    declare_function_with_name(cg, decl, &decl.link_name)
}

#[cfg(feature = "llvm-backend")]
pub fn declare_function_with_name<'ctx, 'm>(
    cg: &CodegenContext<'ctx, 'm>,
    decl: &CheckedDecl,
    llvm_name: &str,
) -> Result<inkwell::values::FunctionValue<'ctx>, CodegenError> {
    let lowered = classify_function_type(&cg.checked.types, decl.ty)
        .map_err(|_| CodegenError::InvalidFunctionType(decl.name.clone()))?;
    let fn_type = lowered.to_llvm_fn_type(cg.context, false)?;

    let function = cg
        .module
        .add_function(llvm_name, fn_type, Some(Linkage::External));
    Ok(function)
}

#[cfg(feature = "llvm-backend")]
pub fn declare_global_stub<'ctx, 'm>(
    cg: &CodegenContext<'ctx, 'm>,
    decl: &CheckedDecl,
) -> Result<(), CodegenError> {
    let value_ty = classify_type(&cg.checked.types, decl.ty)?;
    let basic_ty = match value_ty {
        super::types::AuraValueType::Void => cg.context.i8_type().as_basic_type_enum(),
        _ => value_ty.to_basic_type(cg.context)?,
    };

    let global = cg
        .module
        .add_global(basic_ty, None, &format!("{}_global", decl.link_name));
    if decl.is_extern {
        global.set_linkage(Linkage::External);
    } else {
        global.set_initializer(&basic_ty.const_zero());
    }
    Ok(())
}

#[cfg(not(feature = "llvm-backend"))]
pub fn declare_function(_decl: &CheckedDecl) -> Result<(), CodegenError> {
    Err(CodegenError::BackendDisabled)
}
