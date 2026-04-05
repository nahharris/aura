#[cfg(feature = "llvm-backend")]
use inkwell::{
    builder::Builder,
    context::Context,
    module::Module,
    targets::{CodeModel, InitializationConfig, RelocMode, Target, TargetMachine},
};

#[cfg(feature = "llvm-backend")]
use aura_typecheck::CheckedModule;

use super::error::CodegenError;

#[cfg(feature = "llvm-backend")]
pub struct CodegenContext<'ctx, 'm> {
    pub context: &'ctx Context,
    pub module: Module<'ctx>,
    pub builder: Builder<'ctx>,
    pub checked: &'m CheckedModule,
}

#[cfg(feature = "llvm-backend")]
impl<'ctx, 'm> CodegenContext<'ctx, 'm> {
    pub fn new(context: &'ctx Context, module_name: &str, checked: &'m CheckedModule) -> Self {
        let module = context.create_module(module_name);
        let builder = context.create_builder();
        Self {
            context,
            module,
            builder,
            checked,
        }
    }

    pub fn initialize_native_target() -> Result<(), CodegenError> {
        Target::initialize_native(&InitializationConfig::default())
            .map_err(|_| CodegenError::NativeTargetInit)?;
        Ok(())
    }

    pub fn native_target_machine() -> Option<TargetMachine> {
        let triple = TargetMachine::get_default_triple();
        let target = Target::from_triple(&triple).ok()?;
        target.create_target_machine(
            &triple,
            "generic",
            "",
            inkwell::OptimizationLevel::None,
            RelocMode::Default,
            CodeModel::Default,
        )
    }
}

#[cfg(not(feature = "llvm-backend"))]
pub struct CodegenContext;

#[cfg(not(feature = "llvm-backend"))]
impl CodegenContext {
    pub fn initialize_native_target() -> Result<(), CodegenError> {
        Err(CodegenError::BackendDisabled)
    }
}
