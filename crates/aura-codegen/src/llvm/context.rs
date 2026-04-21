#[cfg(feature = "llvm-backend")]
use std::{cell::RefCell, collections::HashMap};

#[cfg(feature = "llvm-backend")]
use inkwell::{
    builder::Builder,
    context::Context,
    module::Module,
    values::PointerValue,
    targets::{CodeModel, InitializationConfig, RelocMode, Target, TargetMachine},
};

#[cfg(feature = "llvm-backend")]
use aura_typecheck::CheckedModule;

use super::error::CodegenError;

#[cfg(feature = "llvm-backend")]
#[derive(Clone, Copy)]
pub struct LocalSlot<'ctx> {
    pub ptr: PointerValue<'ctx>,
    pub ty: aura_typecheck::TyId,
}

#[cfg(feature = "llvm-backend")]
pub struct CodegenContext<'ctx, 'm> {
    pub context: &'ctx Context,
    pub module: Module<'ctx>,
    pub builder: Builder<'ctx>,
    pub checked: &'m CheckedModule,
    pub local_scopes: RefCell<Vec<HashMap<String, LocalSlot<'ctx>>>>,
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
            local_scopes: RefCell::new(vec![HashMap::new()]),
        }
    }

    pub fn push_local_scope(&self) {
        self.local_scopes.borrow_mut().push(HashMap::new());
    }

    pub fn pop_local_scope(&self) {
        let mut scopes = self.local_scopes.borrow_mut();
        if scopes.len() > 1 {
            let _ = scopes.pop();
        }
    }

    pub fn insert_local(&self, name: String, slot: LocalSlot<'ctx>) {
        if let Some(scope) = self.local_scopes.borrow_mut().last_mut() {
            scope.insert(name, slot);
        }
    }

    pub fn lookup_local(&self, name: &str) -> Option<LocalSlot<'ctx>> {
        self.local_scopes
            .borrow()
            .iter()
            .rev()
            .find_map(|scope| scope.get(name).copied())
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
