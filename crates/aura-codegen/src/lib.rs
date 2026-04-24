pub mod llvm;
pub mod project;

use std::path::Path;

use aura_typecheck::CheckedModule;

use llvm::CodegenError;

pub fn backend_name() -> &'static str {
    "aura-codegen"
}

pub fn emit_llvm_ir(module_name: &str, checked: &CheckedModule) -> Result<String, CodegenError> {
    llvm::emit_module_stub(module_name, checked)
}

pub fn emit_object_file(
    module_name: &str,
    checked: &CheckedModule,
    out_path: &Path,
) -> Result<(), CodegenError> {
    llvm::module::emit_object_file(module_name, checked, out_path)
}

pub fn emit_object_file_with_options(
    module_name: &str,
    checked: &CheckedModule,
    out_path: &Path,
    include_native_entry: bool,
) -> Result<(), CodegenError> {
    llvm::module::emit_object_file_with_options(
        module_name,
        checked,
        out_path,
        include_native_entry,
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn crate_is_wired_in_workspace() {
        assert_eq!(backend_name(), "aura-codegen");
    }
}
