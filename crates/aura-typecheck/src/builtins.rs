use std::collections::HashMap;

use aura_runtime_host::{runtime_functions, RuntimeTypeRef};

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BuiltinTypeRef {
    Int32,
    ISize,
    USize,
    UInt8,
    Void,
    Bytes,
    String,
    Never,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BuiltinSignature {
    pub name: String,
    pub params: Vec<BuiltinTypeRef>,
    pub ret: BuiltinTypeRef,
}

#[derive(Debug, Clone)]
pub struct BuiltinRegistry {
    entries: HashMap<String, BuiltinSignature>,
}

impl BuiltinRegistry {
    pub fn with_prelude() -> Self {
        let entries = runtime_functions()
            .iter()
            .map(|abi| {
                (
                    abi.name.to_string(),
                    BuiltinSignature {
                        name: abi.name.to_string(),
                        params: abi.params.iter().map(builtin_type_from_runtime).collect(),
                        ret: builtin_type_from_runtime(&abi.ret),
                    },
                )
            })
            .collect();
        Self { entries }
    }

    pub fn get(&self, name: &str) -> Option<&BuiltinSignature> {
        self.entries.get(name)
    }

    pub fn signatures(&self) -> impl Iterator<Item = &BuiltinSignature> {
        self.entries.values()
    }
}

impl Default for BuiltinRegistry {
    fn default() -> Self {
        Self::with_prelude()
    }
}

fn builtin_type_from_runtime(ty: &RuntimeTypeRef) -> BuiltinTypeRef {
    match ty {
        RuntimeTypeRef::Int32 => BuiltinTypeRef::Int32,
        RuntimeTypeRef::ISize => BuiltinTypeRef::ISize,
        RuntimeTypeRef::USize => BuiltinTypeRef::USize,
        RuntimeTypeRef::UInt8 => BuiltinTypeRef::UInt8,
        RuntimeTypeRef::Void => BuiltinTypeRef::Void,
        RuntimeTypeRef::Bytes => BuiltinTypeRef::Bytes,
        RuntimeTypeRef::String => BuiltinTypeRef::String,
        RuntimeTypeRef::Never => BuiltinTypeRef::Never,
    }
}

#[cfg(test)]
mod tests {
    use crate::builtins::{BuiltinRegistry, BuiltinTypeRef};
    use crate::{check_module, Ty};
    use aura_frontend::Parser;

    #[test]
    fn prelude_registry_contains_expected_builtins() {
        let registry = BuiltinRegistry::with_prelude();
        assert!(registry.get("syscall_exit").is_some());
        assert!(registry.get("syscall_write").is_some());
        assert!(registry.get("rt_exit").is_none());
        assert!(registry.get("missing_builtin").is_none());
    }

    #[test]
    fn syscall_write_signature_uses_fd_and_bytes_abi() {
        let registry = BuiltinRegistry::with_prelude();
        let write = registry
            .get("syscall_write")
            .expect("syscall_write must exist");

        assert_eq!(
            write.params,
            vec![BuiltinTypeRef::Int32, BuiltinTypeRef::Bytes]
        );
        assert_eq!(write.ret, BuiltinTypeRef::ISize);
    }

    #[test]
    fn core_runtime_stubs_match_runtime_host_abi() {
        let core_path =
            std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../aura-stl/src/core.aura");
        let source = std::fs::read_to_string(&core_path).expect("core.aura should be readable");
        let program = Parser::parse_source(&source).expect("core.aura should parse");
        let checked = check_module(&program);
        let module = checked.module.expect("core.aura stubs should typecheck");
        let registry = BuiltinRegistry::with_prelude();

        for signature in registry.signatures() {
            let decl = module
                .ir
                .declarations
                .iter()
                .find(|decl| decl.name == signature.name)
                .unwrap_or_else(|| panic!("missing runtime stub `{}`", signature.name));
            let Some(Ty::Func { params, ret }) = module.types.get(decl.ty) else {
                panic!("runtime stub `{}` should be a function", signature.name);
            };

            assert_eq!(
                params.len(),
                signature.params.len(),
                "runtime stub `{}` parameter count",
                signature.name
            );
            for (param, expected) in params.iter().zip(signature.params.iter()) {
                assert_builtin_ty(&module.types, param.ty, expected, &signature.name);
            }
            assert_builtin_ty(&module.types, *ret, &signature.ret, &signature.name);
        }
    }

    fn assert_builtin_ty(
        types: &crate::TyInterner,
        ty: crate::TyId,
        expected: &BuiltinTypeRef,
        name: &str,
    ) {
        let actual = types.get(ty).expect("type id should exist");
        let matches = match (actual, expected) {
            (Ty::Int32, BuiltinTypeRef::Int32)
            | (Ty::ISize, BuiltinTypeRef::ISize)
            | (Ty::USize, BuiltinTypeRef::USize)
            | (Ty::UInt8, BuiltinTypeRef::UInt8)
            | (Ty::Void, BuiltinTypeRef::Void)
            | (Ty::Never, BuiltinTypeRef::Never) => true,
            (Ty::Nominal(actual), BuiltinTypeRef::Bytes) if actual == "Bytes" => true,
            (Ty::Nominal(actual), BuiltinTypeRef::String) if actual == "String" => true,
            _ => false,
        };

        assert!(
            matches,
            "runtime stub `{name}` expected {expected:?}, got {actual:?}"
        );
    }
}
