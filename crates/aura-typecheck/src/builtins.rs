use std::collections::HashMap;

use aura_runtime_host::{RuntimeTypeRef, runtime_functions};

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
}
