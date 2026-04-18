use std::collections::HashMap;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum BuiltinTypeRef {
    Int32,
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
        let mut entries = HashMap::new();

        entries.insert(
            "syscall_exit".to_string(),
            BuiltinSignature {
                name: "syscall_exit".to_string(),
                params: vec![BuiltinTypeRef::Int32],
                ret: BuiltinTypeRef::Never,
            },
        );
        Self { entries }
    }

    pub fn get(&self, name: &str) -> Option<&BuiltinSignature> {
        self.entries.get(name)
    }
}

impl Default for BuiltinRegistry {
    fn default() -> Self {
        Self::with_prelude()
    }
}

#[cfg(test)]
mod tests {
    use crate::builtins::BuiltinRegistry;

    #[test]
    fn prelude_registry_contains_expected_builtins() {
        let registry = BuiltinRegistry::with_prelude();
        assert!(registry.get("syscall_exit").is_some());
        assert!(registry.get("rt_exit").is_none());
        assert!(registry.get("missing_builtin").is_none());
    }
}
