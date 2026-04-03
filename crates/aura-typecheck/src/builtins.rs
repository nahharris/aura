use std::collections::HashMap;

use crate::types::Ty;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct BuiltinSignature {
    pub name: String,
    pub params: Vec<Ty>,
    pub ret: Ty,
}

#[derive(Debug, Clone)]
pub struct BuiltinRegistry {
    entries: HashMap<String, BuiltinSignature>,
}

impl BuiltinRegistry {
    pub fn with_prelude() -> Self {
        let mut entries = HashMap::new();
        entries.insert(
            "io_write".to_string(),
            BuiltinSignature {
                name: "io_write".to_string(),
                params: vec![Ty::Nominal("String".to_string())],
                ret: Ty::Void,
            },
        );
        entries.insert(
            "to_str".to_string(),
            BuiltinSignature {
                name: "to_str".to_string(),
                params: vec![Ty::Any],
                ret: Ty::Nominal("String".to_string()),
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
        assert!(registry.get("io_write").is_some());
        assert!(registry.get("to_str").is_some());
        assert!(registry.get("missing_builtin").is_none());
    }
}
