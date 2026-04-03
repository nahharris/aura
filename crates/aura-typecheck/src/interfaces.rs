use std::collections::HashSet;

#[derive(Debug, Clone)]
pub struct InterfaceRegistry {
    known: HashSet<String>,
}

impl InterfaceRegistry {
    pub fn with_prelude() -> Self {
        let mut known = HashSet::new();
        for name in [
            "Eq",
            "Hash",
            "Show",
            "ToStr",
            "From",
            "Iterable",
            "Hasheable",
        ] {
            known.insert(name.to_string());
        }
        Self { known }
    }

    pub fn contains(&self, name: &str) -> bool {
        self.known.contains(name)
    }
}

impl Default for InterfaceRegistry {
    fn default() -> Self {
        Self::with_prelude()
    }
}

#[cfg(test)]
mod tests {
    use crate::interfaces::InterfaceRegistry;

    #[test]
    fn prelude_contains_common_interfaces() {
        let registry = InterfaceRegistry::with_prelude();
        assert!(registry.contains("Eq"));
        assert!(registry.contains("ToStr"));
        assert!(!registry.contains("Unknown"));
    }
}
