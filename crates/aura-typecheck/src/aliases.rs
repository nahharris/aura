use std::collections::HashMap;

use crate::types::{Ty, TyId, TyInterner};

#[derive(Debug, Clone)]
pub struct TypeAliases {
    aliases: HashMap<String, TyId>,
}

impl TypeAliases {
    pub fn with_prelude(interner: &mut TyInterner) -> Self {
        let mut aliases = HashMap::new();
        aliases.insert("Int".to_string(), interner.intern(Ty::Int32));
        aliases.insert("Float".to_string(), interner.intern(Ty::Float32));
        Self { aliases }
    }

    pub fn get(&self, name: &str) -> Option<TyId> {
        self.aliases.get(name).copied()
    }
}

#[cfg(test)]
mod tests {
    use crate::aliases::TypeAliases;
    use crate::types::{Ty, TyInterner};

    #[test]
    fn prelude_aliases_int_and_float() {
        let mut interner = TyInterner::new();
        let aliases = TypeAliases::with_prelude(&mut interner);

        let int = aliases.get("Int").expect("Int alias missing");
        let float = aliases.get("Float").expect("Float alias missing");

        assert!(matches!(interner.get(int), Some(Ty::Int32)));
        assert!(matches!(interner.get(float), Some(Ty::Float32)));
        assert!(aliases.get("String").is_none());
    }
}
