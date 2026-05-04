use std::collections::HashMap;

use aura_frontend::ast::{StaticParam, TypeExpr};

use crate::types::{Ty, TyId, TyInterner};

#[derive(Debug, Clone)]
pub struct TypeAliases {
    aliases: HashMap<String, TypeAlias>,
}

#[derive(Debug, Clone)]
pub enum TypeAlias {
    Concrete(TyId),
    Generic {
        static_params: Vec<StaticParam>,
        body: TypeExpr,
    },
}

impl TypeAliases {
    pub fn with_prelude(interner: &mut TyInterner) -> Self {
        let mut aliases = HashMap::new();
        aliases.insert(
            "Int".to_string(),
            TypeAlias::Concrete(interner.intern(Ty::Int32)),
        );
        aliases.insert(
            "Float".to_string(),
            TypeAlias::Concrete(interner.intern(Ty::Float32)),
        );
        aliases.insert(
            "Any".to_string(),
            TypeAlias::Concrete(interner.intern(Ty::Interface(Vec::new()))),
        );
        Self { aliases }
    }

    pub fn get(&self, name: &str) -> Option<TyId> {
        match self.aliases.get(name) {
            Some(TypeAlias::Concrete(ty)) => Some(*ty),
            Some(TypeAlias::Generic { .. }) | None => None,
        }
    }

    pub fn get_generic(&self, name: &str) -> Option<(Vec<StaticParam>, TypeExpr)> {
        match self.aliases.get(name) {
            Some(TypeAlias::Generic {
                static_params,
                body,
            }) => Some((static_params.clone(), body.clone())),
            Some(TypeAlias::Concrete(_)) | None => None,
        }
    }

    pub fn insert(&mut self, name: impl Into<String>, ty: TyId) {
        self.aliases.insert(name.into(), TypeAlias::Concrete(ty));
    }

    pub fn insert_generic(
        &mut self,
        name: impl Into<String>,
        static_params: Vec<StaticParam>,
        body: TypeExpr,
    ) {
        self.aliases.insert(
            name.into(),
            TypeAlias::Generic {
                static_params,
                body,
            },
        );
    }

    pub fn contains(&self, name: &str) -> bool {
        self.aliases.contains_key(name)
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
        let any = aliases.get("Any").expect("Any alias");
        assert!(matches!(
            interner.get(any),
            Some(Ty::Interface(m)) if m.is_empty()
        ));
        assert!(aliases.get("String").is_none());
    }
}
