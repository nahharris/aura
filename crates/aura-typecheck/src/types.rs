use std::collections::HashMap;

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct TyId(pub usize);

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct FuncParam {
    pub name: Option<String>,
    pub label: Option<String>,
    pub trailing: bool,
    pub ty: TyId,
}

impl FuncParam {
    pub fn positional(ty: TyId) -> Self {
        Self {
            name: None,
            label: None,
            trailing: false,
            ty,
        }
    }

    pub fn named(name: impl Into<String>, ty: TyId) -> Self {
        let name = name.into();
        Self {
            label: Some(name.clone()),
            name: Some(name),
            trailing: false,
            ty,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Ty {
    InferVar(u32),
    GenericParam(String),
    Int8,
    Int16,
    Int32,
    Int64,
    Int128,
    ISize,
    UInt8,
    UInt16,
    UInt32,
    UInt64,
    UInt128,
    USize,
    Float32,
    Float64,
    Bool,
    Char,
    Void,
    Never,
    /// Structural interface type: empty `interface()` is the universal top type (stdlib `Any`).
    Interface(Vec<(String, TyId)>),
    Nominal(String),
    RawAlloc(TyId),
    Slice(TyId),
    Ref(TyId),
    List(TyId),
    Dict { key: TyId, value: TyId },
    Set(TyId),
    Array { item: TyId, size: u64 },
    Func { params: Vec<FuncParam>, ret: TyId },
    Macro { params: Vec<FuncParam>, ret: TyId },
    Tuple(Vec<TyId>),
    Struct(Vec<(String, TyId)>),
    Union(Vec<TyId>),
    InterfaceObject(Vec<(String, TyId)>),
    Enum(Vec<(String, Option<TyId>)>),
}

#[derive(Debug, Default, Clone)]
pub struct TyInterner {
    types: Vec<Ty>,
    index: HashMap<Ty, TyId>,
}

impl TyInterner {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn intern(&mut self, ty: Ty) -> TyId {
        let ty = match ty {
            Ty::Interface(mut members) => {
                members.sort_by(|a, b| a.0.cmp(&b.0));
                Ty::Interface(members)
            }
            other => other,
        };
        if let Some(id) = self.index.get(&ty) {
            return *id;
        }
        let id = TyId(self.types.len());
        self.types.push(ty.clone());
        self.index.insert(ty, id);
        id
    }

    pub fn get(&self, id: TyId) -> Option<&Ty> {
        self.types.get(id.0)
    }

    pub fn prelude_primitives(&mut self) -> PreludeTypeIds {
        PreludeTypeIds {
            int8: self.intern(Ty::Int8),
            int16: self.intern(Ty::Int16),
            int32: self.intern(Ty::Int32),
            int64: self.intern(Ty::Int64),
            int128: self.intern(Ty::Int128),
            isize: self.intern(Ty::ISize),
            uint8: self.intern(Ty::UInt8),
            uint16: self.intern(Ty::UInt16),
            uint32: self.intern(Ty::UInt32),
            uint64: self.intern(Ty::UInt64),
            uint128: self.intern(Ty::UInt128),
            usize: self.intern(Ty::USize),
            float32: self.intern(Ty::Float32),
            float64: self.intern(Ty::Float64),
            bool_: self.intern(Ty::Bool),
            char_: self.intern(Ty::Char),
            void: self.intern(Ty::Void),
            never: self.intern(Ty::Never),
        }
    }

    pub fn fresh_infer_var(&mut self, next: &mut u32) -> TyId {
        let id = self.intern(Ty::InferVar(*next));
        *next += 1;
        id
    }
}

#[derive(Debug, Clone, Copy)]
pub struct PreludeTypeIds {
    pub int8: TyId,
    pub int16: TyId,
    pub int32: TyId,
    pub int64: TyId,
    pub int128: TyId,
    pub isize: TyId,
    pub uint8: TyId,
    pub uint16: TyId,
    pub uint32: TyId,
    pub uint64: TyId,
    pub uint128: TyId,
    pub usize: TyId,
    pub float32: TyId,
    pub float64: TyId,
    pub bool_: TyId,
    pub char_: TyId,
    pub void: TyId,
    pub never: TyId,
}

#[cfg(test)]
mod tests {
    use crate::types::{Ty, TyInterner};

    #[test]
    fn prelude_primitives_include_sized_numeric_types() {
        let mut interner = TyInterner::new();
        let ids = interner.prelude_primitives();

        assert!(matches!(interner.get(ids.int32), Some(Ty::Int32)));
        assert!(matches!(interner.get(ids.float32), Some(Ty::Float32)));
        assert!(matches!(interner.get(ids.float64), Some(Ty::Float64)));
        assert!(matches!(interner.get(ids.uint64), Some(Ty::UInt64)));
    }
}
