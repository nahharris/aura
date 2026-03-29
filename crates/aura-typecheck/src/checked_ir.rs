use crate::types::TyId;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CheckedIr {
    pub declarations: Vec<CheckedDecl>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CheckedDecl {
    pub name: String,
    pub ty: TyId,
    pub value: CheckedExpr,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CheckedExpr {
    Int(String),
    Float(String),
    Char(String),
    String(String),
    Any,
    List(Vec<CheckedExpr>),
    Dict(Vec<(CheckedExpr, CheckedExpr)>),
}

impl CheckedIr {
    pub fn empty() -> Self {
        Self {
            declarations: Vec::new(),
        }
    }
}
