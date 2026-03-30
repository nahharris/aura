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
pub enum CheckedStaticArg {
    Type(String),
    Value(String),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CheckedExpr {
    Ident(String),
    Int(String),
    Float(String),
    Char(String),
    String(String),
    DotIdent {
        name: String,
        payload: Option<Box<CheckedExpr>>,
    },
    Any,
    List(Vec<CheckedExpr>),
    Dict(Vec<(CheckedExpr, CheckedExpr)>),
    Call {
        callee: Box<CheckedExpr>,
        args: Vec<CheckedExpr>,
    },
    MacroApply {
        macro_name: String,
        static_args: Vec<CheckedStaticArg>,
        operand: Box<CheckedExpr>,
    },
    Label {
        label: String,
        expr: Box<CheckedExpr>,
    },
    MultiArm(Vec<CheckedExpr>),
    Coerce {
        from: TyId,
        to: TyId,
        expr: Box<CheckedExpr>,
    },
    Cast {
        from: TyId,
        to: TyId,
        expr: Box<CheckedExpr>,
    },
}

impl CheckedIr {
    pub fn empty() -> Self {
        Self {
            declarations: Vec::new(),
        }
    }
}
