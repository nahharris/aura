#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Program {
    pub declarations: Vec<Decl>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Decl {
    Macro(MacroDecl),
    Assign { name: String, value: Expr },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MacroDecl {
    pub name: String,
    pub static_params: Vec<StaticParam>,
    pub params: Vec<Param>,
    pub return_type: TypeExpr,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct StaticParam {
    pub name: String,
    pub kind: StaticParamKind,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StaticParamKind {
    Type,
    Constraint(TypeExpr),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Param {
    pub name: String,
    pub ty: TypeExpr,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TypeExpr {
    Named { name: String, args: Vec<StaticArg> },
    Static(Box<TypeExpr>),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StaticArg {
    Type(TypeExpr),
    Value(StaticValueExpr),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum StaticValueExpr {
    Int(i64),
    Ident(String),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expr {
    Ident(String),
    Int(i64),
    Closure {
        params: Vec<Param>,
        return_type: Option<TypeExpr>,
    },
    MacroApply {
        macro_name: String,
        static_args: Vec<StaticArg>,
        operand: Box<Expr>,
    },
}
