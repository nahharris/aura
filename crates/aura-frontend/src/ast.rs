#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Program {
    pub declarations: Vec<Decl>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Decl {
    Macro(MacroDecl),
    Assign { name: String, value: Expr },
    Function(FunctionDecl),
    Use(UseDecl),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MacroDecl {
    pub name: String,
    pub static_params: Vec<StaticParam>,
    pub params: Vec<Param>,
    pub return_type: TypeExpr,
    pub body: Expr,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FunctionDecl {
    pub static_params: Vec<String>,
    pub receiver: Option<TypeExpr>,
    pub name: String,
    pub params: Vec<Param>,
    pub return_type: TypeExpr,
    pub body: Expr,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct UseDecl {
    pub target: String,
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
    Int(String),
    Float(String),
    Ident(String),
    String(String),
    Char(String),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Expr {
    Ident(String),
    Int(String),
    Float(String),
    String(String),
    Char(String),
    DotIdent {
        name: String,
        payload: Option<Box<Expr>>,
    },
    List(Vec<Expr>),
    Dict(Vec<(Expr, Expr)>),
    Closure {
        params: Vec<Param>,
        return_type: Option<TypeExpr>,
    },
    MultiArm(Vec<Arm>),
    Call {
        callee: Box<Expr>,
        static_args: Vec<StaticArg>,
        args: Vec<Expr>,
    },
    MacroApply {
        macro_name: String,
        static_args: Vec<StaticArg>,
        operand: Box<Expr>,
    },
    Label {
        label: String,
        expr: Box<Expr>,
    },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Arm {
    pub patterns: Vec<Pattern>,
    pub body: Expr,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Pattern {
    Wildcard,
    Ident(String),
    DotVariant {
        name: String,
        payload: Option<Box<Pattern>>,
    },
}
