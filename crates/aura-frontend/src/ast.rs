#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Program {
    pub declarations: Vec<Decl>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Decl {
    Macro(MacroDecl),
    Assign {
        name: String,
        value: Expr,
        doc: Option<DocAttribute>,
    },
    Function(FunctionDecl),
    Use(UseDecl),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DocAttribute {
    pub markdown: String,
    pub symbol_docs: Vec<SymbolDoc>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SymbolDoc {
    pub name: String,
    pub doc: String,
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
    pub static_params: Vec<StaticParam>,
    pub receiver: Option<TypeExpr>,
    pub name: String,
    pub params: Vec<Param>,
    pub return_type: TypeExpr,
    pub body: Expr,
    pub doc: Option<DocAttribute>,
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
    Tuple(Vec<TypeExpr>),
    Struct(Vec<(String, TypeExpr)>),
    Static(Box<TypeExpr>),
    InferHole,
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
    Spanned {
        span: aura_diagnostics::Span,
        expr: Box<Expr>,
    },
    Ident(String),
    Int(String),
    Float(String),
    String(String),
    Char(String),
    DotIdent {
        name: String,
        payload: Option<Box<Expr>>,
    },
    Tuple(Vec<Expr>),
    Struct(Vec<(String, Expr)>),
    List(Vec<Expr>),
    Dict(Vec<(Expr, Expr)>),
    Closure {
        params: Vec<Param>,
        return_type: Option<TypeExpr>,
    },
    Placeholder,
    MultiArm(Vec<Arm>),
    Call {
        callee: Box<Expr>,
        static_args: Vec<StaticArg>,
        args: Vec<Expr>,
        trailing: Vec<LabeledClosureArg>,
    },
    Member {
        object: Box<Expr>,
        field: String,
    },
    MacroApply {
        macro_name: String,
        static_args: Vec<StaticArg>,
        operand: Box<Expr>,
    },
    Binary {
        op: BinaryOp,
        lhs: Box<Expr>,
        rhs: Box<Expr>,
    },
    TypeExpr(TypeExpr),
    Label {
        label: String,
        expr: Box<Expr>,
    },
    Cast {
        expr: Box<Expr>,
        ty: TypeExpr,
    },
}

impl Expr {
    pub fn span(&self) -> Option<aura_diagnostics::Span> {
        match self {
            Expr::Spanned { span, .. } => Some(*span),
            _ => None,
        }
    }

    pub fn unspanned(&self) -> &Expr {
        let mut cur = self;
        while let Expr::Spanned { expr, .. } = cur {
            cur = expr.as_ref();
        }
        cur
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LabeledClosureArg {
    pub label: String,
    pub body: Expr,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinaryOp {
    Elvis,
    Or,
    And,
    Eq,
    Neq,
    Lt,
    Le,
    Gt,
    Ge,
    Range,
    Pipe,
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Colon,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Arm {
    pub patterns: Vec<Pattern>,
    pub guard: Option<Expr>,
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
