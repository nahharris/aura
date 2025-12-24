use std::fmt;

#[derive(Debug, Clone, PartialEq)]
pub enum Stmt {
    Let { assignments: Vec<(String, Expr)> },
    Const { assignments: Vec<(String, Expr)> },
    Fn(FnDecl),
    Type(TypeDecl),
    Macro(MacroDecl),
    Expr(Expr),
}

#[derive(Debug, Clone, PartialEq)]
pub struct FnDecl {
    pub name: String,
    pub params: Vec<Param>,
    pub return_type: Option<String>, // Simplified for now
    pub body: Block,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Param {
    pub name: String,
    pub label: Option<String>,
    pub ty: Option<String>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TypeDecl {
    pub name: String,
    // Simplified type def
}

#[derive(Debug, Clone, PartialEq)]
pub struct MacroDecl {
    pub name: String,
}

#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    Literal(Literal),
    Identifier(String),
    DotIdentifier(String), // .ok, .break
    
    // Operation nodes
    BinaryOp {
        lhs: Box<Expr>,
        op: BinaryOp,
        rhs: Box<Expr>,
    },
    UnaryOp {
        op: UnaryOp,
        expr: Box<Expr>,
    },

    // Function logic
    Call {
        func: Box<Expr>,
        args: Vec<Argument>,
        trailing: Vec<TrailingLambda>, 
    },
    Block(Block),

    // Collections
    List(Vec<Expr>),
    Tuple(Vec<Expr>),

    // Control Flow (Optimized Built-ins)
    If {
        cond: Box<Expr>,
        then_block: Box<Block>,
        else_block: Option<Box<Block>>,
    },
    While {
        cond: Box<Expr>,
        body: Box<Block>,
    },
    Loop {
        body: Box<Block>,
    },
}

#[derive(Debug, Clone, PartialEq)]
pub struct Block {
    pub stmts: Vec<Stmt>,
    pub final_expr: Option<Box<Expr>>,
}

#[derive(Debug, Clone, PartialEq)]
pub struct Argument {
    pub label: Option<String>,
    pub value: Expr,
}

#[derive(Debug, Clone, PartialEq)]
pub struct TrailingLambda {
    pub label: Option<String>,
    pub lambda: Block, // Closures are blocks in this AST simplification
}

#[derive(Debug, Clone, PartialEq)]
pub enum Literal {
    Int(i64),
    Float(f64),
    String(String),
    Bool(bool),
    Null,
}

#[derive(Debug, Clone, PartialEq)]
pub enum BinaryOp {
    Add, Sub, Mul, Div,
    Eq, Neq, Lt, Gt, Le, Ge,
    And, Or,
    Assign, // =
}

#[derive(Debug, Clone, PartialEq)]
pub enum UnaryOp {
    Neg, Not,
}

impl fmt::Display for BinaryOp {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            BinaryOp::Add => write!(f, "+"),
            BinaryOp::Sub => write!(f, "-"),
            BinaryOp::Mul => write!(f, "*"),
            BinaryOp::Div => write!(f, "/"),
            BinaryOp::Eq => write!(f, "=="),
            BinaryOp::Neq => write!(f, "!="),
            BinaryOp::Lt => write!(f, "<"),
            BinaryOp::Gt => write!(f, ">"),
            BinaryOp::Le => write!(f, "<="),
            BinaryOp::Ge => write!(f, ">="),
            BinaryOp::And => write!(f, "&&"),
            BinaryOp::Or => write!(f, "||"),
            BinaryOp::Assign => write!(f, "="),
        }
    }
}

