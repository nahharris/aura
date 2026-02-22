//! Abstract Syntax Tree (AST) node types for the Aura language.
//!
//! The AST is the output of the parser and the input to the compiler.
//! Every node carries a [`Span`] so that the compiler and later the VM can
//! produce error messages that point back into the original source text.
//!
//! # Design Principles
//!
//! - **Completeness**: every syntactic construct in the language spec has a
//!   corresponding AST representation.
//! - **Flatness**: the tree is deliberately shallow.  Complex sub-trees (e.g.,
//!   multi-arm closures) are represented as `Vec` of a small helper type rather
//!   than deeply nested node trees.
//! - **No lifetimes**: all strings are owned (`String`) so the AST can be freely
//!   moved and stored without tying its lifetime to the source text.
//! - **Span everywhere**: every major node carries a `span: Span` field for
//!   diagnostics.

use crate::token::{Span, StringPart};

// ─────────────────────────────────────────────────────────────────────────────
// Top-level program
// ─────────────────────────────────────────────────────────────────────────────

/// A parsed Aura source file.
///
/// A program is a flat sequence of top-level items.  Each item is either a
/// module import (`use`) or a declaration.
#[derive(Debug, Clone, PartialEq)]
pub struct Program {
    /// The items in declaration order.
    pub items: Vec<Item>,
    /// Span covering the whole file (or [`Span::dummy`] when unavailable).
    pub span: Span,
}

/// A top-level item in an Aura source file.
#[derive(Debug, Clone, PartialEq)]
pub enum Item {
    /// `use (x, y) = "path";` — module import with optional destructuring.
    Use(UseDecl),
    /// Any declaration: `def`, `defn`, `deftype`, `defmacro`, or a `pub`-prefixed one.
    Decl(Decl),
}

// ─────────────────────────────────────────────────────────────────────────────
// Import declarations
// ─────────────────────────────────────────────────────────────────────────────

/// A `use` import declaration.
///
/// ```aura
/// use (println, print) = "@stl/io";    // destructuring import
/// use io = "@stl/io";                  // namespace import
/// use (helper) = "./utils";            // relative path
/// ```
///
/// The `path` is a string literal that may:
/// - Start with `@name/` — library reference resolved via the library lookup path.
/// - Start with `./` or `../` — relative path from the importing file's directory.
#[derive(Debug, Clone, PartialEq)]
pub struct UseDecl {
    /// The import pattern: what names to bring into scope.
    pub pattern: UsePattern,
    /// The module path string (without quotes).
    pub path: String,
    pub span: Span,
}

/// The left-hand side of a `use` declaration.
#[derive(Debug, Clone, PartialEq)]
pub enum UsePattern {
    /// `use (x, y, z) = "path"` — import and destructure specific names.
    Destructure(Vec<String>),
    /// `use name = "path"` — import as a namespace binding.
    Namespace(String),
}

// ─────────────────────────────────────────────────────────────────────────────
// Declarations
// ─────────────────────────────────────────────────────────────────────────────

/// A module-level declaration, optionally prefixed with `pub`.
#[derive(Debug, Clone, PartialEq)]
pub struct Decl {
    /// Whether this declaration is publicly exported.
    pub public: bool,
    /// The declaration kind.
    pub kind: DeclKind,
    pub span: Span,
}

/// The concrete kind of a module-level declaration.
#[derive(Debug, Clone, PartialEq)]
pub enum DeclKind {
    /// `def name = expr` — a module-level constant.
    Def(DefDecl),
    /// `defn name(params) -> RetType { body }` — a named function or method.
    Defn(DefnDecl),
    /// `deftype Name(fields)` — a named product type.
    Deftype(DeftypeDecl),
    /// `defmacro name(params) -> RetType { body }` — a compile-time macro.
    /// The body is stored as an AST but macro expansion is a future feature.
    Defmacro(DefmacroDecl),
}

// ── def ──────────────────────────────────────────────────────────────────────

/// `def name = expr` — a module-level compile-time constant.
///
/// Multiple bindings may appear in a single `def`:
/// ```aura
/// def pi = 3.14159
/// def MaxRetries = 3
/// ```
#[derive(Debug, Clone, PartialEq)]
pub struct DefDecl {
    /// The bindings: one or more `(name, initializer)` pairs.
    pub bindings: Vec<(String, Expr)>,
    pub span: Span,
}

// ── defn ─────────────────────────────────────────────────────────────────────

/// `defn name(params) -> RetType { body }` — a named function or method.
///
/// The optional receiver prefix (`Point.distanceTo`) makes this a method.
///
/// ```aura
/// defn add(a: Int, b: Int) -> Int { a + b }
/// defn Point.distanceTo(self, other: Point) -> Float { ... }
/// ```
#[derive(Debug, Clone, PartialEq)]
pub struct DefnDecl {
    /// Optional receiver type name for method declarations (e.g., `"Point"`).
    pub receiver: Option<String>,
    /// The function's own name.
    pub name: String,
    /// Optional generic type parameters (e.g., `[T, U]`).
    pub type_params: Vec<String>,
    /// The parameter list.
    pub params: Vec<Param>,
    /// Optional declared return type.
    pub return_type: Option<TypeExpr>,
    /// The function body.
    pub body: Block,
    pub span: Span,
}

/// A single parameter in a function signature.
///
/// Aura parameters support:
/// - A bare internal name: `x`
/// - An internal name with type annotation: `x: Int`
/// - An internal name with external label: `internal external_label: Type`
///
/// The external label is the name used at the call site; the internal name is
/// used inside the function body.
#[derive(Debug, Clone, PartialEq)]
pub struct Param {
    /// The name used inside the function body.
    pub internal: String,
    /// The label used at call sites (if different from internal).
    pub label: Option<String>,
    /// Optional declared type.
    pub ty: Option<TypeExpr>,
    pub span: Span,
}

// ── deftype ───────────────────────────────────────────────────────────────────

/// `deftype Name(field: Type, ...)` — a named product type (struct).
///
/// ```aura
/// deftype Point(x: Int, y: Int)
/// deftype Pair[A, B](first: A, second: B)
/// ```
///
/// The compiler automatically generates:
/// - A constructor function `Name(field = val, ...)`.
/// - Field accessors `instance.field`.
#[derive(Debug, Clone, PartialEq)]
pub struct DeftypeDecl {
    /// The type name.
    pub name: String,
    /// Optional generic type parameters.
    pub type_params: Vec<String>,
    /// The fields of the struct.
    pub fields: Vec<TypedField>,
    pub span: Span,
}

/// A field in a `deftype` declaration (or an anonymous struct literal).
#[derive(Debug, Clone, PartialEq)]
pub struct TypedField {
    pub name: String,
    pub ty: TypeExpr,
    pub span: Span,
}

// ── defmacro ─────────────────────────────────────────────────────────────────

/// `defmacro name(params) -> RetType { body }` — a compile-time macro declaration.
///
/// Macro bodies receive unevaluated `Expr[T]` arguments and produce AST nodes.
/// In this implementation, `defmacro` is parsed and stored but not expanded at
/// compile time — that is a future feature.
#[derive(Debug, Clone, PartialEq)]
pub struct DefmacroDecl {
    pub name: String,
    pub type_params: Vec<String>,
    pub params: Vec<Param>,
    pub return_type: Option<TypeExpr>,
    pub body: Option<Block>,
    pub span: Span,
}

// ─────────────────────────────────────────────────────────────────────────────
// Type expressions
// ─────────────────────────────────────────────────────────────────────────────

/// A type expression as written in the source.
///
/// ```aura
/// Int
/// List[T]
/// Dict[String, Int]
/// Func[Int, Bool]
/// (Int, String)       // tuple type
/// (x: Int, y: Float)  // named-field tuple (struct type)
/// ```
#[derive(Debug, Clone, PartialEq)]
pub enum TypeExpr {
    /// A named type, optionally with generic arguments: `Int`, `List[T]`, `Dict[K, V]`.
    Named {
        name: String,
        args: Vec<TypeExpr>,
        span: Span,
    },
    /// A positional tuple type: `(Int, String, Bool)`.
    Tuple(Vec<TypeExpr>, Span),
    /// A named-field tuple (struct) type: `(x: Int, y: Float)`.
    Struct(Vec<TypedField>, Span),
}

impl TypeExpr {
    pub fn span(&self) -> Span {
        match self {
            TypeExpr::Named { span, .. } => *span,
            TypeExpr::Tuple(_, span) => *span,
            TypeExpr::Struct(_, span) => *span,
        }
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Statements
// ─────────────────────────────────────────────────────────────────────────────

/// A statement inside a block (function body, `if` branch, loop body, etc.).
#[derive(Debug, Clone, PartialEq)]
pub enum Stmt {
    /// `let x = expr, y = expr;` — mutable local binding(s).
    Let(LetStmt),
    /// `const x = expr;` — immutable local binding.
    Const(ConstStmt),
    /// `return value` or `return 'label value` — exit a scope with a value.
    Return(ReturnStmt),
    /// `break` or `break 'label value` — exit a loop.
    Break(BreakStmt),
    /// `continue` or `continue 'label` — begin next iteration.
    Continue(ContinueStmt),
    /// An expression used as a statement (value discarded unless it is the
    /// final expression in a block).
    Expr(ExprStmt),
}

impl Stmt {
    pub fn span(&self) -> Span {
        match self {
            Stmt::Let(s) => s.span,
            Stmt::Const(s) => s.span,
            Stmt::Return(s) => s.span,
            Stmt::Break(s) => s.span,
            Stmt::Continue(s) => s.span,
            Stmt::Expr(s) => s.span,
        }
    }
}

// ── let / const ───────────────────────────────────────────────────────────────

/// `let x = expr, y = expr;`
#[derive(Debug, Clone, PartialEq)]
pub struct LetStmt {
    /// One or more `(name, optional_type, initializer)` bindings.
    pub bindings: Vec<LocalBinding>,
    pub span: Span,
}

/// `const x = expr;`
#[derive(Debug, Clone, PartialEq)]
pub struct ConstStmt {
    pub bindings: Vec<LocalBinding>,
    pub span: Span,
}

/// A single `name [: Type] = expr` binding used by `let` and `const`.
#[derive(Debug, Clone, PartialEq)]
pub struct LocalBinding {
    pub name: String,
    pub ty: Option<TypeExpr>,
    pub init: Expr,
    pub span: Span,
}

// ── return / break / continue ─────────────────────────────────────────────────

/// `return value` or `return 'label value`
#[derive(Debug, Clone, PartialEq)]
pub struct ReturnStmt {
    /// Optional explicit jump target label (e.g., `'outer`).
    pub label: Option<String>,
    /// The value to return, or `None` for bare `return` (returns Void).
    pub value: Option<Box<Expr>>,
    pub span: Span,
}

/// `break` / `break value` / `break 'label` / `break 'label value`
#[derive(Debug, Clone, PartialEq)]
pub struct BreakStmt {
    pub label: Option<String>,
    pub value: Option<Box<Expr>>,
    pub span: Span,
}

/// `continue` / `continue 'label`
#[derive(Debug, Clone, PartialEq)]
pub struct ContinueStmt {
    pub label: Option<String>,
    pub span: Span,
}

/// An expression used as a statement.  The semicolon is NOT stored here; it is
/// consumed by the parser.
#[derive(Debug, Clone, PartialEq)]
pub struct ExprStmt {
    pub expr: Expr,
    pub span: Span,
}

// ─────────────────────────────────────────────────────────────────────────────
// Expressions
// ─────────────────────────────────────────────────────────────────────────────

/// An expression — any syntactic construct that produces a value.
#[derive(Debug, Clone, PartialEq)]
pub enum Expr {
    // ── Literals ─────────────────────────────────────────────────────────────
    /// An integer literal: `42`, `1_000_000`.
    Int(i64, Span),
    /// A floating-point literal: `3.14`.
    Float(f64, Span),
    /// A boolean literal: `true` or `false`.
    Bool(bool, Span),
    /// The `null` literal.
    Null(Span),
    /// A string literal, potentially with interpolation segments.
    Str(Vec<StringPart>, Span),

    // ── Names ────────────────────────────────────────────────────────────────
    /// A plain identifier: `foo`, `x`, `add`.
    Ident(String, Span),
    /// A dot-identifier variant constructor: `.ok`, `.null`, `.some`.
    DotIdent(String, Span),
    /// A builtin reference: `builtin("name")` — binds to a native function.
    Builtin { name: String, span: Span },

    // ── Arithmetic / logic ───────────────────────────────────────────────────
    /// A binary operation: `a + b`, `x == y`, `p && q`.
    Binary {
        op: BinOp,
        lhs: Box<Expr>,
        rhs: Box<Expr>,
        span: Span,
    },
    /// A prefix unary operation: `-x`, `!flag`.
    Unary {
        op: UnOp,
        expr: Box<Expr>,
        span: Span,
    },

    // ── Assignment ───────────────────────────────────────────────────────────
    /// Assignment to a declared variable: `x = expr`.
    ///
    /// Note: `let` and `const` declarations are *statements*, not expressions.
    /// This variant only covers re-assignment to an already-declared local.
    Assign {
        /// The assignment target (always an `Ident` or postfix chain ending in
        /// a field/index access in the full language, but we model it as an
        /// arbitrary `Expr` for flexibility).
        target: Box<Expr>,
        value: Box<Expr>,
        span: Span,
    },

    // ── Postfix ──────────────────────────────────────────────────────────────
    /// `expr.field` or `expr.method()` field access.
    FieldAccess {
        object: Box<Expr>,
        field: String,
        span: Span,
    },
    /// `expr[index]` index access.
    Index {
        object: Box<Expr>,
        index: Box<Expr>,
        span: Span,
    },
    /// `expr?.field` safe-navigation: propagates null without panicking.
    SafeNav {
        object: Box<Expr>,
        field: String,
        span: Span,
    },
    /// `expr!!` force-unwrap: panics if the value is null or an error.
    ForceUnwrap { expr: Box<Expr>, span: Span },
    /// `x++` post-increment.
    PostIncrement { target: Box<Expr>, span: Span },
    /// `x--` post-decrement.
    PostDecrement { target: Box<Expr>, span: Span },
    /// `expr : Type` explicit cast.
    Cast {
        expr: Box<Expr>,
        ty: TypeExpr,
        span: Span,
    },
    /// `left ?: right` Elvis operator: `left` if non-null/non-error, else `right`.
    Elvis {
        left: Box<Expr>,
        right: Box<Expr>,
        span: Span,
    },
    /// `start .. end` range expression.
    Range {
        start: Box<Expr>,
        end: Box<Expr>,
        span: Span,
    },

    // ── Calls ─────────────────────────────────────────────────────────────────
    /// A function or macro call.
    ///
    /// ```aura
    /// add(1, 2)
    /// do_stuff(12) task { doWork(); } finally { cleanup(); }
    /// loop { ... }
    /// if (cond) { ... } else { ... }
    /// ```
    Call {
        /// The callable expression (typically an [`Expr::Ident`]).
        callee: Box<Expr>,
        /// Positional and named arguments inside `( )`.
        args: Vec<Arg>,
        /// Trailing closure arguments written outside `( )`.
        trailing: Vec<TrailingArg>,
        span: Span,
    },

    // ── Collections ──────────────────────────────────────────────────────────
    /// A list literal: `[1, 2, 3]`.
    List {
        items: Vec<CollectionItem>,
        span: Span,
    },
    /// A dict literal: `["a" = 1, "b" = 2]` or `[x = 10, y = 20]`.
    Dict { entries: Vec<DictEntry>, span: Span },
    /// A positional tuple: `(1, 2, 3)`.
    Tuple {
        items: Vec<CollectionItem>,
        span: Span,
    },
    /// A named-field struct literal: `(x = 1, y = 2)`.
    Struct { fields: Vec<FieldInit>, span: Span },

    // ── Closures ─────────────────────────────────────────────────────────────
    /// A block / closure expression.
    ///
    /// This covers:
    /// - A bare block: `{ stmt; stmt; expr }`
    /// - A single-arm closure: `{ a: Int, b: Int -> a + b }`
    /// - A multi-arm closure: `{ 0, b -> b, a, 0 -> a, a, b -> a + b }`
    Closure(Closure),

    // ── Blocks ───────────────────────────────────────────────────────────────
    /// A block expression (bare `{ }` with no closure parameters).
    Block(Block),

    // ── Control flow (built-in macro forms) ──────────────────────────────────
    /// `if (cond) { then } else { else }`
    If(IfExpr),
    /// `cases { ~ cond -> expr, ... }`
    Cases(CasesExpr),
    /// `loop { ... }` or `loop while { cond } do { body }`
    Loop(LoopExpr),
}

impl Expr {
    /// Return the span of this expression.
    pub fn span(&self) -> Span {
        match self {
            Expr::Int(_, s) => *s,
            Expr::Float(_, s) => *s,
            Expr::Bool(_, s) => *s,
            Expr::Null(s) => *s,
            Expr::Str(_, s) => *s,
            Expr::Ident(_, s) => *s,
            Expr::DotIdent(_, s) => *s,
            Expr::Builtin { span, .. } => *span,
            Expr::Binary { span, .. } => *span,
            Expr::Unary { span, .. } => *span,
            Expr::Assign { span, .. } => *span,
            Expr::FieldAccess { span, .. } => *span,
            Expr::Index { span, .. } => *span,
            Expr::SafeNav { span, .. } => *span,
            Expr::ForceUnwrap { span, .. } => *span,
            Expr::PostIncrement { span, .. } => *span,
            Expr::PostDecrement { span, .. } => *span,
            Expr::Cast { span, .. } => *span,
            Expr::Elvis { span, .. } => *span,
            Expr::Range { span, .. } => *span,
            Expr::Call { span, .. } => *span,
            Expr::List { span, .. } => *span,
            Expr::Dict { span, .. } => *span,
            Expr::Tuple { span, .. } => *span,
            Expr::Struct { span, .. } => *span,
            Expr::Closure(c) => c.span,
            Expr::Block(b) => b.span,
            Expr::If(i) => i.span,
            Expr::Cases(c) => c.span,
            Expr::Loop(l) => l.span,
        }
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Operator enums
// ─────────────────────────────────────────────────────────────────────────────

/// Binary operators, ordered by precedence group (lowest first) to match the
/// DESIGN.md operator table.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinOp {
    // Prec 2
    Or,
    // Prec 3
    And,
    // Prec 4
    Eq,
    Ne,
    // Prec 5
    Lt,
    Gt,
    Le,
    Ge,
    // Prec 6
    Add,
    Sub,
    // Prec 7
    Mul,
    Div,
    Rem,
}

impl std::fmt::Display for BinOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            BinOp::Or => write!(f, "||"),
            BinOp::And => write!(f, "&&"),
            BinOp::Eq => write!(f, "=="),
            BinOp::Ne => write!(f, "!="),
            BinOp::Lt => write!(f, "<"),
            BinOp::Gt => write!(f, ">"),
            BinOp::Le => write!(f, "<="),
            BinOp::Ge => write!(f, ">="),
            BinOp::Add => write!(f, "+"),
            BinOp::Sub => write!(f, "-"),
            BinOp::Mul => write!(f, "*"),
            BinOp::Div => write!(f, "/"),
            BinOp::Rem => write!(f, "%"),
        }
    }
}

/// Prefix unary operators.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum UnOp {
    /// `-x`
    Neg,
    /// `!x`
    Not,
}

impl std::fmt::Display for UnOp {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            UnOp::Neg => write!(f, "-"),
            UnOp::Not => write!(f, "!"),
        }
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Call arguments
// ─────────────────────────────────────────────────────────────────────────────

/// A single argument in a `( )` argument list.
#[derive(Debug, Clone, PartialEq)]
pub struct Arg {
    /// The optional named-argument label (e.g., `b = 2` → `Some("b")`).
    pub label: Option<String>,
    pub value: Expr,
    pub span: Span,
}

/// A trailing closure argument written outside `( )`.
///
/// ```aura
/// do_stuff(12) task { doWork(); } finally { cleanup(); }
///              ^^^^ label         ^^^^^^^ label
/// ```
///
/// The first trailing closure may have `label = None`.
#[derive(Debug, Clone, PartialEq)]
pub struct TrailingArg {
    /// The parameter label for this trailing closure (e.g., `"task"`, `"finally"`).
    /// `None` for the first (unlabelled) trailing closure.
    pub label: Option<String>,
    /// The block for this trailing closure, which may optionally be labelled
    /// itself with an atom (`'worker: { ... }`).
    pub block: LabelledBlock,
    pub span: Span,
}

// ─────────────────────────────────────────────────────────────────────────────
// Collections
// ─────────────────────────────────────────────────────────────────────────────

/// An item in a list or tuple literal.
///
/// Items may contain inline scoped statements before the value expression:
/// ```aura
/// [let x = 0; x = x + 1; x, 42]
/// ```
#[derive(Debug, Clone, PartialEq)]
pub struct CollectionItem {
    /// Preliminary statements scoped to this item only (e.g., `let x = 0; x++`).
    pub stmts: Vec<Stmt>,
    /// The item's value expression.
    pub value: Expr,
    pub span: Span,
}

/// A key-value entry in a dict literal: `key = value`.
#[derive(Debug, Clone, PartialEq)]
pub struct DictEntry {
    pub key: Expr,
    pub value: Expr,
    pub span: Span,
}

/// A named-field initialiser in a struct literal: `name = value`.
#[derive(Debug, Clone, PartialEq)]
pub struct FieldInit {
    pub name: String,
    pub value: Expr,
    pub span: Span,
}

// ─────────────────────────────────────────────────────────────────────────────
// Closures
// ─────────────────────────────────────────────────────────────────────────────

/// A closure expression: either a single-arm or multi-arm closure.
///
/// Single-arm: `{ a: Int, b: Int -> a + b }` — has exactly one arm with an
/// ordinary parameter list.
///
/// Multi-arm (pattern matching):
/// ```aura
/// {
///     0, b -> b,
///     a, 0 -> a,
///     a, b ~ a > b -> a * b,
///     a, b         -> a / b
/// }
/// ```
#[derive(Debug, Clone, PartialEq)]
pub struct Closure {
    /// The arms of the closure.  A single-arm closure has exactly one element.
    pub arms: Vec<ClosureArm>,
    pub span: Span,
}

/// A single arm in a closure.
///
/// ```text
/// patterns... [~ guard] -> body
/// ```
#[derive(Debug, Clone, PartialEq)]
pub struct ClosureArm {
    /// The pattern(s) for the arm's parameters.  A plain parameter list has
    /// identifier patterns; pattern matching arms may have literal or
    /// tuple patterns.
    pub patterns: Vec<Pattern>,
    /// Optional guard expression.  The arm is only taken if this evaluates to `true`.
    pub guard: Option<Expr>,
    /// The arm body.
    pub body: Expr,
    pub span: Span,
}

/// A pattern used in closure arm matching.
#[derive(Debug, Clone, PartialEq)]
pub enum Pattern {
    /// A wildcard `_` that matches anything and discards the value.
    Wildcard(Span),
    /// A literal pattern: matches the exact value.
    Literal(Expr),
    /// A binding pattern: matches anything and binds to `name`.
    Bind(String, Span),
    /// A tuple pattern: `(p1, p2, p3)`.
    Tuple(Vec<Pattern>, Span),
    /// A dot-identifier variant pattern: `.ok(inner)` or `.null`.
    Variant {
        name: String,
        inner: Option<Box<Pattern>>,
        span: Span,
    },
}

// ─────────────────────────────────────────────────────────────────────────────
// Blocks
// ─────────────────────────────────────────────────────────────────────────────

/// A `{ }` block: a sequence of statements with an optional trailing expression.
///
/// The block's value is the trailing expression, or `Void` if absent.
#[derive(Debug, Clone, PartialEq)]
pub struct Block {
    pub stmts: Vec<Stmt>,
    /// The optional trailing (return) expression.
    pub tail: Option<Box<Expr>>,
    pub span: Span,
}

/// A block that may be prefixed with an atom label: `'outer: { ... }`.
#[derive(Debug, Clone, PartialEq)]
pub struct LabelledBlock {
    /// The atom label, if present (e.g., `"outer"` for `'outer: { ... }`).
    pub label: Option<String>,
    pub block: Block,
    pub span: Span,
}

// ─────────────────────────────────────────────────────────────────────────────
// Built-in control flow AST nodes
// ─────────────────────────────────────────────────────────────────────────────

/// `if (condition) { then } [else { else_branch }]`
///
/// Both branches are treated as zero-argument closures that are inlined at the
/// call site.  The `else` branch is optional; its absence makes the whole `if`
/// return `Void`.
#[derive(Debug, Clone, PartialEq)]
pub struct IfExpr {
    pub condition: Box<Expr>,
    pub then_block: Block,
    /// The `else` block, if present.
    pub else_block: Option<Block>,
    pub span: Span,
}

/// `cases { ~ cond -> expr, ~ cond -> expr, ... }`
///
/// A multi-branch conditional where every arm has only a guard (no patterns).
/// Arms are tried in order; the first whose guard is `true` is taken.
#[derive(Debug, Clone, PartialEq)]
pub struct CasesExpr {
    pub arms: Vec<CasesArm>,
    pub span: Span,
}

/// A single arm in a `cases` expression.
#[derive(Debug, Clone, PartialEq)]
pub struct CasesArm {
    pub guard: Expr,
    pub body: Expr,
    pub span: Span,
}

/// A `loop` expression (either indefinite or conditional).
///
/// ```aura
/// loop { body }                          // indefinite
/// loop while { cond } do { body }        // conditional
/// ```
#[derive(Debug, Clone, PartialEq)]
pub struct LoopExpr {
    /// The optional condition closure (`while` parameter).
    /// `None` means an indefinite loop.
    pub condition: Option<Block>,
    /// The loop body.
    pub body: LabelledBlock,
    pub span: Span,
}

// ─────────────────────────────────────────────────────────────────────────────
// Tests
// ─────────────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_binop_display() {
        assert_eq!(format!("{}", BinOp::Add), "+");
        assert_eq!(format!("{}", BinOp::Mul), "*");
        assert_eq!(format!("{}", BinOp::Or), "||");
        assert_eq!(format!("{}", BinOp::Eq), "==");
    }

    #[test]
    fn test_unop_display() {
        assert_eq!(format!("{}", UnOp::Neg), "-");
        assert_eq!(format!("{}", UnOp::Not), "!");
    }

    #[test]
    fn test_span_on_expr() {
        let span = Span::new(0, 2, 1, 1);
        let expr = Expr::Int(42, span);
        assert_eq!(expr.span(), span);
    }
}
