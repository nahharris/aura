//! Token types and source location tracking for the Aura lexer.
//!
//! Every [`Token`] carries a [`Span`] pointing back into the original source
//! text, enabling high-quality error messages throughout the compiler pipeline.
//!
//! # Design Notes
//!
//! Tokens are kept small (`Copy`-able via `Clone`) by storing string content as
//! owned `String` rather than borrowed slices, which avoids lifetime parameters
//! in the parser and compiler. The performance cost is negligible given that
//! lexing is not the bottleneck in any real workload.

use std::fmt;

// ─────────────────────────────────────────────────────────────────────────────
// Source location
// ─────────────────────────────────────────────────────────────────────────────

/// A half-open byte range `[start, end)` within the original source string,
/// together with human-readable line and column numbers (1-indexed).
///
/// Spans are attached to every [`Token`] so that diagnostics can point directly
/// at the offending source text.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub struct Span {
    /// Byte offset of the first character (inclusive).
    pub start: usize,
    /// Byte offset one past the last character (exclusive).
    pub end: usize,
    /// 1-indexed source line of `start`.
    pub line: u32,
    /// 1-indexed source column of `start` (in chars, not bytes).
    pub col: u32,
}

impl Span {
    /// Construct a span from its raw parts.
    #[inline]
    pub fn new(start: usize, end: usize, line: u32, col: u32) -> Self {
        Self {
            start,
            end,
            line,
            col,
        }
    }

    /// Return the length in bytes of the spanned region.
    #[inline]
    pub fn len(&self) -> usize {
        self.end - self.start
    }

    /// Return `true` if this span covers zero bytes.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.start == self.end
    }

    /// Merge two spans, producing a span that covers both.  The spans need not
    /// be adjacent; the result covers `min(start)..max(end)`.
    pub fn merge(self, other: Self) -> Self {
        let start = self.start.min(other.start);
        let end = self.end.max(other.end);
        // Preserve line/col from whichever span starts earlier.
        let (line, col) = if self.start <= other.start {
            (self.line, self.col)
        } else {
            (other.line, other.col)
        };
        Self {
            start,
            end,
            line,
            col,
        }
    }

    /// Create a zero-length dummy span (used for synthetic nodes and tests).
    #[inline]
    pub fn dummy() -> Self {
        Self {
            start: 0,
            end: 0,
            line: 0,
            col: 0,
        }
    }
}

impl fmt::Display for Span {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}:{}", self.line, self.col)
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Token
// ─────────────────────────────────────────────────────────────────────────────

/// A single lexical token produced by the [`Lexer`](crate::lexer::Lexer).
///
/// The token carries both its [`TokenKind`] (what it is) and its [`Span`]
/// (where in the source it appeared).
#[derive(Debug, Clone, PartialEq)]
pub struct Token {
    pub kind: TokenKind,
    pub span: Span,
}

impl Token {
    #[inline]
    pub fn new(kind: TokenKind, span: Span) -> Self {
        Self { kind, span }
    }

    /// Convenience: is this the end-of-file sentinel?
    #[inline]
    pub fn is_eof(&self) -> bool {
        self.kind == TokenKind::Eof
    }
}

impl fmt::Display for Token {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{} at {}", self.kind, self.span)
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// TokenKind
// ─────────────────────────────────────────────────────────────────────────────

/// The complete set of token kinds in the Aura language.
///
/// Variants are grouped by category in declaration order:
/// - **Literals** — integer, float, string (with optional interpolation), bool, null
/// - **Identifiers and special names** — plain identifier, dot-identifier, atom
/// - **Keywords** — reserved words that cannot be identifiers
/// - **Operators** — arithmetic, comparison, logical, assignment, special
/// - **Punctuation** — delimiters and separators
/// - **Synthetic** — `Newline` (implicit semicolon carrier), `Eof`
#[derive(Debug, Clone, PartialEq)]
pub enum TokenKind {
    // ── Literals ──────────────────────────────────────────────────────────────
    /// A decimal integer literal, e.g. `42` or `1_000_000`.
    /// The stored value is the raw source text (digits only, underscores stripped
    /// at the lexer level for the actual numeric value; kept here for diagnostics).
    Int(i64),

    /// A floating-point literal, e.g. `3.14` or `1_000.0`.
    Float(f64),

    /// A string literal, which may contain zero or more interpolation segments.
    ///
    /// `"Hello, $(name)!"` becomes `Str(vec![Raw("Hello, "), Interp(tokens_for_name), Raw("!")])`.
    Str(Vec<StringPart>),

    /// The literal `true`.
    True,

    /// The literal `false`.
    False,

    /// The literal `null`.
    Null,

    // ── Identifiers / special names ───────────────────────────────────────────
    /// A plain identifier, e.g. `foo`, `myVar`, `_unused`.
    Ident(String),

    /// A dot-identifier (`.name`), used for variant constructors, e.g. `.ok`, `.null`, `.some`.
    /// The leading `.` is consumed; the stored string is the bare name.
    DotIdent(String),

    /// An atom label (`'name`), used for labelled scopes / jump targets,
    /// e.g. `'outer`, `'loop1`. The leading `'` is consumed; the stored string
    /// is the bare name.
    Atom(String),

    // ── Keywords ──────────────────────────────────────────────────────────────
    // The `def`-family names (def, defn, deftype, defmacro) are NOT keywords;
    // they are ordinary identifiers that happen to be recognized by the parser.
    // Only the following identifiers are reserved and may not be used as names.
    /// `let`
    Let,
    /// `const`
    Const,
    /// `fn` — kept as a keyword for forward-compat, but `defn` is the preferred form
    Fn,
    /// `type` — kept for forward-compat; `deftype` is the preferred form
    Type,
    /// `macro` — kept for forward-compat; `defmacro` is the preferred form
    Macro,
    /// `pub`
    Pub,
    /// `use`
    Use,
    /// `return`
    Return,
    /// `break`
    Break,
    /// `continue`
    Continue,
    /// `self` — implicit receiver in methods (not truly reserved but treated specially)
    SelfKw,

    // ── Operators ─────────────────────────────────────────────────────────────
    /// `+`
    Plus,
    /// `-`
    Minus,
    /// `*`
    Star,
    /// `/`
    Slash,
    /// `%`
    Percent,
    /// `=`  (assignment / named-arg separator / dict key-value)
    Eq,
    /// `==`
    EqEq,
    /// `!=`
    BangEq,
    /// `<`
    Lt,
    /// `>`
    Gt,
    /// `<=`
    LtEq,
    /// `>=`
    GtEq,
    /// `&&`
    AmpAmp,
    /// `||`
    PipePipe,
    /// `!`
    Bang,
    /// `++`  (post-increment)
    PlusPlus,
    /// `--`  (post-decrement)
    MinusMinus,
    /// `!!`  (force-unwrap)
    BangBang,
    /// `?.`  (safe navigation)
    QuestionDot,
    /// `?:`  (Elvis operator)
    QuestionColon,
    /// `..`  (range / spread in destructuring)
    DotDot,
    /// `.`   (field/method access)
    Dot,
    /// `:`   (type annotation / cast)
    Colon,
    /// `->`  (closure arrow, return-type arrow)
    Arrow,
    /// `~`   (guard separator in multi-arm closures)
    Tilde,

    // ── Punctuation ───────────────────────────────────────────────────────────
    /// `(`
    LParen,
    /// `)`
    RParen,
    /// `{`
    LBrace,
    /// `}`
    RBrace,
    /// `[`
    LBracket,
    /// `]`
    RBracket,
    /// `,`
    Comma,
    /// `;`
    Semicolon,
    /// `@`  (library reference prefix in `use` paths, e.g. `@stl`)
    At,

    // ── Synthetic ────────────────────────────────────────────────────────────
    /// A newline that immediately follows a `}` and is treated as a `;` by the
    /// implicit-semicolon rule (see DESIGN.md §Whitespace).  The parser handles
    /// `Newline` tokens identically to `Semicolon` in statement-terminal position.
    Newline,

    /// End-of-file sentinel.  Always the last token in the stream.
    Eof,
}

impl fmt::Display for TokenKind {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TokenKind::Int(n) => write!(f, "integer `{n}`"),
            TokenKind::Float(n) => write!(f, "float `{n}`"),
            TokenKind::Str(_) => write!(f, "string literal"),
            TokenKind::True => write!(f, "`true`"),
            TokenKind::False => write!(f, "`false`"),
            TokenKind::Null => write!(f, "`null`"),
            TokenKind::Ident(s) => write!(f, "identifier `{s}`"),
            TokenKind::DotIdent(s) => write!(f, "`.{s}`"),
            TokenKind::Atom(s) => write!(f, "atom `'{s}`"),
            TokenKind::Let => write!(f, "`let`"),
            TokenKind::Const => write!(f, "`const`"),
            TokenKind::Fn => write!(f, "`fn`"),
            TokenKind::Type => write!(f, "`type`"),
            TokenKind::Macro => write!(f, "`macro`"),
            TokenKind::Pub => write!(f, "`pub`"),
            TokenKind::Use => write!(f, "`use`"),
            TokenKind::Return => write!(f, "`return`"),
            TokenKind::Break => write!(f, "`break`"),
            TokenKind::Continue => write!(f, "`continue`"),
            TokenKind::SelfKw => write!(f, "`self`"),
            TokenKind::Plus => write!(f, "`+`"),
            TokenKind::Minus => write!(f, "`-`"),
            TokenKind::Star => write!(f, "`*`"),
            TokenKind::Slash => write!(f, "`/`"),
            TokenKind::Percent => write!(f, "`%`"),
            TokenKind::Eq => write!(f, "`=`"),
            TokenKind::EqEq => write!(f, "`==`"),
            TokenKind::BangEq => write!(f, "`!=`"),
            TokenKind::Lt => write!(f, "`<`"),
            TokenKind::Gt => write!(f, "`>`"),
            TokenKind::LtEq => write!(f, "`<=`"),
            TokenKind::GtEq => write!(f, "`>=`"),
            TokenKind::AmpAmp => write!(f, "`&&`"),
            TokenKind::PipePipe => write!(f, "`||`"),
            TokenKind::Bang => write!(f, "`!`"),
            TokenKind::PlusPlus => write!(f, "`++`"),
            TokenKind::MinusMinus => write!(f, "`--`"),
            TokenKind::BangBang => write!(f, "`!!`"),
            TokenKind::QuestionDot => write!(f, "`?.`"),
            TokenKind::QuestionColon => write!(f, "`?:`"),
            TokenKind::DotDot => write!(f, "`..`"),
            TokenKind::Dot => write!(f, "`.`"),
            TokenKind::Colon => write!(f, "`:`"),
            TokenKind::Arrow => write!(f, "`->`"),
            TokenKind::Tilde => write!(f, "`~`"),
            TokenKind::LParen => write!(f, "`(`"),
            TokenKind::RParen => write!(f, "`)`"),
            TokenKind::LBrace => write!(f, "`{{`"),
            TokenKind::RBrace => write!(f, "`}}`"),
            TokenKind::LBracket => write!(f, "`[`"),
            TokenKind::RBracket => write!(f, "`]`"),
            TokenKind::Comma => write!(f, "`,`"),
            TokenKind::Semicolon => write!(f, "`;`"),
            TokenKind::At => write!(f, "`@`"),
            TokenKind::Newline => write!(f, "newline (implicit `;`)"),
            TokenKind::Eof => write!(f, "end of file"),
        }
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// String interpolation
// ─────────────────────────────────────────────────────────────────────────────

/// A single segment of a (potentially interpolated) string literal.
///
/// A string like `"Hello, $(name)! You are $(age) years old."` is represented
/// as three parts:
/// ```text
/// [Raw("Hello, "), Interp([Ident("name")]), Raw("! You are "), Interp([Ident("age")]), Raw(" years old.")]
/// ```
///
/// Plain strings with no `$()` sites contain exactly one `Raw` part.
#[derive(Debug, Clone, PartialEq)]
pub enum StringPart {
    /// A literal text segment (with escape sequences already resolved).
    Raw(String),
    /// An interpolated expression, represented as the token stream of the
    /// expression inside `$( )`.  The parser will re-parse this token stream
    /// into an AST expression node.
    Interp(Vec<Token>),
}

// ─────────────────────────────────────────────────────────────────────────────
// Keyword table
// ─────────────────────────────────────────────────────────────────────────────

/// Map a bare identifier string to its keyword [`TokenKind`], if it is one.
///
/// Returns `None` for non-reserved identifiers (including `def`-family names
/// like `defn`, `deftype`, `defmacro`, which are not reserved keywords in Aura).
pub fn keyword(s: &str) -> Option<TokenKind> {
    match s {
        "let" => Some(TokenKind::Let),
        "const" => Some(TokenKind::Const),
        "fn" => Some(TokenKind::Fn),
        "type" => Some(TokenKind::Type),
        "macro" => Some(TokenKind::Macro),
        "true" => Some(TokenKind::True),
        "false" => Some(TokenKind::False),
        "null" => Some(TokenKind::Null),
        "pub" => Some(TokenKind::Pub),
        "use" => Some(TokenKind::Use),
        "return" => Some(TokenKind::Return),
        "break" => Some(TokenKind::Break),
        "continue" => Some(TokenKind::Continue),
        "self" => Some(TokenKind::SelfKw),
        _ => None,
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Tests
// ─────────────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_span_merge() {
        let a = Span::new(0, 5, 1, 1);
        let b = Span::new(3, 10, 1, 4);
        let m = a.merge(b);
        assert_eq!(m.start, 0);
        assert_eq!(m.end, 10);
        assert_eq!(m.line, 1);
        assert_eq!(m.col, 1);
    }

    #[test]
    fn test_keyword_recognition() {
        assert_eq!(keyword("let"), Some(TokenKind::Let));
        assert_eq!(keyword("const"), Some(TokenKind::Const));
        assert_eq!(keyword("true"), Some(TokenKind::True));
        assert_eq!(keyword("false"), Some(TokenKind::False));
        assert_eq!(keyword("null"), Some(TokenKind::Null));
        // def-family are NOT reserved keywords
        assert_eq!(keyword("defn"), None);
        assert_eq!(keyword("deftype"), None);
        assert_eq!(keyword("defmacro"), None);
        assert_eq!(keyword("def"), None);
        // regular identifiers
        assert_eq!(keyword("foo"), None);
        assert_eq!(keyword("myVar"), None);
    }

    #[test]
    fn test_token_display() {
        assert_eq!(format!("{}", TokenKind::Plus), "`+`");
        assert_eq!(
            format!("{}", TokenKind::Ident("foo".into())),
            "identifier `foo`"
        );
        assert_eq!(
            format!("{}", TokenKind::Atom("outer".into())),
            "atom `'outer`"
        );
        assert_eq!(format!("{}", TokenKind::DotIdent("ok".into())), "`.ok`");
    }
}
