#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Span {
    pub start: usize,
    pub end: usize,
    pub line: usize,
    pub column: usize,
}

impl From<Span> for aura_diagnostics::Span {
    fn from(value: Span) -> Self {
        Self {
            start: value.start,
            end: value.end,
            line: value.line,
            column: value.column,
        }
    }
}

impl From<aura_diagnostics::Span> for Span {
    fn from(value: aura_diagnostics::Span) -> Self {
        Self {
            start: value.start,
            end: value.end,
            line: value.line,
            column: value.column,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum TokenKind {
    Ident(String),
    Int(String),
    Float(String),
    String(String),
    Char(String),
    Defmacro,
    Arrow,
    Ellipsis,
    Colon,
    Comma,
    Dot,
    Eq,
    Semi,
    Tilde,
    Underscore,
    LParen,
    RParen,
    LBrace,
    RBrace,
    LBracket,
    RBracket,
    Plus,
    Minus,
    Star,
    Slash,
    Percent,
    PlusPlus,
    MinusMinus,
    EqEq,
    NotEq,
    Lt,
    Lte,
    Gt,
    Gte,
    PipePipe,
    AmpAmp,
    QuestionColon,
    QuestionDot,
    BangBang,
    Range,
    Eof,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Token {
    pub kind: TokenKind,
    pub span: Span,
}

impl Token {
    pub fn new(kind: TokenKind, span: Span) -> Self {
        Self { kind, span }
    }
}
