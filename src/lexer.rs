//! Hand-rolled lexer (scanner) for the Aura language.
//!
//! The [`Lexer`] consumes a source string and produces a flat `Vec<Token>`.
//! Tokens carry [`Span`] information for precise error reporting.
//!
//! # Implicit Semicolons
//!
//! Per the language specification, a newline that immediately follows a `}`
//! is treated as a `;`.  The lexer emits a [`TokenKind::Newline`] token in
//! that position so the parser can handle it uniformly.  All other newlines
//! and whitespace are silently skipped.
//!
//! # String Interpolation
//!
//! Interpolated strings (`"Hello, $(name)!"`) are lexed in a single pass.
//! The interpolated sub-expressions are collected as nested `Vec<Token>` stored
//! inside [`StringPart::Interp`].  The parser receives the outer token stream
//! and recursively re-parses the inner token streams for each `$()` site.
//!
//! # Error Handling
//!
//! Lexer errors are collected into an internal list rather than immediately
//! aborting.  This lets the lexer report multiple problems in a single pass.
//! Call [`Lexer::scan`] to get both the token stream and the error list.

use crate::token::{keyword, Span, StringPart, Token, TokenKind};

// ─────────────────────────────────────────────────────────────────────────────
// Lexer struct
// ─────────────────────────────────────────────────────────────────────────────

/// The Aura lexical scanner.
///
/// Construct one with [`Lexer::new`] and then call [`Lexer::scan`] to obtain
/// the full token stream.  The lexer itself is consumed after scanning.
pub struct Lexer<'src> {
    /// The full source text being scanned.
    #[allow(dead_code)]
    src: &'src str,
    /// Iterator over `(byte_offset, char)` pairs.
    chars: std::str::CharIndices<'src>,
    /// The current character and its byte offset, or `None` at EOF.
    current: Option<(usize, char)>,
    /// The *next* character peeked without consuming (for two-character lookahead).
    peeked: Option<(usize, char)>,
    /// Current source line (1-indexed).
    line: u32,
    /// Current source column in *characters* (1-indexed).
    col: u32,
    /// Byte offset of the character immediately after the most recently consumed one.
    /// Used to set `span.end` after consuming a token.
    pos: usize,
    /// Accumulated lex errors.  Non-fatal; scanning continues after recording.
    errors: Vec<LexError>,
}

/// A non-fatal lexical error.  Lexing continues after recording these so
/// the parser sees as many tokens as possible.
#[derive(Debug, Clone)]
pub struct LexError {
    pub message: String,
    pub span: Span,
}

impl<'src> Lexer<'src> {
    /// Create a new lexer for the given source text.
    pub fn new(src: &'src str) -> Self {
        let mut chars = src.char_indices();
        let current = chars.next();
        let peeked = chars.next();
        Self {
            src,
            chars,
            current,
            peeked,
            line: 1,
            col: 1,
            pos: 0,
            errors: Vec::new(),
        }
    }

    /// Run the full scan, returning `(tokens, errors)`.
    ///
    /// `tokens` always ends with an [`TokenKind::Eof`] sentinel.
    /// `errors` is empty on a clean input.
    pub fn scan(mut self) -> (Vec<Token>, Vec<LexError>) {
        let mut tokens = Vec::new();
        // Track whether the previous non-whitespace token was `}` so we can
        // emit an implicit Newline/semicolon when a newline follows.
        let mut prev_was_rbrace = false;

        loop {
            // Skip whitespace and comments, but watch for newlines after `}`.
            let saw_newline = self.skip_whitespace_and_comments();

            if saw_newline && prev_was_rbrace {
                // Emit an implicit semicolon token at the current position.
                let span = Span::new(self.pos, self.pos, self.line, self.col);
                tokens.push(Token::new(TokenKind::Newline, span));
            }

            if self.current.is_none() {
                let span = Span::new(self.pos, self.pos, self.line, self.col);
                tokens.push(Token::new(TokenKind::Eof, span));
                break;
            }

            let tok = self.next_token();
            prev_was_rbrace = tok.kind == TokenKind::RBrace;
            tokens.push(tok);
        }

        (tokens, self.errors)
    }

    // ─────────────────────────────────────────────────────────────────────────
    // Internal scanning helpers
    // ─────────────────────────────────────────────────────────────────────────

    /// Return the current character without consuming it.
    #[inline]
    fn peek(&self) -> Option<char> {
        self.current.map(|(_, c)| c)
    }

    /// Return the next character without consuming either current or next.
    #[inline]
    fn peek2(&self) -> Option<char> {
        self.peeked.map(|(_, c)| c)
    }

    /// Consume the current character and advance the iterator.
    /// Updates line/column counters and `self.pos`.
    fn advance(&mut self) -> Option<char> {
        let result = self.current;
        self.current = self.peeked;
        self.peeked = self.chars.next();

        if let Some((offset, ch)) = result {
            // Update position to the byte offset AFTER this character.
            self.pos = offset + ch.len_utf8();
            if ch == '\n' {
                self.line += 1;
                self.col = 1;
            } else {
                self.col += 1;
            }
            Some(ch)
        } else {
            None
        }
    }

    /// Consume the current character only if it equals `expected`.
    /// Returns whether the character was consumed.
    fn eat(&mut self, expected: char) -> bool {
        if self.peek() == Some(expected) {
            self.advance();
            true
        } else {
            false
        }
    }

    /// Build a [`Span`] that begins at `start_pos/start_line/start_col` and
    /// ends at the current `self.pos`.
    #[inline]
    fn make_span(&self, start_pos: usize, start_line: u32, start_col: u32) -> Span {
        Span::new(start_pos, self.pos, start_line, start_col)
    }

    /// Skip all whitespace and `//` line comments.
    ///
    /// Returns `true` if at least one `\n` character was encountered (used to
    /// detect implicit semicolons after `}`).
    fn skip_whitespace_and_comments(&mut self) -> bool {
        let mut saw_newline = false;
        loop {
            match self.peek() {
                Some(' ' | '\t' | '\r') => {
                    self.advance();
                }
                Some('\n') => {
                    saw_newline = true;
                    self.advance();
                }
                Some('/') if self.peek2() == Some('/') => {
                    // Consume until end-of-line.
                    while self.peek().map(|c| c != '\n').unwrap_or(false) {
                        self.advance();
                    }
                }
                _ => break,
            }
        }
        saw_newline
    }

    /// Lex the next token from the current position.
    /// Precondition: `self.current` is `Some` (not EOF).
    fn next_token(&mut self) -> Token {
        let start_pos = self.current.map(|(o, _)| o).unwrap_or(self.pos);
        let start_line = self.line;
        let start_col = self.col;

        let ch = self.advance().expect("next_token called at EOF");

        let kind = match ch {
            // ── Single-character unambiguous tokens ──────────────────────────
            '(' => TokenKind::LParen,
            ')' => TokenKind::RParen,
            '{' => TokenKind::LBrace,
            '}' => TokenKind::RBrace,
            '[' => TokenKind::LBracket,
            ']' => TokenKind::RBracket,
            ',' => TokenKind::Comma,
            ';' => TokenKind::Semicolon,
            '@' => TokenKind::At,
            '*' => TokenKind::Star,
            '%' => TokenKind::Percent,
            '~' => TokenKind::Tilde,

            // ── Multi-character or overloaded tokens ─────────────────────────
            '+' => {
                if self.eat('+') {
                    TokenKind::PlusPlus
                } else {
                    TokenKind::Plus
                }
            }
            '-' => {
                if self.eat('-') {
                    TokenKind::MinusMinus
                } else if self.eat('>') {
                    TokenKind::Arrow
                } else {
                    TokenKind::Minus
                }
            }
            '!' => {
                if self.eat('!') {
                    TokenKind::BangBang
                } else if self.eat('=') {
                    TokenKind::BangEq
                } else {
                    TokenKind::Bang
                }
            }
            '=' => {
                if self.eat('=') {
                    TokenKind::EqEq
                } else {
                    TokenKind::Eq
                }
            }
            '<' => {
                if self.eat('=') {
                    TokenKind::LtEq
                } else {
                    TokenKind::Lt
                }
            }
            '>' => {
                if self.eat('=') {
                    TokenKind::GtEq
                } else {
                    TokenKind::Gt
                }
            }
            '&' => {
                if self.eat('&') {
                    TokenKind::AmpAmp
                } else {
                    let span = self.make_span(start_pos, start_line, start_col);
                    self.errors.push(LexError {
                        message: "unexpected character `&`; did you mean `&&`?".into(),
                        span,
                    });
                    // Recover by returning a dummy token.
                    TokenKind::Bang // placeholder
                }
            }
            '|' => {
                if self.eat('|') {
                    TokenKind::PipePipe
                } else {
                    let span = self.make_span(start_pos, start_line, start_col);
                    self.errors.push(LexError {
                        message: "unexpected character `|`; did you mean `||`?".into(),
                        span,
                    });
                    TokenKind::Bang // placeholder
                }
            }
            '?' => {
                if self.eat('.') {
                    TokenKind::QuestionDot
                } else if self.eat(':') {
                    TokenKind::QuestionColon
                } else {
                    let span = self.make_span(start_pos, start_line, start_col);
                    self.errors.push(LexError {
                        message: "unexpected character `?`; expected `?.` or `?:`".into(),
                        span,
                    });
                    TokenKind::Bang // placeholder
                }
            }
            '.' => {
                if self.eat('.') {
                    TokenKind::DotDot
                } else if self
                    .peek()
                    .map(|c| c.is_alphabetic() || c == '_')
                    .unwrap_or(false)
                {
                    // dot-identifier: `.name`
                    let name = self.scan_ident_tail();
                    TokenKind::DotIdent(name)
                } else {
                    TokenKind::Dot
                }
            }
            ':' => TokenKind::Colon,
            '/' => TokenKind::Slash,

            // ── Atom: 'identifier ────────────────────────────────────────────
            '\'' => {
                if self
                    .peek()
                    .map(|c| c.is_alphabetic() || c == '_')
                    .unwrap_or(false)
                {
                    let name = self.scan_ident_tail();
                    TokenKind::Atom(name)
                } else {
                    let span = self.make_span(start_pos, start_line, start_col);
                    self.errors.push(LexError {
                        message: "expected identifier after `'` for atom label".into(),
                        span,
                    });
                    TokenKind::Bang // placeholder
                }
            }

            // ── String literal ───────────────────────────────────────────────
            '"' => self.scan_string(start_pos, start_line, start_col),

            // ── Number literals ──────────────────────────────────────────────
            c if c.is_ascii_digit() => self.scan_number(c, start_pos, start_line, start_col),

            // ── Identifiers and keywords ─────────────────────────────────────
            c if c.is_alphabetic() || c == '_' => {
                let mut ident = String::new();
                ident.push(c);
                let tail = self.scan_ident_tail();
                ident.push_str(&tail);
                keyword(&ident).unwrap_or(TokenKind::Ident(ident))
            }

            other => {
                let span = self.make_span(start_pos, start_line, start_col);
                self.errors.push(LexError {
                    message: format!("unexpected character `{other}`"),
                    span,
                });
                // Emit a dummy token and continue.
                TokenKind::Bang
            }
        };

        let span = self.make_span(start_pos, start_line, start_col);
        Token::new(kind, span)
    }

    // ─────────────────────────────────────────────────────────────────────────
    // Sub-scanners
    // ─────────────────────────────────────────────────────────────────────────

    /// Scan the tail of an identifier (everything after the first character).
    /// Returns the collected characters as a `String`, NOT including the first char.
    fn scan_ident_tail(&mut self) -> String {
        let mut s = String::new();
        while let Some(c) = self.peek() {
            if c.is_alphanumeric() || c == '_' {
                s.push(c);
                self.advance();
            } else {
                break;
            }
        }
        s
    }

    /// Scan a numeric literal starting with the character `first`.
    ///
    /// Handles:
    /// - Plain integers: `42`, `1_000_000`
    /// - Floats: `3.14`, `1_000.0`
    ///
    /// The `_` separator is ignored in the numeric value but consumed.
    fn scan_number(
        &mut self,
        first: char,
        start_pos: usize,
        start_line: u32,
        start_col: u32,
    ) -> TokenKind {
        let mut raw = String::new();
        raw.push(first);

        // Integer part.
        while let Some(c) = self.peek() {
            if c.is_ascii_digit() || c == '_' {
                if c != '_' {
                    raw.push(c);
                }
                self.advance();
            } else {
                break;
            }
        }

        // Check for fractional part — must have both sides of `.`.
        if self.peek() == Some('.') && self.peek2().map(|c| c.is_ascii_digit()).unwrap_or(false) {
            raw.push('.');
            self.advance(); // consume '.'
            while let Some(c) = self.peek() {
                if c.is_ascii_digit() || c == '_' {
                    if c != '_' {
                        raw.push(c);
                    }
                    self.advance();
                } else {
                    break;
                }
            }
            match raw.parse::<f64>() {
                Ok(v) => TokenKind::Float(v),
                Err(_) => {
                    let span = self.make_span(start_pos, start_line, start_col);
                    self.errors.push(LexError {
                        message: format!("invalid float literal `{raw}`"),
                        span,
                    });
                    TokenKind::Float(0.0)
                }
            }
        } else {
            match raw.parse::<i64>() {
                Ok(v) => TokenKind::Int(v),
                Err(_) => {
                    let span = self.make_span(start_pos, start_line, start_col);
                    self.errors.push(LexError {
                        message: format!("integer literal `{raw}` overflows i64"),
                        span,
                    });
                    TokenKind::Int(0)
                }
            }
        }
    }

    /// Scan a string literal that begins after the opening `"` has been consumed.
    ///
    /// Handles:
    /// - Standard escape sequences: `\n`, `\t`, `\\`, `\"`, `\r`, `\0`
    /// - Interpolation sites: `$( expr_tokens )`
    ///   The content between `$(` and `)` is recursively lexed and stored as
    ///   a [`StringPart::Interp`] containing its own token stream.
    fn scan_string(&mut self, start_pos: usize, start_line: u32, start_col: u32) -> TokenKind {
        let mut parts: Vec<StringPart> = Vec::new();
        let mut current_raw = String::new();

        loop {
            match self.peek() {
                None => {
                    let span = self.make_span(start_pos, start_line, start_col);
                    self.errors.push(LexError {
                        message: "unterminated string literal".into(),
                        span,
                    });
                    break;
                }
                Some('"') => {
                    self.advance(); // consume closing `"`
                    break;
                }
                Some('\\') => {
                    self.advance(); // consume `\`
                    match self.advance() {
                        Some('n') => current_raw.push('\n'),
                        Some('t') => current_raw.push('\t'),
                        Some('r') => current_raw.push('\r'),
                        Some('0') => current_raw.push('\0'),
                        Some('\\') => current_raw.push('\\'),
                        Some('"') => current_raw.push('"'),
                        Some(c) => {
                            let span = self.make_span(start_pos, start_line, start_col);
                            self.errors.push(LexError {
                                message: format!("unknown string escape `\\{c}`"),
                                span,
                            });
                            current_raw.push(c);
                        }
                        None => {
                            let span = self.make_span(start_pos, start_line, start_col);
                            self.errors.push(LexError {
                                message: "unterminated string escape at end of file".into(),
                                span,
                            });
                            break;
                        }
                    }
                }
                Some('$') if self.peek2() == Some('(') => {
                    // Flush accumulated raw text.
                    if !current_raw.is_empty() {
                        parts.push(StringPart::Raw(std::mem::take(&mut current_raw)));
                    }
                    self.advance(); // consume `$`
                    self.advance(); // consume `(`

                    // Collect characters until the matching `)`, tracking nesting.
                    let interp_src = self.collect_interp_source(start_pos, start_line, start_col);

                    // Lex the collected source as a nested token stream.
                    let (interp_tokens, mut interp_errors) = Lexer::new(&interp_src).scan();
                    self.errors.append(&mut interp_errors);
                    parts.push(StringPart::Interp(interp_tokens));
                }
                Some(c) => {
                    current_raw.push(c);
                    self.advance();
                }
            }
        }

        // Flush any remaining raw text.
        if !current_raw.is_empty() {
            parts.push(StringPart::Raw(current_raw));
        }

        // Normalise: a plain string with no interpolation sites is represented
        // as a single Raw part (or an empty vec for "").
        TokenKind::Str(parts)
    }

    /// Collect the raw source characters of a `$( )` interpolation site.
    ///
    /// The opening `$(` has already been consumed.  This function collects
    /// characters until the matching `)`, counting nested `(` / `)` pairs.
    /// Returns the collected text as an owned `String`.
    fn collect_interp_source(
        &mut self,
        err_start_pos: usize,
        err_start_line: u32,
        err_start_col: u32,
    ) -> String {
        let mut src = String::new();
        let mut depth = 1usize;

        loop {
            match self.peek() {
                None => {
                    let span = self.make_span(err_start_pos, err_start_line, err_start_col);
                    self.errors.push(LexError {
                        message: "unterminated string interpolation `$( ... )`".into(),
                        span,
                    });
                    break;
                }
                Some('(') => {
                    depth += 1;
                    src.push('(');
                    self.advance();
                }
                Some(')') => {
                    depth -= 1;
                    if depth == 0 {
                        self.advance(); // consume closing `)`
                        break;
                    }
                    src.push(')');
                    self.advance();
                }
                Some(c) => {
                    src.push(c);
                    self.advance();
                }
            }
        }
        src
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Public convenience function
// ─────────────────────────────────────────────────────────────────────────────

/// Lex `src` and return `(tokens, errors)`.
///
/// This is the primary entry point for the rest of the compiler.
/// The returned `tokens` always end with `TokenKind::Eof`.
pub fn lex(src: &str) -> (Vec<Token>, Vec<LexError>) {
    Lexer::new(src).scan()
}

// ─────────────────────────────────────────────────────────────────────────────
// Tests
// ─────────────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    fn kinds(src: &str) -> Vec<TokenKind> {
        let (toks, errs) = lex(src);
        assert!(errs.is_empty(), "unexpected lex errors: {errs:?}");
        toks.into_iter().map(|t| t.kind).collect()
    }

    #[test]
    fn test_single_chars() {
        let k = kinds("( ) { } [ ] , ; @");
        assert_eq!(
            k,
            vec![
                TokenKind::LParen,
                TokenKind::RParen,
                TokenKind::LBrace,
                TokenKind::RBrace,
                TokenKind::LBracket,
                TokenKind::RBracket,
                TokenKind::Comma,
                TokenKind::Semicolon,
                TokenKind::At,
                TokenKind::Eof,
            ]
        );
    }

    #[test]
    fn test_operators() {
        let k = kinds("+ - * / % == != <= >= < > && || ! ++ -- !! ?. ?: .. . : -> ~");
        assert_eq!(k[0], TokenKind::Plus);
        assert_eq!(k[1], TokenKind::Minus);
        assert_eq!(k[2], TokenKind::Star);
        assert_eq!(k[3], TokenKind::Slash);
        assert_eq!(k[4], TokenKind::Percent);
        assert_eq!(k[5], TokenKind::EqEq);
        assert_eq!(k[6], TokenKind::BangEq);
        assert_eq!(k[7], TokenKind::LtEq);
        assert_eq!(k[8], TokenKind::GtEq);
        assert_eq!(k[9], TokenKind::Lt);
        assert_eq!(k[10], TokenKind::Gt);
        assert_eq!(k[11], TokenKind::AmpAmp);
        assert_eq!(k[12], TokenKind::PipePipe);
        assert_eq!(k[13], TokenKind::Bang);
        assert_eq!(k[14], TokenKind::PlusPlus);
        assert_eq!(k[15], TokenKind::MinusMinus);
        assert_eq!(k[16], TokenKind::BangBang);
        assert_eq!(k[17], TokenKind::QuestionDot);
        assert_eq!(k[18], TokenKind::QuestionColon);
        assert_eq!(k[19], TokenKind::DotDot);
        assert_eq!(k[20], TokenKind::Dot);
        assert_eq!(k[21], TokenKind::Colon);
        assert_eq!(k[22], TokenKind::Arrow);
        assert_eq!(k[23], TokenKind::Tilde);
    }

    #[test]
    fn test_keywords() {
        let k = kinds("let const true false null pub use return break continue self");
        assert_eq!(k[0], TokenKind::Let);
        assert_eq!(k[1], TokenKind::Const);
        assert_eq!(k[2], TokenKind::True);
        assert_eq!(k[3], TokenKind::False);
        assert_eq!(k[4], TokenKind::Null);
        assert_eq!(k[5], TokenKind::Pub);
        assert_eq!(k[6], TokenKind::Use);
        assert_eq!(k[7], TokenKind::Return);
        assert_eq!(k[8], TokenKind::Break);
        assert_eq!(k[9], TokenKind::Continue);
        assert_eq!(k[10], TokenKind::SelfKw);
    }

    #[test]
    fn test_def_family_are_not_keywords() {
        let k = kinds("def defn deftype defmacro");
        assert_eq!(k[0], TokenKind::Ident("def".into()));
        assert_eq!(k[1], TokenKind::Ident("defn".into()));
        assert_eq!(k[2], TokenKind::Ident("deftype".into()));
        assert_eq!(k[3], TokenKind::Ident("defmacro".into()));
    }

    #[test]
    fn test_integer_literals() {
        let k = kinds("0 42 1_000_000");
        assert_eq!(k[0], TokenKind::Int(0));
        assert_eq!(k[1], TokenKind::Int(42));
        assert_eq!(k[2], TokenKind::Int(1_000_000));
    }

    #[test]
    fn test_float_literals() {
        let k = kinds("3.14 0.5 1_000.0");
        assert_eq!(k[0], TokenKind::Float(3.14));
        assert_eq!(k[1], TokenKind::Float(0.5));
        assert_eq!(k[2], TokenKind::Float(1000.0));
    }

    #[test]
    fn test_plain_string() {
        let k = kinds(r#""hello world""#);
        assert_eq!(
            k[0],
            TokenKind::Str(vec![StringPart::Raw("hello world".into())])
        );
    }

    #[test]
    fn test_string_escapes() {
        let k = kinds(r#""\n\t\\\"" "#);
        assert_eq!(
            k[0],
            TokenKind::Str(vec![StringPart::Raw("\n\t\\\"".into())])
        );
    }

    #[test]
    fn test_interpolated_string() {
        let (toks, errs) = lex(r#""Hello, $(name)!""#);
        assert!(errs.is_empty());
        if let TokenKind::Str(parts) = &toks[0].kind {
            assert_eq!(parts.len(), 3);
            assert_eq!(parts[0], StringPart::Raw("Hello, ".into()));
            // The interp part should contain tokens for `name` + Eof
            if let StringPart::Interp(inner) = &parts[1] {
                assert!(inner.len() >= 2);
                assert_eq!(inner[0].kind, TokenKind::Ident("name".into()));
            } else {
                panic!("expected Interp part");
            }
            assert_eq!(parts[2], StringPart::Raw("!".into()));
        } else {
            panic!("expected Str token");
        }
    }

    #[test]
    fn test_identifiers() {
        let k = kinds("foo _bar myVar _123");
        assert_eq!(k[0], TokenKind::Ident("foo".into()));
        assert_eq!(k[1], TokenKind::Ident("_bar".into()));
        assert_eq!(k[2], TokenKind::Ident("myVar".into()));
        assert_eq!(k[3], TokenKind::Ident("_123".into()));
    }

    #[test]
    fn test_dot_ident() {
        let k = kinds(".ok .null .some");
        assert_eq!(k[0], TokenKind::DotIdent("ok".into()));
        assert_eq!(k[1], TokenKind::DotIdent("null".into()));
        assert_eq!(k[2], TokenKind::DotIdent("some".into()));
    }

    #[test]
    fn test_atoms() {
        let k = kinds("'outer 'loop1 'search");
        assert_eq!(k[0], TokenKind::Atom("outer".into()));
        assert_eq!(k[1], TokenKind::Atom("loop1".into()));
        assert_eq!(k[2], TokenKind::Atom("search".into()));
    }

    #[test]
    fn test_implicit_semicolon_after_rbrace() {
        // A newline after `}` should produce a Newline token between `}` and the next token.
        let k = kinds("}\nfoo");
        assert_eq!(k[0], TokenKind::RBrace);
        assert_eq!(k[1], TokenKind::Newline);
        assert_eq!(k[2], TokenKind::Ident("foo".into()));
    }

    #[test]
    fn test_no_implicit_semicolon_midline() {
        // Newlines that don't follow `}` should be ignored.
        let k = kinds("foo\nbar");
        assert_eq!(k[0], TokenKind::Ident("foo".into()));
        assert_eq!(k[1], TokenKind::Ident("bar".into()));
        assert_eq!(k[2], TokenKind::Eof);
    }

    #[test]
    fn test_line_comment() {
        let k = kinds("foo // this is a comment\nbar");
        assert_eq!(k[0], TokenKind::Ident("foo".into()));
        assert_eq!(k[1], TokenKind::Ident("bar".into()));
    }

    #[test]
    fn test_spans() {
        let (toks, _) = lex("let x = 42;");
        // `let` starts at col 1, `x` at col 5, `=` at col 7, `42` at col 9, `;` at col 11
        assert_eq!(toks[0].span.col, 1); // let
        assert_eq!(toks[1].span.col, 5); // x
        assert_eq!(toks[2].span.col, 7); // =
        assert_eq!(toks[3].span.col, 9); // 42
    }
}
