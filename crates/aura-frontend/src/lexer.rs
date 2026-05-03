#![allow(clippy::result_large_err)]

use crate::token::{Span, Token, TokenKind};
use aura_diagnostics::{Diagnostic, Issue, Stage};

pub fn lex(source: &str) -> Result<Vec<Token>, Diagnostic> {
    let mut lexer = Lexer::new(source, false);
    lexer.lex_all()
}

pub fn lex_with_comments(source: &str) -> Result<Vec<Token>, Diagnostic> {
    let mut lexer = Lexer::new(source, true);
    lexer.lex_all()
}

struct Lexer<'a> {
    chars: Vec<char>,
    len: usize,
    pos: usize,
    line: usize,
    column: usize,
    tokens: Vec<Token>,
    include_comments: bool,
    _source: &'a str,
}

impl<'a> Lexer<'a> {
    fn new(source: &'a str, include_comments: bool) -> Self {
        let chars: Vec<char> = source.chars().collect();
        let len = chars.len();
        Self {
            chars,
            len,
            pos: 0,
            line: 1,
            column: 1,
            tokens: Vec::new(),
            include_comments,
            _source: source,
        }
    }

    fn lex_all(&mut self) -> Result<Vec<Token>, Diagnostic> {
        while let Some(ch) = self.peek() {
            match ch {
                ' ' | '\t' | '\r' => {
                    self.bump();
                }
                '\n' => {
                    self.bump();
                    self.maybe_insert_implicit_semi();
                }
                '/' if self.peek_n(1) == Some('/') => {
                    self.consume_line_comment();
                }
                '/' if self.peek_n(1) == Some('*') => {
                    self.consume_block_comment()?;
                }
                ';' => self.push_simple(TokenKind::Semi),
                '(' => self.push_simple(TokenKind::LParen),
                ')' => self.push_simple(TokenKind::RParen),
                '{' => self.push_simple(TokenKind::LBrace),
                '}' => self.push_simple(TokenKind::RBrace),
                '[' => self.push_simple(TokenKind::LBracket),
                ']' => self.push_simple(TokenKind::RBracket),
                ':' => self.push_simple(TokenKind::Colon),
                ',' => self.push_simple(TokenKind::Comma),
                '~' => self.push_simple(TokenKind::Tilde),
                '_' => self.push_simple(TokenKind::Underscore),
                '.' => {
                    if self.peek_n(1) == Some('.') {
                        self.push_pair(TokenKind::Range);
                    } else if self.peek_n(1).map(|c| c.is_ascii_digit()).unwrap_or(false) {
                        if self.previous_token_allows_numeric_member() {
                            self.push_simple(TokenKind::Dot);
                        } else {
                            return Err(self.error_here(Issue::LexFloatNoIntPart));
                        }
                    } else {
                        self.push_simple(TokenKind::Dot);
                    }
                }
                '=' => {
                    if self.peek_n(1) == Some('=') {
                        self.push_pair(TokenKind::EqEq);
                    } else {
                        self.push_simple(TokenKind::Eq);
                    }
                }
                '!' => {
                    if self.peek_n(1) == Some('!') {
                        self.push_pair(TokenKind::BangBang);
                    } else if self.peek_n(1) == Some('=') {
                        self.push_pair(TokenKind::NotEq);
                    } else {
                        return Err(self.error_here(Issue::LexBangForm));
                    }
                }
                '<' => {
                    if self.peek_n(1) == Some('=') {
                        self.push_pair(TokenKind::Lte);
                    } else {
                        self.push_simple(TokenKind::Lt);
                    }
                }
                '>' => {
                    if self.peek_n(1) == Some('=') {
                        self.push_pair(TokenKind::Gte);
                    } else {
                        self.push_simple(TokenKind::Gt);
                    }
                }
                '|' => {
                    if self.peek_n(1) == Some('>') {
                        self.push_pair(TokenKind::PipeArrow);
                    } else if self.peek_n(1) == Some('|') {
                        self.push_pair(TokenKind::PipePipe);
                    } else {
                        return Err(self.error_here(Issue::LexPipeForm));
                    }
                }
                '&' => {
                    if self.peek_n(1) == Some('&') {
                        self.push_pair(TokenKind::AmpAmp);
                    } else {
                        return Err(self.error_here(Issue::LexAmpForm));
                    }
                }
                '?' => {
                    if self.peek_n(1) == Some(':') {
                        self.push_pair(TokenKind::QuestionColon);
                    } else if self.peek_n(1) == Some('.') {
                        self.push_pair(TokenKind::QuestionDot);
                    } else {
                        return Err(self.error_here(Issue::LexQuestionForm));
                    }
                }
                '+' => {
                    if self.peek_n(1) == Some('+') {
                        self.push_pair(TokenKind::PlusPlus);
                    } else if self.peek_n(1) == Some('=') {
                        self.push_pair(TokenKind::PlusEq);
                    } else {
                        self.push_simple(TokenKind::Plus);
                    }
                }
                '-' => {
                    if self.peek_n(1) == Some('>') {
                        self.push_pair(TokenKind::Arrow);
                    } else if self.peek_n(1) == Some('-') {
                        self.push_pair(TokenKind::MinusMinus);
                    } else if self.peek_n(1) == Some('=') {
                        self.push_pair(TokenKind::MinusEq);
                    } else {
                        self.push_simple(TokenKind::Minus);
                    }
                }
                '*' => {
                    if self.peek_n(1) == Some('=') {
                        self.push_pair(TokenKind::StarEq);
                    } else {
                        self.push_simple(TokenKind::Star);
                    }
                }
                '%' => {
                    if self.peek_n(1) == Some('=') {
                        self.push_pair(TokenKind::PercentEq);
                    } else {
                        self.push_simple(TokenKind::Percent);
                    }
                }
                '/' => {
                    if self.peek_n(1) == Some('=') {
                        self.push_pair(TokenKind::SlashEq);
                    } else {
                        self.push_simple(TokenKind::Slash);
                    }
                }
                '"' => self.lex_string()?,
                '\'' => self.lex_char()?,
                c if c.is_ascii_digit() => self.lex_number()?,
                c if is_ident_start(c) => self.lex_ident_or_keyword(),
                other => {
                    return Err(self.error_here(Issue::LexUnexpectedChar { ch: other }));
                }
            }
        }

        let eof_span = Span {
            start: self.pos,
            end: self.pos,
            line: self.line,
            column: self.column,
        };
        self.tokens.push(Token::new(TokenKind::Eof, eof_span));
        Ok(std::mem::take(&mut self.tokens))
    }

    fn previous_token_allows_numeric_member(&self) -> bool {
        matches!(
            self.tokens.last().map(|token| &token.kind),
            Some(TokenKind::Ident(_) | TokenKind::RParen | TokenKind::RBracket | TokenKind::RBrace)
        )
    }

    fn lex_ident_or_keyword(&mut self) {
        let start_pos = self.pos;
        let start_line = self.line;
        let start_col = self.column;
        let mut ident = String::new();
        while let Some(ch) = self.peek() {
            if is_ident_continue(ch) {
                ident.push(ch);
                self.bump();
            } else {
                break;
            }
        }

        let kind = match ident.as_str() {
            "defmacro" => TokenKind::Defmacro,
            _ => TokenKind::Ident(ident),
        };
        self.tokens.push(Token::new(
            kind,
            Span {
                start: start_pos,
                end: self.pos,
                line: start_line,
                column: start_col,
            },
        ));
    }

    fn lex_number(&mut self) -> Result<(), Diagnostic> {
        let start_pos = self.pos;
        let start_line = self.line;
        let start_col = self.column;

        let mut raw = String::new();
        while let Some(ch) = self.peek() {
            if ch.is_ascii_digit() || ch == '_' {
                raw.push(ch);
                self.bump();
            } else {
                break;
            }
        }

        let mut is_float = false;
        if self.peek() == Some('.') {
            if self.peek_n(1) == Some('.') {
                // range operator starts, keep as integer
            } else if self.peek_n(1).map(|c| c.is_ascii_digit()).unwrap_or(false) {
                is_float = true;
                raw.push('.');
                self.bump();
                while let Some(ch) = self.peek() {
                    if ch.is_ascii_digit() || ch == '_' {
                        raw.push(ch);
                        self.bump();
                    } else {
                        break;
                    }
                }
            } else {
                return Err(self.error_at(
                    Issue::LexFloatNoFraction,
                    Span {
                        start: start_pos,
                        end: self.pos + 1,
                        line: start_line,
                        column: start_col,
                    },
                ));
            }
        }

        let kind = if is_float {
            TokenKind::Float(raw)
        } else {
            TokenKind::Int(raw)
        };
        self.tokens.push(Token::new(
            kind,
            Span {
                start: start_pos,
                end: self.pos,
                line: start_line,
                column: start_col,
            },
        ));
        Ok(())
    }

    fn lex_string(&mut self) -> Result<(), Diagnostic> {
        let start_pos = self.pos;
        let start_line = self.line;
        let start_col = self.column;
        self.bump();

        let mut value = String::new();
        while let Some(ch) = self.peek() {
            match ch {
                '"' => {
                    self.bump();
                    self.tokens.push(Token::new(
                        TokenKind::String(value),
                        Span {
                            start: start_pos,
                            end: self.pos,
                            line: start_line,
                            column: start_col,
                        },
                    ));
                    return Ok(());
                }
                '\\' => {
                    self.bump();
                    let escaped = self.peek().ok_or_else(|| {
                        self.error_at(
                            Issue::LexStringEscapeUnterminated,
                            Span {
                                start: start_pos,
                                end: self.pos,
                                line: start_line,
                                column: start_col,
                            },
                        )
                    })?;
                    self.bump();
                    value.push(match escaped {
                        'n' => '\n',
                        't' => '\t',
                        '\\' => '\\',
                        '"' => '"',
                        other => {
                            return Err(
                                self.error_here(Issue::LexStringEscapeUnsupported { ch: other })
                            );
                        }
                    });
                }
                _ => {
                    value.push(ch);
                    self.bump();
                }
            }
        }

        Err(self.error_at(
            Issue::LexStringUnterminated,
            Span {
                start: start_pos,
                end: self.pos,
                line: start_line,
                column: start_col,
            },
        ))
    }

    fn lex_char(&mut self) -> Result<(), Diagnostic> {
        let start_pos = self.pos;
        let start_line = self.line;
        let start_col = self.column;
        self.bump();

        let value = if self.peek() == Some('\\') {
            self.bump();
            let escaped = self.peek().ok_or_else(|| {
                self.error_at(
                    Issue::LexCharEscapeUnterminated,
                    Span {
                        start: start_pos,
                        end: self.pos,
                        line: start_line,
                        column: start_col,
                    },
                )
            })?;
            self.bump();
            match escaped {
                'n' => "\\n".to_string(),
                't' => "\\t".to_string(),
                '\\' => "\\\\".to_string(),
                '\'' => "\\'".to_string(),
                other => {
                    return Err(self.error_here(Issue::LexCharEscapeUnsupported { ch: other }));
                }
            }
        } else {
            let ch = self.peek().ok_or_else(|| {
                self.error_at(
                    Issue::LexCharUnterminated,
                    Span {
                        start: start_pos,
                        end: self.pos,
                        line: start_line,
                        column: start_col,
                    },
                )
            })?;
            self.bump();
            ch.to_string()
        };

        if self.peek() != Some('\'') {
            return Err(self.error_at(
                Issue::LexCharSize,
                Span {
                    start: start_pos,
                    end: self.pos,
                    line: start_line,
                    column: start_col,
                },
            ));
        }
        self.bump();

        self.tokens.push(Token::new(
            TokenKind::Char(value),
            Span {
                start: start_pos,
                end: self.pos,
                line: start_line,
                column: start_col,
            },
        ));
        Ok(())
    }

    fn consume_line_comment(&mut self) {
        let start_pos = self.pos;
        let start_line = self.line;
        let start_col = self.column;
        self.bump();
        self.bump();
        let mut text = String::from("//");
        while let Some(ch) = self.peek() {
            if ch == '\n' {
                break;
            }
            text.push(ch);
            self.bump();
        }
        if self.include_comments {
            self.tokens.push(Token::new(
                TokenKind::LineComment(text),
                Span {
                    start: start_pos,
                    end: self.pos,
                    line: start_line,
                    column: start_col,
                },
            ));
        }
    }

    fn consume_block_comment(&mut self) -> Result<(), Diagnostic> {
        let start = self.single_span();
        let start_pos = self.pos;
        let start_line = self.line;
        let start_col = self.column;
        self.bump();
        self.bump();
        let mut text = String::from("/*");
        while self.pos < self.len {
            if self.peek() == Some('*') && self.peek_n(1) == Some('/') {
                text.push('*');
                text.push('/');
                self.bump();
                self.bump();
                if self.include_comments {
                    self.tokens.push(Token::new(
                        TokenKind::BlockComment(text),
                        Span {
                            start: start_pos,
                            end: self.pos,
                            line: start_line,
                            column: start_col,
                        },
                    ));
                }
                return Ok(());
            }
            if let Some(ch) = self.peek() {
                text.push(ch);
            }
            self.bump();
        }
        Err(self.error_at(Issue::LexBlockCommentUnterminated, start))
    }

    fn error_here(&self, issue: Issue) -> Diagnostic {
        Diagnostic::error(issue)
            .with_stage(Stage::Lexer)
            .with_span(self.single_span().into())
    }

    fn error_at(&self, issue: Issue, span: Span) -> Diagnostic {
        Diagnostic::error(issue)
            .with_stage(Stage::Lexer)
            .with_span(span.into())
    }

    fn maybe_insert_implicit_semi(&mut self) {
        let Some(last) = self.tokens.last() else {
            return;
        };
        if matches!(last.kind, TokenKind::RBrace)
            && !self
                .tokens
                .last()
                .map(|tok| matches!(tok.kind, TokenKind::Semi))
                .unwrap_or(false)
        {
            let span = Span {
                start: self.pos,
                end: self.pos,
                line: self.line,
                column: self.column,
            };
            self.tokens.push(Token::new(TokenKind::Semi, span));
        }
    }

    fn push_simple(&mut self, kind: TokenKind) {
        let start = self.single_span();
        self.bump();
        let end = Span {
            start: start.start,
            end: self.pos,
            line: start.line,
            column: start.column,
        };
        self.tokens.push(Token::new(kind, end));
    }

    fn push_pair(&mut self, kind: TokenKind) {
        let start = self.single_span();
        self.bump();
        self.bump();
        let span = Span {
            start: start.start,
            end: self.pos,
            line: start.line,
            column: start.column,
        };
        self.tokens.push(Token::new(kind, span));
    }

    fn single_span(&self) -> Span {
        Span {
            start: self.pos,
            end: self.pos.saturating_add(1),
            line: self.line,
            column: self.column,
        }
    }

    fn peek(&self) -> Option<char> {
        self.chars.get(self.pos).copied()
    }

    fn peek_n(&self, n: usize) -> Option<char> {
        self.chars.get(self.pos + n).copied()
    }

    fn bump(&mut self) {
        if let Some(ch) = self.peek() {
            self.pos += 1;
            if ch == '\n' {
                self.line += 1;
                self.column = 1;
            } else {
                self.column += 1;
            }
        }
    }
}

fn is_ident_start(ch: char) -> bool {
    ch.is_ascii_alphabetic() || ch == '_'
}

fn is_ident_continue(ch: char) -> bool {
    ch.is_ascii_alphanumeric() || ch == '_'
}
