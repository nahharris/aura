use crate::token::{Span, Token, TokenKind};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LexError {
    pub message: String,
    pub span: Span,
}

impl LexError {
    fn new(message: impl Into<String>, span: Span) -> Self {
        Self {
            message: message.into(),
            span,
        }
    }
}

pub fn lex(source: &str) -> Result<Vec<Token>, LexError> {
    let mut lexer = Lexer::new(source);
    lexer.lex_all()
}

struct Lexer<'a> {
    chars: Vec<char>,
    len: usize,
    pos: usize,
    line: usize,
    column: usize,
    tokens: Vec<Token>,
    _source: &'a str,
}

impl<'a> Lexer<'a> {
    fn new(source: &'a str) -> Self {
        let chars: Vec<char> = source.chars().collect();
        let len = chars.len();
        Self {
            chars,
            len,
            pos: 0,
            line: 1,
            column: 1,
            tokens: Vec::new(),
            _source: source,
        }
    }

    fn lex_all(&mut self) -> Result<Vec<Token>, LexError> {
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
                        return Err(LexError::new(
                            "float literal requires integer part before '.'",
                            self.single_span(),
                        ));
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
                        return Err(LexError::new(
                            "unexpected '!': expected '!!' or '!='",
                            self.single_span(),
                        ));
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
                    if self.peek_n(1) == Some('|') {
                        self.push_pair(TokenKind::PipePipe);
                    } else {
                        return Err(LexError::new(
                            "unexpected '|': expected '||'",
                            self.single_span(),
                        ));
                    }
                }
                '&' => {
                    if self.peek_n(1) == Some('&') {
                        self.push_pair(TokenKind::AmpAmp);
                    } else {
                        return Err(LexError::new(
                            "unexpected '&': expected '&&'",
                            self.single_span(),
                        ));
                    }
                }
                '?' => {
                    if self.peek_n(1) == Some(':') {
                        self.push_pair(TokenKind::QuestionColon);
                    } else if self.peek_n(1) == Some('.') {
                        self.push_pair(TokenKind::QuestionDot);
                    } else {
                        return Err(LexError::new(
                            "unexpected '?': expected '?:' or '?.'",
                            self.single_span(),
                        ));
                    }
                }
                '+' => {
                    if self.peek_n(1) == Some('+') {
                        self.push_pair(TokenKind::PlusPlus);
                    } else {
                        self.push_simple(TokenKind::Plus);
                    }
                }
                '-' => {
                    if self.peek_n(1) == Some('>') {
                        self.push_pair(TokenKind::Arrow);
                    } else if self.peek_n(1) == Some('-') {
                        self.push_pair(TokenKind::MinusMinus);
                    } else {
                        self.push_simple(TokenKind::Minus);
                    }
                }
                '*' => self.push_simple(TokenKind::Star),
                '%' => self.push_simple(TokenKind::Percent),
                '/' => self.push_simple(TokenKind::Slash),
                '"' => self.lex_string()?,
                '\'' => self.lex_char()?,
                c if c.is_ascii_digit() => self.lex_number()?,
                c if is_ident_start(c) => self.lex_ident_or_keyword(),
                other => {
                    return Err(LexError::new(
                        format!("unexpected character '{other}'"),
                        self.single_span(),
                    ));
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

    fn lex_number(&mut self) -> Result<(), LexError> {
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
                return Err(LexError::new(
                    "float literal requires digits after '.'",
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

    fn lex_string(&mut self) -> Result<(), LexError> {
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
                        LexError::new(
                            "unterminated escape in string literal",
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
                            return Err(LexError::new(
                                format!("unsupported string escape '\\{other}'"),
                                self.single_span(),
                            ));
                        }
                    });
                }
                _ => {
                    value.push(ch);
                    self.bump();
                }
            }
        }

        Err(LexError::new(
            "unterminated string literal",
            Span {
                start: start_pos,
                end: self.pos,
                line: start_line,
                column: start_col,
            },
        ))
    }

    fn lex_char(&mut self) -> Result<(), LexError> {
        let start_pos = self.pos;
        let start_line = self.line;
        let start_col = self.column;
        self.bump();

        let value = if self.peek() == Some('\\') {
            self.bump();
            let escaped = self.peek().ok_or_else(|| {
                LexError::new(
                    "unterminated escape in char literal",
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
                    return Err(LexError::new(
                        format!("unsupported char escape '\\{other}'"),
                        self.single_span(),
                    ));
                }
            }
        } else {
            let ch = self.peek().ok_or_else(|| {
                LexError::new(
                    "unterminated char literal",
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
            return Err(LexError::new(
                "char literal must contain exactly one character",
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
        self.bump();
        self.bump();
        while let Some(ch) = self.peek() {
            if ch == '\n' {
                break;
            }
            self.bump();
        }
    }

    fn consume_block_comment(&mut self) -> Result<(), LexError> {
        let start = self.single_span();
        self.bump();
        self.bump();
        while self.pos < self.len {
            if self.peek() == Some('*') && self.peek_n(1) == Some('/') {
                self.bump();
                self.bump();
                return Ok(());
            }
            self.bump();
        }
        Err(LexError::new("unterminated block comment", start))
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
