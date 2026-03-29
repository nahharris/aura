use crate::token::{Token, TokenKind};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LexError {
    pub message: String,
}

impl LexError {
    fn new(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
        }
    }
}

pub fn lex(source: &str) -> Result<Vec<Token>, LexError> {
    let mut chars = source.chars().peekable();
    let mut tokens = Vec::new();

    while let Some(ch) = chars.peek().copied() {
        match ch {
            ' ' | '\t' | '\r' | '\n' => {
                chars.next();
            }
            '(' => {
                chars.next();
                tokens.push(Token::new(TokenKind::LParen));
            }
            ')' => {
                chars.next();
                tokens.push(Token::new(TokenKind::RParen));
            }
            '{' => {
                chars.next();
                tokens.push(Token::new(TokenKind::LBrace));
            }
            '}' => {
                chars.next();
                tokens.push(Token::new(TokenKind::RBrace));
            }
            '[' => {
                chars.next();
                tokens.push(Token::new(TokenKind::LBracket));
            }
            ']' => {
                chars.next();
                tokens.push(Token::new(TokenKind::RBracket));
            }
            ':' => {
                chars.next();
                tokens.push(Token::new(TokenKind::Colon));
            }
            ',' => {
                chars.next();
                tokens.push(Token::new(TokenKind::Comma));
            }
            '.' => {
                chars.next();
                tokens.push(Token::new(TokenKind::Dot));
            }
            '=' => {
                chars.next();
                tokens.push(Token::new(TokenKind::Eq));
            }
            '-' => {
                chars.next();
                if chars.peek() == Some(&'>') {
                    chars.next();
                    tokens.push(Token::new(TokenKind::Arrow));
                } else {
                    return Err(LexError::new("unexpected '-'"));
                }
            }
            c if c.is_ascii_digit() => {
                let mut number = String::new();
                while let Some(n) = chars.peek().copied() {
                    if n.is_ascii_digit() {
                        number.push(n);
                        chars.next();
                    } else {
                        break;
                    }
                }
                tokens.push(Token::new(TokenKind::Int(number)));
            }
            c if is_ident_start(c) => {
                let mut ident = String::new();
                ident.push(c);
                chars.next();

                while let Some(n) = chars.peek().copied() {
                    if is_ident_continue(n) {
                        ident.push(n);
                        chars.next();
                    } else {
                        break;
                    }
                }

                let kind = match ident.as_str() {
                    "defmacro" => TokenKind::Defmacro,
                    "static" => TokenKind::Static,
                    _ => TokenKind::Ident(ident),
                };
                tokens.push(Token::new(kind));
            }
            other => {
                return Err(LexError::new(format!("unexpected character '{other}'")));
            }
        }
    }

    tokens.push(Token::new(TokenKind::Eof));
    Ok(tokens)
}

fn is_ident_start(ch: char) -> bool {
    ch.is_ascii_alphabetic() || ch == '_'
}

fn is_ident_continue(ch: char) -> bool {
    ch.is_ascii_alphanumeric() || ch == '_'
}
