//! Destructuring and match-adjacent [`Pattern`] parsing.

use crate::ast::*;
use crate::token::TokenKind;

use super::ParseError;
use super::Parser;

impl Parser {
    /// Parse a single pattern (literal, identifier, wildcard, tuple, struct, constructor, or variant).
    pub(super) fn parse_pattern(&mut self) -> Result<Pattern, ParseError> {
        let start = self.cur_span();
        match self.cur_kind().clone() {
            TokenKind::Ident(name) if name == "_" => {
                self.advance();
                Ok(Pattern::Wildcard(start))
            }
            TokenKind::DotDot => {
                // Rest pattern: `..name` or `..`
                self.advance();
                let rest_name = if let TokenKind::Ident(n) = self.cur_kind().clone() {
                    if n != "_" {
                        self.advance();
                        Some(n)
                    } else {
                        self.advance();
                        None
                    }
                } else {
                    None
                };
                let span = start.merge(self.cur_span());
                Ok(Pattern::Rest {
                    name: rest_name,
                    span,
                })
            }
            TokenKind::Ident(name) => {
                self.advance();
                // Check for type-check pattern: `name: Type`
                if self.eat(TokenKind::Colon) {
                    let ty = self.parse_type_expr()?;
                    let span = start.merge(self.cur_span());
                    return Ok(Pattern::TypeCheck { name, ty, span });
                }
                // Check for constructor pattern: `TypeName(inner)` — PascalCase ident + `(`
                let is_pascal = name.chars().next().is_some_and(|c| c.is_uppercase());
                if is_pascal && self.check(&TokenKind::LParen) {
                    self.advance(); // consume `(`
                    let inner = self.parse_pattern()?;
                    self.expect(TokenKind::RParen)?;
                    let span = start.merge(self.cur_span());
                    return Ok(Pattern::Constructor {
                        type_name: name,
                        inner: Box::new(inner),
                        span,
                    });
                }
                Ok(Pattern::Bind(name, start))
            }
            TokenKind::Int(n) => {
                self.advance();
                Ok(Pattern::Literal(Expr::Int(n, start)))
            }
            TokenKind::Float(n) => {
                self.advance();
                Ok(Pattern::Literal(Expr::Float(n, start)))
            }
            TokenKind::Str(parts) => {
                self.advance();
                Ok(Pattern::Literal(Expr::Str(parts, start)))
            }
            TokenKind::Char(c) => {
                self.advance();
                Ok(Pattern::Literal(Expr::Char(c, start)))
            }
            TokenKind::LBracket => {
                // Only `[]` (empty list) is supported as a literal pattern.
                self.advance(); // consume `[`
                self.expect(TokenKind::RBracket)?;
                let span = start.merge(self.cur_span());
                Ok(Pattern::Literal(Expr::List {
                    items: vec![],
                    span,
                }))
            }
            TokenKind::LParen => {
                self.advance();
                // Peek: if first element is `ident =` → struct pattern;
                // otherwise → tuple pattern.
                let is_struct = matches!(self.cur_kind(), TokenKind::Ident(_))
                    && matches!(self.peek_kind(), TokenKind::Eq);
                if is_struct {
                    let mut fields = Vec::new();
                    while !self.check(&TokenKind::RParen) && !self.at_eof() {
                        let f_start = self.cur_span();
                        // Supports both `field` and `field = alias`
                        let field_name = self.expect_ident()?;
                        let binding = if self.eat(TokenKind::Eq) {
                            Some(self.expect_ident()?)
                        } else {
                            None
                        };
                        let f_span = f_start.merge(self.cur_span());
                        fields.push(StructPatternField {
                            name: field_name,
                            binding,
                            span: f_span,
                        });
                        if !self.eat(TokenKind::Comma) {
                            break;
                        }
                    }
                    self.expect(TokenKind::RParen)?;
                    let span = start.merge(self.cur_span());
                    Ok(Pattern::Struct { fields, span })
                } else {
                    let mut pats = Vec::new();
                    while !self.check(&TokenKind::RParen) && !self.at_eof() {
                        pats.push(self.parse_pattern()?);
                        if !self.eat(TokenKind::Comma) {
                            break;
                        }
                    }
                    self.expect(TokenKind::RParen)?;
                    let span = start.merge(self.cur_span());
                    Ok(Pattern::Tuple(pats, span))
                }
            }
            TokenKind::DotIdent(name) => {
                self.advance();
                let inner = if self.check(&TokenKind::LParen) {
                    self.advance();
                    let inner_pat = self.parse_pattern()?;
                    self.expect(TokenKind::RParen)?;
                    Some(Box::new(inner_pat))
                } else {
                    None
                };
                let span = start.merge(self.cur_span());
                Ok(Pattern::Variant { name, inner, span })
            }
            other => Err(self.error(format!("expected pattern, found {other}"))),
        }
    }
}
