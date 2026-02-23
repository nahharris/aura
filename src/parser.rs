//! Recursive-descent parser with Pratt precedence climbing for expressions.
//!
//! The parser consumes the flat `Vec<Token>` produced by the lexer and builds
//! a typed [`Program`] AST.
//!
//! # Structure
//!
//! - **Top level**: [`Parser::parse_program`] → `Vec<Item>`
//! - **Declarations**: `parse_item`, `parse_decl`, `parse_def`, `parse_defmacro`, etc.
//! - **Statements**: `parse_stmt`, `parse_let`, `parse_def_stmt`, `parse_return`, etc.
//! - **Expressions**: [`Parser::parse_expr`] uses Pratt precedence climbing;
//!   each precedence level is a `parse_bp` call with a minimum binding power.
//! - **Primaries**: `parse_primary` dispatches on the current token to literals,
//!   identifiers, closures, collection literals, control-flow forms, and calls.
//!
//! # Pratt Operator Precedences (binding power pairs, left and right)
//!
//! | Operator  | L-bp | R-bp | Assoc |
//! |-----------|------|------|-------|
//! | `=`       |  1   |  2   | right |
//! | `\|\|`    |  3   |  4   | left  |
//! | `&&`      |  5   |  6   | left  |
//! | `==` `!=` |  7   |  8   | left  |
//! | `<><=>=`  |  9   |  10  | left  |
//! | `+ -`     |  11  |  12  | left  |
//! | `* / %`   |  13  |  14  | left  |
//! | unary `-!`|  —   |  15  | prefix|
//! | `++` `--` |  17  |  —   | postfix|
//! | `!!`      |  19  |  —   | postfix|
//! | `?.`      |  21  |  —   | postfix|
//! | `.`       |  23  |  —   | postfix|
//! | `()`  `[]`|  25  |  —   | postfix|
//! | `:` (cast)|  27  |  —   | postfix|
//!
//! # Error Recovery
//!
//! Errors are collected rather than aborting immediately.  On a parse error the
//! parser records the error, advances past the offending token, and attempts to
//! continue.  This produces multiple diagnostics from a single pass.

use crate::ast::*;
use crate::token::{Span, StringPart, Token, TokenKind};

// ─────────────────────────────────────────────────────────────────────────────
// Error type
// ─────────────────────────────────────────────────────────────────────────────

/// A parse error with a source location.
#[derive(Debug, Clone)]
pub struct ParseError {
    pub message: String,
    pub span: Span,
}

impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "[{}:{}] {}", self.span.line, self.span.col, self.message)
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Parser struct
// ─────────────────────────────────────────────────────────────────────────────

/// The Aura recursive-descent parser.
///
/// Construct one with [`Parser::new`], then call [`Parser::parse_program`].
pub struct Parser {
    /// The full token stream (including the trailing `Eof` sentinel).
    tokens: Vec<Token>,
    /// Index of the *current* token (not yet consumed).
    cursor: usize,
    /// Accumulated parse errors (non-fatal; parsing continues after each).
    errors: Vec<ParseError>,
}

impl Parser {
    /// Create a new parser for the given token stream.
    ///
    /// `tokens` must end with a [`TokenKind::Eof`] sentinel (as produced by
    /// [`crate::lexer::lex`]).
    pub fn new(tokens: Vec<Token>) -> Self {
        Self {
            tokens,
            cursor: 0,
            errors: Vec::new(),
        }
    }

    /// Parse the full program and return `(program, errors)`.
    ///
    /// `program` is always a valid (possibly partial) AST; `errors` is empty
    /// on a clean input.
    pub fn parse_program(mut self) -> (Program, Vec<ParseError>) {
        let start = self.cur_span();
        let mut items = Vec::new();

        while !self.at_eof() {
            // Skip any leading semicolons / implicit newlines at module level.
            while self.eat(TokenKind::Semicolon) || self.eat(TokenKind::Newline) {}
            if self.at_eof() {
                break;
            }
            match self.parse_item() {
                Ok(item) => items.push(item),
                Err(e) => {
                    self.errors.push(e);
                    self.recover_to_next_decl();
                }
            }
        }

        let span = start.merge(self.cur_span());
        let program = Program { items, span };
        (program, self.errors)
    }

    // ─────────────────────────────────────────────────────────────────────────
    // Token stream helpers
    // ─────────────────────────────────────────────────────────────────────────

    /// Return the current token (without consuming it).
    #[inline]
    fn cur(&self) -> &Token {
        &self.tokens[self.cursor]
    }

    /// Return the current token kind.
    #[inline]
    fn cur_kind(&self) -> &TokenKind {
        &self.cur().kind
    }

    /// Return the span of the current token.
    #[inline]
    fn cur_span(&self) -> Span {
        self.cur().span
    }

    /// Return the *next* token kind (one ahead) without consuming anything.
    #[inline]
    fn peek_kind(&self) -> &TokenKind {
        let next = (self.cursor + 1).min(self.tokens.len() - 1);
        &self.tokens[next].kind
    }

    /// Consume and return the current token.
    fn advance(&mut self) -> Token {
        let tok = self.tokens[self.cursor].clone();
        if self.cursor + 1 < self.tokens.len() {
            self.cursor += 1;
        }
        tok
    }

    /// Return `true` if the current token matches `kind` (by discriminant for
    /// unit variants, or by value for data-bearing variants checked with `==`).
    fn check(&self, kind: &TokenKind) -> bool {
        self.cur_kind() == kind
    }

    /// Consume the current token if it matches `kind`. Returns `true` if consumed.
    fn eat(&mut self, kind: TokenKind) -> bool {
        if self.cur_kind() == &kind {
            self.advance();
            true
        } else {
            false
        }
    }

    /// Consume the current token and return it, or return an error if it does
    /// not match the expected kind.
    fn expect(&mut self, kind: TokenKind) -> Result<Token, ParseError> {
        if self.cur_kind() == &kind {
            Ok(self.advance())
        } else {
            Err(self.error(format!("expected {kind}, found {}", self.cur_kind())))
        }
    }

    /// Return `true` if at the end of the token stream.
    #[inline]
    fn at_eof(&self) -> bool {
        self.cur_kind() == &TokenKind::Eof
    }

    /// Create a [`ParseError`] at the current position.
    fn error(&self, message: String) -> ParseError {
        ParseError {
            message,
            span: self.cur_span(),
        }
    }

    /// Eat semicolons and implicit newlines (statement terminators).
    fn eat_terminators(&mut self) {
        while self.eat(TokenKind::Semicolon) || self.eat(TokenKind::Newline) {}
    }

    /// Skip to the next declaration boundary for error recovery.
    fn recover_to_next_decl(&mut self) {
        // A declaration starts at the beginning of a line after a `}` or `;`,
        // or when we see a keyword that can start a declaration.
        loop {
            match self.cur_kind() {
                TokenKind::Eof => break,
                TokenKind::Semicolon | TokenKind::Newline => {
                    self.advance();
                    break;
                }
                // Common declaration starters.
                TokenKind::Pub
                | TokenKind::Use
                | TokenKind::Let
                | TokenKind::Return
                | TokenKind::Break
                | TokenKind::Continue => break,
                // `def`, `defmacro` are plain identifiers.
                TokenKind::Ident(s) if matches!(s.as_str(), "def" | "defmacro") => break,
                _ => {
                    self.advance();
                }
            }
        }
    }

    /// Check if the current identifier is one of the `def`-family names.
    fn cur_is_def_family(&self) -> bool {
        matches!(
            self.cur_kind(),
            TokenKind::Ident(s) if matches!(
                s.as_str(),
                "def" | "defmacro"
            )
        )
    }

    // ─────────────────────────────────────────────────────────────────────────
    // Top-level item parsing
    // ─────────────────────────────────────────────────────────────────────────

    /// Parse one top-level item: either a `use` import or a declaration.
    fn parse_item(&mut self) -> Result<Item, ParseError> {
        if self.check(&TokenKind::Use) {
            Ok(Item::Use(self.parse_use()?))
        } else {
            Ok(Item::Decl(self.parse_decl()?))
        }
    }

    /// Parse a `use` import declaration.
    ///
    /// ```aura
    /// use (println, print) = "@stl/io";
    /// use io = "@stl/io";
    /// ```
    fn parse_use(&mut self) -> Result<UseDecl, ParseError> {
        let start = self.cur_span();
        self.expect(TokenKind::Use)?;

        let pattern = if self.check(&TokenKind::LParen) {
            // Destructuring: `use (x, y, z) = "path"` or `use (print = my_print) = "path"`
            self.advance(); // consume `(`
            let mut fields = Vec::new();
            while !self.check(&TokenKind::RParen) && !self.at_eof() {
                let field_start = self.cur_span();
                let first = self.expect_ident()?;
                // Check for rename syntax: `exported_name = local_alias`
                let (name, binding) = if self.eat(TokenKind::Eq) {
                    let alias = self.expect_ident()?;
                    (first, Some(alias))
                } else {
                    (first, None)
                };
                let field_span = field_start.merge(self.cur_span());
                fields.push(StructPatternField {
                    name,
                    binding,
                    span: field_span,
                });
                if !self.eat(TokenKind::Comma) {
                    break;
                }
            }
            self.expect(TokenKind::RParen)?;
            let span = self.cur_span();
            Pattern::Struct { fields, span }
        } else {
            // Namespace: `use name = "path"`
            let name_span = self.cur_span();
            let name = self.expect_ident()?;
            Pattern::Bind(name, name_span)
        };

        self.expect(TokenKind::Eq)?;

        // The path is a string literal.
        let path = match self.cur_kind().clone() {
            TokenKind::Str(parts) => {
                // A simple string (no interpolation) for paths.
                if parts.len() == 1 {
                    if let StringPart::Raw(s) = &parts[0] {
                        let path = s.clone();
                        self.advance();
                        path
                    } else {
                        return Err(self.error("module path must be a plain string".into()));
                    }
                } else if parts.is_empty() {
                    self.advance();
                    String::new()
                } else {
                    return Err(
                        self.error("module path must be a plain string (no interpolation)".into())
                    );
                }
            }
            _ => return Err(self.error("expected string literal for module path".into())),
        };

        self.eat_terminators();
        let span = start.merge(self.cur_span());
        Ok(UseDecl {
            pattern,
            path,
            span,
        })
    }

    /// Parse a declaration (optionally preceded by `pub`).
    fn parse_decl(&mut self) -> Result<Decl, ParseError> {
        let start = self.cur_span();
        let public = self.eat(TokenKind::Pub);

        let kind = if self.cur_is_def_family() {
            let name = match self.cur_kind() {
                TokenKind::Ident(s) => s.clone(),
                _ => unreachable!(),
            };
            self.advance();
            match name.as_str() {
                "def" => DeclKind::Def(self.parse_def(start)?),
                "defmacro" => DeclKind::Defmacro(self.parse_defmacro(start)?),
                _ => unreachable!(),
            }
        } else {
            return Err(self.error(format!(
                "expected declaration (`def`, `defmacro`), found {}",
                self.cur_kind()
            )));
        };

        let span = start.merge(self.cur_span());
        Ok(Decl { public, kind, span })
    }

    // ── def ───────────────────────────────────────────────────────────────────

    /// Parse the body of a `def` declaration (after consuming the `def` keyword).
    ///
    /// Handles value bindings, type aliases, and function/method definitions:
    /// ```aura
    /// def pi = 3.14159
    /// def a = 1, b = 2
    /// def[T] Result = enum(ok: T, err: String)
    /// def Point = (x: Int, y: Int)
    /// def add(a: Int, b: Int) -> Int { a + b }
    /// def[T: Show] show(t: T) { println(t.to_string()) }
    /// def Point.distance(self, other: Point) -> Float { ... }
    /// ```
    fn parse_def(&mut self, start: Span) -> Result<DefDecl, ParseError> {
        let mut bindings = Vec::new();
        loop {
            let b_start = self.cur_span();

            // Optional generic type parameters: `[T, U: Bound]`
            let type_params = self.parse_type_params_constrained()?;

            // Destructuring global binding: `def (a, b) = expr`
            if type_params.is_empty() && self.check(&TokenKind::LParen) {
                let saved = self.cursor;
                self.advance(); // consume `(`
                let is_named_field = matches!(self.cur_kind(), TokenKind::Ident(_))
                    && matches!(self.peek_kind(), TokenKind::Colon);
                let is_positional_tuple = matches!(
                    self.cur_kind(),
                    TokenKind::Ident(s) if s.chars().next().map(char::is_uppercase).unwrap_or(false)
                );
                self.cursor = saved;

                if !is_named_field && !is_positional_tuple {
                    let pattern = self.parse_pattern()?;
                    self.expect(TokenKind::Eq)?;
                    let value = self.parse_expr(0)?;
                    let b_span = b_start.merge(self.cur_span());
                    bindings.push(DefBinding::Value {
                        pattern,
                        init: Box::new(value),
                        span: b_span,
                    });
                    if !self.eat(TokenKind::Comma) {
                        break;
                    }
                    continue;
                }
            }

            // Parse optional receiver prefix: `Type.name` or just `name`.
            let name = self.expect_ident()?;
            let (receiver, func_name) = if self.eat(TokenKind::Dot) {
                let method_name = self.expect_ident()?;
                (Some(name), method_name)
            } else if let TokenKind::DotIdent(method_name) = self.cur_kind().clone() {
                self.advance();
                (Some(name), method_name)
            } else {
                (None, name)
            };

            // If followed by `(`, this is a function/method definition.
            if self.check(&TokenKind::LParen) {
                let params = self.parse_param_list()?;
                let return_type = if self.eat(TokenKind::Arrow) {
                    Some(self.parse_type_expr()?)
                } else {
                    None
                };
                let body = self.parse_block()?;
                self.eat_terminators();
                let b_span = b_start.merge(self.cur_span());
                bindings.push(DefBinding::FuncDef {
                    receiver,
                    name: func_name,
                    type_params,
                    params,
                    return_type,
                    body,
                    span: b_span,
                });
                // FuncDef bindings don't use comma-chaining; stop after one.
                break;
            }

            // Not a function def — must be `=` for a value or type alias.
            // (receiver.name without `(` is not valid; just use `func_name` as binding name
            //  and let `=` follow normally.)
            let full_name = if let Some(recv) = receiver {
                // `Receiver.name = ...` is not a valid non-function def; error.
                return Err(self.error(format!(
                    "expected `(` for method definition after `{recv}.{func_name}`"
                )));
            } else {
                func_name
            };

            self.expect(TokenKind::Eq)?;

            let is_type_alias = !type_params.is_empty()
                || matches!(self.cur_kind(), TokenKind::Ident(s) if matches!(s.as_str(), "union" | "enum" | "interface"))
                || (self.check(&TokenKind::LParen)
                    && {
                        let saved = self.cursor;
                        self.advance();
                        let is_named_field = matches!(self.cur_kind(), TokenKind::Ident(_))
                            && matches!(self.peek_kind(), TokenKind::Colon);
                        let is_positional_tuple = matches!(
                            self.cur_kind(),
                            TokenKind::Ident(s) if s.chars().next().map(char::is_uppercase).unwrap_or(false)
                        );
                        self.cursor = saved;
                        is_named_field || is_positional_tuple
                    });

            if is_type_alias {
                let ty = self.parse_type_expr()?;
                let b_span2 = b_start.merge(self.cur_span());
                bindings.push(DefBinding::TypeAlias {
                    name: full_name,
                    type_params,
                    ty,
                    span: b_span2,
                });
            } else {
                let value = self.parse_expr(0)?;
                let b_span2 = b_start.merge(self.cur_span());
                bindings.push(DefBinding::Value {
                    pattern: Pattern::Bind(full_name, b_start),
                    init: Box::new(value),
                    span: b_span2,
                });
            }

            if !self.eat(TokenKind::Comma) {
                break;
            }
        }
        self.eat_terminators();
        let span = start.merge(self.cur_span());
        Ok(DefDecl { bindings, span })
    }

    // ── defn (removed — parse_defn no longer exists) ──────────────────────────

    // ── defmacro ──────────────────────────────────────────────────────────────

    /// Parse a `defmacro` declaration.  The body, if present, is stored as an
    /// AST block but is not expanded by the current implementation.
    fn parse_defmacro(&mut self, start: Span) -> Result<DefmacroDecl, ParseError> {
        let name = self.expect_ident()?;
        let type_params = self.parse_type_params_constrained()?;
        let params = self.parse_param_list()?;
        let return_type = if self.eat(TokenKind::Arrow) {
            Some(self.parse_type_expr()?)
        } else {
            None
        };
        let body = if self.check(&TokenKind::LBrace) {
            Some(self.parse_block()?)
        } else {
            self.eat_terminators();
            None
        };
        let span = start.merge(self.cur_span());
        Ok(DefmacroDecl {
            name,
            type_params,
            params,
            return_type,
            body,
            span,
        })
    }

    // ─────────────────────────────────────────────────────────────────────────
    // Parameter and type helpers
    // ─────────────────────────────────────────────────────────────────────────

    /// Parse an optional `[T, U: Bound, V: (B1, B2)]` type parameter list.
    ///
    /// Each type parameter has an optional constraint after `:`:
    /// - `T` — unconstrained
    /// - `T: Show` — single constraint
    /// - `T: (Show, Eq)` — multiple constraints (tuple syntax)
    fn parse_type_params_constrained(&mut self) -> Result<Vec<TypeParam>, ParseError> {
        if !self.check(&TokenKind::LBracket) {
            return Ok(Vec::new());
        }
        self.advance(); // consume `[`
        let mut params = Vec::new();
        while !self.check(&TokenKind::RBracket) && !self.at_eof() {
            let p_start = self.cur_span();
            let name = self.expect_ident()?;
            let constraints = if self.eat(TokenKind::Colon) {
                if self.check(&TokenKind::LParen) {
                    // Multi-constraint: `T: (B1, B2)`
                    self.advance(); // consume `(`
                    let mut cs = Vec::new();
                    while !self.check(&TokenKind::RParen) && !self.at_eof() {
                        cs.push(self.parse_type_expr()?);
                        if !self.eat(TokenKind::Comma) {
                            break;
                        }
                    }
                    self.expect(TokenKind::RParen)?;
                    cs
                } else {
                    // Single constraint: `T: Bound`
                    vec![self.parse_type_expr()?]
                }
            } else {
                Vec::new()
            };
            let p_span = p_start.merge(self.cur_span());
            params.push(TypeParam {
                name,
                constraints,
                span: p_span,
            });
            if !self.eat(TokenKind::Comma) {
                break;
            }
        }
        self.expect(TokenKind::RBracket)?;
        Ok(params)
    }

    /// Parse a `(param, param, ...)` parameter list.
    fn parse_param_list(&mut self) -> Result<Vec<Param>, ParseError> {
        self.expect(TokenKind::LParen)?;
        let mut params = Vec::new();
        while !self.check(&TokenKind::RParen) && !self.at_eof() {
            params.push(self.parse_param()?);
            if !self.eat(TokenKind::Comma) {
                break;
            }
        }
        self.expect(TokenKind::RParen)?;
        Ok(params)
    }

    /// Parse a single parameter.
    ///
    /// Forms:
    /// - `name` — bare name, no type
    /// - `name: Type` — name with type
    /// - `internal external: Type` — internal name + external label + type
    fn parse_param(&mut self) -> Result<Param, ParseError> {
        let start = self.cur_span();
        let first = self.expect_ident_or_self()?;

        // Two-identifier form: `internal external_label: Type`
        let (internal, label) = if matches!(self.cur_kind(), TokenKind::Ident(_)) {
            let second = self.expect_ident_or_self()?;
            (first, Some(second))
        } else {
            (first, None)
        };

        let ty = if self.eat(TokenKind::Colon) {
            Some(self.parse_type_expr()?)
        } else {
            None
        };

        let span = start.merge(self.cur_span());
        Ok(Param {
            internal,
            label,
            ty,
            span,
        })
    }

    /// Parse a type expression.
    ///
    /// ```text
    /// Int
    /// List[T]
    /// Dict[String, Int]
    /// (Int, String)
    /// ```
    fn parse_type_expr(&mut self) -> Result<TypeExpr, ParseError> {
        let start = self.cur_span();

        if self.check(&TokenKind::LParen) {
            return self.parse_tuple_or_struct_type(start);
        }

        // Handle `union(T, U, ...)`, `enum(name: T, ...)`, `interface(name: T, ...)`.
        if let TokenKind::Ident(kw) = self.cur_kind().clone() {
            match kw.as_str() {
                "union" => {
                    self.advance();
                    self.expect(TokenKind::LParen)?;
                    let mut variants = Vec::new();
                    while !self.check(&TokenKind::RParen) && !self.at_eof() {
                        variants.push(self.parse_type_expr()?);
                        if !self.eat(TokenKind::Comma) {
                            break;
                        }
                    }
                    self.expect(TokenKind::RParen)?;
                    let span = start.merge(self.cur_span());
                    return Ok(TypeExpr::Union(variants, span));
                }
                "enum" => {
                    self.advance();
                    self.expect(TokenKind::LParen)?;
                    let mut variants = Vec::new();
                    while !self.check(&TokenKind::RParen) && !self.at_eof() {
                        let v_start = self.cur_span();
                        let name = self.expect_ident()?;
                        let ty = if self.eat(TokenKind::Colon) {
                            Some(self.parse_type_expr()?)
                        } else {
                            None
                        };
                        let v_span = v_start.merge(self.cur_span());
                        variants.push(EnumVariant {
                            name,
                            ty,
                            span: v_span,
                        });
                        if !self.eat(TokenKind::Comma) {
                            break;
                        }
                    }
                    self.expect(TokenKind::RParen)?;
                    let span = start.merge(self.cur_span());
                    return Ok(TypeExpr::Enum(variants, span));
                }
                "interface" => {
                    self.advance();
                    self.expect(TokenKind::LParen)?;
                    let mut fields = Vec::new();
                    while !self.check(&TokenKind::RParen) && !self.at_eof() {
                        let f_start = self.cur_span();
                        let field_name = self.expect_ident()?;
                        self.expect(TokenKind::Colon)?;
                        let ty = self.parse_type_expr()?;
                        let f_span = f_start.merge(self.cur_span());
                        fields.push(TypedField {
                            name: field_name,
                            ty,
                            span: f_span,
                        });
                        if !self.eat(TokenKind::Comma) {
                            break;
                        }
                    }
                    self.expect(TokenKind::RParen)?;
                    let span = start.merge(self.cur_span());
                    return Ok(TypeExpr::Interface(fields, span));
                }
                _ => {}
            }
        }

        let name = self.expect_ident()?;
        let args = if self.check(&TokenKind::LBracket) {
            self.advance(); // consume `[`
            let mut args = Vec::new();
            while !self.check(&TokenKind::RBracket) && !self.at_eof() {
                args.push(self.parse_type_expr()?);
                if !self.eat(TokenKind::Comma) {
                    break;
                }
            }
            self.expect(TokenKind::RBracket)?;
            args
        } else {
            Vec::new()
        };

        let span = start.merge(self.cur_span());
        Ok(TypeExpr::Named { name, args, span })
    }

    /// Parse a `(T, U)` tuple type or `(x: T, y: U)` struct type.
    fn parse_tuple_or_struct_type(&mut self, start: Span) -> Result<TypeExpr, ParseError> {
        self.expect(TokenKind::LParen)?;
        let mut items: Vec<(Option<String>, TypeExpr)> = Vec::new();

        while !self.check(&TokenKind::RParen) && !self.at_eof() {
            // Peek ahead: `name : Type` means a named field.
            let named = matches!(self.peek_kind(), TokenKind::Colon)
                && matches!(self.cur_kind(), TokenKind::Ident(_));
            if named {
                let field_start = self.cur_span();
                let field_name = self.expect_ident()?;
                self.expect(TokenKind::Colon)?;
                let ty = self.parse_type_expr()?;
                items.push((Some(field_name), ty));
                let _ = field_start; // used for span only
            } else {
                let ty = self.parse_type_expr()?;
                items.push((None, ty));
            }
            if !self.eat(TokenKind::Comma) {
                break;
            }
        }
        self.expect(TokenKind::RParen)?;
        let span = start.merge(self.cur_span());

        // If all items are named → struct type; otherwise → tuple type.
        let all_named = items.iter().all(|(n, _)| n.is_some());
        if all_named && !items.is_empty() {
            let fields = items
                .into_iter()
                .map(|(n, ty)| TypedField {
                    name: n.unwrap(),
                    ty,
                    span,
                })
                .collect();
            Ok(TypeExpr::Struct(fields, span))
        } else {
            let tys = items.into_iter().map(|(_, ty)| ty).collect();
            Ok(TypeExpr::Tuple(tys, span))
        }
    }

    // ─────────────────────────────────────────────────────────────────────────
    // Statement parsing
    // ─────────────────────────────────────────────────────────────────────────

    /// Parse one statement inside a block.
    fn parse_stmt(&mut self) -> Result<Stmt, ParseError> {
        match self.cur_kind() {
            TokenKind::Let => Ok(Stmt::Let(self.parse_let()?)),
            TokenKind::Return => Ok(Stmt::Return(self.parse_return()?)),
            TokenKind::Break => Ok(Stmt::Break(self.parse_break()?)),
            TokenKind::Continue => Ok(Stmt::Continue(self.parse_continue()?)),
            TokenKind::Ident(s) if s == "def" => Ok(Stmt::Def(self.parse_def_stmt()?)),
            _ => Ok(Stmt::Expr(self.parse_expr_stmt()?)),
        }
    }

    /// Parse `let x [: T] = expr, y = expr;`
    fn parse_let(&mut self) -> Result<LetStmt, ParseError> {
        let start = self.cur_span();
        self.expect(TokenKind::Let)?;
        let bindings = self.parse_local_bindings()?;
        self.eat_terminators();
        let span = start.merge(self.cur_span());
        Ok(LetStmt { bindings, span })
    }

    /// Parse `def x = expr;` or `def f(params) { body }` as a local statement.
    fn parse_def_stmt(&mut self) -> Result<DefStmt, ParseError> {
        let start = self.cur_span();
        // consume `def` identifier
        self.expect_ident()?; // "def"
        let def_decl = self.parse_def(start)?;
        let span = start.merge(self.cur_span());
        Ok(DefStmt {
            bindings: def_decl.bindings,
            span,
        })
    }

    /// Parse the shared `name [: Type] = expr, ...` part of `let` / `const`.
    fn parse_local_bindings(&mut self) -> Result<Vec<LocalBinding>, ParseError> {
        let mut bindings = Vec::new();
        loop {
            let b_start = self.cur_span();
            let raw_pattern = self.parse_pattern()?;

            // `parse_pattern` eagerly consumes `name: Type` as a `Pattern::TypeCheck`.
            // For let/const bindings the `: Type` is the type *annotation* on the
            // binding itself, not a runtime type-check pattern.  Lift it out here so
            // `LocalBinding.ty` is populated and the pattern reduces to a simple bind.
            let (pattern, ty) = match raw_pattern {
                Pattern::TypeCheck { name, ty, span } => (Pattern::Bind(name, span), Some(ty)),
                other => (other, None),
            };

            self.expect(TokenKind::Eq)?;
            let init = self.parse_expr(0)?;
            let b_span = b_start.merge(self.cur_span());
            bindings.push(LocalBinding {
                pattern,
                ty,
                init,
                span: b_span,
            });
            if !self.eat(TokenKind::Comma) {
                break;
            }
            // Don't consume comma if the next token starts a new statement
            // (handles `let x = 1, b = 2;` vs `let x = 1; b = 2;`).
        }
        Ok(bindings)
    }

    /// Parse `return [' label] [expr]`
    fn parse_return(&mut self) -> Result<ReturnStmt, ParseError> {
        let start = self.cur_span();
        self.expect(TokenKind::Return)?;

        // Optional `'label` atom.
        let label = if let TokenKind::Atom(name) = self.cur_kind().clone() {
            self.advance();
            Some(name)
        } else {
            None
        };

        // Optional value expression (absent at a `;` / newline / `}`).
        let value = if self.is_at_stmt_end() {
            None
        } else {
            Some(Box::new(self.parse_expr(0)?))
        };

        self.eat_terminators();
        let span = start.merge(self.cur_span());
        Ok(ReturnStmt { label, value, span })
    }

    /// Parse `break ['label] [value]`
    fn parse_break(&mut self) -> Result<BreakStmt, ParseError> {
        let start = self.cur_span();
        self.expect(TokenKind::Break)?;

        let label = if let TokenKind::Atom(name) = self.cur_kind().clone() {
            self.advance();
            Some(name)
        } else {
            None
        };

        let value = if self.is_at_stmt_end() {
            None
        } else {
            Some(Box::new(self.parse_expr(0)?))
        };

        self.eat_terminators();
        let span = start.merge(self.cur_span());
        Ok(BreakStmt { label, value, span })
    }

    /// Parse `continue ['label]`
    fn parse_continue(&mut self) -> Result<ContinueStmt, ParseError> {
        let start = self.cur_span();
        self.expect(TokenKind::Continue)?;

        let label = if let TokenKind::Atom(name) = self.cur_kind().clone() {
            self.advance();
            Some(name)
        } else {
            None
        };

        self.eat_terminators();
        let span = start.merge(self.cur_span());
        Ok(ContinueStmt { label, span })
    }

    /// Return `true` if the current position looks like the end of a statement
    /// (i.e., a value expression cannot follow here).
    fn is_at_stmt_end(&self) -> bool {
        matches!(
            self.cur_kind(),
            TokenKind::Semicolon | TokenKind::Newline | TokenKind::RBrace | TokenKind::Eof
        )
    }

    /// Parse an expression statement (expression followed by `;` or implicit newline).
    fn parse_expr_stmt(&mut self) -> Result<ExprStmt, ParseError> {
        let start = self.cur_span();
        let expr = self.parse_expr(0)?;
        self.eat_terminators();
        let span = start.merge(self.cur_span());
        Ok(ExprStmt { expr, span })
    }

    // ─────────────────────────────────────────────────────────────────────────
    // Block parsing
    // ─────────────────────────────────────────────────────────────────────────

    /// Parse a `{ ... }` block.
    ///
    /// Blocks contain:
    /// - Zero or more statements.
    /// - An optional trailing expression (no trailing `;`).
    pub fn parse_block(&mut self) -> Result<Block, ParseError> {
        let start = self.cur_span();
        self.expect(TokenKind::LBrace)?;

        let mut stmts = Vec::new();

        loop {
            // Eat leading terminators.
            while self.eat(TokenKind::Semicolon) || self.eat(TokenKind::Newline) {}

            if self.check(&TokenKind::RBrace) || self.at_eof() {
                break;
            }

            // Attempt to parse the next statement.  If this is the last item and
            // it's not terminated by `;`, it becomes the tail expression.
            let is_let_or_control = matches!(
                self.cur_kind(),
                TokenKind::Let | TokenKind::Return | TokenKind::Break | TokenKind::Continue
            ) || matches!(self.cur_kind(), TokenKind::Ident(s) if s == "def");

            if is_let_or_control {
                let stmt = self.parse_stmt()?;
                stmts.push(stmt);
                continue;
            }

            // Parse as expression; check for terminator to decide stmt vs tail.
            let expr = self.parse_expr(0)?;

            // Skip implicit newlines emitted right after a `}` inside expressions
            // (e.g., `if (...) { } else { }` continuation).
            while self.eat(TokenKind::Newline) {}

            if self.eat(TokenKind::Semicolon) {
                // Expression statement.
                let span = expr.span();
                stmts.push(Stmt::Expr(ExprStmt { expr, span }));
            } else if self.check(&TokenKind::RBrace) || self.at_eof() {
                // Tail expression — forms the block's return value.
                let tail = expr;
                // Consume closing `}`.
                self.expect(TokenKind::RBrace)?;
                let span = start.merge(self.cur_span());
                return Ok(Block {
                    stmts,
                    tail: Some(Box::new(tail)),
                    span,
                });
            } else {
                // No terminator and not at `}` — treat as an expr statement and
                // let the next iteration deal with what follows.
                let span = expr.span();
                stmts.push(Stmt::Expr(ExprStmt { expr, span }));
            }
        }

        self.expect(TokenKind::RBrace)?;
        let span = start.merge(self.cur_span());
        Ok(Block {
            stmts,
            tail: None,
            span,
        })
    }

    /// Parse an optional `'atom:` label followed by a block or closure.
    ///
    /// The `{ }` content may be either a plain block *or* a closure arm
    /// (`{ params -> body }`).  `parse_block_or_closure` handles both;
    /// when the result is a closure we wrap it as the tail expression of
    /// an otherwise-empty `Block` so that the caller receives a uniform
    /// `LabelledBlock` regardless of which form was written.
    fn parse_labelled_block(&mut self) -> Result<LabelledBlock, ParseError> {
        let start = self.cur_span();
        let label = if let TokenKind::Atom(name) = self.cur_kind().clone() {
            let name = name.clone();
            self.advance(); // consume atom
            self.expect(TokenKind::Colon)?;
            Some(name)
        } else {
            None
        };
        let expr = self.parse_block_or_closure()?;
        let block = match expr {
            Expr::Block(b) => b,
            // Closure form `{ params -> body }`: wrap as tail of an empty block
            // so that the rest of the compiler sees a uniform Block type.
            other => {
                let s = other.span();
                Block {
                    stmts: vec![],
                    tail: Some(Box::new(other)),
                    span: s,
                }
            }
        };
        let span = start.merge(self.cur_span());
        Ok(LabelledBlock { label, block, span })
    }

    /// Parse a builtin reference: `builtin("name")`
    fn parse_builtin(&mut self, start: Span) -> Result<Expr, ParseError> {
        self.expect(TokenKind::LParen)?;
        let name = match self.cur_kind().clone() {
            TokenKind::Str(parts) => {
                self.advance();
                // Extract the raw string from parts
                if parts.len() == 1 {
                    if let StringPart::Raw(s) = &parts[0] {
                        s.clone()
                    } else {
                        return Err(
                            self.error("builtin name must be a plain string literal".to_string())
                        );
                    }
                } else {
                    return Err(
                        self.error("builtin name must be a plain string literal".to_string())
                    );
                }
            }
            _ => return Err(self.error("expected string literal for builtin name".to_string())),
        };
        self.expect(TokenKind::RParen)?;
        let span = start.merge(self.cur_span());
        Ok(Expr::Builtin { name, span })
    }

    // ─────────────────────────────────────────────────────────────────────────
    // Expression parsing — Pratt precedence climbing
    // ─────────────────────────────────────────────────────────────────────────

    /// Parse an expression with minimum binding power `min_bp`.
    ///
    /// This is the heart of the Pratt parser.  `min_bp = 0` parses any expression.
    pub fn parse_expr(&mut self, min_bp: u8) -> Result<Expr, ParseError> {
        // ── Prefix ────────────────────────────────────────────────────────────
        let mut lhs = self.parse_prefix()?;

        // ── Infix / Postfix loop ──────────────────────────────────────────────
        loop {
            // Peek at postfix / infix operators.
            let (l_bp, r_bp_or_none) = infix_binding_power(self.cur_kind());

            if l_bp < min_bp {
                break;
            }

            let op_span = self.cur_span();

            match self.cur_kind().clone() {
                // ── Assignment (right-assoc) ───────────────────────────────────
                TokenKind::Eq => {
                    self.advance();
                    let rhs = self.parse_expr(r_bp_or_none.unwrap_or(1))?;
                    let span = lhs.span().merge(rhs.span());
                    lhs = Expr::Assign {
                        target: Box::new(lhs),
                        value: Box::new(rhs),
                        span,
                    };
                }

                // ── Range `..` ────────────────────────────────────────────────
                TokenKind::DotDot => {
                    self.advance();
                    let rhs = self.parse_expr(r_bp_or_none.unwrap_or(1))?;
                    let span = lhs.span().merge(rhs.span());
                    lhs = Expr::Range {
                        start: Box::new(lhs),
                        end: Box::new(rhs),
                        span,
                    };
                }

                // ── Binary operators ──────────────────────────────────────────
                TokenKind::PipePipe
                | TokenKind::AmpAmp
                | TokenKind::EqEq
                | TokenKind::BangEq
                | TokenKind::Lt
                | TokenKind::Gt
                | TokenKind::LtEq
                | TokenKind::GtEq
                | TokenKind::Plus
                | TokenKind::Minus
                | TokenKind::Star
                | TokenKind::Slash
                | TokenKind::Percent => {
                    let op = token_to_binop(self.cur_kind());
                    self.advance();
                    let rhs = self.parse_expr(r_bp_or_none.unwrap_or(l_bp + 1))?;
                    let span = lhs.span().merge(rhs.span());
                    lhs = Expr::Binary {
                        op,
                        lhs: Box::new(lhs),
                        rhs: Box::new(rhs),
                        span,
                    };
                }

                // ── Elvis `?:` ────────────────────────────────────────────────
                TokenKind::QuestionColon => {
                    self.advance();
                    let rhs = self.parse_expr(r_bp_or_none.unwrap_or(l_bp + 1))?;
                    let span = lhs.span().merge(rhs.span());
                    lhs = Expr::Elvis {
                        left: Box::new(lhs),
                        right: Box::new(rhs),
                        span,
                    };
                }

                // ── Cast `: Type` ─────────────────────────────────────────────
                TokenKind::Colon => {
                    self.advance();
                    let ty = self.parse_type_expr()?;
                    let span = lhs.span().merge(ty.span());
                    lhs = Expr::Cast {
                        expr: Box::new(lhs),
                        ty,
                        span,
                    };
                }

                // ── Postfix: field access `.name` or `.0` ─────────────────────
                TokenKind::Dot => {
                    self.advance();
                    // Allow numeric field access: `tuple.0`, `tuple.1`, …
                    let field = if let TokenKind::Int(n) = self.cur_kind().clone() {
                        let s = n.to_string();
                        self.advance();
                        s
                    } else {
                        self.expect_ident()?
                    };
                    // If followed by `(`, this is a method call.
                    if self.check(&TokenKind::LParen) {
                        let (args, trailing) = self.parse_call_args()?;
                        let span = lhs.span().merge(self.cur_span());
                        // Method calls are represented as `FieldAccess` of the object
                        // followed by a `Call` of that field.
                        let method_span = op_span.merge(self.cur_span());
                        let callee = Expr::FieldAccess {
                            object: Box::new(lhs),
                            field,
                            span: method_span,
                        };
                        lhs = Expr::Call {
                            callee: Box::new(callee),
                            args,
                            trailing,
                            span,
                        };
                    } else {
                        let span = lhs.span().merge(self.cur_span());
                        lhs = Expr::FieldAccess {
                            object: Box::new(lhs),
                            field,
                            span,
                        };
                    }
                }

                // ── Postfix: method call via DotIdent `.name(...)` ──────────────
                // When `.method` appears after an expression (not at the start),
                // treat it as a method call.
                TokenKind::DotIdent(field) => {
                    self.advance();
                    // If followed by `(`, this is a method call.
                    if self.check(&TokenKind::LParen) {
                        let (args, trailing) = self.parse_call_args()?;
                        let span = lhs.span().merge(self.cur_span());
                        let callee = Expr::FieldAccess {
                            object: Box::new(lhs),
                            field,
                            span: op_span.merge(self.cur_span()),
                        };
                        lhs = Expr::Call {
                            callee: Box::new(callee),
                            args,
                            trailing,
                            span,
                        };
                    } else {
                        // Field access without call
                        let span = lhs.span().merge(self.cur_span());
                        lhs = Expr::FieldAccess {
                            object: Box::new(lhs),
                            field,
                            span,
                        };
                    }
                }

                // ── Postfix: index access `[expr]` ────────────────────────────
                TokenKind::LBracket => {
                    self.advance();
                    let index = self.parse_expr(0)?;
                    self.expect(TokenKind::RBracket)?;
                    let span = lhs.span().merge(self.cur_span());
                    lhs = Expr::Index {
                        object: Box::new(lhs),
                        index: Box::new(index),
                        span,
                    };
                }

                // ── Postfix: call `(args)` ────────────────────────────────────
                TokenKind::LParen => {
                    let (args, trailing) = self.parse_call_args()?;
                    let span = lhs.span().merge(self.cur_span());
                    lhs = Expr::Call {
                        callee: Box::new(lhs),
                        args,
                        trailing,
                        span,
                    };
                }

                // ── Postfix: safe navigation `?.name` ─────────────────────────
                TokenKind::QuestionDot => {
                    self.advance();
                    let field = self.expect_ident()?;
                    let span = lhs.span().merge(self.cur_span());
                    lhs = Expr::SafeNav {
                        object: Box::new(lhs),
                        field,
                        span,
                    };
                }

                // ── Postfix: force unwrap `!!` ────────────────────────────────
                TokenKind::BangBang => {
                    self.advance();
                    let span = lhs.span().merge(op_span);
                    lhs = Expr::ForceUnwrap {
                        expr: Box::new(lhs),
                        span,
                    };
                }

                // ── Postfix: increment / decrement ────────────────────────────
                TokenKind::PlusPlus => {
                    self.advance();
                    let span = lhs.span().merge(op_span);
                    lhs = Expr::PostIncrement {
                        target: Box::new(lhs),
                        span,
                    };
                }
                TokenKind::MinusMinus => {
                    self.advance();
                    let span = lhs.span().merge(op_span);
                    lhs = Expr::PostDecrement {
                        target: Box::new(lhs),
                        span,
                    };
                }

                // Trailing lambda continuation: if the next token is an identifier
                // followed by a `{`, it might be a continuation trailing arg.
                // This is handled in `parse_call_args` / primary call parsing.
                //
                // Trailing lambda WITHOUT parens: `expr { ... }` or `expr label { ... }`.
                // Only trigger at top-level expression context (min_bp == 0).
                _ => {
                    // `expr { ... }` — implicit no-arg call with one trailing lambda.
                    if min_bp == 0 && self.check(&TokenKind::LBrace) {
                        let t_start = self.cur_span();
                        let block = self.parse_labelled_block()?;
                        let t_span = t_start.merge(block.span);
                        let trailing = vec![TrailingArg {
                            label: None,
                            block,
                            span: t_span,
                        }];
                        let span = lhs.span().merge(t_span);
                        lhs = Expr::Call {
                            callee: Box::new(lhs),
                            args: vec![],
                            trailing,
                            span,
                        };
                        continue;
                    }
                    // `expr label { ... }` — implicit no-arg call with one labelled trailing lambda.
                    if min_bp == 0 {
                        if let TokenKind::Ident(label_name) = self.cur_kind().clone() {
                            let next = self.peek_kind().clone();
                            if matches!(next, TokenKind::LBrace | TokenKind::Atom(_)) {
                                self.advance(); // consume label name
                                let t_start = self.cur_span();
                                let block = self.parse_labelled_block()?;
                                let t_span = t_start.merge(block.span);
                                let trailing = vec![TrailingArg {
                                    label: Some(label_name),
                                    block,
                                    span: t_span,
                                }];
                                let span = lhs.span().merge(t_span);
                                lhs = Expr::Call {
                                    callee: Box::new(lhs),
                                    args: vec![],
                                    trailing,
                                    span,
                                };
                                // Continue to pick up further trailing args via parse_trailing_args
                                // logic — but since we're in the Pratt loop, just continue
                                // and let subsequent iterations handle more `{ }` or `label { }`.
                                continue;
                            }
                        }
                    }
                    break;
                }
            }

            let _ = op_span; // avoid unused warning
        }

        Ok(lhs)
    }

    /// Parse a prefix expression or a primary.
    fn parse_prefix(&mut self) -> Result<Expr, ParseError> {
        let start = self.cur_span();

        match self.cur_kind().clone() {
            // ── Prefix unary ─────────────────────────────────────────────────
            TokenKind::Minus => {
                self.advance();
                let expr = self.parse_expr(15)?; // right-bp for prefix
                let span = start.merge(self.cur_span());
                Ok(Expr::Unary {
                    op: UnOp::Neg,
                    expr: Box::new(expr),
                    span,
                })
            }
            TokenKind::Bang => {
                self.advance();
                let expr = self.parse_expr(15)?;
                let span = start.merge(self.cur_span());
                Ok(Expr::Unary {
                    op: UnOp::Not,
                    expr: Box::new(expr),
                    span,
                })
            }
            _ => self.parse_primary(),
        }
    }

    /// Parse a primary expression (the leaf nodes: literals, identifiers,
    /// collections, closures, control-flow forms, and parenthesised expressions).
    fn parse_primary(&mut self) -> Result<Expr, ParseError> {
        let start = self.cur_span();

        match self.cur_kind().clone() {
            // ── Literals ─────────────────────────────────────────────────────
            TokenKind::Int(n) => {
                self.advance();
                Ok(Expr::Int(n, start))
            }
            TokenKind::Float(n) => {
                self.advance();
                Ok(Expr::Float(n, start))
            }
            TokenKind::Str(parts) => {
                self.advance();
                Ok(Expr::Str(parts, start))
            }
            TokenKind::Char(c) => {
                self.advance();
                Ok(Expr::Char(c, start))
            }
            TokenKind::DotIdent(name) => {
                self.advance();
                Ok(Expr::DotIdent(name, start))
            }

            // ── Identifier / keyword-named calls ─────────────────────────────
            TokenKind::Ident(name) => {
                self.advance();
                let ident_span = start;
                // Check for special built-in call forms.
                match name.as_str() {
                    "if" => self.parse_if(ident_span),
                    "cases" => self.parse_cases(ident_span),
                    "loop" => self.parse_loop(ident_span),
                    "match" => self.parse_match(ident_span),
                    "builtin" => self.parse_builtin(ident_span),
                    _ => Ok(Expr::Ident(name, ident_span)),
                }
            }

            // ── `self` keyword ────────────────────────────────────────────────
            TokenKind::SelfKw => {
                self.advance();
                Ok(Expr::Ident("self".into(), start))
            }

            // ── Block / closure `{ ... }` ─────────────────────────────────────
            TokenKind::LBrace => self.parse_block_or_closure(),

            // ── Atom label prefix for labelled block `'label: { ... }` ────────
            TokenKind::Atom(_) => {
                let labelled = self.parse_labelled_block()?;
                // A standalone labelled block is represented as a Block expr.
                // The label is used by jump resolution, not stored on Expr::Block directly.
                // The compiler handles labelled-block semantics via LoopExpr/etc.
                // For standalone labelled blocks we drop the label here — full label
                // support is wired at the statement level.
                // TODO: represent labelled standalone blocks properly in a follow-up.
                let _ = labelled.span;
                Ok(Expr::Block(labelled.block))
            }

            // ── List / dict literal `[ ... ]` ─────────────────────────────────
            TokenKind::LBracket => self.parse_list_or_dict(),

            // ── Tuple / struct literal or grouping `( expr )` ─────────────────
            TokenKind::LParen => self.parse_paren_expr(),

            other => Err(self.error(format!("unexpected token {other} in expression"))),
        }
    }

    // ─────────────────────────────────────────────────────────────────────────
    // Block / closure parsing
    // ─────────────────────────────────────────────────────────────────────────

    /// Parse `{ ... }` which could be a plain block, a single-arm closure, or a
    /// multi-arm closure (pattern matching).
    ///
    /// Disambiguations:
    /// - `{ stmt; ... expr }` → `Expr::Block`
    /// - `{ params -> body }` → `Expr::Closure` (single arm)
    /// - `{ pattern, pattern -> body, pattern -> body }` → `Expr::Closure` (multi-arm)
    fn parse_block_or_closure(&mut self) -> Result<Expr, ParseError> {
        let start = self.cur_span();
        self.expect(TokenKind::LBrace)?;

        // Skip leading terminators.
        while self.eat(TokenKind::Semicolon) || self.eat(TokenKind::Newline) {}

        // Empty block `{ }` → bare block.
        if self.check(&TokenKind::RBrace) {
            self.advance();
            let span = start.merge(self.cur_span());
            return Ok(Expr::Block(Block {
                stmts: vec![],
                tail: None,
                span,
            }));
        }

        // Lookahead to distinguish closure forms from plain blocks.
        // A closure arm starts with patterns followed by `->` or `~`.
        // We tentatively scan for `->` or `~` before the next `,` or `}`.
        if self.looks_like_closure_arm() {
            return self.parse_closure_body(start);
        }

        // Otherwise, parse as a plain block body.
        // We already consumed `{`, so we parse statements until `}`.
        let mut stmts = Vec::new();
        loop {
            while self.eat(TokenKind::Semicolon) || self.eat(TokenKind::Newline) {}
            if self.check(&TokenKind::RBrace) || self.at_eof() {
                break;
            }

            let is_control = matches!(
                self.cur_kind(),
                TokenKind::Let | TokenKind::Return | TokenKind::Break | TokenKind::Continue
            ) || matches!(self.cur_kind(), TokenKind::Ident(s) if s == "def");

            if is_control {
                stmts.push(self.parse_stmt()?);
                continue;
            }

            let expr = self.parse_expr(0)?;
            while self.eat(TokenKind::Newline) {}

            if self.eat(TokenKind::Semicolon) {
                let span = expr.span();
                stmts.push(Stmt::Expr(ExprStmt { expr, span }));
            } else if self.check(&TokenKind::RBrace) || self.at_eof() {
                // Tail expression — forms the block's return value.
                self.expect(TokenKind::RBrace)?;
                let span = start.merge(self.cur_span());
                return Ok(Expr::Block(Block {
                    stmts,
                    tail: Some(Box::new(expr)),
                    span,
                }));
            } else {
                // No terminator and not at `}` — treat as an expr statement
                // (e.g. `if (...) { ... }` followed by more statements on the
                // next line, separated only by a newline-after-`}` which was
                // already consumed above).
                let span = expr.span();
                stmts.push(Stmt::Expr(ExprStmt { expr, span }));
            }
        }

        self.expect(TokenKind::RBrace)?;
        let span = start.merge(self.cur_span());
        Ok(Expr::Block(Block {
            stmts,
            tail: None,
            span,
        }))
    }

    /// Return `true` if the tokens from the current position look like a closure arm,
    /// i.e., we can find a `->` or `~` before a `;` that is not inside nested `{}`
    /// or `()` or `[]`.
    fn looks_like_closure_arm(&self) -> bool {
        let mut depth = 0usize;
        let mut i = self.cursor;
        while i < self.tokens.len() {
            match &self.tokens[i].kind {
                TokenKind::LParen | TokenKind::LBrace | TokenKind::LBracket => depth += 1,
                TokenKind::RParen | TokenKind::RBrace | TokenKind::RBracket => {
                    if depth == 0 {
                        return false; // hit closing `}` before seeing `->`
                    }
                    depth -= 1;
                }
                TokenKind::Arrow | TokenKind::Tilde if depth == 0 => return true,
                TokenKind::Semicolon | TokenKind::Newline | TokenKind::Eof => return false,
                _ => {}
            }
            i += 1;
        }
        false
    }

    /// Parse the body of a closure (single-arm or multi-arm), after `{` has been consumed.
    fn parse_closure_body(&mut self, start: Span) -> Result<Expr, ParseError> {
        let mut arms = Vec::new();

        loop {
            while self.eat(TokenKind::Semicolon) || self.eat(TokenKind::Newline) {}
            if self.check(&TokenKind::RBrace) || self.at_eof() {
                break;
            }

            let arm = self.parse_closure_arm()?;
            arms.push(arm);

            // Arms are comma-separated; the last arm may have a trailing comma.
            if !self.eat(TokenKind::Comma) {
                break;
            }
            while self.eat(TokenKind::Newline) {}
        }

        self.expect(TokenKind::RBrace)?;
        let span = start.merge(self.cur_span());
        Ok(Expr::Closure(Closure { arms, span }))
    }

    /// Parse one closure arm: `pattern, pattern [~ guard] -> body`
    fn parse_closure_arm(&mut self) -> Result<ClosureArm, ParseError> {
        let start = self.cur_span();

        // A guard-only arm (used in `cases`): `~ cond -> expr`
        if self.check(&TokenKind::Tilde) {
            self.advance();
            let guard = self.parse_expr(0)?;
            self.expect(TokenKind::Arrow)?;
            let body = self.parse_expr(0)?;
            let span = start.merge(body.span());
            return Ok(ClosureArm {
                patterns: vec![],
                guard: Some(guard),
                body,
                span,
            });
        }

        // Pattern list.
        let mut patterns = Vec::new();
        loop {
            patterns.push(self.parse_pattern()?);
            // Peek: if next is `,` followed by a pattern (not `-> or `~`), continue.
            if self.check(&TokenKind::Comma) {
                // Look ahead: is the next thing a pattern or a body?
                // If after the comma we'd see `->` or `~`, stop.
                let next_is_pattern = !matches!(
                    self.peek_kind(),
                    TokenKind::Arrow | TokenKind::Tilde | TokenKind::RBrace
                );
                if next_is_pattern {
                    self.advance(); // consume `,`
                } else {
                    break;
                }
            } else {
                break;
            }
        }

        // Optional guard `~ expr`.
        let guard = if self.eat(TokenKind::Tilde) {
            Some(self.parse_expr(0)?)
        } else {
            None
        };

        self.expect(TokenKind::Arrow)?;
        let body = self.parse_expr(0)?;
        let span = start.merge(body.span());
        Ok(ClosureArm {
            patterns,
            guard,
            body,
            span,
        })
    }

    /// Parse a single pattern (literal, identifier, wildcard, tuple, struct, constructor, or variant).
    fn parse_pattern(&mut self) -> Result<Pattern, ParseError> {
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

    // ─────────────────────────────────────────────────────────────────────────
    // Collection literals
    // ─────────────────────────────────────────────────────────────────────────

    /// Parse `[ ... ]` — either a list or a dict literal.
    ///
    /// Disambiguation: if the first item looks like `expr = expr`, it's a dict.
    fn parse_list_or_dict(&mut self) -> Result<Expr, ParseError> {
        let start = self.cur_span();
        self.expect(TokenKind::LBracket)?;

        if self.eat(TokenKind::RBracket) {
            // Empty list.
            let span = start.merge(self.cur_span());
            return Ok(Expr::List {
                items: vec![],
                span,
            });
        }

        // Peek ahead: if the first expression is followed by `=`, it's a dict.
        // We parse the first expression at min_bp=2 so that `=` (l_bp=1) is NOT
        // consumed as an assignment operator — it stays for the dict-key check below.
        let item_start = self.cur_span();
        let first_stmts = self.parse_collection_item_stmts()?;
        let first_val = self.parse_expr(2)?;

        if self.eat(TokenKind::Eq) {
            // Dict literal: `first_val = value, ...`
            let dict_start = item_start;
            let value = self.parse_expr(2)?;
            let entry_span = dict_start.merge(value.span());
            let mut entries = vec![DictEntry {
                key: first_val,
                value,
                span: entry_span,
            }];

            while self.eat(TokenKind::Comma) {
                if self.check(&TokenKind::RBracket) {
                    break;
                }
                let e_start = self.cur_span();
                let _stmts = self.parse_collection_item_stmts()?; // TODO: thread scoped stmts
                let key = self.parse_expr(2)?;
                self.expect(TokenKind::Eq)?;
                let val = self.parse_expr(2)?;
                let e_span = e_start.merge(val.span());
                entries.push(DictEntry {
                    key,
                    value: val,
                    span: e_span,
                });
            }
            self.expect(TokenKind::RBracket)?;
            let span = start.merge(self.cur_span());
            return Ok(Expr::Dict { entries, span });
        }

        // List literal.
        let first_span = item_start.merge(first_val.span());
        let mut items = vec![CollectionItem {
            stmts: first_stmts,
            value: first_val,
            span: first_span,
        }];

        while self.eat(TokenKind::Comma) {
            if self.check(&TokenKind::RBracket) {
                break;
            } // trailing comma
            let i_start = self.cur_span();
            let stmts = self.parse_collection_item_stmts()?;
            let val = self.parse_expr(0)?;
            let i_span = i_start.merge(val.span());
            items.push(CollectionItem {
                stmts,
                value: val,
                span: i_span,
            });
        }
        self.expect(TokenKind::RBracket)?;
        let span = start.merge(self.cur_span());
        Ok(Expr::List { items, span })
    }

    /// Parse the optional preliminary `let` statements in a collection item.
    /// These are scoped to the item only (e.g., `let x = 0; x++; x`).
    fn parse_collection_item_stmts(&mut self) -> Result<Vec<Stmt>, ParseError> {
        let mut stmts = Vec::new();
        // Consume as many `let` / expr `;` pairs as appear before
        // the final expression.  We can't easily distinguish "stmt before value"
        // from "the value itself" without speculative parsing, so we use a
        // simple heuristic: if `let` is present, it's always a stmt.
        while matches!(self.cur_kind(), TokenKind::Let) {
            stmts.push(self.parse_stmt()?);
        }
        Ok(stmts)
    }

    /// Parse `( ... )` — a grouped expression, positional tuple, or named-field struct.
    fn parse_paren_expr(&mut self) -> Result<Expr, ParseError> {
        let start = self.cur_span();
        self.expect(TokenKind::LParen)?;

        if self.eat(TokenKind::RParen) {
            // Empty parens = unit / Void.
            let span = start.merge(self.cur_span());
            return Ok(Expr::Tuple {
                items: vec![],
                span,
            });
        }

        // Peek to see if this is a named-field struct: `(name = value, ...)`.
        let is_struct = matches!(self.cur_kind(), TokenKind::Ident(_))
            && matches!(self.peek_kind(), TokenKind::Eq);

        if is_struct {
            return self.parse_struct_literal(start);
        }

        // Parse the first expression.
        let first = self.parse_expr(0)?;

        // If a single expression without comma, it's a grouping.
        if self.eat(TokenKind::RParen) {
            return Ok(first);
        }

        // Otherwise it's a tuple.
        self.expect(TokenKind::Comma)?;
        let first_span = first.span();
        let mut items = vec![CollectionItem {
            stmts: vec![],
            value: first,
            span: first_span,
        }];
        while !self.check(&TokenKind::RParen) && !self.at_eof() {
            let val = self.parse_expr(0)?;
            let s = val.span();
            items.push(CollectionItem {
                stmts: vec![],
                value: val,
                span: s,
            });
            if !self.eat(TokenKind::Comma) {
                break;
            }
        }
        self.expect(TokenKind::RParen)?;
        let span = start.merge(self.cur_span());
        Ok(Expr::Tuple { items, span })
    }

    /// Parse a named-field struct literal `(name = value, ...)`, after `(` was consumed.
    fn parse_struct_literal(&mut self, start: Span) -> Result<Expr, ParseError> {
        let mut fields = Vec::new();
        while !self.check(&TokenKind::RParen) && !self.at_eof() {
            let f_start = self.cur_span();
            let name = self.expect_ident()?;
            self.expect(TokenKind::Eq)?;
            let value = self.parse_expr(0)?;
            let f_span = f_start.merge(value.span());
            fields.push(FieldInit {
                name,
                value,
                span: f_span,
            });
            if !self.eat(TokenKind::Comma) {
                break;
            }
        }
        self.expect(TokenKind::RParen)?;
        let span = start.merge(self.cur_span());
        Ok(Expr::Struct { fields, span })
    }

    // ─────────────────────────────────────────────────────────────────────────
    // Call argument parsing
    // ─────────────────────────────────────────────────────────────────────────

    /// Parse `(args)` and any following trailing lambda arguments.
    ///
    /// Returns `(positional_args, trailing_args)`.
    fn parse_call_args(&mut self) -> Result<(Vec<Arg>, Vec<TrailingArg>), ParseError> {
        self.expect(TokenKind::LParen)?;
        let mut args = Vec::new();

        while !self.check(&TokenKind::RParen) && !self.at_eof() {
            let a_start = self.cur_span();
            // Check for named argument `name = expr`.
            let label = if matches!(self.cur_kind(), TokenKind::Ident(_))
                && matches!(self.peek_kind(), TokenKind::Eq)
            {
                let name = self.expect_ident()?;
                self.advance(); // consume `=`
                Some(name)
            } else {
                None
            };
            let value = self.parse_expr(0)?;
            let a_span = a_start.merge(value.span());
            args.push(Arg {
                label,
                value,
                span: a_span,
            });
            if !self.eat(TokenKind::Comma) {
                break;
            }
        }
        self.expect(TokenKind::RParen)?;

        // Trailing lambda arguments: `label? { ... }` chains.
        let trailing = self.parse_trailing_args()?;

        Ok((args, trailing))
    }

    /// Parse zero or more trailing lambda arguments after the `( )` close.
    ///
    /// ```aura
    /// do_stuff(12) task { doWork(); } finally { cleanup(); }
    ///              ^^^^ trailing         ^^^^^^^ continuation
    /// ```
    ///
    /// The implicit-semicolon rule means continuations must start on the
    /// SAME LINE as the preceding `}` (since `}` followed by newline emits a
    /// `Newline` token which terminates the statement).
    fn parse_trailing_args(&mut self) -> Result<Vec<TrailingArg>, ParseError> {
        let mut trailing = Vec::new();

        loop {
            // First trailing arg may be an unlabelled `{ ... }` or `'label: { ... }`.
            // Subsequent args must be `external_label { ... }` or `external_label 'label: { ... }`.

            let is_first = trailing.is_empty();

            if is_first {
                // `{` or `'atom: {` = first trailing arg (no label required).
                if self.check(&TokenKind::LBrace) || matches!(self.cur_kind(), TokenKind::Atom(_)) {
                    let t_start = self.cur_span();
                    let block = self.parse_labelled_block()?;
                    let span = t_start.merge(block.span);
                    trailing.push(TrailingArg {
                        label: None,
                        block,
                        span,
                    });
                    continue;
                }
            }

            // `ident { ... }` or `ident 'atom: { ... }` = labelled trailing arg.
            if let TokenKind::Ident(label_name) = self.cur_kind().clone() {
                // Must be followed by `{` or an atom to be a trailing arg (not a new statement).
                let next = self.peek_kind().clone();
                if matches!(next, TokenKind::LBrace) || matches!(next, TokenKind::Atom(_)) {
                    self.advance(); // consume label name
                    let t_start = self.cur_span();
                    let block = self.parse_labelled_block()?;
                    let span = t_start.merge(block.span);
                    trailing.push(TrailingArg {
                        label: Some(label_name),
                        block,
                        span,
                    });
                    continue;
                }
            }

            break;
        }

        Ok(trailing)
    }

    // ─────────────────────────────────────────────────────────────────────────
    // Built-in control flow
    // ─────────────────────────────────────────────────────────────────────────

    /// Parse an `if` expression.
    ///
    /// ```aura
    /// if (cond) { then }
    /// if (cond) { then } else { else }
    /// if (ok) then { thing } else { other }
    /// ```
    fn parse_if(&mut self, start: Span) -> Result<Expr, ParseError> {
        // Condition in `( )`.
        self.expect(TokenKind::LParen)?;
        let condition = self.parse_expr(0)?;
        self.expect(TokenKind::RParen)?;

        // Optional `then` label before the then block.
        if let TokenKind::Ident(s) = self.cur_kind() {
            if s == "then" {
                self.advance();
            }
        }

        let then_block = self.parse_block()?;

        // Optional `else` branch; must be on the same line due to implicit-semicolon rule.
        // We check for `Newline` token: if present, the `else` would be a separate statement.
        while self.eat(TokenKind::Newline) {}

        let else_block = if let TokenKind::Ident(s) = self.cur_kind() {
            if s == "else" {
                self.advance(); // consume `else`
                Some(self.parse_block()?)
            } else {
                None
            }
        } else {
            None
        };

        let span = start.merge(self.cur_span());
        Ok(Expr::If(IfExpr {
            condition: Box::new(condition),
            then_block,
            else_block,
            span,
        }))
    }

    /// Parse a `cases { ~ cond -> expr, ... }` expression.
    fn parse_cases(&mut self, start: Span) -> Result<Expr, ParseError> {
        self.expect(TokenKind::LBrace)?;
        let mut arms = Vec::new();

        loop {
            while self.eat(TokenKind::Semicolon) || self.eat(TokenKind::Newline) {}
            if self.check(&TokenKind::RBrace) || self.at_eof() {
                break;
            }

            let arm_start = self.cur_span();
            self.expect(TokenKind::Tilde)?;
            let guard = self.parse_expr(0)?;
            self.expect(TokenKind::Arrow)?;
            let body = self.parse_expr(0)?;
            let arm_span = arm_start.merge(body.span());
            arms.push(CasesArm {
                guard,
                body,
                span: arm_span,
            });

            if !self.eat(TokenKind::Comma) {
                break;
            }
        }

        self.expect(TokenKind::RBrace)?;
        let span = start.merge(self.cur_span());
        Ok(Expr::Cases(CasesExpr { arms, span }))
    }

    /// Parse a `loop` expression in either form:
    /// - `loop { body }`
    /// - `loop while { cond } do { body }`
    fn parse_loop(&mut self, start: Span) -> Result<Expr, ParseError> {
        // Check for `while` parameter label.
        let condition = if let TokenKind::Ident(s) = self.cur_kind() {
            if s == "while" {
                self.advance(); // consume `while`
                Some(self.parse_block()?)
            } else {
                None
            }
        } else {
            None
        };

        // Optional `do` label before the body block.
        if let TokenKind::Ident(s) = self.cur_kind() {
            if s == "do" {
                self.advance();
            }
        }

        let body = self.parse_labelled_block()?;
        let span = start.merge(self.cur_span());
        Ok(Expr::Loop(LoopExpr {
            condition,
            body,
            span,
        }))
    }

    /// Parse a `match (scrutinee) with { pattern => expr, ... }` expression.
    ///
    /// Desugars into an immediately-invoked multi-arm closure:
    /// `({ pat -> expr, ... })(scrutinee)`
    fn parse_match(&mut self, start: Span) -> Result<Expr, ParseError> {
        // Scrutinee in `( )`.
        self.expect(TokenKind::LParen)?;
        let scrutinee = self.parse_expr(0)?;
        self.expect(TokenKind::RParen)?;

        // Expect the `with` keyword (parsed as an identifier).
        match self.cur_kind().clone() {
            TokenKind::Ident(s) if s == "with" => {
                self.advance();
            }
            _ => {
                return Err(self.error(format!(
                    "expected `with` after match scrutinee, found {}",
                    self.cur_kind()
                )));
            }
        }

        // Parse `{ arm, arm, ... }` where each arm uses `=>` as separator.
        self.expect(TokenKind::LBrace)?;
        let mut arms = Vec::new();
        loop {
            while self.eat(TokenKind::Semicolon) || self.eat(TokenKind::Newline) {}
            if self.check(&TokenKind::RBrace) || self.at_eof() {
                break;
            }

            let arm = self.parse_match_arm()?;
            arms.push(arm);

            // Arms are comma-separated; trailing comma is allowed.
            if !self.eat(TokenKind::Comma) {
                break;
            }
            while self.eat(TokenKind::Newline) {}
        }
        self.expect(TokenKind::RBrace)?;

        let closure_span = start.merge(self.cur_span());
        let closure = Expr::Closure(Closure {
            arms,
            span: closure_span,
        });

        // Desugar: call the closure with the scrutinee as the sole argument.
        let arg = Arg {
            label: None,
            span: scrutinee.span(),
            value: scrutinee,
        };
        let span = start.merge(self.cur_span());
        Ok(Expr::Call {
            callee: Box::new(closure),
            args: vec![arg],
            trailing: vec![],
            span,
        })
    }

    /// Parse one match arm: `pattern => expr`  (uses `=>` instead of `->`)
    fn parse_match_arm(&mut self) -> Result<ClosureArm, ParseError> {
        let start = self.cur_span();
        let pattern = self.parse_pattern()?;
        self.expect(TokenKind::FatArrow)?;
        let body = self.parse_expr(0)?;
        let span = start.merge(body.span());
        Ok(ClosureArm {
            patterns: vec![pattern],
            guard: None,
            body,
            span,
        })
    }

    // ─────────────────────────────────────────────────────────────────────────
    // Utility
    // ─────────────────────────────────────────────────────────────────────────

    /// Consume the current token as an identifier and return the name, or error.
    fn expect_ident(&mut self) -> Result<String, ParseError> {
        match self.cur_kind().clone() {
            TokenKind::Ident(name) => {
                self.advance();
                Ok(name)
            }
            _ => Err(self.error(format!("expected identifier, found {}", self.cur_kind()))),
        }
    }

    fn expect_ident_or_self(&mut self) -> Result<String, ParseError> {
        match self.cur_kind().clone() {
            TokenKind::Ident(name) => {
                self.advance();
                Ok(name)
            }
            TokenKind::SelfKw => {
                self.advance();
                Ok("self".to_string())
            }
            _ => Err(self.error(format!("expected identifier, found {}", self.cur_kind()))),
        }
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Pratt binding-power table
// ─────────────────────────────────────────────────────────────────────────────

/// Return `(left_bp, right_bp)` for an infix/postfix token.
///
/// For pure postfix operators, `right_bp` is `None` (they have no right operand).
/// For infix operators, both are `Some`.
/// Returns `(0, None)` for tokens that are not infix/postfix operators (which
/// causes the Pratt loop to exit).
fn infix_binding_power(kind: &TokenKind) -> (u8, Option<u8>) {
    match kind {
        // Right-associative assignment — l_bp must be LESS than r_bp.
        TokenKind::Eq => (1, Some(2)),
        // Elvis ?:
        TokenKind::QuestionColon => (3, Some(4)),
        // Logical OR
        TokenKind::PipePipe => (5, Some(6)),
        // Logical AND
        TokenKind::AmpAmp => (7, Some(8)),
        // Equality
        TokenKind::EqEq | TokenKind::BangEq => (9, Some(10)),
        // Comparison
        TokenKind::Lt | TokenKind::Gt | TokenKind::LtEq | TokenKind::GtEq => (11, Some(12)),
        // Range
        TokenKind::DotDot => (13, Some(14)),
        // Additive
        TokenKind::Plus | TokenKind::Minus => (15, Some(16)),
        // Multiplicative
        TokenKind::Star | TokenKind::Slash | TokenKind::Percent => (17, Some(18)),
        // Cast `:` — postfix, no right operand in the expression sense (type follows).
        TokenKind::Colon => (19, None),
        // Post-increment / decrement — postfix.
        TokenKind::PlusPlus | TokenKind::MinusMinus => (21, None),
        // Force unwrap `!!` — postfix.
        TokenKind::BangBang => (23, None),
        // Safe navigation `?.` — postfix.
        TokenKind::QuestionDot => (25, None),
        // Field access `.` — postfix.
        TokenKind::Dot => (27, None),
        // Method call via DotIdent `.method(...)` — postfix.
        TokenKind::DotIdent(_) => (27, None),
        // Call `()` and index `[]` — postfix, highest precedence.
        TokenKind::LParen | TokenKind::LBracket => (29, None),
        // Everything else is not an infix/postfix operator.
        _ => (0, None),
    }
}

/// Map an infix token kind to a [`BinOp`].
/// Panics if the token is not a binary operator (caller must ensure correctness).
fn token_to_binop(kind: &TokenKind) -> BinOp {
    match kind {
        TokenKind::PipePipe => BinOp::Or,
        TokenKind::AmpAmp => BinOp::And,
        TokenKind::EqEq => BinOp::Eq,
        TokenKind::BangEq => BinOp::Ne,
        TokenKind::Lt => BinOp::Lt,
        TokenKind::Gt => BinOp::Gt,
        TokenKind::LtEq => BinOp::Le,
        TokenKind::GtEq => BinOp::Ge,
        TokenKind::Plus => BinOp::Add,
        TokenKind::Minus => BinOp::Sub,
        TokenKind::Star => BinOp::Mul,
        TokenKind::Slash => BinOp::Div,
        TokenKind::Percent => BinOp::Rem,
        _ => panic!("token_to_binop called on non-binary-op token: {kind:?}"),
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Public convenience function
// ─────────────────────────────────────────────────────────────────────────────

/// Parse `src` and return `(program, errors)`.
///
/// This is the primary entry point for the rest of the compiler.
pub fn parse(src: &str) -> (Program, Vec<ParseError>) {
    let (tokens, lex_errors) = crate::lexer::lex(src);
    let parser = Parser::new(tokens);
    let (program, mut parse_errors) = parser.parse_program();

    // Convert lex errors to parse errors and prepend them.
    let mut errors: Vec<ParseError> = lex_errors
        .into_iter()
        .map(|e| ParseError {
            message: e.message,
            span: e.span,
        })
        .collect();
    errors.append(&mut parse_errors);
    (program, errors)
}

/// Parse a pre-lexed token stream and return `(program, errors)`.
///
/// This entry point is used by the compiler when re-parsing interpolated string
/// tokens (where lexing has already occurred).
pub fn parse_tokens(tokens: Vec<crate::token::Token>) -> (Program, Vec<ParseError>) {
    let parser = Parser::new(tokens);
    parser.parse_program()
}

/// Parse a single expression from a pre-lexed token stream.
///
/// Used by the compiler's string-interpolation handler to extract the expression
/// inside `$(…)`.  The tokens are wrapped in a synthetic
/// `def __interp__() { <tokens> }` token stream (no source text involved) so
/// the parser can resolve them as a tail expression or expression statement.
/// Returns `None` if the tokens do not produce a parseable expression (e.g. empty
/// interpolation or parse errors).
pub fn parse_expr_from_tokens(tokens: Vec<crate::token::Token>) -> Option<Expr> {
    use crate::token::{Span, Token, TokenKind};

    let dummy = Span::dummy();

    // Build a wrapper token stream: `def __interp__() { <tokens> }` + Eof.
    // `def` and `__interp__` are plain identifiers (not keywords in Aura).
    let mut wrapped: Vec<Token> = vec![
        Token::new(TokenKind::Ident("def".into()), dummy),
        Token::new(TokenKind::Ident("__interp__".into()), dummy),
        Token::new(TokenKind::LParen, dummy),
        Token::new(TokenKind::RParen, dummy),
        Token::new(TokenKind::LBrace, dummy),
    ];
    // Strip any trailing Eof tokens produced by the nested lexer call in
    // `scan_string` — inserting them before our synthetic `}` would cause the
    // parser to terminate early and return `None`, triggering a null fallback.
    wrapped.extend(tokens.into_iter().filter(|t| t.kind != TokenKind::Eof));
    wrapped.push(Token::new(TokenKind::RBrace, dummy));
    wrapped.push(Token::new(TokenKind::Eof, dummy));

    let (prog, _errors) = parse_tokens(wrapped);

    // Extract the tail expression or last expression statement from the body.
    if let Some(Item::Decl(d)) = prog.items.into_iter().next() {
        if let DeclKind::Def(def_decl) = d.kind {
            if let Some(DefBinding::FuncDef { body, .. }) = def_decl.bindings.into_iter().next() {
                if let Some(tail) = body.tail {
                    return Some(*tail);
                }
                if let Some(Stmt::Expr(es)) = body.stmts.into_iter().last() {
                    return Some(es.expr);
                }
            }
        }
    }
    None
}

// ─────────────────────────────────────────────────────────────────────────────
// Tests
// ─────────────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;

    fn parse_ok(src: &str) -> Program {
        let (prog, errors) = parse(src);
        assert!(
            errors.is_empty(),
            "parse errors for `{src}`:\n{}",
            errors
                .iter()
                .map(|e| e.to_string())
                .collect::<Vec<_>>()
                .join("\n")
        );
        prog
    }

    fn parse_expr_ok(src: &str) -> Expr {
        // Wrap in a def to parse as a top-level expression.
        let wrapped = format!("def __test__() {{ {src} }}");
        let prog = parse_ok(&wrapped);
        let decl = &prog.items[0];
        if let Item::Decl(d) = decl {
            if let DeclKind::Def(def_decl) = &d.kind {
                if let Some(DefBinding::FuncDef { body, .. }) = def_decl.bindings.first() {
                    if let Some(tail) = &body.tail {
                        return *tail.clone();
                    }
                    if let Some(Stmt::Expr(es)) = body.stmts.last() {
                        return es.expr.clone();
                    }
                }
            }
        }
        panic!("could not extract expression from parse result");
    }

    #[test]
    fn test_parse_integer_literal() {
        let e = parse_expr_ok("42");
        assert_eq!(e, Expr::Int(42, e.span()));
    }

    #[test]
    fn test_parse_float_literal() {
        match parse_expr_ok("3.14") {
            Expr::Float(f, _) => assert!((f - 3.14).abs() < f64::EPSILON),
            other => panic!("expected Float, got {other:?}"),
        }
    }

    #[test]
    fn test_parse_bool_literals() {
        // true/false are now plain identifiers (prelude globals), not keywords.
        assert!(matches!(parse_expr_ok("true"), Expr::Ident(s, _) if s == "true"));
        assert!(matches!(parse_expr_ok("false"), Expr::Ident(s, _) if s == "false"));
    }

    #[test]
    fn test_parse_null() {
        // null is now a plain identifier (prelude global), not a keyword.
        assert!(matches!(parse_expr_ok("null"), Expr::Ident(s, _) if s == "null"));
    }

    #[test]
    fn test_parse_binary_add() {
        let e = parse_expr_ok("1 + 2");
        assert!(matches!(e, Expr::Binary { op: BinOp::Add, .. }));
    }

    #[test]
    fn test_parse_operator_precedence() {
        // `1 + 2 * 3` should parse as `1 + (2 * 3)`
        let e = parse_expr_ok("1 + 2 * 3");
        if let Expr::Binary {
            op: BinOp::Add,
            rhs,
            ..
        } = e
        {
            assert!(matches!(*rhs, Expr::Binary { op: BinOp::Mul, .. }));
        } else {
            panic!("expected Add at top level");
        }
    }

    #[test]
    fn test_parse_unary_neg() {
        let e = parse_expr_ok("-x");
        assert!(matches!(e, Expr::Unary { op: UnOp::Neg, .. }));
    }

    #[test]
    fn test_parse_let_stmt() {
        let prog = parse_ok("def f() { let x = 42; }");
        if let Item::Decl(d) = &prog.items[0] {
            if let DeclKind::Def(def_decl) = &d.kind {
                if let Some(DefBinding::FuncDef { body, .. }) = def_decl.bindings.first() {
                    assert!(matches!(body.stmts[0], Stmt::Let(_)));
                    return;
                }
            }
        }
        panic!("unexpected parse result");
    }

    #[test]
    fn test_parse_def_func() {
        let prog = parse_ok("def add(a: Int, b: Int) -> Int { a + b }");
        assert_eq!(prog.items.len(), 1);
        if let Item::Decl(d) = &prog.items[0] {
            if let DeclKind::Def(def_decl) = &d.kind {
                if let Some(DefBinding::FuncDef { name, params, .. }) = def_decl.bindings.first() {
                    assert_eq!(name, "add");
                    assert_eq!(params.len(), 2);
                    assert_eq!(params[0].internal, "a");
                    assert_eq!(params[1].internal, "b");
                    return;
                }
            }
        }
        panic!("unexpected parse result");
    }

    #[test]
    fn test_parse_use_destructure() {
        let prog = parse_ok(r#"use (println, print) = "@stl/io";"#);
        if let Item::Use(u) = &prog.items[0] {
            assert_eq!(u.path, "@stl/io");
            // Pattern should be a struct pattern with two fields (println, print)
            assert!(matches!(u.pattern, Pattern::Struct { .. }));
        } else {
            panic!("expected use decl");
        }
    }

    #[test]
    fn test_parse_if_else() {
        let e = parse_expr_ok("if (x > 0) { 1 } else { 0 }");
        assert!(matches!(
            e,
            Expr::If(IfExpr {
                else_block: Some(_),
                ..
            })
        ));
    }

    #[test]
    fn test_parse_loop() {
        let e = parse_expr_ok("loop { x++; }");
        assert!(matches!(e, Expr::Loop(_)));
    }

    #[test]
    fn test_parse_closure_single_arm() {
        let e = parse_expr_ok("{ a, b -> a + b }");
        if let Expr::Closure(c) = e {
            assert_eq!(c.arms.len(), 1);
            assert_eq!(c.arms[0].patterns.len(), 2);
        } else {
            panic!("expected Closure");
        }
    }

    #[test]
    fn test_parse_cases() {
        let e = parse_expr_ok("cases { ~ x > 0 -> 1, ~ true -> 0 }");
        if let Expr::Cases(c) = e {
            assert_eq!(c.arms.len(), 2);
        } else {
            panic!("expected Cases");
        }
    }

    #[test]
    fn test_parse_list_literal() {
        let e = parse_expr_ok("[1, 2, 3]");
        assert!(matches!(e, Expr::List { .. }));
    }

    #[test]
    fn test_parse_dict_literal() {
        let e = parse_expr_ok(r#"["a" = 1, "b" = 2]"#);
        assert!(matches!(e, Expr::Dict { .. }));
    }

    #[test]
    fn test_parse_method_call() {
        let e = parse_expr_ok("x.toString()");
        // Should be Call { callee: FieldAccess { .. }, .. }
        assert!(matches!(e, Expr::Call { .. }));
    }

    #[test]
    fn test_parse_safe_nav() {
        let e = parse_expr_ok("x?.foo");
        assert!(matches!(e, Expr::SafeNav { .. }));
    }

    #[test]
    fn test_parse_force_unwrap() {
        let e = parse_expr_ok("x!!");
        assert!(matches!(e, Expr::ForceUnwrap { .. }));
    }

    #[test]
    fn test_parse_post_increment() {
        let e = parse_expr_ok("x++");
        assert!(matches!(e, Expr::PostIncrement { .. }));
    }

    #[test]
    fn test_parse_trailing_lambda() {
        let prog = parse_ok(
            r#"
            def main() {
                do_stuff(12) task { doWork(); } finally { cleanup(); }
            }
        "#,
        );
        if let Item::Decl(d) = &prog.items[0] {
            if let DeclKind::Def(def_decl) = &d.kind {
                if let Some(DefBinding::FuncDef { body, .. }) = def_decl.bindings.first() {
                    // The call has no trailing `;`, so it lands in `body.tail`.
                    if let Some(tail) = &body.tail {
                        if let Expr::Call { trailing, .. } = tail.as_ref() {
                            assert_eq!(trailing.len(), 2);
                            return;
                        }
                    }
                    // Fallback: also accept it as a stmt (with semicolon).
                    if let Some(Stmt::Expr(es)) = body.stmts.first() {
                        if let Expr::Call { trailing, .. } = &es.expr {
                            assert_eq!(trailing.len(), 2);
                            return;
                        }
                    }
                }
            }
        }
        panic!("unexpected parse result");
    }

    #[test]
    fn test_parse_deftype() {
        // `deftype` is removed; `def Name = (fields...)` is the replacement.
        let prog = parse_ok("def Point = (x: Int, y: Int)");
        if let Item::Decl(d) = &prog.items[0] {
            if let DeclKind::Def(def) = &d.kind {
                assert_eq!(def.bindings.len(), 1);
                if let DefBinding::TypeAlias { name, .. } = &def.bindings[0] {
                    assert_eq!(name, "Point");
                    return;
                }
            }
        }
        panic!("unexpected parse result");
    }

    #[test]
    fn test_parse_range_expr() {
        let e = parse_expr_ok("1..10");
        assert!(matches!(e, Expr::Range { .. }));
    }

    #[test]
    fn test_parse_cast() {
        let e = parse_expr_ok("x : Int");
        assert!(matches!(e, Expr::Cast { .. }));
    }

    #[test]
    fn test_parse_return_with_label() {
        let prog = parse_ok("def f() { return 'outer 42; }");
        if let Item::Decl(d) = &prog.items[0] {
            if let DeclKind::Def(def_decl) = &d.kind {
                if let Some(DefBinding::FuncDef { body, .. }) = def_decl.bindings.first() {
                    if let Stmt::Return(r) = &body.stmts[0] {
                        assert_eq!(r.label, Some("outer".into()));
                        return;
                    }
                }
            }
        }
        panic!("unexpected parse result");
    }

    #[test]
    fn test_parse_expr_from_tokens_ident() {
        // A single identifier token should parse as Expr::Ident.
        use crate::token::{Span, Token, TokenKind};
        let dummy = Span::dummy();
        let tokens = vec![Token::new(TokenKind::Ident("name".into()), dummy)];
        let expr = parse_expr_from_tokens(tokens).expect("expected Some(Expr)");
        assert!(
            matches!(&expr, Expr::Ident(i, _) if i == "name"),
            "expected Expr::Ident(\"name\"), got: {expr:?}"
        );
    }

    #[test]
    fn test_parse_expr_from_tokens_arithmetic() {
        // A simple `1 + 2` expression should parse as BinaryOp.
        use crate::token::{Span, Token, TokenKind};
        let dummy = Span::dummy();
        let tokens = vec![
            Token::new(TokenKind::Int(1), dummy),
            Token::new(TokenKind::Plus, dummy),
            Token::new(TokenKind::Int(2), dummy),
        ];
        let expr = parse_expr_from_tokens(tokens).expect("expected Some(Expr)");
        assert!(
            matches!(expr, Expr::Binary { .. }),
            "expected Expr::Binary, got: {expr:?}"
        );
    }

    #[test]
    fn test_parse_expr_from_tokens_empty_returns_none() {
        // Empty token list should return None (no expression to parse).
        let expr = parse_expr_from_tokens(vec![]);
        assert!(expr.is_none(), "expected None for empty token list");
    }

    /// Regression test: trailing-lambda-without-parens on a method call must parse
    /// without errors and produce a `Call` with exactly one trailing closure arg.
    ///
    /// Before the fix, `parse_labelled_block` called `parse_block` which did not
    /// recognise `{ x -> x * x }` as a closure arm, causing a parse error that
    /// triggered error-recovery and left the parser in a broken state.
    #[test]
    fn test_parse_trailing_closure_on_method_call_no_parens() {
        let prog = parse_ok(
            r#"
            def main() {
                nums.map { x -> x * x }
            }
        "#,
        );
        if let Item::Decl(d) = &prog.items[0] {
            if let DeclKind::Def(def_decl) = &d.kind {
                if let Some(DefBinding::FuncDef { body, .. }) = def_decl.bindings.first() {
                    // The call is the tail expression of the function body.
                    let call_expr = body
                        .tail
                        .as_deref()
                        .or_else(|| {
                            body.stmts.last().and_then(|s| {
                                if let Stmt::Expr(es) = s {
                                    Some(&es.expr)
                                } else {
                                    None
                                }
                            })
                        })
                        .expect("expected a tail or statement expression");

                    if let Expr::Call { trailing, .. } = call_expr {
                        assert_eq!(
                            trailing.len(),
                            1,
                            "expected exactly one trailing closure arg"
                        );
                        // The trailing arg's block must have a Closure as its tail expression.
                        let trail_block = &trailing[0].block.block;
                        assert!(
                            matches!(trail_block.tail.as_deref(), Some(Expr::Closure(_))),
                            "expected trailing block tail to be a Closure, got: {:?}",
                            trail_block.tail
                        );
                        return;
                    }
                }
            }
        }
        panic!("unexpected parse result");
    }
}
