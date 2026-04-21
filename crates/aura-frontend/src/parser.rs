#![allow(clippy::result_large_err)]

use crate::ast::{
    Arm, BinaryOp, Binding, Decl, DocAttribute, Expr, FunctionDecl, LabeledClosureArg, MacroDecl,
    Param, Pattern, Program, StaticArg, StaticParam, StaticParamKind, StaticValueExpr, SymbolDoc,
    TypeExpr, UseBinding, UseDecl, UseField,
};
use crate::lexer::lex;
use crate::static_eval::{MinimalStaticChecker, StaticSatisfies};
use crate::token::{Token, TokenKind};
use aura_diagnostics::{Diagnostic, Issue, Stage};
use std::collections::HashSet;

const BUILTIN_MACROS: &[&str] = &[
    "def", "let", "const", "inline", "builtin", "return", "break", "continue", "loop", "doc",
];

const KNOWN_GENERIC_RECEIVERS: &[&str] = &[
    "List", "Dict", "Set", "Array", "Func", "Option", "Result", "Seq",
];

pub type ParseError = Diagnostic;

pub struct Parser;

impl Parser {
    pub fn parse_source(source: &str) -> Result<Program, ParseError> {
        let tokens = lex(source)?;
        let macro_symbols = collect_macro_symbols(&tokens);
        let mut inner = InnerParser {
            tokens,
            cursor: 0,
            static_checker: MinimalStaticChecker,
            macro_symbols,
            declared_macros: BUILTIN_MACROS.iter().map(|m| (*m).to_string()).collect(),
        };
        inner.parse_program()
    }
}

struct InnerParser<C> {
    tokens: Vec<Token>,
    cursor: usize,
    static_checker: C,
    macro_symbols: HashSet<String>,
    declared_macros: HashSet<String>,
}

impl<C> InnerParser<C>
where
    C: StaticSatisfies,
{
    fn mark(&self) -> usize {
        self.cursor
    }

    fn span_from_mark(&self, mark: usize) -> aura_diagnostics::Span {
        let start_idx = mark.min(self.tokens.len().saturating_sub(1));
        let end_idx = self
            .cursor
            .saturating_sub(1)
            .min(self.tokens.len().saturating_sub(1));
        let start = self.tokens[start_idx].span;
        let end = self.tokens[end_idx].span;
        aura_diagnostics::Span {
            start: start.start,
            end: end.end,
            line: start.line,
            column: start.column,
        }
    }

    fn with_span(&self, mark: usize, expr: Expr) -> Expr {
        if matches!(expr, Expr::Spanned { .. }) {
            return expr;
        }
        Expr::Spanned {
            span: self.span_from_mark(mark),
            expr: Box::new(expr),
        }
    }

    fn parse_program(&mut self) -> Result<Program, ParseError> {
        let mut declarations = Vec::new();
        while !self.is_eof() {
            if self.peek_is(&TokenKind::Semi) {
                self.bump();
                continue;
            }
            declarations.push(self.parse_decl()?);
            if self.peek_is(&TokenKind::Semi) {
                self.bump();
            }
        }
        Ok(Program { declarations })
    }

    fn parse_decl(&mut self) -> Result<Decl, ParseError> {
        let pending_doc = if self.peek_ident_is("doc") {
            Some(self.parse_doc_attribute()?)
        } else {
            None
        };

        if self.peek_is(&TokenKind::Defmacro) {
            if pending_doc.is_some() {
                return Err(self.error_here(
                    "doc attribute can only annotate a `def` declaration",
                    vec!["def"],
                    Some("use `doc[...] def ...`".to_string()),
                ));
            }
            return self.parse_macro_decl();
        }

        if self.peek_ident_is("use") {
            if pending_doc.is_some() {
                return Err(self.error_here(
                    "doc attribute can only annotate a `def` declaration",
                    vec!["def"],
                    Some("use `doc[...] def ...`".to_string()),
                ));
            }
            return self.parse_use_decl();
        }

        if self.peek_ident_is("def") && self.looks_like_function_decl() {
            return self.parse_function_decl(pending_doc);
        }

        if self.peek_ident_is("def") {
            return self.parse_static_def_assignment_decl(pending_doc);
        }

        if pending_doc.is_some() {
            return Err(self.error_here(
                "doc attribute must be immediately followed by `def`",
                vec!["def"],
                Some(
                    "use `doc[...] def symbol = ...` or `doc[...] def name(...) -> T { ... }`"
                        .to_string(),
                ),
            ));
        }

        Err(self.error_here(
            "top-level scope only allows static declarations (def/defmacro/use)",
            vec!["def", "defmacro", "use"],
            Some("move runtime code inside a function body".to_string()),
        ))
    }

    fn parse_static_def_assignment_decl(
        &mut self,
        doc: Option<DocAttribute>,
    ) -> Result<Decl, ParseError> {
        self.expect_ident_exact("def")?;
        if self.peek_is(&TokenKind::LBracket) {
            let _ = self.parse_static_params()?;
        }
        let name = self.expect_ident("expected declaration name after 'def'")?;
        self.ensure_not_macro_symbol(&name, "declaration name")?;
        let declared_ty = if self.peek_is(&TokenKind::Colon) {
            self.bump();
            Some(self.parse_type_expr()?)
        } else {
            None
        };
        self.expect_simple(
            &TokenKind::Eq,
            "expected '=' in static def declaration",
            vec!["="],
        )?;
        let type_mark = self.mark();
        let mut value = if self.starts_type_expr() {
            match self.parse_type_expr() {
                Ok(ty)
                    if self.peek_is(&TokenKind::Semi)
                        || self.peek_is(&TokenKind::Eof)
                        || self.peek_is(&TokenKind::RBrace) =>
                {
                    Expr::TypeExpr(ty)
                }
                _ => {
                    self.cursor = type_mark;
                    self.parse_expr()?
                }
            }
        } else {
            self.parse_expr()?
        };
        if let Some(ty) = declared_ty {
            value = Expr::Binary {
                op: BinaryOp::Colon,
                lhs: Box::new(value),
                rhs: Box::new(Expr::TypeExpr(ty)),
            };
        }
        Ok(Decl::Assign { name, value, doc })
    }

    fn parse_doc_attribute(&mut self) -> Result<DocAttribute, ParseError> {
        self.expect_ident_exact("doc")?;
        let static_args = self.parse_static_args()?;
        if static_args.len() != 1 {
            return Err(self.error_here(
                "doc requires exactly one static string argument",
                vec!["string"],
                Some("use `doc[\"...markdown...\"] def ...`".to_string()),
            ));
        }
        let markdown = match &static_args[0] {
            StaticArg::Value(StaticValueExpr::String(s)) => s.clone(),
            _ => {
                return Err(self.error_here(
                    "doc static argument must be a string literal",
                    vec!["string"],
                    Some("use `doc[\"...markdown...\"]`".to_string()),
                ));
            }
        };
        Ok(build_doc_attribute(markdown))
    }

    fn ensure_not_macro_symbol(&self, name: &str, context: &str) -> Result<(), ParseError> {
        if self.macro_symbols.contains(name) {
            return Err(self.error_here(
                format!("{context} '{name}' cannot shadow final macro symbol"),
                vec!["non-macro identifier"],
                Some(
                    "pick a different name; macro symbols are final and non-shadowable".to_string(),
                ),
            ));
        }
        Ok(())
    }

    fn parse_use_decl(&mut self) -> Result<Decl, ParseError> {
        self.expect_ident_exact("use")?;
        let binding = if self.peek_is(&TokenKind::LParen) {
            self.bump();
            let mut fields = Vec::new();
            loop {
                let first = self.expect_ident("expected imported symbol name")?;
                let (local_name, source_name) = if self.peek_is(&TokenKind::Eq) {
                    self.bump();
                    let source = self.expect_ident("expected exported symbol name after '='")?;
                    (first, source)
                } else {
                    (first.clone(), first)
                };
                fields.push(UseField {
                    local_name,
                    source_name,
                });

                if self.peek_is(&TokenKind::Comma) {
                    self.bump();
                    if self.peek_is(&TokenKind::RParen) {
                        self.bump();
                        break;
                    }
                    continue;
                }

                self.expect_simple(
                    &TokenKind::RParen,
                    "expected ')' after imported fields",
                    vec![")"],
                )?;
                break;
            }
            UseBinding::Fields(fields)
        } else {
            let alias = self.expect_ident("expected use target alias")?;
            UseBinding::Namespace(alias)
        };
        self.expect_simple(&TokenKind::Eq, "expected '=' after use binding", vec!["="])?;
        let source_expr = self.parse_atom_expr()?;
        let source = match source_expr.unspanned() {
            Expr::String(source) => source.clone(),
            _ => {
                return Err(self.error_here(
                    "expected string literal module source after '='",
                    vec!["string"],
                    Some("use `use io = \"@stl/io\";`".to_string()),
                ));
            }
        };
        Ok(Decl::Use(UseDecl { binding, source }))
    }

    fn parse_function_decl(&mut self, doc: Option<DocAttribute>) -> Result<Decl, ParseError> {
        self.expect_ident_exact("def")?;

        let static_params = if self.peek_is(&TokenKind::LBracket) {
            self.parse_static_params()?
        } else {
            Vec::new()
        };

        let (receiver, name) = if matches!(self.peek(), TokenKind::Ident(_))
            && matches!(self.peek_n(1), Some(TokenKind::LParen))
        {
            (None, self.expect_ident("expected function name")?)
        } else {
            let head_ty = self.parse_type_expr()?;
            self.ensure_receiver_generic_args(&head_ty)?;
            self.expect_simple(
                &TokenKind::Dot,
                "expected '.' before method name",
                vec!["."],
            )?;
            let name = self.expect_ident("expected method name")?;
            (Some(head_ty), name)
        };
        self.ensure_not_macro_symbol(&name, "function name")?;
        let params = self.parse_params()?;
        self.expect_simple(
            &TokenKind::Arrow,
            "expected '->' in function declaration",
            vec!["->"],
        )?;
        let return_type = self.parse_type_expr()?;
        let body = self.parse_brace_body_expr()?;

        Ok(Decl::Function(FunctionDecl {
            static_params,
            receiver,
            name,
            params,
            return_type,
            body,
            doc,
        }))
    }

    fn ensure_receiver_generic_args(&self, receiver: &TypeExpr) -> Result<(), ParseError> {
        let TypeExpr::Named { name, args } = receiver else {
            return Ok(());
        };
        if !args.is_empty() {
            return Ok(());
        }
        if !KNOWN_GENERIC_RECEIVERS.contains(&name.as_str()) {
            return Ok(());
        }

        Err(self.error_here(
            format!(
                "receiver type '{name}' requires explicit static arguments in method declarations"
            ),
            vec!["type[args]"],
            Some(format!(
                "use `def[T] {name}[T].method(...) -> ... {{ ... }}`"
            )),
        ))
    }

    fn looks_like_function_decl(&self) -> bool {
        let mut i = self.cursor + 1;
        if matches!(self.peek_n(1), Some(TokenKind::LBracket)) {
            while let Some(tok) = self.peek_n(i - self.cursor) {
                if matches!(tok, TokenKind::RBracket) {
                    i += 1;
                    break;
                }
                i += 1;
            }
        }

        while let Some(tok) = self.peek_n(i - self.cursor) {
            match tok {
                TokenKind::LParen => return true,
                TokenKind::Colon => return false,
                TokenKind::Eof | TokenKind::Semi | TokenKind::Eq => return false,
                _ => i += 1,
            }
        }
        false
    }

    fn parse_macro_decl(&mut self) -> Result<Decl, ParseError> {
        self.expect_simple(
            &TokenKind::Defmacro,
            "expected 'defmacro'",
            vec!["defmacro"],
        )?;
        let static_params = if self.peek_is(&TokenKind::LBracket) {
            self.parse_static_params()?
        } else {
            Vec::new()
        };

        let name = self.expect_ident("expected macro name")?;
        if self.declared_macros.contains(&name) {
            return Err(self.error_here(
                format!("macro symbol '{name}' is final and cannot be redefined"),
                vec!["unique macro name"],
                Some(
                    "choose a different macro name; builtin and prior macros are non-shadowable"
                        .to_string(),
                ),
            ));
        }
        self.declared_macros.insert(name.clone());
        let params = self.parse_params()?;
        self.expect_simple(
            &TokenKind::Arrow,
            "expected '->' in macro declaration",
            vec!["->"],
        )?;
        let return_type = self.parse_type_expr()?;
        let body = self.parse_brace_body_expr()?;

        Ok(Decl::Macro(MacroDecl {
            name,
            static_params,
            params,
            return_type,
            body,
        }))
    }

    fn parse_brace_body_expr(&mut self) -> Result<Expr, ParseError> {
        self.expect_simple(&TokenKind::LBrace, "expected '{'", vec!["{"])?;
        if self.peek_is(&TokenKind::RBrace) {
            self.bump();
            return Ok(Expr::Block(Vec::new()));
        }

        let is_multi_arm = self.is_multi_arm_body();
        if is_multi_arm {
            let mut arms = Vec::new();
            loop {
                let mut patterns = Vec::new();
                if !self.peek_is(&TokenKind::Arrow) && !self.peek_is(&TokenKind::Tilde) {
                    patterns.push(self.parse_pattern()?);
                    while self.peek_is(&TokenKind::Comma) {
                        let Some(next) = self.peek_n(1) else {
                            break;
                        };
                        if matches!(next, TokenKind::Arrow | TokenKind::Tilde) {
                            break;
                        }
                        self.bump();
                        patterns.push(self.parse_pattern()?);
                    }
                }

                let guard = if self.peek_is(&TokenKind::Tilde) {
                    self.bump();
                    Some(self.parse_expr()?)
                } else {
                    None
                };
                self.expect_simple(&TokenKind::Arrow, "expected '->' in arm", vec!["->"])?;
                let body = self.parse_expr()?;
                arms.push(Arm {
                    patterns,
                    guard,
                    body,
                });

                if self.peek_is(&TokenKind::Comma) {
                    self.bump();
                    if self.peek_is(&TokenKind::RBrace) {
                        break;
                    }
                    continue;
                }
                break;
            }
            self.expect_simple(
                &TokenKind::RBrace,
                "expected '}' after arm block",
                vec!["}"],
            )?;
            Ok(Expr::MultiArm(arms))
        } else {
            let body = self.parse_sequence_until(&[TokenKind::RBrace])?;
            self.expect_simple(
                &TokenKind::RBrace,
                "expected '}' after block body",
                vec!["}"],
            )?;
            Ok(body)
        }
    }

    fn is_multi_arm_body(&self) -> bool {
        let mut i = self.cursor;
        while i < self.tokens.len() {
            match &self.tokens[i].kind {
                TokenKind::Arrow => return true,
                TokenKind::LBrace | TokenKind::LParen | TokenKind::LBracket => i += 1,
                TokenKind::RBrace => return false,
                _ => i += 1,
            }
        }
        false
    }

    fn parse_pattern(&mut self) -> Result<Pattern, ParseError> {
        if self.peek_is(&TokenKind::Underscore) {
            self.bump();
            return Ok(Pattern::Wildcard);
        }

        if self.peek_is(&TokenKind::Dot) {
            self.bump();
            let name = self.expect_ident("expected variant name after '.'")?;
            let payload = if self.peek_is(&TokenKind::LParen) {
                self.bump();
                let inner = self.parse_pattern()?;
                self.expect_simple(&TokenKind::RParen, "expected ')'", vec![")"])?;
                Some(Box::new(inner))
            } else {
                None
            };
            return Ok(Pattern::DotVariant { name, payload });
        }

        let ident = self.expect_ident("expected pattern")?;
        Ok(Pattern::Ident(ident))
    }

    fn parse_static_params(&mut self) -> Result<Vec<StaticParam>, ParseError> {
        self.expect_simple(&TokenKind::LBracket, "expected '['", vec!["["])?;
        if self.peek_is(&TokenKind::RBracket) {
            self.bump();
            return Ok(Vec::new());
        }

        let mut params = Vec::new();
        loop {
            let name = self.expect_ident("expected static parameter name")?;
            let kind = if self.peek_is(&TokenKind::Colon) {
                self.bump();
                let ty = self.parse_type_expr()?;
                StaticParamKind::Constraint(ty)
            } else {
                StaticParamKind::Type
            };
            params.push(StaticParam { name, kind });

            if self.peek_is(&TokenKind::Comma) {
                self.bump();
                if self.peek_is(&TokenKind::RBracket) {
                    self.bump();
                    break;
                }
                if self.peek_is(&TokenKind::Comma) {
                    return Err(self.error_here(
                        "malformed static parameter list",
                        vec!["identifier"],
                        None,
                    ));
                }
                continue;
            }

            self.expect_simple(
                &TokenKind::RBracket,
                "expected ']' after static parameters",
                vec!["]"],
            )?;
            break;
        }

        Ok(params)
    }

    fn parse_params(&mut self) -> Result<Vec<Param>, ParseError> {
        self.expect_simple(&TokenKind::LParen, "expected '('", vec!["("])?;
        if self.peek_is(&TokenKind::RParen) {
            self.bump();
            return Ok(Vec::new());
        }

        let mut params = Vec::new();
        loop {
            let name = self.expect_ident("expected parameter name")?;
            self.expect_simple(
                &TokenKind::Colon,
                "expected ':' after parameter name",
                vec![":"],
            )?;
            let ty = self.parse_type_expr()?;
            params.push(Param { name, ty });

            if self.peek_is(&TokenKind::Comma) {
                self.bump();
                if self.peek_is(&TokenKind::RParen) {
                    self.bump();
                    break;
                }
                continue;
            }

            self.expect_simple(
                &TokenKind::RParen,
                "expected ')' after parameters",
                vec![")"],
            )?;
            break;
        }

        Ok(params)
    }

    fn parse_type_expr(&mut self) -> Result<TypeExpr, ParseError> {
        if self.peek_is(&TokenKind::LParen) {
            return self.parse_paren_type_expr();
        }

        if self.peek_ident_is("static") {
            self.bump();
            let inner = self.parse_type_expr().map_err(|_| {
                self.error_here(
                    "expected type expression after 'static'",
                    vec!["type_expr"],
                    Some("use forms like 'static Int' or 'static Expr[T]'".to_string()),
                )
            })?;
            return Ok(TypeExpr::Static(Box::new(inner)));
        }

        if self.peek_is(&TokenKind::Underscore) {
            self.bump();
            return Ok(TypeExpr::InferHole);
        }

        let name = self.expect_ident("expected type identifier")?;
        let args = if self.peek_is(&TokenKind::LBracket) {
            self.parse_static_args()?
        } else if self.peek_is(&TokenKind::LParen) {
            self.parse_paren_type_args()?
        } else {
            Vec::new()
        };

        Ok(TypeExpr::Named { name, args })
    }

    fn parse_paren_type_expr(&mut self) -> Result<TypeExpr, ParseError> {
        self.expect_simple(&TokenKind::LParen, "expected '('", vec!["("])?;
        if self.peek_is(&TokenKind::RParen) {
            self.bump();
            return Ok(TypeExpr::Tuple(Vec::new()));
        }

        let is_struct = matches!(self.peek(), TokenKind::Ident(_))
            && matches!(self.peek_n(1), Some(TokenKind::Colon));

        if is_struct {
            let mut fields = Vec::new();
            loop {
                let field = self.expect_ident("expected struct field name")?;
                let ty = if self.peek_is(&TokenKind::Colon) {
                    self.bump();
                    self.parse_type_expr()?
                } else {
                    TypeExpr::Named {
                        name: "Void".to_string(),
                        args: Vec::new(),
                    }
                };
                fields.push((field, ty));
                if self.peek_is(&TokenKind::Comma) {
                    self.bump();
                    if self.peek_is(&TokenKind::RParen) {
                        break;
                    }
                    continue;
                }
                break;
            }
            self.expect_simple(
                &TokenKind::RParen,
                "expected ')' after struct type",
                vec![")"],
            )?;
            return Ok(TypeExpr::Struct(fields));
        }

        let mut items = Vec::new();
        loop {
            items.push(self.parse_type_expr()?);
            if self.peek_is(&TokenKind::Comma) {
                self.bump();
                if self.peek_is(&TokenKind::RParen) {
                    break;
                }
                continue;
            }
            break;
        }
        self.expect_simple(
            &TokenKind::RParen,
            "expected ')' after tuple type",
            vec![")"],
        )?;
        Ok(TypeExpr::Tuple(items))
    }

    fn parse_paren_type_args(&mut self) -> Result<Vec<StaticArg>, ParseError> {
        self.expect_simple(&TokenKind::LParen, "expected '('", vec!["("])?;
        if self.peek_is(&TokenKind::RParen) {
            self.bump();
            return Ok(Vec::new());
        }
        let mut args = Vec::new();
        loop {
            if matches!(self.peek(), TokenKind::Ident(_))
                && self.peek_n(1) == Some(&TokenKind::Colon)
            {
                let field = self.expect_ident("expected enum field name")?;
                self.expect_simple(
                    &TokenKind::Colon,
                    "expected ':' after enum field name",
                    vec![":"],
                )?;
                let ty = self.parse_type_expr()?;
                args.push(StaticArg::Type(TypeExpr::Struct(vec![(field, ty)])));
            } else {
                args.push(StaticArg::Type(self.parse_type_expr()?));
            }
            if self.peek_is(&TokenKind::Comma) {
                self.bump();
                if self.peek_is(&TokenKind::RParen) {
                    self.bump();
                    break;
                }
                continue;
            }
            self.expect_simple(
                &TokenKind::RParen,
                "expected ')' after type arguments",
                vec![")"],
            )?;
            break;
        }
        Ok(args)
    }

    fn parse_static_args(&mut self) -> Result<Vec<StaticArg>, ParseError> {
        self.expect_simple(&TokenKind::LBracket, "expected '['", vec!["["])?;
        if self.peek_is(&TokenKind::RBracket) {
            self.bump();
            return Ok(Vec::new());
        }

        let mut args = Vec::new();
        loop {
            let arg = self.parse_static_arg()?;
            args.push(arg);

            if self.peek_is(&TokenKind::Comma) {
                self.bump();
                if self.peek_is(&TokenKind::RBracket) {
                    self.bump();
                    break;
                }
                if self.peek_is(&TokenKind::Comma) {
                    return Err(self.error_here(
                        "malformed static argument list",
                        vec!["type_expr", "static_value"],
                        None,
                    ));
                }
                continue;
            }

            self.expect_simple(
                &TokenKind::RBracket,
                "expected ']' after static arguments",
                vec!["]"],
            )?;
            break;
        }

        Ok(args)
    }

    fn parse_static_arg(&mut self) -> Result<StaticArg, ParseError> {
        match self.peek() {
            TokenKind::Int(raw) => {
                let raw = raw.clone();
                self.bump();
                let value = StaticValueExpr::Int(raw);
                if !self.static_checker.is_compile_time_known(&value) {
                    return Err(self.error_here(
                        "static value is not compile-time known",
                        vec!["compile_time_value"],
                        None,
                    ));
                }
                Ok(StaticArg::Value(value))
            }
            TokenKind::Float(raw) => {
                let raw = raw.clone();
                self.bump();
                let value = StaticValueExpr::Float(raw);
                if !self.static_checker.is_compile_time_known(&value) {
                    return Err(self.error_here(
                        "static value is not compile-time known",
                        vec!["compile_time_value"],
                        None,
                    ));
                }
                Ok(StaticArg::Value(value))
            }
            TokenKind::String(raw) => {
                let raw = raw.clone();
                self.bump();
                let value = StaticValueExpr::String(raw);
                if !self.static_checker.is_compile_time_known(&value) {
                    return Err(self.error_here(
                        "static value is not compile-time known",
                        vec!["compile_time_value"],
                        None,
                    ));
                }
                Ok(StaticArg::Value(value))
            }
            TokenKind::Char(raw) => {
                let raw = raw.clone();
                self.bump();
                let value = StaticValueExpr::Char(raw);
                if !self.static_checker.is_compile_time_known(&value) {
                    return Err(self.error_here(
                        "static value is not compile-time known",
                        vec!["compile_time_value"],
                        None,
                    ));
                }
                Ok(StaticArg::Value(value))
            }
            TokenKind::Ident(name) => {
                if name == "static"
                    || name == "_"
                    || name
                        .chars()
                        .next()
                        .map(|ch| ch.is_ascii_uppercase())
                        .unwrap_or(false)
                {
                    let ty = self.parse_type_expr()?;
                    Ok(StaticArg::Type(ty))
                } else {
                    let name = name.clone();
                    self.bump();
                    let value = StaticValueExpr::Ident(name);
                    if !self.static_checker.is_compile_time_known(&value) {
                        return Err(self.error_here(
                            "static value is not compile-time known",
                            vec!["compile_time_value"],
                            None,
                        ));
                    }
                    Ok(StaticArg::Value(value))
                }
            }
            TokenKind::Underscore => {
                let ty = self.parse_type_expr()?;
                Ok(StaticArg::Type(ty))
            }
            _ => Err(self.error_here(
                "expected static argument",
                vec!["type_expr", "int", "float", "string", "char", "identifier"],
                None,
            )),
        }
    }

    fn parse_expr(&mut self) -> Result<Expr, ParseError> {
        let mark = self.mark();
        let expr = self.parse_assign_expr()?;
        Ok(self.with_span(mark, expr))
    }

    fn parse_assign_expr(&mut self) -> Result<Expr, ParseError> {
        let mark = self.mark();
        let expr = self.parse_elvis_expr()?;
        if !self.peek_is(&TokenKind::Eq) {
            return Ok(self.with_span(mark, expr));
        }

        let Some(name) = self.ident_assign_target(&expr) else {
            return Ok(self.with_span(mark, expr));
        };

        self.bump();
        let value = self.parse_assign_expr()?;
        Ok(self.with_span(
            mark,
            Expr::Assign {
                name,
                value: Box::new(value),
            },
        ))
    }

    fn starts_type_expr(&self) -> bool {
        if self.peek_is(&TokenKind::LParen) || self.peek_is(&TokenKind::Underscore) {
            return true;
        }
        if let TokenKind::Ident(name) = self.peek() {
            if name == "static" || name == "union" || name == "enum" || name == "interface" {
                return true;
            }
            return name
                .chars()
                .next()
                .map(|ch| ch.is_ascii_uppercase())
                .unwrap_or(false);
        }
        false
    }

    fn parse_elvis_expr(&mut self) -> Result<Expr, ParseError> {
        let mark = self.mark();
        let lhs = self.parse_or_expr()?;
        if self.peek_is(&TokenKind::QuestionColon) {
            self.bump();
            let rhs = self.parse_elvis_expr()?;
            return Ok(self.with_span(
                mark,
                Expr::Binary {
                    op: BinaryOp::Elvis,
                    lhs: Box::new(lhs),
                    rhs: Box::new(rhs),
                },
            ));
        }
        Ok(self.with_span(mark, lhs))
    }

    fn parse_or_expr(&mut self) -> Result<Expr, ParseError> {
        self.parse_left_assoc_binary(Self::parse_and_expr, &[(TokenKind::PipePipe, BinaryOp::Or)])
    }

    fn parse_and_expr(&mut self) -> Result<Expr, ParseError> {
        self.parse_left_assoc_binary(
            Self::parse_equality_expr,
            &[(TokenKind::AmpAmp, BinaryOp::And)],
        )
    }

    fn parse_equality_expr(&mut self) -> Result<Expr, ParseError> {
        self.parse_left_assoc_binary(
            Self::parse_comparison_expr,
            &[
                (TokenKind::EqEq, BinaryOp::Eq),
                (TokenKind::NotEq, BinaryOp::Neq),
            ],
        )
    }

    fn parse_comparison_expr(&mut self) -> Result<Expr, ParseError> {
        self.parse_left_assoc_binary(
            Self::parse_range_expr,
            &[
                (TokenKind::Lt, BinaryOp::Lt),
                (TokenKind::Lte, BinaryOp::Le),
                (TokenKind::Gt, BinaryOp::Gt),
                (TokenKind::Gte, BinaryOp::Ge),
            ],
        )
    }

    fn parse_range_expr(&mut self) -> Result<Expr, ParseError> {
        self.parse_left_assoc_binary(
            Self::parse_pipe_expr,
            &[(TokenKind::Range, BinaryOp::Range)],
        )
    }

    fn parse_pipe_expr(&mut self) -> Result<Expr, ParseError> {
        self.parse_left_assoc_binary(
            Self::parse_add_expr,
            &[(TokenKind::PipeArrow, BinaryOp::Pipe)],
        )
    }

    fn parse_add_expr(&mut self) -> Result<Expr, ParseError> {
        self.parse_left_assoc_binary(
            Self::parse_mul_expr,
            &[
                (TokenKind::Plus, BinaryOp::Add),
                (TokenKind::Minus, BinaryOp::Sub),
            ],
        )
    }

    fn parse_mul_expr(&mut self) -> Result<Expr, ParseError> {
        self.parse_left_assoc_binary(
            Self::parse_colon_expr,
            &[
                (TokenKind::Star, BinaryOp::Mul),
                (TokenKind::Slash, BinaryOp::Div),
                (TokenKind::Percent, BinaryOp::Mod),
            ],
        )
    }

    fn parse_colon_expr(&mut self) -> Result<Expr, ParseError> {
        let mark = self.mark();
        let mut expr = self.parse_macro_or_postfix_expr()?;
        while self.peek_is(&TokenKind::Colon) {
            self.bump();
            let ty = self.parse_type_expr()?;
            expr = Expr::Binary {
                op: BinaryOp::Colon,
                lhs: Box::new(expr),
                rhs: Box::new(Expr::TypeExpr(ty)),
            };
        }
        Ok(self.with_span(mark, expr))
    }

    fn parse_macro_or_postfix_expr(&mut self) -> Result<Expr, ParseError> {
        if self.peek_ident_is("label") {
            return self.parse_label_expr();
        }
        if self.is_macro_apply_start() {
            self.parse_macro_apply_expr()
        } else {
            self.parse_postfix_expr()
        }
    }

    fn parse_left_assoc_binary(
        &mut self,
        sub_expr: fn(&mut Self) -> Result<Expr, ParseError>,
        ops: &[(TokenKind, BinaryOp)],
    ) -> Result<Expr, ParseError> {
        let mark = self.mark();
        let mut expr = sub_expr(self)?;
        while let Some(op) = self.match_binary_op(ops) {
            let rhs = sub_expr(self)?;
            expr = Expr::Binary {
                op,
                lhs: Box::new(expr),
                rhs: Box::new(rhs),
            };
        }
        Ok(self.with_span(mark, expr))
    }

    fn match_binary_op(&mut self, ops: &[(TokenKind, BinaryOp)]) -> Option<BinaryOp> {
        for (token, op) in ops {
            if self.peek_is(token) {
                self.bump();
                return Some(*op);
            }
        }
        None
    }

    fn parse_label_expr(&mut self) -> Result<Expr, ParseError> {
        let mark = self.mark();
        self.expect_ident_exact("label")?;
        self.expect_simple(&TokenKind::LBracket, "expected '[' after label", vec!["["])?;
        self.expect_simple(&TokenKind::Dot, "expected '.' in label target", vec!["."])?;
        let label = self.expect_ident("expected label name")?;
        self.expect_simple(
            &TokenKind::RBracket,
            "expected ']' after label target",
            vec!["]"],
        )?;
        let expr = self.parse_expr()?;
        Ok(self.with_span(
            mark,
            Expr::Label {
                label,
                expr: Box::new(expr),
            },
        ))
    }

    fn parse_postfix_expr(&mut self) -> Result<Expr, ParseError> {
        let mark = self.mark();
        let mut expr = self.parse_atom_expr()?;

        loop {
            if self.peek_is(&TokenKind::Dot) && matches!(self.peek_n(1), Some(TokenKind::Ident(_)))
            {
                self.bump();
                let field = self.expect_ident("expected member name after '.'")?;
                expr = Expr::Member {
                    object: Box::new(expr),
                    field,
                };
                continue;
            }

            if self.peek_is(&TokenKind::LParen)
                || self.peek_is(&TokenKind::LBracket)
                || self.starts_labeled_closure_arg()
            {
                expr = self.parse_call_suffix(expr)?;
                continue;
            }

            break;
        }

        Ok(self.with_span(mark, expr))
    }

    fn parse_call_suffix(&mut self, callee: Expr) -> Result<Expr, ParseError> {
        let mark = self.mark();
        let static_args = if self.peek_is(&TokenKind::LBracket) {
            self.parse_static_args()?
        } else {
            Vec::new()
        };

        let args = if self.peek_is(&TokenKind::LParen) {
            self.parse_call_args()?
        } else {
            Vec::new()
        };

        let trailing = self.parse_labeled_closure_args()?;

        if !static_args.is_empty() && args.is_empty() && trailing.is_empty() {
            return Err(self.error_here(
                "expected '(' or labeled closure after static call arguments",
                vec!["(", "identifier"],
                Some("use either foo[T](x) or foo[T] label { ... }".to_string()),
            ));
        }

        if args.is_empty()
            && trailing.is_empty()
            && !self.peek_is(&TokenKind::LParen)
            && !static_args.is_empty()
        {
            return Err(self.error_here(
                "invalid call suffix",
                vec!["(", "identifier"],
                Some("call syntax requires runtime args and/or labeled closures".to_string()),
            ));
        }

        Ok(self.with_span(
            mark,
            Expr::Call {
                callee: Box::new(callee),
                static_args,
                args,
                trailing,
            },
        ))
    }

    fn parse_labeled_closure_args(&mut self) -> Result<Vec<LabeledClosureArg>, ParseError> {
        let mut trailing = Vec::new();
        while self.starts_labeled_closure_arg() {
            let label = self.expect_ident("expected trailing closure label")?;
            let body = self.parse_brace_body_expr()?;
            trailing.push(LabeledClosureArg { label, body });
        }
        Ok(trailing)
    }

    fn starts_labeled_closure_arg(&self) -> bool {
        matches!(self.peek(), TokenKind::Ident(_))
            && matches!(self.peek_n(1), Some(TokenKind::LBrace))
    }

    fn parse_call_args(&mut self) -> Result<Vec<Expr>, ParseError> {
        self.expect_simple(&TokenKind::LParen, "expected '('", vec!["("])?;
        let mut args = Vec::new();
        if self.peek_is(&TokenKind::RParen) {
            self.bump();
            return Ok(args);
        }
        loop {
            if self.peek_is(&TokenKind::Underscore) {
                self.bump();
                args.push(Expr::Placeholder);
            } else {
                args.push(self.parse_expr()?);
            }
            if self.peek_is(&TokenKind::Comma) {
                self.bump();
                if self.peek_is(&TokenKind::RParen) {
                    self.bump();
                    break;
                }
                continue;
            }
            self.expect_simple(&TokenKind::RParen, "expected ')'", vec![")"])?;
            break;
        }
        Ok(args)
    }

    fn parse_macro_apply_expr(&mut self) -> Result<Expr, ParseError> {
        let mark = self.mark();
        let head_name = self.expect_ident("expected macro name")?;
        let static_args = if self.peek_is(&TokenKind::LBracket) {
            self.parse_static_args()?
        } else {
            Vec::new()
        };

        if !self.starts_operand() {
            return Err(self.error_here(
                "macro application missing operand",
                vec!["expression"],
                Some(
                    "macro application uses the form 'macro_name node' or 'macro_name[args] node'"
                        .to_string(),
                ),
            ));
        }

        let operand = if head_name == "let" || head_name == "def" {
            let operand_mark = self.mark();
            match self.parse_binding_payload() {
                Ok(operand) => operand,
                Err(err) if err.message.contains("expected '=' in binding") => {
                    self.cursor = operand_mark;
                    if self.is_macro_apply_start() {
                        self.parse_macro_apply_expr()?
                    } else {
                        self.parse_assign_expr()?
                    }
                }
                Err(err) => return Err(err),
            }
        } else if self.is_macro_apply_start() {
            self.parse_macro_apply_expr()?
        } else {
            self.parse_assign_expr()?
        };
        Ok(self.with_span(
            mark,
            Expr::MacroApply {
                macro_name: head_name,
                static_args,
                operand: Box::new(operand),
            },
        ))
    }

    fn parse_atom_expr(&mut self) -> Result<Expr, ParseError> {
        let mark = self.mark();
        match self.peek() {
            TokenKind::Ident(name) => {
                let name = name.clone();
                self.bump();
                Ok(self.with_span(mark, Expr::Ident(name)))
            }
            TokenKind::Int(raw) => {
                let value = raw.clone();
                self.bump();
                Ok(self.with_span(mark, Expr::Int(value)))
            }
            TokenKind::Float(raw) => {
                let value = raw.clone();
                self.bump();
                Ok(self.with_span(mark, Expr::Float(value)))
            }
            TokenKind::String(raw) => {
                let value = raw.clone();
                self.bump();
                Ok(self.with_span(mark, Expr::String(value)))
            }
            TokenKind::Char(raw) => {
                let value = raw.clone();
                self.bump();
                Ok(self.with_span(mark, Expr::Char(value)))
            }
            TokenKind::LParen => self.parse_paren_literal_expr(),
            TokenKind::Dot => self.parse_dot_ident_expr(),
            TokenKind::LBracket => self.parse_bracket_literal_expr(),
            TokenKind::LBrace => self.parse_brace_body_expr(),
            _ => Err(self.error_here(
                "expected expression operand",
                vec!["identifier", "literal", ".ident", "[", "{"],
                None,
            )),
        }
    }

    fn parse_dot_ident_expr(&mut self) -> Result<Expr, ParseError> {
        let mark = self.mark();
        self.expect_simple(&TokenKind::Dot, "expected '.'", vec!["."])?;
        let name = self.expect_ident("expected identifier after '.'")?;
        let payload = if self.peek_is(&TokenKind::LParen) {
            self.bump();
            let expr = self.parse_expr()?;
            self.expect_simple(
                &TokenKind::RParen,
                "expected ')' after dot payload",
                vec![")"],
            )?;
            Some(Box::new(expr))
        } else {
            None
        };
        Ok(self.with_span(mark, Expr::DotIdent { name, payload }))
    }

    fn parse_paren_literal_expr(&mut self) -> Result<Expr, ParseError> {
        self.expect_simple(&TokenKind::LParen, "expected '('", vec!["("])?;
        if self.peek_is(&TokenKind::RParen) {
            self.bump();
            return Ok(Expr::Tuple(Vec::new()));
        }

        if matches!(self.peek(), TokenKind::Ident(_)) && self.peek_n(1) == Some(&TokenKind::Eq) {
            let mut fields = Vec::new();
            loop {
                let field = self.expect_ident("expected struct field name")?;
                self.expect_simple(
                    &TokenKind::Eq,
                    "expected '=' after struct field name",
                    vec!["="],
                )?;
                let value = self.parse_expr()?;
                fields.push((field, value));

                if self.peek_is(&TokenKind::Comma) {
                    self.bump();
                    if self.peek_is(&TokenKind::RParen) {
                        break;
                    }
                    continue;
                }
                break;
            }
            self.expect_simple(
                &TokenKind::RParen,
                "expected ')' after struct literal",
                vec![")"],
            )?;
            return Ok(Expr::Struct(fields));
        }

        let first = self.parse_elvis_expr()?;
        if !self.peek_is(&TokenKind::Comma) {
            self.expect_simple(
                &TokenKind::RParen,
                "expected ')' after parenthesized expression",
                vec![")"],
            )?;
            return Ok(first);
        }

        let mut items = vec![first];
        while self.peek_is(&TokenKind::Comma) {
            self.bump();
            if self.peek_is(&TokenKind::RParen) {
                break;
            }
            items.push(self.parse_expr()?);
        }
        self.expect_simple(
            &TokenKind::RParen,
            "expected ')' after tuple literal",
            vec![")"],
        )?;
        Ok(Expr::Tuple(items))
    }

    fn parse_bracket_literal_expr(&mut self) -> Result<Expr, ParseError> {
        self.expect_simple(&TokenKind::LBracket, "expected '['", vec!["["])?;
        if self.peek_is(&TokenKind::RBracket) {
            self.bump();
            return Ok(Expr::List(Vec::new()));
        }

        let first = self.parse_sequence_until(&[TokenKind::Comma, TokenKind::RBracket])?;
        if self.peek_is(&TokenKind::Eq) {
            self.bump();
            let value = self.parse_sequence_until(&[TokenKind::Comma, TokenKind::RBracket])?;
            let mut entries = vec![(first, value)];
            while self.peek_is(&TokenKind::Comma) {
                self.bump();
                if self.peek_is(&TokenKind::RBracket) {
                    break;
                }
                let key = self.parse_elvis_expr()?;
                self.expect_simple(&TokenKind::Eq, "expected '=' in dict entry", vec!["="])?;
                let value = self.parse_sequence_until(&[TokenKind::Comma, TokenKind::RBracket])?;
                entries.push((key, value));
            }
            self.expect_simple(
                &TokenKind::RBracket,
                "expected ']' after dict literal",
                vec!["]"],
            )?;
            return Ok(Expr::Dict(entries));
        }

        let mut items = vec![first];
        while self.peek_is(&TokenKind::Comma) {
            self.bump();
            if self.peek_is(&TokenKind::RBracket) {
                break;
            }
            items.push(self.parse_sequence_until(&[TokenKind::Comma, TokenKind::RBracket])?);
        }
        self.expect_simple(
            &TokenKind::RBracket,
            "expected ']' after list literal",
            vec!["]"],
        )?;
        Ok(Expr::List(items))
    }

    fn parse_binding_payload(&mut self) -> Result<Expr, ParseError> {
        let mut bindings = Vec::new();
        loop {
            let pattern = self.parse_pattern()?;
            self.expect_simple(&TokenKind::Eq, "expected '=' in binding", vec!["="])?;
            let value = self.parse_assign_expr()?;
            bindings.push(Binding { pattern, value });
            if self.peek_is(&TokenKind::Comma) {
                self.bump();
                continue;
            }
            break;
        }
        Ok(Expr::Bindings(bindings))
    }

    fn parse_sequence_until(&mut self, terminators: &[TokenKind]) -> Result<Expr, ParseError> {
        let mut items = vec![self.parse_expr()?];
        let mut saw_semi = false;
        while self.peek_is(&TokenKind::Semi) {
            saw_semi = true;
            self.bump();
            if terminators.iter().any(|tok| self.peek_is(tok)) {
                break;
            }
            items.push(self.parse_expr()?);
        }
        if saw_semi {
            Ok(Expr::Block(items))
        } else {
            Ok(items
                .into_iter()
                .next()
                .expect("sequence parser should produce at least one expression"))
        }
    }

    fn ident_assign_target(&self, expr: &Expr) -> Option<String> {
        match expr.unspanned() {
            Expr::Ident(name) => Some(name.clone()),
            _ => None,
        }
    }

    fn starts_operand(&self) -> bool {
        matches!(
            self.peek(),
            TokenKind::Ident(_)
                | TokenKind::Int(_)
                | TokenKind::Float(_)
                | TokenKind::String(_)
                | TokenKind::Char(_)
                | TokenKind::Dot
                | TokenKind::LBracket
                | TokenKind::LBrace
        )
    }

    fn is_macro_apply_start(&self) -> bool {
        let Some(TokenKind::Ident(name)) = self.peek_n(0) else {
            return false;
        };
        if name == "true" || name == "false" {
            return false;
        }
        let known_macro = self.macro_symbols.contains(name);
        if matches!(self.peek_n(1), Some(TokenKind::Ident(_)))
            && matches!(self.peek_n(2), Some(TokenKind::LBrace))
        {
            return false;
        }

        if matches!(self.peek_n(1), Some(TokenKind::LBracket)) {
            if known_macro {
                return !self.looks_like_static_call_head();
            }
            return matches!(
                self.token_after_static_args(),
                Some(TokenKind::Ident(_))
                    | Some(TokenKind::Int(_))
                    | Some(TokenKind::Float(_))
                    | Some(TokenKind::String(_))
                    | Some(TokenKind::Char(_))
                    | Some(TokenKind::Dot)
                    | Some(TokenKind::LBracket)
                    | Some(TokenKind::LBrace)
            ) && !self.looks_like_static_call_head();
        }

        if !known_macro {
            if matches!(self.peek_n(1), Some(TokenKind::Ident(next)) if next == "def" || next == "use")
            {
                return false;
            }
            return matches!(
                self.peek_n(1),
                Some(TokenKind::Ident(_))
                    | Some(TokenKind::Int(_))
                    | Some(TokenKind::Float(_))
                    | Some(TokenKind::String(_))
                    | Some(TokenKind::Char(_))
                    | Some(TokenKind::LBrace)
                    | Some(TokenKind::LBracket)
            );
        }

        matches!(
            self.peek_n(1),
            Some(TokenKind::Ident(_))
                | Some(TokenKind::Int(_))
                | Some(TokenKind::Float(_))
                | Some(TokenKind::String(_))
                | Some(TokenKind::Char(_))
                | Some(TokenKind::Dot)
                | Some(TokenKind::LBrace)
                | Some(TokenKind::LBracket)
        )
    }

    fn looks_like_static_call_head(&self) -> bool {
        let Some(TokenKind::Ident(_)) = self.peek_n(0) else {
            return false;
        };
        if !matches!(self.peek_n(1), Some(TokenKind::LBracket)) {
            return false;
        }

        let mut i = self.cursor + 1;
        let mut depth = 0usize;
        while i < self.tokens.len() {
            match self.tokens[i].kind {
                TokenKind::LBracket => depth += 1,
                TokenKind::RBracket => {
                    if depth == 0 {
                        return false;
                    }
                    depth -= 1;
                    if depth == 0 {
                        if matches!(
                            self.tokens.get(i + 1).map(|t| &t.kind),
                            Some(TokenKind::LParen)
                        ) {
                            return true;
                        }
                        if matches!(
                            self.tokens.get(i + 1).map(|t| &t.kind),
                            Some(TokenKind::Ident(_))
                        ) && matches!(
                            self.tokens.get(i + 2).map(|t| &t.kind),
                            Some(TokenKind::LBrace)
                        ) {
                            return true;
                        }
                        return false;
                    }
                }
                _ => {}
            }
            i += 1;
        }
        false
    }

    fn token_after_static_args(&self) -> Option<&TokenKind> {
        if !matches!(self.peek_n(1), Some(TokenKind::LBracket)) {
            return None;
        }

        let mut i = self.cursor + 1;
        let mut depth = 0usize;
        while i < self.tokens.len() {
            match self.tokens[i].kind {
                TokenKind::LBracket => depth += 1,
                TokenKind::RBracket => {
                    if depth == 0 {
                        return None;
                    }
                    depth -= 1;
                    if depth == 0 {
                        return self.tokens.get(i + 1).map(|t| &t.kind);
                    }
                }
                _ => {}
            }
            i += 1;
        }
        None
    }

    fn expect_ident(&mut self, message: &str) -> Result<String, ParseError> {
        match self.peek() {
            TokenKind::Ident(name) => {
                let name = name.clone();
                self.bump();
                Ok(name)
            }
            _ => Err(self.error_here(message, vec!["identifier"], None)),
        }
    }

    fn expect_ident_exact(&mut self, expected: &str) -> Result<(), ParseError> {
        match self.peek() {
            TokenKind::Ident(name) if name == expected => {
                self.bump();
                Ok(())
            }
            _ => Err(self.error_here(format!("expected '{expected}'"), vec!["identifier"], None)),
        }
    }

    fn expect_simple(
        &mut self,
        expected: &TokenKind,
        message: &str,
        expected_names: Vec<&'static str>,
    ) -> Result<(), ParseError> {
        if self.peek_is(expected) {
            self.bump();
            return Ok(());
        }
        Err(self.error_here(message, expected_names, None))
    }

    fn error_here(
        &self,
        message: impl Into<String>,
        expected: Vec<&'static str>,
        hint: Option<String>,
    ) -> ParseError {
        let mut diagnostic = Diagnostic::error(Issue::ParseUnexpectedToken {
            detail: format!(
                "{} (expected: {}; found: {})",
                message.into(),
                if expected.is_empty() {
                    "<unspecified>".to_string()
                } else {
                    expected.join(" | ")
                },
                token_debug_name(&self.peek_token().kind)
            ),
        })
        .with_stage(Stage::Parser)
        .with_span(self.peek_token().span.into());

        if let Some(hint) = hint {
            diagnostic = diagnostic.with_hint(hint);
        }

        diagnostic
    }

    fn peek_ident_is(&self, value: &str) -> bool {
        matches!(self.peek(), TokenKind::Ident(name) if name == value)
    }

    fn peek_is(&self, expected: &TokenKind) -> bool {
        same_token_variant(self.peek(), expected)
    }

    fn peek(&self) -> &TokenKind {
        &self.tokens[self.cursor].kind
    }

    fn peek_token(&self) -> &Token {
        &self.tokens[self.cursor]
    }

    fn peek_n(&self, n: usize) -> Option<&TokenKind> {
        self.tokens.get(self.cursor + n).map(|token| &token.kind)
    }

    fn bump(&mut self) {
        if !self.is_eof() {
            self.cursor += 1;
        }
    }

    fn is_eof(&self) -> bool {
        matches!(self.peek(), TokenKind::Eof)
    }
}

fn token_debug_name(kind: &TokenKind) -> String {
    match kind {
        TokenKind::Ident(_) => "identifier".to_string(),
        TokenKind::Int(_) => "int".to_string(),
        TokenKind::Float(_) => "float".to_string(),
        TokenKind::String(_) => "string".to_string(),
        TokenKind::Char(_) => "char".to_string(),
        TokenKind::LineComment(_) => "line_comment".to_string(),
        TokenKind::BlockComment(_) => "block_comment".to_string(),
        TokenKind::Defmacro => "defmacro".to_string(),
        TokenKind::Arrow => "->".to_string(),
        TokenKind::Ellipsis => "...".to_string(),
        TokenKind::Colon => ":".to_string(),
        TokenKind::Comma => ",".to_string(),
        TokenKind::Dot => ".".to_string(),
        TokenKind::Eq => "=".to_string(),
        TokenKind::Semi => ";".to_string(),
        TokenKind::Tilde => "~".to_string(),
        TokenKind::Underscore => "_".to_string(),
        TokenKind::LParen => "(".to_string(),
        TokenKind::RParen => ")".to_string(),
        TokenKind::LBrace => "{".to_string(),
        TokenKind::RBrace => "}".to_string(),
        TokenKind::LBracket => "[".to_string(),
        TokenKind::RBracket => "]".to_string(),
        TokenKind::Plus => "+".to_string(),
        TokenKind::Minus => "-".to_string(),
        TokenKind::Star => "*".to_string(),
        TokenKind::Slash => "/".to_string(),
        TokenKind::Percent => "%".to_string(),
        TokenKind::PlusPlus => "++".to_string(),
        TokenKind::MinusMinus => "--".to_string(),
        TokenKind::EqEq => "==".to_string(),
        TokenKind::NotEq => "!=".to_string(),
        TokenKind::Lt => "<".to_string(),
        TokenKind::Lte => "<=".to_string(),
        TokenKind::Gt => ">".to_string(),
        TokenKind::Gte => ">=".to_string(),
        TokenKind::PipePipe => "||".to_string(),
        TokenKind::PipeArrow => "|>".to_string(),
        TokenKind::AmpAmp => "&&".to_string(),
        TokenKind::QuestionColon => "?:".to_string(),
        TokenKind::QuestionDot => "?.".to_string(),
        TokenKind::BangBang => "!!".to_string(),
        TokenKind::Range => "..".to_string(),
        TokenKind::Eof => "eof".to_string(),
    }
}

fn same_token_variant(left: &TokenKind, right: &TokenKind) -> bool {
    matches!(
        (left, right),
        (TokenKind::Defmacro, TokenKind::Defmacro)
            | (TokenKind::Arrow, TokenKind::Arrow)
            | (TokenKind::Ellipsis, TokenKind::Ellipsis)
            | (TokenKind::Colon, TokenKind::Colon)
            | (TokenKind::Comma, TokenKind::Comma)
            | (TokenKind::Dot, TokenKind::Dot)
            | (TokenKind::Eq, TokenKind::Eq)
            | (TokenKind::Semi, TokenKind::Semi)
            | (TokenKind::Tilde, TokenKind::Tilde)
            | (TokenKind::Underscore, TokenKind::Underscore)
            | (TokenKind::LParen, TokenKind::LParen)
            | (TokenKind::RParen, TokenKind::RParen)
            | (TokenKind::LBrace, TokenKind::LBrace)
            | (TokenKind::RBrace, TokenKind::RBrace)
            | (TokenKind::LBracket, TokenKind::LBracket)
            | (TokenKind::RBracket, TokenKind::RBracket)
            | (TokenKind::LineComment(_), TokenKind::LineComment(_))
            | (TokenKind::BlockComment(_), TokenKind::BlockComment(_))
            | (TokenKind::Plus, TokenKind::Plus)
            | (TokenKind::Minus, TokenKind::Minus)
            | (TokenKind::Star, TokenKind::Star)
            | (TokenKind::Slash, TokenKind::Slash)
            | (TokenKind::Percent, TokenKind::Percent)
            | (TokenKind::PlusPlus, TokenKind::PlusPlus)
            | (TokenKind::MinusMinus, TokenKind::MinusMinus)
            | (TokenKind::EqEq, TokenKind::EqEq)
            | (TokenKind::NotEq, TokenKind::NotEq)
            | (TokenKind::Lt, TokenKind::Lt)
            | (TokenKind::Lte, TokenKind::Lte)
            | (TokenKind::Gt, TokenKind::Gt)
            | (TokenKind::Gte, TokenKind::Gte)
            | (TokenKind::PipePipe, TokenKind::PipePipe)
            | (TokenKind::PipeArrow, TokenKind::PipeArrow)
            | (TokenKind::AmpAmp, TokenKind::AmpAmp)
            | (TokenKind::QuestionColon, TokenKind::QuestionColon)
            | (TokenKind::QuestionDot, TokenKind::QuestionDot)
            | (TokenKind::BangBang, TokenKind::BangBang)
            | (TokenKind::Range, TokenKind::Range)
            | (TokenKind::Eof, TokenKind::Eof)
            | (TokenKind::Ident(_), TokenKind::Ident(_))
            | (TokenKind::Int(_), TokenKind::Int(_))
            | (TokenKind::Float(_), TokenKind::Float(_))
            | (TokenKind::String(_), TokenKind::String(_))
            | (TokenKind::Char(_), TokenKind::Char(_))
    )
}

fn build_doc_attribute(markdown: String) -> DocAttribute {
    let mut symbol_docs = Vec::new();
    let mut in_args = false;
    let mut pending_returns = false;

    for raw_line in markdown.lines() {
        let line = raw_line.trim();
        if line.is_empty() {
            continue;
        }
        if let Some(rest) = line.strip_prefix("# ") {
            let name = rest.trim().to_string();
            if !name.is_empty() {
                symbol_docs.push(SymbolDoc {
                    name,
                    doc: markdown.clone(),
                });
            }
            in_args = false;
            pending_returns = false;
            continue;
        }
        if line.eq_ignore_ascii_case("## Arguments") {
            in_args = true;
            pending_returns = false;
            continue;
        }
        if line.eq_ignore_ascii_case("## Returns") {
            in_args = false;
            pending_returns = true;
            continue;
        }

        if in_args {
            if let Some(rest) = line.strip_prefix("- ") {
                let name_part = rest.split(':').next().unwrap_or(rest).trim();
                if !name_part.is_empty() {
                    symbol_docs.push(SymbolDoc {
                        name: name_part.to_string(),
                        doc: line.to_string(),
                    });
                }
            }
            continue;
        }

        if pending_returns {
            symbol_docs.push(SymbolDoc {
                name: "return".to_string(),
                doc: line.to_string(),
            });
            pending_returns = false;
        }
    }

    DocAttribute {
        markdown,
        symbol_docs,
    }
}

fn collect_macro_symbols(tokens: &[Token]) -> HashSet<String> {
    let mut symbols = HashSet::new();
    for builtin in BUILTIN_MACROS {
        symbols.insert((*builtin).to_string());
    }

    let mut i = 0usize;
    while i + 1 < tokens.len() {
        if matches!(tokens[i].kind, TokenKind::Defmacro) {
            i += 1;
            if matches!(tokens.get(i).map(|t| &t.kind), Some(TokenKind::LBracket)) {
                let mut depth = 0usize;
                while i < tokens.len() {
                    match tokens[i].kind {
                        TokenKind::LBracket => depth += 1,
                        TokenKind::RBracket => {
                            if depth == 0 {
                                break;
                            }
                            depth -= 1;
                            if depth == 0 {
                                i += 1;
                                break;
                            }
                        }
                        _ => {}
                    }
                    i += 1;
                }
            }

            if let Some(Token {
                kind: TokenKind::Ident(name),
                ..
            }) = tokens.get(i)
            {
                symbols.insert(name.clone());
            }
        }
        i += 1;
    }

    symbols
}

#[cfg(test)]
mod tests {
    use crate::ast::{
        BinaryOp, Decl, Expr, Pattern, StaticArg, StaticParamKind, TypeExpr, UseBinding, UseDecl,
    };
    use crate::parser::Parser;

    fn u(expr: &Expr) -> &Expr {
        expr.unspanned()
    }

    #[test]
    fn parse_complex_method_declaration_contract() {
        let src = "def[T, E, U] Result[T, E].map(self: Result[T, E], with: Func[T, U]) -> Result[U, E] { .ok(value) -> .ok(with(value)), err -> err }";
        let parsed = Parser::parse_source(src).expect("should parse complex method declaration");
        let decl = parsed.declarations.first().expect("expected declaration");

        let Decl::Function(function) = decl else {
            panic!("expected function declaration")
        };

        assert_eq!(function.static_params.len(), 3);
        assert!(matches!(
            function.static_params[0].kind,
            StaticParamKind::Type
        ));
        assert_eq!(function.name, "map");
        assert_eq!(function.params.len(), 2);
        assert!(matches!(function.receiver, Some(TypeExpr::Named { .. })));
        assert!(matches!(function.return_type, TypeExpr::Named { .. }));

        let Expr::MultiArm(arms) = u(&function.body) else {
            panic!("expected multi-arm body")
        };
        assert_eq!(arms.len(), 2);
        assert!(matches!(arms[0].patterns[0], Pattern::DotVariant { .. }));
        assert!(matches!(arms[1].patterns[0], Pattern::Ident(_)));
        assert!(arms[0].guard.is_none());
        assert!(arms[1].guard.is_none());
    }

    #[test]
    fn reject_method_receiver_without_required_static_args() {
        let src = "def Seq.len(self: Seq[Int]) -> Int { 0 }";
        let err = Parser::parse_source(src).expect_err("receiver should require static args");
        assert_eq!(err.code_str(), "E_PARSE_UNEXPECTED_TOKEN");
        assert!(err.message.contains("requires explicit static arguments"));
    }

    #[test]
    fn parse_multi_arm_with_optional_left_side_and_guards() {
        let src = "def x = { ~ gt(x, 10) -> a, x ~ lt(x, 0) -> b, -> c }";
        let parsed = Parser::parse_source(src).expect("should parse guarded/default arms");
        let decl = parsed.declarations.first().expect("expected declaration");
        let value = match decl {
            Decl::Assign { value, .. } => value,
            _ => panic!("expected assignment"),
        };

        let Expr::MultiArm(arms) = u(value) else {
            panic!("expected multi-arm expression")
        };
        assert_eq!(arms.len(), 3);
        assert!(arms[0].patterns.is_empty());
        assert!(arms[0].guard.is_some());
        assert_eq!(arms[1].patterns.len(), 1);
        assert!(arms[1].guard.is_some());
        assert!(arms[2].patterns.is_empty());
        assert!(arms[2].guard.is_none());
    }

    #[test]
    fn parse_type_expr_infer_hole_in_type_args() {
        let src = "def x = id[Array[_, 3]](a)";
        let parsed = Parser::parse_source(src).expect("should parse infer hole in type args");
        let Decl::Assign { value, .. } = parsed.declarations.first().expect("expected decl") else {
            panic!("expected assignment")
        };

        let Expr::Call { static_args, .. } = u(value) else {
            panic!("expected call")
        };
        let Some(StaticArg::Type(TypeExpr::Named { name, args })) = static_args.first() else {
            panic!("expected static type arg")
        };
        assert_eq!(name, "Array");
        assert!(matches!(args[0], StaticArg::Type(TypeExpr::InferHole)));
    }

    #[test]
    fn parse_postfix_cast_expression() {
        let src = "def x = y: Int";
        let parsed = Parser::parse_source(src).expect("should parse postfix cast expression");
        let decl = parsed.declarations.first().expect("expected declaration");
        let value = match decl {
            Decl::Assign { value, .. } => value,
            _ => panic!("expected assignment"),
        };

        let Expr::Binary { op, lhs, rhs } = u(value) else {
            panic!("expected binary cast expression")
        };
        assert!(matches!(op, crate::ast::BinaryOp::Colon));
        assert!(matches!(u(lhs.as_ref()), Expr::Ident(name) if name == "y"));
        assert!(
            matches!(rhs.as_ref(), Expr::TypeExpr(TypeExpr::Named { name, .. }) if name == "Int")
        );
    }

    #[test]
    fn parse_infer_hole_as_direct_call_static_arg() {
        let src = "def x = f[_](1)";
        let parsed = Parser::parse_source(src).expect("should parse hole call arg");
        let Decl::Assign { value, .. } = parsed.declarations.first().expect("expected decl") else {
            panic!("expected assignment")
        };
        let Expr::Call { static_args, .. } = u(value) else {
            panic!("expected call")
        };
        assert!(matches!(
            static_args[0],
            StaticArg::Type(TypeExpr::InferHole)
        ));
    }

    #[test]
    fn parse_pipe_operator_left_associative() {
        let src = "def x = baz |> foo |> bar";
        let parsed = Parser::parse_source(src).expect("should parse pipe chain");
        let Decl::Assign { value, .. } = parsed.declarations.first().expect("expected decl") else {
            panic!("expected assignment")
        };

        let Expr::Binary { op, lhs, rhs } = u(value) else {
            panic!("expected binary pipe expression")
        };
        assert!(matches!(op, crate::ast::BinaryOp::Pipe));
        assert!(matches!(u(rhs.as_ref()), Expr::Ident(name) if name == "bar"));

        let Expr::Binary {
            op: inner_op,
            lhs: inner_lhs,
            rhs: inner_rhs,
        } = u(lhs.as_ref())
        else {
            panic!("expected left-associated inner pipe")
        };
        assert!(matches!(inner_op, crate::ast::BinaryOp::Pipe));
        assert!(matches!(u(inner_lhs.as_ref()), Expr::Ident(name) if name == "baz"));
        assert!(matches!(u(inner_rhs.as_ref()), Expr::Ident(name) if name == "foo"));
    }

    #[test]
    fn parse_pipe_has_lower_precedence_than_addition() {
        let src = "def x = a |> b + c";
        let parsed = Parser::parse_source(src).expect("should parse pipe precedence");
        let Decl::Assign { value, .. } = parsed.declarations.first().expect("expected decl") else {
            panic!("expected assignment")
        };

        let Expr::Binary { op, lhs, rhs } = u(value) else {
            panic!("expected outer pipe")
        };
        assert!(matches!(op, crate::ast::BinaryOp::Pipe));
        assert!(matches!(u(lhs.as_ref()), Expr::Ident(name) if name == "a"));
        assert!(matches!(
            u(rhs.as_ref()),
            Expr::Binary {
                op: crate::ast::BinaryOp::Add,
                ..
            }
        ));
    }

    #[test]
    fn parse_call_args_allow_placeholders() {
        let src = "def x = f(5, _, _)";
        let parsed = Parser::parse_source(src).expect("should parse placeholders in call args");
        let Decl::Assign { value, .. } = parsed.declarations.first().expect("expected decl") else {
            panic!("expected assignment")
        };

        let Expr::Call { args, .. } = u(value) else {
            panic!("expected call")
        };
        assert_eq!(args.len(), 3);
        assert!(matches!(u(&args[0]), Expr::Int(v) if v == "5"));
        assert!(matches!(u(&args[1]), Expr::Placeholder));
        assert!(matches!(u(&args[2]), Expr::Placeholder));
    }

    #[test]
    fn parse_call_with_labeled_trailing_closures() {
        let src = "def x = f(1) then { 2 } else { 3 }";
        let parsed = Parser::parse_source(src).expect("should parse call with labeled closures");
        let Decl::Assign { value, .. } = parsed.declarations.first().expect("expected decl") else {
            panic!("expected assignment")
        };

        let Expr::Call {
            callee,
            static_args,
            args,
            trailing,
        } = u(value)
        else {
            panic!("expected call")
        };

        assert!(matches!(u(callee.as_ref()), Expr::Ident(name) if name == "f"));
        assert!(static_args.is_empty());
        assert_eq!(args.len(), 1);
        assert_eq!(trailing.len(), 2);
        assert_eq!(trailing[0].label, "then");
        assert_eq!(trailing[1].label, "else");
    }

    #[test]
    fn parse_call_form_1_callee_args() {
        let src = "def x = f(1, 2)";
        let parsed = Parser::parse_source(src).expect("should parse call form 1");
        let Decl::Assign { value, .. } = parsed.declarations.first().expect("expected decl") else {
            panic!("expected assignment")
        };
        let Expr::Call { args, trailing, .. } = u(value) else {
            panic!("expected call")
        };
        assert_eq!(args.len(), 2);
        assert!(trailing.is_empty());
    }

    #[test]
    fn parse_call_form_2_callee_static_args_args() {
        let src = "def x = f[Int](1)";
        let parsed = Parser::parse_source(src).expect("should parse call form 2");
        let Decl::Assign { value, .. } = parsed.declarations.first().expect("expected decl") else {
            panic!("expected assignment")
        };
        let Expr::Call {
            static_args,
            args,
            trailing,
            ..
        } = u(value)
        else {
            panic!("expected call")
        };
        assert_eq!(static_args.len(), 1);
        assert_eq!(args.len(), 1);
        assert!(trailing.is_empty());
    }

    #[test]
    fn parse_call_form_4_static_args_args_and_labels() {
        let src = "def x = f[Int](1) then { 2 } else { 3 }";
        let parsed = Parser::parse_source(src).expect("should parse call form 4");
        let Decl::Assign { value, .. } = parsed.declarations.first().expect("expected decl") else {
            panic!("expected assignment")
        };
        let Expr::Call {
            static_args,
            args,
            trailing,
            ..
        } = u(value)
        else {
            panic!("expected call")
        };
        assert_eq!(static_args.len(), 1);
        assert_eq!(args.len(), 1);
        assert_eq!(trailing.len(), 2);
    }

    #[test]
    fn parse_call_form_6_labeled_closures_only() {
        let src = "def x = f then { 1 } else { 2 }";
        let parsed = Parser::parse_source(src).expect("should parse call form 6");
        let Decl::Assign { value, .. } = parsed.declarations.first().expect("expected decl") else {
            panic!("expected assignment")
        };
        let Expr::Call { args, trailing, .. } = u(value) else {
            panic!("expected call")
        };
        assert!(args.is_empty());
        assert_eq!(trailing.len(), 2);
    }

    #[test]
    fn parse_call_form_7_static_args_and_labeled_closures_only() {
        let src = "def x = f[Int] then { 1 } else { 2 }";
        let parsed = Parser::parse_source(src).expect("should parse call form 7");
        let Decl::Assign { value, .. } = parsed.declarations.first().expect("expected decl") else {
            panic!("expected assignment")
        };
        let Expr::Call {
            static_args,
            args,
            trailing,
            ..
        } = u(value)
        else {
            panic!("expected call")
        };
        assert_eq!(static_args.len(), 1);
        assert!(args.is_empty());
        assert_eq!(trailing.len(), 2);
    }

    #[test]
    fn parse_call_with_only_labeled_trailing_closure() {
        let src = "def x = f do { 1 }";
        let parsed =
            Parser::parse_source(src).expect("should parse call with only labeled closure");
        let Decl::Assign { value, .. } = parsed.declarations.first().expect("expected decl") else {
            panic!("expected assignment")
        };

        let Expr::Call { args, trailing, .. } = u(value) else {
            panic!("expected call")
        };
        assert!(args.is_empty());
        assert_eq!(trailing.len(), 1);
        assert_eq!(trailing[0].label, "do");
    }

    #[test]
    fn parse_method_call_with_labeled_trailing_closure() {
        let src = "def x = object.method do { 1 }";
        let parsed =
            Parser::parse_source(src).expect("should parse method call with labeled closure");
        let Decl::Assign { value, .. } = parsed.declarations.first().expect("expected decl") else {
            panic!("expected assignment")
        };

        let Expr::Call {
            callee, trailing, ..
        } = u(value)
        else {
            panic!("expected call")
        };
        assert_eq!(trailing.len(), 1);
        assert_eq!(trailing[0].label, "do");
        assert!(matches!(
            callee.as_ref(),
            Expr::Member { field, .. } if field == "method"
        ));
    }

    #[test]
    fn parse_method_call_with_static_args_and_labeled_closures() {
        let src = "def x = object.method[T] do { 1 } else { 2 }";
        let parsed =
            Parser::parse_source(src).expect("should parse method call static args and closures");
        let Decl::Assign { value, .. } = parsed.declarations.first().expect("expected decl") else {
            panic!("expected assignment")
        };

        let Expr::Call {
            callee,
            static_args,
            args,
            trailing,
        } = u(value)
        else {
            panic!("expected call")
        };
        assert!(matches!(
            callee.as_ref(),
            Expr::Member { field, .. } if field == "method"
        ));
        assert_eq!(static_args.len(), 1);
        assert!(args.is_empty());
        assert_eq!(trailing.len(), 2);
    }

    #[test]
    fn parse_method_call_form_8_args_and_labels() {
        let src = "def x = object.method(1) then { 2 } else { 3 }";
        let parsed = Parser::parse_source(src).expect("should parse method form 8");
        let Decl::Assign { value, .. } = parsed.declarations.first().expect("expected decl") else {
            panic!("expected assignment")
        };
        let Expr::Call {
            callee,
            args,
            trailing,
            ..
        } = u(value)
        else {
            panic!("expected call")
        };
        assert!(matches!(callee.as_ref(), Expr::Member { field, .. } if field == "method"));
        assert_eq!(args.len(), 1);
        assert_eq!(trailing.len(), 2);
    }

    #[test]
    fn unlabeled_trailing_closure_is_not_a_call() {
        let src = "def x = foo { 1 }";
        let parsed = Parser::parse_source(src).expect("should parse as macro-style apply");
        let Decl::Assign { value, .. } = parsed.declarations.first().expect("expected decl") else {
            panic!("expected assignment")
        };
        assert!(matches!(
            u(value),
            Expr::MacroApply { macro_name, .. } if macro_name == "foo"
        ));
    }

    #[test]
    fn unlabeled_trailing_closure_after_paren_call_is_rejected() {
        let src = "def x = foo(1) { 2 }";
        let err = Parser::parse_source(src).expect_err("should reject unlabeled trailing closure");
        assert!(err.message.contains("top-level") || err.message.contains("expected"));
    }

    #[test]
    fn parse_cases_when_call_shape() {
        let src = "def x = cases when { ~ true -> 1, -> 0 }";
        let parsed = Parser::parse_source(src).expect("should parse cases when call");
        let Decl::Assign { value, .. } = parsed.declarations.first().expect("expected decl") else {
            panic!("expected assignment")
        };

        let Expr::Call {
            callee,
            args,
            trailing,
            ..
        } = u(value)
        else {
            panic!("expected call")
        };
        assert!(matches!(u(callee.as_ref()), Expr::Ident(name) if name == "cases"));
        assert!(args.is_empty());
        assert_eq!(trailing.len(), 1);
        assert_eq!(trailing[0].label, "when");
        assert!(matches!(u(&trailing[0].body), Expr::MultiArm(_)));
    }

    #[test]
    fn top_level_runtime_statement_is_rejected() {
        let src = "x = 1";
        let err =
            Parser::parse_source(src).expect_err("should reject runtime top-level assignment");
        assert!(err.message.contains("top-level") || err.message.contains("static declaration"));
    }

    #[test]
    fn top_level_def_cannot_shadow_builtin_macro_symbol() {
        let src = "def inline = 1";
        let err = Parser::parse_source(src).expect_err("should reject macro shadowing");
        assert!(err.message.contains("cannot shadow final macro symbol"));
    }

    #[test]
    fn function_name_cannot_shadow_builtin_macro_symbol() {
        let src = "def return() -> Int { 1 }";
        let err = Parser::parse_source(src).expect_err("should reject macro shadowing");
        assert!(err.message.contains("cannot shadow final macro symbol"));
    }

    #[test]
    fn redefining_macro_symbol_is_rejected() {
        let src = "defmacro m(node: Expr[Int]) -> Expr[Int] { node }; defmacro m(node: Expr[Int]) -> Expr[Int] { node }";
        let err = Parser::parse_source(src).expect_err("should reject macro redefinition");
        assert!(err.message.contains("final and cannot be redefined"));
    }

    #[test]
    fn function_then_macro_name_conflict_errors_on_function_side() {
        let src = "def foo() -> Int { 1 }; defmacro foo(node: Expr[Int]) -> Expr[Int] { node }";
        let err =
            Parser::parse_source(src).expect_err("should reject function shadowing macro symbol");
        assert!(err
            .message
            .contains("function name 'foo' cannot shadow final macro symbol"));
    }

    #[test]
    fn macro_then_function_name_conflict_errors_on_function_side() {
        let src = "defmacro foo(node: Expr[Int]) -> Expr[Int] { node }; def foo() -> Int { 1 }";
        let err =
            Parser::parse_source(src).expect_err("should reject function shadowing macro symbol");
        assert!(err
            .message
            .contains("function name 'foo' cannot shadow final macro symbol"));
    }

    #[test]
    fn parse_defmacro_with_static_params_contract() {
        let src = "defmacro[T, n: static Int] m(node: Expr[T]) -> Expr[T] { node }";
        let parsed = Parser::parse_source(src).expect("should parse defmacro declaration");

        let decl = parsed
            .declarations
            .first()
            .expect("expected one declaration");
        let macro_decl = match decl {
            Decl::Macro(decl) => decl,
            other => panic!("expected macro declaration, got {other:?}"),
        };

        assert_eq!(macro_decl.name, "m");
        assert_eq!(macro_decl.static_params.len(), 2);
        assert!(matches!(
            macro_decl.static_params[0].kind,
            StaticParamKind::Type
        ));
        assert!(matches!(
            macro_decl.static_params[1].kind,
            StaticParamKind::Constraint(TypeExpr::Static(_))
        ));
    }

    #[test]
    fn parse_function_with_constrained_static_params_contract() {
        let src = "def[T: Show, n: static Int] box(x: T) -> T { x }";
        let parsed =
            Parser::parse_source(src).expect("should parse constrained function static params");
        let decl = parsed
            .declarations
            .first()
            .expect("expected one declaration");
        let function = match decl {
            Decl::Function(decl) => decl,
            other => panic!("expected function declaration, got {other:?}"),
        };

        assert_eq!(function.static_params.len(), 2);
        assert_eq!(function.static_params[0].name, "T");
        assert!(matches!(
            function.static_params[0].kind,
            StaticParamKind::Constraint(TypeExpr::Named { .. })
        ));
        assert_eq!(function.static_params[1].name, "n");
        assert!(matches!(
            function.static_params[1].kind,
            StaticParamKind::Constraint(TypeExpr::Static(_))
        ));
    }

    #[test]
    fn parse_function_body_with_multiple_expressions() {
        let src = "def main() -> Void { 0; syscall_exit(0) }";
        let parsed =
            Parser::parse_source(src).expect("should parse function body with multiple expressions");
        let Decl::Function(function) = &parsed.declarations[0] else {
            panic!("expected function declaration")
        };
        assert!(matches!(u(&function.body), Expr::Block(items) if items.len() == 2));
    }

    #[test]
    fn parse_function_body_with_optional_trailing_semicolon() {
        let src = "def main() -> Void { 0; syscall_exit(0); }";
        let parsed = Parser::parse_source(src)
            .expect("should parse function body with optional trailing semicolon");
        let Decl::Function(function) = &parsed.declarations[0] else {
            panic!("expected function declaration")
        };
        assert!(matches!(u(&function.body), Expr::Block(items) if items.len() == 2));
    }

    #[test]
    fn parse_function_body_with_local_let_binding() {
        let src = "def main() -> Void { let exit_code = 0; syscall_exit(exit_code) }";
        let parsed = Parser::parse_source(src).expect("should parse local let binding");
        let Decl::Function(function) = &parsed.declarations[0] else {
            panic!("expected function declaration")
        };
        let Expr::Block(items) = u(&function.body) else {
            panic!("expected block body")
        };
        assert_eq!(items.len(), 2);
        assert!(matches!(
            u(&items[0]),
            Expr::MacroApply { macro_name, operand, .. }
                if macro_name == "let"
                    && matches!(
                        u(operand.as_ref()),
                        Expr::Bindings(bindings)
                            if bindings.len() == 1
                                && matches!(bindings[0].pattern, Pattern::Ident(ref name) if name == "exit_code")
                                && matches!(u(&bindings[0].value), Expr::Int(ref v) if v == "0")
                    )
        ));
    }

    #[test]
    fn parse_local_def_binding_in_block() {
        let src = "def main() -> Int { def x = 1; x }";
        let parsed = Parser::parse_source(src).expect("should parse local def binding");
        let Decl::Function(function) = &parsed.declarations[0] else {
            panic!("expected function declaration")
        };
        let Expr::Block(items) = u(&function.body) else {
            panic!("expected block body")
        };
        assert_eq!(items.len(), 2);
        assert!(matches!(
            u(&items[0]),
            Expr::MacroApply { macro_name, .. } if macro_name == "def"
        ));
    }

    #[test]
    fn parse_assignment_expression_is_right_associative_and_low_precedence() {
        let src = "def main() -> Int { let x = 0; let y = 0; x = y = 1 + 2; x }";
        let parsed = Parser::parse_source(src).expect("should parse assignment expression");
        let Decl::Function(function) = &parsed.declarations[0] else {
            panic!("expected function declaration")
        };
        let Expr::Block(items) = u(&function.body) else {
            panic!("expected block body")
        };
        assert!(matches!(
            u(&items[2]),
            Expr::Assign { name, value }
                if name == "x"
                    && matches!(
                        u(value.as_ref()),
                        Expr::Assign { name, value }
                            if name == "y"
                                && matches!(
                                    u(value.as_ref()),
                                    Expr::Binary { op: BinaryOp::Add, .. }
                                )
                    )
        ));
    }

    #[test]
    fn parse_comma_chained_bindings_for_local_let() {
        let src = "def main() -> Int { let a = 1, b = 2, c = a + b; c }";
        let parsed = Parser::parse_source(src).expect("should parse chained local bindings");
        let Decl::Function(function) = &parsed.declarations[0] else {
            panic!("expected function declaration")
        };
        let Expr::Block(items) = u(&function.body) else {
            panic!("expected block body")
        };
        assert!(matches!(
            u(&items[0]),
            Expr::MacroApply { macro_name, operand, .. }
                if macro_name == "let"
                    && matches!(u(operand.as_ref()), Expr::Bindings(bindings) if bindings.len() == 3)
        ));
    }

    #[test]
    fn parse_collection_item_sequences_are_scoped_per_comma() {
        let src = "def xs = [let x = 0; x = x + 1; x, 42]";
        let parsed =
            Parser::parse_source(src).expect("should parse collection item scoped sequences");
        let Decl::Assign { value, .. } = &parsed.declarations[0] else {
            panic!("expected assignment declaration")
        };
        let Expr::List(items) = u(value) else {
            panic!("expected list literal")
        };
        assert_eq!(items.len(), 2);
        let Expr::Block(first_item) = u(&items[0]) else {
            panic!("expected scoped block for first list item")
        };
        assert_eq!(first_item.len(), 3);
        assert!(matches!(
            u(&first_item[0]),
            Expr::MacroApply { macro_name, .. } if macro_name == "let"
        ));
        assert!(matches!(u(&first_item[1]), Expr::Assign { name, .. } if name == "x"));
        assert!(matches!(u(&first_item[2]), Expr::Ident(name) if name == "x"));
        assert!(matches!(u(&items[1]), Expr::Int(value) if value == "42"));
    }

    #[test]
    fn parse_macro_name_node() {
        let src = "def x = macro_name node";
        let parsed = Parser::parse_source(src).expect("should parse macro application");
        let decl = parsed.declarations.first().expect("expected declaration");
        let value = match decl {
            Decl::Assign { value, .. } => value,
            other => panic!("expected assignment declaration, got {other:?}"),
        };

        let Expr::MacroApply {
            macro_name,
            static_args,
            operand,
        } = u(value)
        else {
            panic!("expected macro application")
        };

        assert_eq!(macro_name, "macro_name");
        assert!(static_args.is_empty());
        assert!(matches!(u(operand.as_ref()), Expr::Ident(name) if name == "node"));
    }

    #[test]
    fn parse_macro_name_with_static_args_node() {
        let src = "def x = macro_name[T, 4] node";
        let parsed = Parser::parse_source(src).expect("should parse macro application with args");
        let decl = parsed.declarations.first().expect("expected declaration");
        let value = match decl {
            Decl::Assign { value, .. } => value,
            other => panic!("expected assignment declaration, got {other:?}"),
        };

        let Expr::MacroApply { static_args, .. } = u(value) else {
            panic!("expected macro application")
        };

        assert_eq!(static_args.len(), 2);
        assert!(matches!(static_args[0], StaticArg::Type(_)));
        assert!(matches!(static_args[1], StaticArg::Value(_)));
    }

    #[test]
    fn parse_macro_application_is_right_associative() {
        let src = "def x = a b node";
        let parsed = Parser::parse_source(src).expect("should parse chained macro applications");
        let decl = parsed.declarations.first().expect("expected declaration");
        let value = match decl {
            Decl::Assign { value, .. } => value,
            other => panic!("expected assignment declaration, got {other:?}"),
        };

        let Expr::MacroApply {
            macro_name,
            operand,
            ..
        } = u(value)
        else {
            panic!("expected outer macro apply")
        };
        assert_eq!(macro_name, "a");

        let Expr::MacroApply {
            macro_name,
            operand,
            ..
        } = u(operand.as_ref())
        else {
            panic!("expected inner macro apply")
        };
        assert_eq!(macro_name, "b");
        assert!(matches!(u(operand.as_ref()), Expr::Ident(name) if name == "node"));
    }

    #[test]
    fn parse_assignment_to_plain_atom_expression() {
        let src = "def x = node";
        let parsed = Parser::parse_source(src).expect("should parse plain atom assignment");
        let decl = parsed.declarations.first().expect("expected declaration");
        let value = match decl {
            Decl::Assign { value, .. } => value,
            other => panic!("expected assignment declaration, got {other:?}"),
        };

        assert!(matches!(u(value), Expr::Ident(name) if name == "node"));
    }

    #[test]
    fn parse_assignment_to_integer_atom_expression() {
        let src = "def x = 7";
        let parsed = Parser::parse_source(src).expect("should parse integer assignment");
        let decl = parsed.declarations.first().expect("expected declaration");
        let value = match decl {
            Decl::Assign { value, .. } => value,
            other => panic!("expected assignment declaration, got {other:?}"),
        };

        assert!(matches!(u(value), Expr::Int(v) if v == "7"));
    }

    #[test]
    fn parse_float_char_string_dot_ident_and_payload() {
        let src = "def a = 3.14; def b = \"hi\"; def c = 'x'; def d = .ok; def e = .ok(value)";
        let parsed = Parser::parse_source(src).expect("should parse literals and dot-ident");
        assert_eq!(parsed.declarations.len(), 5);

        let expr = match &parsed.declarations[0] {
            Decl::Assign { value, .. } => value,
            _ => panic!("expected assignment"),
        };
        assert!(matches!(u(expr), Expr::Float(v) if v == "3.14"));

        let expr = match &parsed.declarations[1] {
            Decl::Assign { value, .. } => value,
            _ => panic!("expected assignment"),
        };
        assert!(matches!(u(expr), Expr::String(v) if v == "hi"));

        let expr = match &parsed.declarations[2] {
            Decl::Assign { value, .. } => value,
            _ => panic!("expected assignment"),
        };
        assert!(matches!(u(expr), Expr::Char(v) if v == "x"));

        let expr = match &parsed.declarations[3] {
            Decl::Assign { value, .. } => value,
            _ => panic!("expected assignment"),
        };
        assert!(matches!(
            u(expr),
            Expr::DotIdent {
                name,
                payload: None
            } if name == "ok"
        ));

        let expr = match &parsed.declarations[4] {
            Decl::Assign { value, .. } => value,
            _ => panic!("expected assignment"),
        };
        assert!(matches!(
            u(expr),
            Expr::DotIdent {
                name,
                payload: Some(_)
            } if name == "ok"
        ));
    }

    #[test]
    fn parse_list_and_dict_literals() {
        let src = "def a = [1, 2, 3]; def b = [\"a\" = 1, \"b\" = 2]";
        let parsed = Parser::parse_source(src).expect("should parse list and dict");
        assert_eq!(parsed.declarations.len(), 2);

        let list = match &parsed.declarations[0] {
            Decl::Assign { value, .. } => value,
            _ => panic!("expected assignment"),
        };
        assert!(matches!(u(list), Expr::List(items) if items.len() == 3));

        let dict = match &parsed.declarations[1] {
            Decl::Assign { value, .. } => value,
            _ => panic!("expected assignment"),
        };
        assert!(matches!(u(dict), Expr::Dict(entries) if entries.len() == 2));
    }

    #[test]
    fn parse_tuple_and_struct_literals() {
        let src = "def pair = (4, .false); def person = (name = \"John Doe\", age = 30)";
        let parsed = Parser::parse_source(src).expect("should parse tuple and struct literals");
        assert_eq!(parsed.declarations.len(), 2);

        let tuple = match &parsed.declarations[0] {
            Decl::Assign { value, .. } => value,
            _ => panic!("expected assignment"),
        };
        assert!(matches!(u(tuple), Expr::Tuple(items) if items.len() == 2));

        let strukt = match &parsed.declarations[1] {
            Decl::Assign { value, .. } => value,
            _ => panic!("expected assignment"),
        };
        assert!(matches!(u(strukt), Expr::Struct(fields) if fields.len() == 2));
    }

    #[test]
    fn parse_def_with_type_annotation_and_named_sum_type_syntax() {
        let src =
            "def n: union(Int, Float) = 4; def res: enum(err: String, ok: Int) = .err(\"Failed\")";
        let parsed = Parser::parse_source(src).expect("should parse typed defs with union/enum");
        assert_eq!(parsed.declarations.len(), 2);

        let n = match &parsed.declarations[0] {
            Decl::Assign { value, .. } => value,
            _ => panic!("expected assignment"),
        };
        assert!(matches!(
            u(n),
            Expr::Binary {
                op: crate::ast::BinaryOp::Colon,
                rhs,
                ..
            } if matches!(u(rhs.as_ref()), Expr::TypeExpr(TypeExpr::Named { name, .. }) if name == "union")
        ));

        let res = match &parsed.declarations[1] {
            Decl::Assign { value, .. } => value,
            _ => panic!("expected assignment"),
        };
        assert!(matches!(
            u(res),
            Expr::Binary {
                op: crate::ast::BinaryOp::Colon,
                rhs,
                ..
            } if matches!(u(rhs.as_ref()), Expr::TypeExpr(TypeExpr::Named { name, .. }) if name == "enum")
        ));
    }

    #[test]
    fn parse_type_alias_defs_for_tuple_struct_union_enum() {
        let src = "def Coords = (Int, Int); def Person = (name: String, age: Int); def Number = union(Int, Float); def[T, E] Result = enum(err: E, ok: T)";
        let parsed = Parser::parse_source(src).expect("should parse type alias defs");
        assert_eq!(parsed.declarations.len(), 4);

        let coords = match &parsed.declarations[0] {
            Decl::Assign { value, .. } => value,
            _ => panic!("expected assignment"),
        };
        assert!(matches!(u(coords), Expr::TypeExpr(TypeExpr::Tuple(items)) if items.len() == 2));

        let person = match &parsed.declarations[1] {
            Decl::Assign { value, .. } => value,
            _ => panic!("expected assignment"),
        };
        assert!(matches!(u(person), Expr::TypeExpr(TypeExpr::Struct(fields)) if fields.len() == 2));
    }

    #[test]
    fn parse_namespace_use_decl() {
        let src = "use io = \"@stl/io\"";
        let parsed = Parser::parse_source(src).expect("should parse namespace use");
        assert_eq!(parsed.declarations.len(), 1);
        assert!(matches!(
            &parsed.declarations[0],
            Decl::Use(UseDecl {
                binding: UseBinding::Namespace(alias),
                source,
            }) if alias == "io" && source == "@stl/io"
        ));
    }

    #[test]
    fn parse_destructured_use_decl() {
        let src = "use (print, read) = \"@stl/io\"";
        let parsed = Parser::parse_source(src).expect("should parse destructured use");
        assert!(matches!(
            &parsed.declarations[0],
            Decl::Use(UseDecl {
                binding: UseBinding::Fields(fields),
                source,
            }) if source == "@stl/io"
                && fields.len() == 2
                && fields[0].source_name == "print"
                && fields[0].local_name == "print"
                && fields[1].source_name == "read"
                && fields[1].local_name == "read"
        ));
    }

    #[test]
    fn parse_renamed_use_decl() {
        let src = "use (my_print = print, read) = \"@stl/io\"";
        let parsed = Parser::parse_source(src).expect("should parse renamed use");
        assert!(matches!(
            &parsed.declarations[0],
            Decl::Use(UseDecl {
                binding: UseBinding::Fields(fields),
                source,
            }) if source == "@stl/io"
                && fields.len() == 2
                && fields[0].source_name == "print"
                && fields[0].local_name == "my_print"
                && fields[1].source_name == "read"
                && fields[1].local_name == "read"
        ));
    }

    #[test]
    fn parse_reinforcement_no_special_cases() {
        let src = "def a = def value; def b = let value; def c = if cond; def d = cases cond; def e = loop body; def f = return value; def g = break value; def h = continue value; use io = \"./io\"; def i = builtin foo; def j = label[.outer] { value }";
        let parsed = Parser::parse_source(src).expect("should parse mundane macro forms");
        assert_eq!(parsed.declarations.len(), 11);
        assert!(matches!(parsed.declarations[8], Decl::Use(_)));
        let last = match &parsed.declarations[10] {
            Decl::Assign { value, .. } => value,
            _ => panic!("expected assignment"),
        };
        assert!(matches!(u(last), Expr::Label { label, .. } if label == "outer"));
    }

    #[test]
    fn malformed_static_arg_list_is_rejected() {
        let src = "defmacro[T,,] m(node: Expr[T]) -> Expr[T] { node }";
        let err = Parser::parse_source(src).expect_err("should reject malformed static arg list");
        assert!(!err.message.is_empty());
        assert!(err.message.contains("found:"));
    }

    #[test]
    fn missing_macro_operand_is_rejected() {
        let src = "def x = macro_name[T]";
        let err = Parser::parse_source(src).expect_err("should reject missing macro operand");
        assert!(
            err.message.contains("expected '(' or labeled closure")
                || err.message.contains("missing operand")
        );
        assert!(err.hint.is_some());
    }

    #[test]
    fn invalid_macro_declaration_header_is_rejected() {
        let src = "defmacro m node -> Expr[T] { node }";
        let err =
            Parser::parse_source(src).expect_err("should reject invalid macro declaration header");
        assert!(!err.message.is_empty());
        assert!(err.span.expect("span should exist").line >= 1);
    }

    #[test]
    fn parse_static_type_expr_in_return_type() {
        let src = "defmacro[T] m(node: Expr[T]) -> static Expr[T] { node }";
        let parsed = Parser::parse_source(src).expect("should parse static return type");
        let decl = parsed.declarations.first().expect("expected declaration");

        let Decl::Macro(macro_decl) = decl else {
            panic!("expected macro declaration")
        };

        assert!(matches!(macro_decl.return_type, TypeExpr::Static(_)));
    }

    #[test]
    fn parse_static_type_expr_inside_type_args() {
        let src = "defmacro[T] m(node: Expr[static Int]) -> Expr[T] { node }";
        let parsed = Parser::parse_source(src).expect("should parse static in type args");
        let decl = parsed.declarations.first().expect("expected declaration");
        let Decl::Macro(macro_decl) = decl else {
            panic!("expected macro declaration")
        };

        let first_param = macro_decl.params.first().expect("expected one parameter");
        let TypeExpr::Named { args, .. } = &first_param.ty else {
            panic!("expected named type for parameter")
        };

        assert!(matches!(
            args.first(),
            Some(StaticArg::Type(TypeExpr::Static(_)))
        ));
    }

    #[test]
    fn dangling_static_type_expr_is_rejected() {
        let src = "defmacro[T] m(node: Expr[T]) -> static { node }";
        let err = Parser::parse_source(src).expect_err("should reject dangling static");
        assert!(!err.message.is_empty());
    }

    #[test]
    fn doc_attribute_attaches_to_function_and_params() {
        let src = "doc[\"# do_thing\\n\\nDoes thing\\n\\n## Arguments\\n\\n- arg: Int - purpose\\n- arg2: String - something else\\n\\n## Returns\\n\\nA boolean\\n\"] def do_thing(arg: Int, arg2: String) -> Bool { true }";
        let parsed = Parser::parse_source(src).expect("should parse documented function");
        let decl = parsed.declarations.first().expect("expected declaration");
        let Decl::Function(function) = decl else {
            panic!("expected function declaration")
        };
        let doc = function.doc.as_ref().expect("expected doc attached");
        assert!(doc.markdown.contains("# do_thing"));
        assert!(doc.symbol_docs.iter().any(|d| d.name == "do_thing"));
        assert!(doc.symbol_docs.iter().any(|d| d.name == "arg"));
        assert!(doc.symbol_docs.iter().any(|d| d.name == "arg2"));
    }

    #[test]
    fn doc_attribute_attaches_to_assignment() {
        let src = "doc[\"# answer\\n\\nThe answer\\n\"] def answer = 42";
        let parsed = Parser::parse_source(src).expect("should parse documented assignment");
        let decl = parsed.declarations.first().expect("expected declaration");
        let Decl::Assign { doc, .. } = decl else {
            panic!("expected assignment declaration")
        };
        assert!(doc.is_some());
    }

    #[test]
    fn doc_attribute_only_allows_def_target() {
        let src = "doc[\"# io\"] use io = \"./io\"";
        let err = Parser::parse_source(src).expect_err("doc should only annotate def");
        assert!(err.message.contains("doc attribute"));
    }

    #[test]
    fn lexer_diagnostics_are_precise_for_unterminated_string() {
        let src = "def x = \"hello";
        let err = Parser::parse_source(src).expect_err("should reject unterminated string");
        assert!(err.message.contains("unterminated string"));
        assert_eq!(err.span.expect("span should exist").line, 1);
    }
}
