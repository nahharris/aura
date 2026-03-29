use crate::ast::{
    Arm, Decl, Expr, FunctionDecl, MacroDecl, Param, Pattern, Program, StaticArg, StaticParam,
    StaticParamKind, StaticValueExpr, TypeExpr, UseDecl,
};
use crate::lexer::{lex, LexError};
use crate::static_eval::{MinimalStaticChecker, StaticSatisfies};
use crate::token::{Span, Token, TokenKind};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParseError {
    pub message: Box<str>,
    pub span: Span,
    pub expected: Box<[&'static str]>,
    pub found: Box<str>,
    pub hint: Option<Box<str>>,
}

impl ParseError {
    fn new(
        message: impl Into<String>,
        span: Span,
        expected: Vec<&'static str>,
        found: String,
        hint: Option<String>,
    ) -> Self {
        Self {
            message: message.into().into_boxed_str(),
            span,
            expected: expected.into_boxed_slice(),
            found: found.into_boxed_str(),
            hint: hint.map(String::into_boxed_str),
        }
    }
}

impl From<LexError> for ParseError {
    fn from(value: LexError) -> Self {
        Self {
            message: value.message.into_boxed_str(),
            span: value.span,
            expected: Vec::new().into_boxed_slice(),
            found: "lexer".to_string().into_boxed_str(),
            hint: None,
        }
    }
}

pub struct Parser;

impl Parser {
    pub fn parse_source(source: &str) -> Result<Program, ParseError> {
        let tokens = lex(source)?;
        let mut inner = InnerParser {
            tokens,
            cursor: 0,
            static_checker: MinimalStaticChecker,
        };
        inner.parse_program()
    }
}

struct InnerParser<C> {
    tokens: Vec<Token>,
    cursor: usize,
    static_checker: C,
}

impl<C> InnerParser<C>
where
    C: StaticSatisfies,
{
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
        if self.peek_is(&TokenKind::Defmacro) {
            return self.parse_macro_decl();
        }

        if self.peek_ident_is("use") {
            return self.parse_use_decl();
        }

        if self.peek_ident_is("def") && self.looks_like_function_decl() {
            return self.parse_function_decl();
        }

        let name = self.expect_ident("expected declaration name")?;
        self.expect_simple(
            &TokenKind::Eq,
            "expected '=' in assignment declaration",
            vec!["="],
        )?;
        let value = self.parse_expr()?;
        Ok(Decl::Assign { name, value })
    }

    fn parse_use_decl(&mut self) -> Result<Decl, ParseError> {
        self.expect_ident_exact("use")?;
        let target = self.expect_ident("expected use target")?;
        Ok(Decl::Use(UseDecl { target }))
    }

    fn parse_function_decl(&mut self) -> Result<Decl, ParseError> {
        self.expect_ident_exact("def")?;

        let static_params = if self.peek_is(&TokenKind::LBracket) {
            self.parse_generic_ident_list()?
        } else {
            Vec::new()
        };

        let head_ty = self.parse_type_expr()?;
        self.expect_simple(
            &TokenKind::Dot,
            "expected '.' before method name",
            vec!["."],
        )?;
        let name = self.expect_ident("expected method name")?;
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
            receiver: Some(head_ty),
            name,
            params,
            return_type,
            body,
        }))
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

        let mut saw_dot = false;
        while let Some(tok) = self.peek_n(i - self.cursor) {
            match tok {
                TokenKind::Dot => {
                    saw_dot = true;
                    i += 1;
                }
                TokenKind::LParen => return saw_dot,
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
            return Ok(Expr::List(Vec::new()));
        }

        let is_multi_arm = self.is_multi_arm_body();
        if is_multi_arm {
            let mut arms = Vec::new();
            loop {
                let pattern = self.parse_pattern()?;
                self.expect_simple(&TokenKind::Arrow, "expected '->' in arm", vec!["->"])?;
                let body = self.parse_expr()?;
                arms.push(Arm {
                    patterns: vec![pattern],
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
            let expr = self.parse_expr()?;
            self.expect_simple(
                &TokenKind::RBrace,
                "expected '}' after block body",
                vec!["}"],
            )?;
            Ok(expr)
        }
    }

    fn is_multi_arm_body(&self) -> bool {
        let mut i = self.cursor;
        while i < self.tokens.len() {
            match &self.tokens[i].kind {
                TokenKind::Arrow => return true,
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

    fn parse_generic_ident_list(&mut self) -> Result<Vec<String>, ParseError> {
        self.expect_simple(&TokenKind::LBracket, "expected '['", vec!["["])?;
        let mut values = Vec::new();
        if self.peek_is(&TokenKind::RBracket) {
            self.bump();
            return Ok(values);
        }
        loop {
            values.push(self.expect_ident("expected identifier in generic parameter list")?);
            if self.peek_is(&TokenKind::Comma) {
                self.bump();
                if self.peek_is(&TokenKind::RBracket) {
                    self.bump();
                    break;
                }
                continue;
            }
            self.expect_simple(&TokenKind::RBracket, "expected ']'", vec!["]"])?;
            break;
        }
        Ok(values)
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

        let name = self.expect_ident("expected type identifier")?;
        let args = if self.peek_is(&TokenKind::LBracket) {
            self.parse_static_args()?
        } else {
            Vec::new()
        };

        Ok(TypeExpr::Named { name, args })
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
            _ => Err(self.error_here(
                "expected static argument",
                vec!["type_expr", "int", "float", "string", "char", "identifier"],
                None,
            )),
        }
    }

    fn parse_expr(&mut self) -> Result<Expr, ParseError> {
        if self.peek_ident_is("label") {
            return self.parse_label_expr();
        }
        if self.is_macro_apply_start() {
            self.parse_macro_apply_expr()
        } else {
            self.parse_postfix_expr()
        }
    }

    fn parse_label_expr(&mut self) -> Result<Expr, ParseError> {
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
        Ok(Expr::Label {
            label,
            expr: Box::new(expr),
        })
    }

    fn parse_postfix_expr(&mut self) -> Result<Expr, ParseError> {
        let mut expr = self.parse_atom_expr()?;

        loop {
            if self.peek_is(&TokenKind::LBracket) {
                let static_args = self.parse_static_args()?;
                if self.peek_is(&TokenKind::LParen) {
                    let args = self.parse_call_args()?;
                    expr = Expr::Call {
                        callee: Box::new(expr),
                        static_args,
                        args,
                    };
                    continue;
                }
                return Err(self.error_here(
                    "expected '(' after static call arguments",
                    vec!["("],
                    Some("static args attach to call syntax like foo[T](x)".to_string()),
                ));
            }

            if self.peek_is(&TokenKind::LParen) {
                let args = self.parse_call_args()?;
                expr = Expr::Call {
                    callee: Box::new(expr),
                    static_args: Vec::new(),
                    args,
                };
                continue;
            }

            break;
        }

        Ok(expr)
    }

    fn parse_call_args(&mut self) -> Result<Vec<Expr>, ParseError> {
        self.expect_simple(&TokenKind::LParen, "expected '('", vec!["("])?;
        let mut args = Vec::new();
        if self.peek_is(&TokenKind::RParen) {
            self.bump();
            return Ok(args);
        }
        loop {
            args.push(self.parse_expr()?);
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
                Some("macro application uses the form 'macro_name[args] node'".to_string()),
            ));
        }

        let operand = self.parse_expr()?;
        Ok(Expr::MacroApply {
            macro_name: head_name,
            static_args,
            operand: Box::new(operand),
        })
    }

    fn parse_atom_expr(&mut self) -> Result<Expr, ParseError> {
        match self.peek() {
            TokenKind::Ident(name) => {
                let name = name.clone();
                self.bump();
                Ok(Expr::Ident(name))
            }
            TokenKind::Int(raw) => {
                let value = raw.clone();
                self.bump();
                Ok(Expr::Int(value))
            }
            TokenKind::Float(raw) => {
                let value = raw.clone();
                self.bump();
                Ok(Expr::Float(value))
            }
            TokenKind::String(raw) => {
                let value = raw.clone();
                self.bump();
                Ok(Expr::String(value))
            }
            TokenKind::Char(raw) => {
                let value = raw.clone();
                self.bump();
                Ok(Expr::Char(value))
            }
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
        Ok(Expr::DotIdent { name, payload })
    }

    fn parse_bracket_literal_expr(&mut self) -> Result<Expr, ParseError> {
        self.expect_simple(&TokenKind::LBracket, "expected '['", vec!["["])?;
        if self.peek_is(&TokenKind::RBracket) {
            self.bump();
            return Ok(Expr::List(Vec::new()));
        }

        let first = self.parse_expr()?;
        if self.peek_is(&TokenKind::Eq) {
            self.bump();
            let value = self.parse_expr()?;
            let mut entries = vec![(first, value)];
            while self.peek_is(&TokenKind::Comma) {
                self.bump();
                if self.peek_is(&TokenKind::RBracket) {
                    break;
                }
                let key = self.parse_expr()?;
                self.expect_simple(&TokenKind::Eq, "expected '=' in dict entry", vec!["="])?;
                let value = self.parse_expr()?;
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
            items.push(self.parse_expr()?);
        }
        self.expect_simple(
            &TokenKind::RBracket,
            "expected ']' after list literal",
            vec!["]"],
        )?;
        Ok(Expr::List(items))
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
        matches!(self.peek(), TokenKind::Ident(_))
            && matches!(
                self.peek_n(1),
                Some(TokenKind::Ident(_))
                    | Some(TokenKind::Int(_))
                    | Some(TokenKind::Float(_))
                    | Some(TokenKind::String(_))
                    | Some(TokenKind::Char(_))
                    | Some(TokenKind::Dot)
                    | Some(TokenKind::LBracket)
                    | Some(TokenKind::LBrace)
            )
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
        ParseError::new(
            message,
            self.peek_token().span,
            expected,
            token_debug_name(&self.peek_token().kind),
            hint,
        )
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

#[cfg(test)]
mod tests {
    use crate::ast::{Decl, Expr, Pattern, StaticArg, StaticParamKind, TypeExpr};
    use crate::parser::Parser;

    #[test]
    fn parse_complex_method_declaration_contract() {
        let src = "def[T, E, U] Result[T, E].map(self: Result[T, E], with: Func[T, U]) -> Result[U, E] { .ok(value) -> .ok(with(value)), err -> err }";
        let parsed = Parser::parse_source(src).expect("should parse complex method declaration");
        let decl = parsed.declarations.first().expect("expected declaration");

        let Decl::Function(function) = decl else {
            panic!("expected function declaration")
        };

        assert_eq!(function.static_params, vec!["T", "E", "U"]);
        assert_eq!(function.name, "map");
        assert_eq!(function.params.len(), 2);
        assert!(matches!(function.receiver, Some(TypeExpr::Named { .. })));
        assert!(matches!(function.return_type, TypeExpr::Named { .. }));

        let Expr::MultiArm(arms) = &function.body else {
            panic!("expected multi-arm body")
        };
        assert_eq!(arms.len(), 2);
        assert!(matches!(arms[0].patterns[0], Pattern::DotVariant { .. }));
        assert!(matches!(arms[1].patterns[0], Pattern::Ident(_)));
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
    fn parse_macro_name_node() {
        let src = "x = macro_name node";
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
        } = value
        else {
            panic!("expected macro application")
        };

        assert_eq!(macro_name, "macro_name");
        assert!(static_args.is_empty());
        assert!(matches!(operand.as_ref(), Expr::Ident(name) if name == "node"));
    }

    #[test]
    fn parse_macro_name_with_static_args_node() {
        let src = "x = macro_name[T, 4] node";
        let parsed = Parser::parse_source(src).expect("should parse macro application with args");
        let decl = parsed.declarations.first().expect("expected declaration");
        let value = match decl {
            Decl::Assign { value, .. } => value,
            other => panic!("expected assignment declaration, got {other:?}"),
        };

        let Expr::MacroApply { static_args, .. } = value else {
            panic!("expected macro application")
        };

        assert_eq!(static_args.len(), 2);
        assert!(matches!(static_args[0], StaticArg::Type(_)));
        assert!(matches!(static_args[1], StaticArg::Value(_)));
    }

    #[test]
    fn parse_macro_application_is_right_associative() {
        let src = "x = a b node";
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
        } = value
        else {
            panic!("expected outer macro apply")
        };
        assert_eq!(macro_name, "a");

        let Expr::MacroApply {
            macro_name,
            operand,
            ..
        } = operand.as_ref()
        else {
            panic!("expected inner macro apply")
        };
        assert_eq!(macro_name, "b");
        assert!(matches!(operand.as_ref(), Expr::Ident(name) if name == "node"));
    }

    #[test]
    fn parse_assignment_to_plain_atom_expression() {
        let src = "x = node";
        let parsed = Parser::parse_source(src).expect("should parse plain atom assignment");
        let decl = parsed.declarations.first().expect("expected declaration");
        let value = match decl {
            Decl::Assign { value, .. } => value,
            other => panic!("expected assignment declaration, got {other:?}"),
        };

        assert!(matches!(value, Expr::Ident(name) if name == "node"));
    }

    #[test]
    fn parse_assignment_to_integer_atom_expression() {
        let src = "x = 7";
        let parsed = Parser::parse_source(src).expect("should parse integer assignment");
        let decl = parsed.declarations.first().expect("expected declaration");
        let value = match decl {
            Decl::Assign { value, .. } => value,
            other => panic!("expected assignment declaration, got {other:?}"),
        };

        assert!(matches!(value, Expr::Int(v) if v == "7"));
    }

    #[test]
    fn parse_float_char_string_dot_ident_and_payload() {
        let src = "a = 3.14; b = \"hi\"; c = 'x'; d = .ok; e = .ok(value)";
        let parsed = Parser::parse_source(src).expect("should parse literals and dot-ident");
        assert_eq!(parsed.declarations.len(), 5);

        let expr = match &parsed.declarations[0] {
            Decl::Assign { value, .. } => value,
            _ => panic!("expected assignment"),
        };
        assert!(matches!(expr, Expr::Float(v) if v == "3.14"));

        let expr = match &parsed.declarations[1] {
            Decl::Assign { value, .. } => value,
            _ => panic!("expected assignment"),
        };
        assert!(matches!(expr, Expr::String(v) if v == "hi"));

        let expr = match &parsed.declarations[2] {
            Decl::Assign { value, .. } => value,
            _ => panic!("expected assignment"),
        };
        assert!(matches!(expr, Expr::Char(v) if v == "x"));

        let expr = match &parsed.declarations[3] {
            Decl::Assign { value, .. } => value,
            _ => panic!("expected assignment"),
        };
        assert!(matches!(
            expr,
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
            expr,
            Expr::DotIdent {
                name,
                payload: Some(_)
            } if name == "ok"
        ));
    }

    #[test]
    fn parse_list_and_dict_literals() {
        let src = "a = [1, 2, 3]; b = [\"a\" = 1, \"b\" = 2]";
        let parsed = Parser::parse_source(src).expect("should parse list and dict");
        assert_eq!(parsed.declarations.len(), 2);

        let list = match &parsed.declarations[0] {
            Decl::Assign { value, .. } => value,
            _ => panic!("expected assignment"),
        };
        assert!(matches!(list, Expr::List(items) if items.len() == 3));

        let dict = match &parsed.declarations[1] {
            Decl::Assign { value, .. } => value,
            _ => panic!("expected assignment"),
        };
        assert!(matches!(dict, Expr::Dict(entries) if entries.len() == 2));
    }

    #[test]
    fn parse_reinforcement_no_special_cases() {
        let src = "a = def value; b = let value; c = if cond; d = cases cond; e = loop body; f = return value; g = break value; h = continue value; use io; i = builtin foo; j = label[.outer] { value }";
        let parsed = Parser::parse_source(src).expect("should parse mundane macro forms");
        assert_eq!(parsed.declarations.len(), 11);
        assert!(matches!(parsed.declarations[8], Decl::Use(_)));
        let last = match &parsed.declarations[10] {
            Decl::Assign { value, .. } => value,
            _ => panic!("expected assignment"),
        };
        assert!(matches!(last, Expr::Label { label, .. } if label == "outer"));
    }

    #[test]
    fn malformed_static_arg_list_is_rejected() {
        let src = "defmacro[T,,] m(node: Expr[T]) -> Expr[T] { node }";
        let err = Parser::parse_source(src).expect_err("should reject malformed static arg list");
        assert!(!err.message.is_empty());
        assert!(!err.found.is_empty());
    }

    #[test]
    fn missing_macro_operand_is_rejected() {
        let src = "x = macro_name[T]";
        let err = Parser::parse_source(src).expect_err("should reject missing macro operand");
        assert!(err.message.contains("missing operand"));
        assert_eq!(err.expected.as_ref(), ["expression"]);
        assert!(err.hint.is_some());
    }

    #[test]
    fn invalid_macro_declaration_header_is_rejected() {
        let src = "defmacro m node -> Expr[T] { node }";
        let err =
            Parser::parse_source(src).expect_err("should reject invalid macro declaration header");
        assert!(!err.message.is_empty());
        assert!(err.span.line >= 1);
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
    fn lexer_diagnostics_are_precise_for_unterminated_string() {
        let src = "x = \"hello";
        let err = Parser::parse_source(src).expect_err("should reject unterminated string");
        assert!(err.message.contains("unterminated string"));
        assert_eq!(err.span.line, 1);
    }
}
