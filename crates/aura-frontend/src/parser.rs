use crate::ast::{
    Decl, Expr, MacroDecl, Param, Program, StaticArg, StaticParam, StaticParamKind,
    StaticValueExpr, TypeExpr,
};
use crate::lexer::lex;
use crate::static_eval::{MinimalStaticChecker, StaticSatisfies};
use crate::token::{Token, TokenKind};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ParseError {
    pub message: String,
}

impl ParseError {
    fn new(message: impl Into<String>) -> Self {
        Self {
            message: message.into(),
        }
    }
}

pub struct Parser;

impl Parser {
    pub fn parse_source(source: &str) -> Result<Program, ParseError> {
        let tokens = lex(source).map_err(|err| ParseError::new(err.message))?;
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
            declarations.push(self.parse_decl()?);
        }
        Ok(Program { declarations })
    }

    fn parse_decl(&mut self) -> Result<Decl, ParseError> {
        if self.peek_is(&TokenKind::Defmacro) {
            return self.parse_macro_decl();
        }

        let name = self.expect_ident("expected declaration name")?;

        if self.peek_is(&TokenKind::LParen) {
            let params = self.parse_params()?;
            self.expect_simple(&TokenKind::Arrow, "expected '->' in function declaration")?;
            let return_type = self.parse_type_expr()?;
            self.expect_simple(&TokenKind::LBrace, "expected '{' for function body")?;
            self.expect_simple(&TokenKind::RBrace, "expected '}' for function body")?;
            return Ok(Decl::Assign {
                name,
                value: Expr::Closure {
                    params,
                    return_type: Some(return_type),
                },
            });
        }

        self.expect_simple(&TokenKind::Eq, "expected '=' in assignment declaration")?;
        let value = self.parse_macro_apply_expr()?;
        Ok(Decl::Assign { name, value })
    }

    fn parse_macro_decl(&mut self) -> Result<Decl, ParseError> {
        self.expect_simple(&TokenKind::Defmacro, "expected 'defmacro'")?;
        let static_params = if self.peek_is(&TokenKind::LBracket) {
            self.parse_static_params()?
        } else {
            Vec::new()
        };

        let name = self.expect_ident("expected macro name")?;
        let params = self.parse_params()?;
        self.expect_simple(&TokenKind::Arrow, "expected '->' in macro declaration")?;
        let return_type = self.parse_type_expr()?;
        self.expect_simple(&TokenKind::LBrace, "expected '{' for macro body")?;
        self.expect_simple(&TokenKind::RBrace, "expected '}' for macro body")?;

        Ok(Decl::Macro(MacroDecl {
            name,
            static_params,
            params,
            return_type,
        }))
    }

    fn parse_static_params(&mut self) -> Result<Vec<StaticParam>, ParseError> {
        self.expect_simple(&TokenKind::LBracket, "expected '['")?;
        if self.peek_is(&TokenKind::RBracket) {
            self.bump();
            return Ok(Vec::new());
        }

        let mut params = Vec::new();
        loop {
            let name = self.expect_ident("expected static parameter name")?;
            let kind = if self.peek_is(&TokenKind::Colon) {
                self.bump();
                self.expect_simple(&TokenKind::Static, "expected 'static' after ':'")?;
                let ty = self.parse_type_expr()?;
                StaticParamKind::StaticValue(ty)
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
                    return Err(ParseError::new("malformed static parameter list"));
                }
                continue;
            }

            self.expect_simple(&TokenKind::RBracket, "expected ']' after static parameters")?;
            break;
        }

        Ok(params)
    }

    fn parse_params(&mut self) -> Result<Vec<Param>, ParseError> {
        self.expect_simple(&TokenKind::LParen, "expected '('")?;
        if self.peek_is(&TokenKind::RParen) {
            self.bump();
            return Ok(Vec::new());
        }

        let mut params = Vec::new();
        loop {
            let name = self.expect_ident("expected parameter name")?;
            self.expect_simple(&TokenKind::Colon, "expected ':' after parameter name")?;
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

            self.expect_simple(&TokenKind::RParen, "expected ')' after parameters")?;
            break;
        }

        Ok(params)
    }

    fn parse_type_expr(&mut self) -> Result<TypeExpr, ParseError> {
        let name = self.expect_ident("expected type identifier")?;
        let args = if self.peek_is(&TokenKind::LBracket) {
            self.parse_static_args()?
        } else {
            Vec::new()
        };

        Ok(TypeExpr { name, args })
    }

    fn parse_static_args(&mut self) -> Result<Vec<StaticArg>, ParseError> {
        self.expect_simple(&TokenKind::LBracket, "expected '['")?;
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
                    return Err(ParseError::new("malformed static argument list"));
                }
                continue;
            }

            self.expect_simple(&TokenKind::RBracket, "expected ']' after static arguments")?;
            break;
        }

        Ok(args)
    }

    fn parse_static_arg(&mut self) -> Result<StaticArg, ParseError> {
        match self.peek() {
            TokenKind::Int(raw) => {
                let parsed = raw
                    .parse::<i64>()
                    .map_err(|_| ParseError::new("invalid integer in static argument"))?;
                self.bump();
                let value = StaticValueExpr::Int(parsed);
                if !self.static_checker.is_compile_time_known(&value) {
                    return Err(ParseError::new("static value is not compile-time known"));
                }
                Ok(StaticArg::Value(value))
            }
            TokenKind::Ident(name) => {
                if name
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
                        return Err(ParseError::new("static value is not compile-time known"));
                    }
                    Ok(StaticArg::Value(value))
                }
            }
            _ => Err(ParseError::new("expected static argument")),
        }
    }

    fn parse_macro_apply_expr(&mut self) -> Result<Expr, ParseError> {
        let head_name = self.expect_ident("expected macro name")?;
        let static_args = if self.peek_is(&TokenKind::LBracket) {
            self.parse_static_args()?
        } else {
            Vec::new()
        };

        if !self.starts_operand() {
            return Err(ParseError::new("macro application missing operand"));
        }

        let operand = self.parse_macro_operand()?;
        Ok(Expr::MacroApply {
            macro_name: head_name,
            static_args,
            operand: Box::new(operand),
        })
    }

    fn parse_macro_operand(&mut self) -> Result<Expr, ParseError> {
        let expr = if self.starts_macro_head() {
            self.parse_macro_apply_expr()?
        } else {
            self.parse_atom_expr()?
        };
        Ok(expr)
    }

    fn parse_atom_expr(&mut self) -> Result<Expr, ParseError> {
        match self.peek() {
            TokenKind::Ident(name) => {
                let name = name.clone();
                self.bump();
                Ok(Expr::Ident(name))
            }
            TokenKind::Int(raw) => {
                let value = raw
                    .parse::<i64>()
                    .map_err(|_| ParseError::new("invalid integer literal"))?;
                self.bump();
                Ok(Expr::Int(value))
            }
            _ => Err(ParseError::new("expected expression operand")),
        }
    }

    fn starts_macro_head(&self) -> bool {
        matches!(self.peek(), TokenKind::Ident(_))
            && matches!(
                self.peek_n(1),
                Some(TokenKind::Ident(_)) | Some(TokenKind::Int(_)) | Some(TokenKind::LBracket)
            )
    }

    fn starts_operand(&self) -> bool {
        matches!(self.peek(), TokenKind::Ident(_) | TokenKind::Int(_))
    }

    fn expect_ident(&mut self, message: &str) -> Result<String, ParseError> {
        match self.peek() {
            TokenKind::Ident(name) => {
                let name = name.clone();
                self.bump();
                Ok(name)
            }
            _ => Err(ParseError::new(message)),
        }
    }

    fn expect_simple(&mut self, expected: &TokenKind, message: &str) -> Result<(), ParseError> {
        if self.peek_is(expected) {
            self.bump();
            return Ok(());
        }
        Err(ParseError::new(message))
    }

    fn peek_is(&self, expected: &TokenKind) -> bool {
        same_token_variant(self.peek(), expected)
    }

    fn peek(&self) -> &TokenKind {
        &self.tokens[self.cursor].kind
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

fn same_token_variant(left: &TokenKind, right: &TokenKind) -> bool {
    matches!(
        (left, right),
        (TokenKind::Static, TokenKind::Static)
            | (TokenKind::Defmacro, TokenKind::Defmacro)
            | (TokenKind::Arrow, TokenKind::Arrow)
            | (TokenKind::Colon, TokenKind::Colon)
            | (TokenKind::Comma, TokenKind::Comma)
            | (TokenKind::Dot, TokenKind::Dot)
            | (TokenKind::Eq, TokenKind::Eq)
            | (TokenKind::LParen, TokenKind::LParen)
            | (TokenKind::RParen, TokenKind::RParen)
            | (TokenKind::LBrace, TokenKind::LBrace)
            | (TokenKind::RBrace, TokenKind::RBrace)
            | (TokenKind::LBracket, TokenKind::LBracket)
            | (TokenKind::RBracket, TokenKind::RBracket)
            | (TokenKind::Eof, TokenKind::Eof)
            | (TokenKind::Ident(_), TokenKind::Ident(_))
            | (TokenKind::Int(_), TokenKind::Int(_))
    )
}

#[cfg(test)]
mod tests {
    use crate::ast::{Decl, Expr, StaticArg, StaticParamKind};
    use crate::parser::Parser;

    #[test]
    fn parse_defmacro_with_static_params_contract() {
        let src = "defmacro[T, n: static Int] m(node: Expr[T]) -> Expr[T] {}";
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
            StaticParamKind::StaticValue(_)
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
    fn function_form_declaration_normalizes_to_assignment_shape() {
        let src = "name(arg: Int) -> Expr[Int] {}";
        let parsed = Parser::parse_source(src).expect("should parse function form declaration");
        let decl = parsed.declarations.first().expect("expected declaration");

        match decl {
            Decl::Assign { name, value } => {
                assert_eq!(name, "name");
                assert!(matches!(value, Expr::Closure { .. }));
            }
            other => panic!("expected normalized assignment declaration, got {other:?}"),
        }
    }

    #[test]
    fn malformed_static_arg_list_is_rejected() {
        let src = "defmacro[T,,] m(node: Expr[T]) -> Expr[T] {}";
        let err = Parser::parse_source(src).expect_err("should reject malformed static arg list");
        assert!(!err.message.is_empty());
    }

    #[test]
    fn missing_macro_operand_is_rejected() {
        let src = "x = macro_name";
        let err = Parser::parse_source(src).expect_err("should reject missing macro operand");
        assert!(!err.message.is_empty());
    }

    #[test]
    fn invalid_macro_declaration_header_is_rejected() {
        let src = "defmacro m node -> Expr[T] {}";
        let err =
            Parser::parse_source(src).expect_err("should reject invalid macro declaration header");
        assert!(!err.message.is_empty());
    }
}
