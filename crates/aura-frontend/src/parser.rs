use crate::ast::Program;
use crate::lexer::lex;

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
        let _tokens = lex(source).map_err(|err| ParseError::new(err.message))?;
        Err(ParseError::new("parser implementation pending"))
    }
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
