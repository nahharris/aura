use crate::type_ref::TypeRef;
use crate::typing_context::TypingContext;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Issue {
    LexAmpForm,
    LexBangForm,
    LexBlockCommentUnterminated,
    LexCharEscapeUnsupported {
        ch: char,
    },
    LexCharEscapeUnterminated,
    LexCharSize,
    LexCharUnterminated,
    LexFloatNoFraction,
    LexFloatNoIntPart,
    LexPipeForm,
    LexQuestionForm,
    LexStringEscapeUnsupported {
        ch: char,
    },
    LexStringEscapeUnterminated,
    LexStringUnterminated,
    LexUnexpectedChar {
        ch: char,
    },
    ParseUnexpectedToken {
        detail: String,
    },
    ArraySizeInvalid,
    ArraySizeKind,
    ArraySizeMissing,
    BuiltinForm,
    BuiltinUnknown,
    CallStaticArity,
    CallStaticUnexpected,
    CallStaticUnsupported,
    CasesEmpty,
    CasesForm,
    CastInvalid {
        source: TypeRef,
        target: TypeRef,
    },
    CastTarget,
    ClosureArity,
    IfArity,
    IfForm,
    InterfaceBoundUnsatisfied {
        detail: String,
    },
    MacroUntyped,
    OpNonNumeric,
    PatternEmptyArms,
    PatternNonExhaustive,
    PatternUnreachableArm,
    ResolveDuplicate,
    StaticArgKind {
        detail: String,
    },
    StaticArgMissing,
    TypeArgArity,
    TypeArgKind,
    TypeArgMissing,
    TypeMismatch {
        context: TypingContext,
        expected: TypeRef,
        actual: TypeRef,
    },
    UnifyMismatch,
    UnifyOccurs,
    UnifyUnknown,
    UnknownInterface,
    UseDuplicate,
    UnresolvedIdent {
        name: String,
    },
}

impl Issue {
    pub fn code(&self) -> &'static str {
        match self {
            Self::LexAmpForm => "E_LEX_AMP_FORM",
            Self::LexBangForm => "E_LEX_BANG_FORM",
            Self::LexBlockCommentUnterminated => "E_LEX_BLOCK_COMMENT_UNTERMINATED",
            Self::LexCharEscapeUnsupported { .. } => "E_LEX_CHAR_ESCAPE_UNSUPPORTED",
            Self::LexCharEscapeUnterminated => "E_LEX_CHAR_ESCAPE_UNTERMINATED",
            Self::LexCharSize => "E_LEX_CHAR_SIZE",
            Self::LexCharUnterminated => "E_LEX_CHAR_UNTERMINATED",
            Self::LexFloatNoFraction => "E_LEX_FLOAT_NO_FRACTION",
            Self::LexFloatNoIntPart => "E_LEX_FLOAT_NO_INT_PART",
            Self::LexPipeForm => "E_LEX_PIPE_FORM",
            Self::LexQuestionForm => "E_LEX_QUESTION_FORM",
            Self::LexStringEscapeUnsupported { .. } => "E_LEX_STRING_ESCAPE_UNSUPPORTED",
            Self::LexStringEscapeUnterminated => "E_LEX_STRING_ESCAPE_UNTERMINATED",
            Self::LexStringUnterminated => "E_LEX_STRING_UNTERMINATED",
            Self::LexUnexpectedChar { .. } => "E_LEX_UNEXPECTED_CHAR",
            Self::ParseUnexpectedToken { .. } => "E_PARSE_UNEXPECTED_TOKEN",
            Self::ArraySizeInvalid => "E_ARRAY_SIZE_INVALID",
            Self::ArraySizeKind => "E_ARRAY_SIZE_KIND",
            Self::ArraySizeMissing => "E_ARRAY_SIZE_MISSING",
            Self::BuiltinForm => "E_BUILTIN_FORM",
            Self::BuiltinUnknown => "E_BUILTIN_UNKNOWN",
            Self::CallStaticArity => "E_CALL_STATIC_ARITY",
            Self::CallStaticUnexpected => "E_CALL_STATIC_UNEXPECTED",
            Self::CallStaticUnsupported => "E_CALL_STATIC_UNSUPPORTED",
            Self::CasesEmpty => "E_CASES_EMPTY",
            Self::CasesForm => "E_CASES_FORM",
            Self::CastInvalid { .. } => "E_CAST_INVALID",
            Self::CastTarget => "E_CAST_TARGET",
            Self::ClosureArity => "E_CLOSURE_ARITY",
            Self::IfArity => "E_IF_ARITY",
            Self::IfForm => "E_IF_FORM",
            Self::InterfaceBoundUnsatisfied { .. } => "E_INTERFACE_BOUND_UNSAT",
            Self::MacroUntyped => "E_MACRO_UNTYPED",
            Self::OpNonNumeric => "E_OP_NON_NUMERIC",
            Self::PatternEmptyArms => "E_PATTERN_EMPTY_ARMS",
            Self::PatternNonExhaustive => "E_PATTERN_NON_EXHAUSTIVE",
            Self::PatternUnreachableArm => "E_PATTERN_UNREACHABLE_ARM",
            Self::ResolveDuplicate => "E_RESOLVE_DUP",
            Self::StaticArgKind { .. } => "E_STATIC_ARG_KIND",
            Self::StaticArgMissing => "E_STATIC_ARG_MISSING",
            Self::TypeArgArity => "E_TYPE_ARG_ARITY",
            Self::TypeArgKind => "E_TYPE_ARG_KIND",
            Self::TypeArgMissing => "E_TYPE_ARG_MISSING",
            Self::TypeMismatch { .. } => "E_TYPE_MISMATCH",
            Self::UnifyMismatch => "E_UNIFY_MISMATCH",
            Self::UnifyOccurs => "E_UNIFY_OCCURS",
            Self::UnifyUnknown => "E_UNIFY_UNKNOWN",
            Self::UnknownInterface => "E_UNKNOWN_INTERFACE",
            Self::UseDuplicate => "E_USE_DUPLICATE",
            Self::UnresolvedIdent { .. } => "W_UNRESOLVED_IDENT",
        }
    }

    pub fn message(&self) -> String {
        match self {
            Self::LexAmpForm => "unexpected '&': expected '&&'".to_string(),
            Self::LexBangForm => "unexpected '!': expected '!!' or '!='".to_string(),
            Self::LexBlockCommentUnterminated => "unterminated block comment".to_string(),
            Self::LexCharEscapeUnsupported { ch } => format!("unsupported char escape '\\{ch}'"),
            Self::LexCharEscapeUnterminated => {
                "unterminated escape sequence in character literal".to_string()
            }
            Self::LexCharSize => "character literal must contain exactly one character".to_string(),
            Self::LexCharUnterminated => "unterminated character literal".to_string(),
            Self::LexFloatNoFraction => {
                "float literal requires digits after decimal point".to_string()
            }
            Self::LexFloatNoIntPart => "float literal requires integer part before '.'".to_string(),
            Self::LexPipeForm => "unexpected '|': expected '||'".to_string(),
            Self::LexQuestionForm => "unexpected '?': expected '?:' or '?.'".to_string(),
            Self::LexStringEscapeUnsupported { ch } => {
                format!("unsupported string escape '\\{ch}'")
            }
            Self::LexStringEscapeUnterminated => {
                "unterminated escape sequence in string literal".to_string()
            }
            Self::LexStringUnterminated => "unterminated string literal".to_string(),
            Self::LexUnexpectedChar { ch } => format!("unexpected character '{ch}'"),
            Self::ParseUnexpectedToken { detail } => detail.clone(),
            Self::ArraySizeInvalid => {
                "array size must be a compile-time integer literal".to_string()
            }
            Self::ArraySizeKind => "array size static argument has incompatible kind".to_string(),
            Self::ArraySizeMissing => "array type requires a size static argument".to_string(),
            Self::BuiltinForm => "invalid builtin form".to_string(),
            Self::BuiltinUnknown => "unknown builtin".to_string(),
            Self::CallStaticArity => "incorrect number of static arguments in call".to_string(),
            Self::CallStaticUnexpected => {
                "call provided static arguments to a non-generic target".to_string()
            }
            Self::CallStaticUnsupported => {
                "static arguments are not supported for this call target".to_string()
            }
            Self::CasesEmpty => "cases requires at least one arm".to_string(),
            Self::CasesForm => "invalid cases form".to_string(),
            Self::CastInvalid { source, target } => {
                format!("invalid cast from `{source}` to `{target}`")
            }
            Self::CastTarget => "cast target type is invalid".to_string(),
            Self::ClosureArity => {
                "closure arity does not match expected parameter count".to_string()
            }
            Self::IfArity => "if expects one runtime argument: condition".to_string(),
            Self::IfForm => "invalid if form".to_string(),
            Self::InterfaceBoundUnsatisfied { detail } => detail.clone(),
            Self::MacroUntyped => "macro value used where typed value is required".to_string(),
            Self::OpNonNumeric => "numeric operator requires numeric operands".to_string(),
            Self::PatternEmptyArms => {
                "multi-arm expression must contain at least one arm".to_string()
            }
            Self::PatternNonExhaustive => "pattern match is non-exhaustive".to_string(),
            Self::PatternUnreachableArm => "pattern arm is unreachable".to_string(),
            Self::ResolveDuplicate => "duplicate symbol in resolver scope".to_string(),
            Self::StaticArgKind { detail } => detail.clone(),
            Self::StaticArgMissing => {
                "missing static argument for constrained generic parameter".to_string()
            }
            Self::TypeArgArity => "incorrect number of type arguments".to_string(),
            Self::TypeArgKind => "type argument has incompatible kind".to_string(),
            Self::TypeArgMissing => "missing required type argument".to_string(),
            Self::TypeMismatch {
                context,
                expected,
                actual,
            } => format!("type mismatch in {context}: expected `{expected}`, got `{actual}`"),
            Self::UnifyMismatch => "type unification failed".to_string(),
            Self::UnifyOccurs => "occurs check failed during unification".to_string(),
            Self::UnifyUnknown => "internal unify failure: missing type in interner".to_string(),
            Self::UnknownInterface => "unknown interface in constraint".to_string(),
            Self::UseDuplicate => "duplicate imported name in use statement".to_string(),
            Self::UnresolvedIdent { name } => format!("unresolved identifier `{name}`"),
        }
    }

    pub fn default_hint(&self) -> Option<&'static str> {
        match self {
            Self::TypeMismatch { .. } => {
                Some("use an explicit cast for narrowing or cross-domain numeric conversions")
            }
            Self::UnresolvedIdent { .. } => Some("declare the identifier in scope before use"),
            _ => None,
        }
    }
}
