use crate::types::TyId;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CheckedIr {
    pub declarations: Vec<CheckedDecl>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CheckedDecl {
    pub name: String,
    pub ty: TyId,
    pub value: CheckedExpr,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CheckedStaticArg {
    Type(CheckedTypeExpr),
    Value(CheckedStaticValue),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CheckedTypeExpr {
    Named {
        name: String,
        args: Vec<CheckedStaticArg>,
    },
    Static(Box<CheckedTypeExpr>),
    InferHole,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CheckedStaticValue {
    Int(String),
    Float(String),
    Ident(String),
    String(String),
    Char(String),
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CheckedExpr {
    Ident(String),
    Int(String),
    Float(String),
    Char(String),
    String(String),
    DotIdent {
        name: String,
        payload: Option<Box<CheckedExpr>>,
    },
    Tuple(Vec<CheckedExpr>),
    Struct(Vec<(String, CheckedExpr)>),
    Closure {
        params: Vec<String>,
        return_ty: Option<TyId>,
    },
    Any,
    List(Vec<CheckedExpr>),
    Dict(Vec<(CheckedExpr, CheckedExpr)>),
    Call {
        callee: Box<CheckedExpr>,
        args: Vec<CheckedExpr>,
    },
    BinaryOp {
        op: BinaryOpKind,
        lhs: Box<CheckedExpr>,
        rhs: Box<CheckedExpr>,
        ty: TyId,
    },
    MacroApply {
        macro_name: String,
        static_args: Vec<CheckedStaticArg>,
        operand: Box<CheckedExpr>,
    },
    Label {
        label: String,
        expr: Box<CheckedExpr>,
    },
    MultiArm(Vec<CheckedExpr>),
    If {
        condition: Box<CheckedExpr>,
        then_branch: Box<CheckedExpr>,
        else_branch: Option<Box<CheckedExpr>>,
    },
    Cases {
        arms: Vec<CheckedExpr>,
    },
    Return {
        value: Box<CheckedExpr>,
    },
    Break {
        value: Option<Box<CheckedExpr>>,
    },
    Continue,
    Coerce {
        from: TyId,
        to: TyId,
        expr: Box<CheckedExpr>,
    },
    Cast {
        from: TyId,
        to: TyId,
        expr: Box<CheckedExpr>,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BinaryOpKind {
    Add,
    Sub,
    Mul,
    Div,
    Mod,
    Lt,
    Gt,
    Le,
    Ge,
    Eq,
    Neq,
    And,
    Or,
}

impl CheckedIr {
    pub fn empty() -> Self {
        Self {
            declarations: Vec::new(),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::checked_ir::{BinaryOpKind, CheckedDecl, CheckedExpr, CheckedIr};
    use crate::types::TyId;

    #[test]
    fn checked_ir_contract_supports_control_flow_and_conversion_nodes() {
        let ir = CheckedIr {
            declarations: vec![CheckedDecl {
                name: "x".to_string(),
                ty: TyId(0),
                value: CheckedExpr::If {
                    condition: Box::new(CheckedExpr::Ident("cond".to_string())),
                    then_branch: Box::new(CheckedExpr::Coerce {
                        from: TyId(1),
                        to: TyId(2),
                        expr: Box::new(CheckedExpr::Int("1".to_string())),
                    }),
                    else_branch: Some(Box::new(CheckedExpr::Cast {
                        from: TyId(3),
                        to: TyId(4),
                        expr: Box::new(CheckedExpr::Float("2.0".to_string())),
                    })),
                },
            }],
        };

        assert_eq!(ir.declarations.len(), 1);
        assert!(matches!(ir.declarations[0].value, CheckedExpr::If { .. }));
    }

    #[test]
    fn checked_ir_supports_typed_binary_operator_nodes() {
        let ir = CheckedIr {
            declarations: vec![CheckedDecl {
                name: "x".to_string(),
                ty: TyId(2),
                value: CheckedExpr::BinaryOp {
                    op: BinaryOpKind::Add,
                    lhs: Box::new(CheckedExpr::Int("1".to_string())),
                    rhs: Box::new(CheckedExpr::Int("2".to_string())),
                    ty: TyId(2),
                },
            }],
        };

        assert!(matches!(
            ir.declarations[0].value,
            CheckedExpr::BinaryOp {
                op: BinaryOpKind::Add,
                ..
            }
        ));
    }
}
