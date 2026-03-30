use std::collections::HashMap;

use aura_frontend::ast::{Decl, Expr, Program, StaticArg, StaticValueExpr, TypeExpr};

use crate::aliases::TypeAliases;
use crate::builtins::BuiltinRegistry;
use crate::checked_ir::{CheckedDecl, CheckedExpr, CheckedIr, CheckedStaticArg};
use crate::diagnostics::Diagnostic;
use crate::modules::ModuleChecker;
use crate::numeric::can_implicitly_widen;
use crate::patterns::PatternChecker;
use crate::types::{Ty, TyId, TyInterner};
use crate::unify::Unifier;

#[derive(Debug, Clone)]
pub struct TypeChecker {
    interner: TyInterner,
    aliases: TypeAliases,
    builtins: BuiltinRegistry,
    module_checker: ModuleChecker,
    pattern_checker: PatternChecker,
    unifier: Unifier,
    next_infer_var: u32,
    obligation_stack: Vec<String>,
    value_env: HashMap<String, TyId>,
    diagnostics: Vec<Diagnostic>,
    ir: CheckedIr,
}

impl TypeChecker {
    pub fn new() -> Self {
        let mut interner = TyInterner::new();
        interner.prelude_primitives();
        let aliases = TypeAliases::with_prelude(&mut interner);
        Self {
            interner,
            aliases,
            builtins: BuiltinRegistry::with_prelude(),
            module_checker: ModuleChecker::new(),
            pattern_checker: PatternChecker::new(),
            unifier: Unifier::new(),
            next_infer_var: 0,
            obligation_stack: Vec::new(),
            value_env: HashMap::new(),
            diagnostics: Vec::new(),
            ir: CheckedIr::empty(),
        }
    }

    pub fn check_program(&mut self, program: &Program) -> HashMap<String, TyId> {
        let mut values = HashMap::new();
        self.module_checker.check_program(program);

        for decl in &program.declarations {
            if let Decl::Assign { name, value } = decl {
                self.push_obligation(format!("checking declaration '{name}'"));
                let ty = self.infer_expr(value);
                if let Some(existing) = values.get(name).copied() {
                    let lowered = self.lower_expr(value);
                    let coerced = self.coerce_or_cast_for_ir(existing, ty, lowered, name);
                    self.ir.declarations.push(CheckedDecl {
                        name: name.clone(),
                        ty: existing,
                        value: coerced,
                    });
                } else {
                    let lowered = self.lower_expr(value);
                    self.ir.declarations.push(CheckedDecl {
                        name: name.clone(),
                        ty,
                        value: lowered,
                    });
                }
                values.insert(name.clone(), ty);
                self.value_env.insert(name.clone(), ty);
                self.pop_obligation();
            }

            if let Decl::Function(function) = decl {
                self.push_obligation(format!("checking function '{}'", function.name));
                if let Expr::MultiArm(arms) = &function.body {
                    self.diagnostics
                        .extend(self.pattern_checker.validate_multi_arm_exhaustiveness(arms));
                    self.diagnostics
                        .extend(self.pattern_checker.validate_redundancy(arms));
                }

                let expected_ret = self.resolve_type_expr(&function.return_type);
                let actual_ret = self.infer_expr(&function.body);
                self.require_assignable(expected_ret, actual_ret, "function return");
                let lowered_function_body = self.lower_expr(&function.body);
                let lowered_body = self.coerce_or_cast_for_ir(
                    expected_ret,
                    actual_ret,
                    lowered_function_body,
                    "function return",
                );
                self.ir.declarations.push(CheckedDecl {
                    name: function.name.clone(),
                    ty: expected_ret,
                    value: lowered_body,
                });
                let param_tys: Vec<TyId> = function
                    .params
                    .iter()
                    .map(|p| self.resolve_type_expr(&p.ty))
                    .collect();
                let func_ty = self.interner.intern(Ty::Func {
                    params: param_tys,
                    ret: expected_ret,
                });
                self.value_env.insert(function.name.clone(), func_ty);
                self.pop_obligation();
            }

            if let Decl::Macro(macro_decl) = decl {
                self.push_obligation(format!("checking macro '{}'", macro_decl.name));
                if let Expr::MultiArm(arms) = &macro_decl.body {
                    self.diagnostics
                        .extend(self.pattern_checker.validate_multi_arm_exhaustiveness(arms));
                    self.diagnostics
                        .extend(self.pattern_checker.validate_redundancy(arms));
                }

                let expected_ret = self.resolve_type_expr(&macro_decl.return_type);
                let actual_ret = self.infer_expr(&macro_decl.body);
                self.require_assignable(expected_ret, actual_ret, "macro return");
                let lowered_macro_body = self.lower_expr(&macro_decl.body);
                let lowered_body = self.coerce_or_cast_for_ir(
                    expected_ret,
                    actual_ret,
                    lowered_macro_body,
                    "macro return",
                );
                self.ir.declarations.push(CheckedDecl {
                    name: macro_decl.name.clone(),
                    ty: expected_ret,
                    value: lowered_body,
                });
                self.pop_obligation();
            }
        }

        self.diagnostics
            .extend(std::mem::take(&mut self.module_checker).into_diagnostics());

        values
    }

    pub fn into_parts(self) -> (TyInterner, Vec<Diagnostic>, CheckedIr) {
        (self.interner, self.diagnostics, self.ir)
    }

    fn infer_expr(&mut self, expr: &Expr) -> TyId {
        match expr {
            Expr::Ident(name) => {
                if let Some(ty) = self.value_env.get(name).copied() {
                    ty
                } else if name == "true" || name == "false" {
                    self.interner.intern(Ty::Bool)
                } else {
                    self.diagnostics.push(
                        Diagnostic::warning(
                            "W_UNRESOLVED_IDENT",
                            format!("unresolved identifier '{name}'"),
                        )
                        .with_obligations(&self.obligation_stack)
                        .with_hint("declare the identifier in scope before use"),
                    );
                    self.interner.intern(Ty::Any)
                }
            }
            Expr::Int(_) => self.aliases.get("Int").expect("Int alias must exist"),
            Expr::Float(_) => self.aliases.get("Float").expect("Float alias must exist"),
            Expr::Char(_) => self.interner.intern(Ty::Char),
            Expr::String(_) => self.interner.intern(Ty::Nominal("String".to_string())),
            Expr::DotIdent { payload, .. } => {
                if let Some(inner) = payload {
                    self.infer_expr(inner);
                }
                self.interner.intern(Ty::Any)
            }
            Expr::Closure {
                params,
                return_type,
            } => {
                let param_tys = params
                    .iter()
                    .map(|p| self.resolve_type_expr(&p.ty))
                    .collect::<Vec<_>>();
                let ret = return_type
                    .as_ref()
                    .map(|t| self.resolve_type_expr(t))
                    .unwrap_or_else(|| self.interner.intern(Ty::Any));
                self.interner.intern(Ty::Func {
                    params: param_tys,
                    ret,
                })
            }
            Expr::Label { expr, .. } => self.infer_expr(expr),
            Expr::List(items) => {
                if let Some(first) = items.first() {
                    let item_ty = self.infer_expr(first);
                    for item in items.iter().skip(1) {
                        let ty = self.infer_expr(item);
                        self.unify_with_context(item_ty, ty, "list item");
                    }
                    self.interner.intern(Ty::List(item_ty))
                } else {
                    let infer = self.interner.fresh_infer_var(&mut self.next_infer_var);
                    self.interner.intern(Ty::List(infer))
                }
            }
            Expr::Dict(entries) => {
                if let Some((k0, v0)) = entries.first() {
                    let key_ty = self.infer_expr(k0);
                    let val_ty = self.infer_expr(v0);
                    for (k, v) in entries.iter().skip(1) {
                        let k_ty = self.infer_expr(k);
                        let v_ty = self.infer_expr(v);
                        self.unify_with_context(key_ty, k_ty, "dict key");
                        self.unify_with_context(val_ty, v_ty, "dict value");
                    }
                    self.interner.intern(Ty::Dict {
                        key: key_ty,
                        value: val_ty,
                    })
                } else {
                    let any_key = self.interner.intern(Ty::Any);
                    let any_value = self.interner.intern(Ty::Any);
                    self.interner.intern(Ty::Dict {
                        key: any_key,
                        value: any_value,
                    })
                }
            }
            Expr::Call { callee, args, .. } => {
                let callee_ty = self.infer_expr(callee);
                self.infer_call_expr(callee_ty, args)
            }
            Expr::MultiArm(arms) => {
                if let Some(first) = arms.first() {
                    let first_ty = self.infer_expr(&first.body);
                    for arm in arms.iter().skip(1) {
                        let arm_ty = self.infer_expr(&arm.body);
                        self.require_assignable(first_ty, arm_ty, "multi-arm result");
                    }
                    self.unifier.resolve(first_ty)
                } else {
                    self.diagnostics.push(
                        Diagnostic::error(
                            "E_PATTERN_EMPTY_ARMS",
                            "multi-arm expression must contain at least one arm",
                        )
                        .with_obligations(&self.obligation_stack)
                        .with_hint("add at least one pattern arm"),
                    );
                    self.interner.intern(Ty::Any)
                }
            }
            Expr::MacroApply {
                macro_name,
                operand,
                static_args,
            } if macro_name == "builtin" => {
                if let Expr::Ident(name) = operand.as_ref() {
                    if self.builtins.get(name).is_none() {
                        self.diagnostics.push(
                            Diagnostic::error(
                                "E_BUILTIN_UNKNOWN",
                                format!("unknown builtin symbol '{name}'"),
                            )
                            .with_hint(
                                "declare the builtin in the registry or fix the symbol name",
                            ),
                        );
                    }
                } else {
                    self.diagnostics.push(
                        Diagnostic::error(
                            "E_BUILTIN_FORM",
                            "builtin expects an identifier operand",
                        )
                        .with_hint("use form: builtin io_write"),
                    );
                }
                self.interner.intern(Ty::Any)
            }
            Expr::MacroApply {
                macro_name,
                operand,
                static_args,
            } if macro_name == "cast" => {
                let source = self.infer_expr(operand);
                let Some(target) = static_args
                    .first()
                    .and_then(|a| self.resolve_static_arg_type(a))
                else {
                    self.diagnostics.push(
                        Diagnostic::error(
                            "E_CAST_TARGET",
                            "cast requires one target type static argument",
                        )
                        .with_obligations(&self.obligation_stack)
                        .with_hint("use form like cast[Int] value"),
                    );
                    return self.interner.intern(Ty::Any);
                };

                let Some(source_ty) = self.interner.get(source).cloned() else {
                    return self.interner.intern(Ty::Any);
                };
                let Some(target_ty) = self.interner.get(target).cloned() else {
                    return self.interner.intern(Ty::Any);
                };

                if can_implicitly_widen(&source_ty, &target_ty)
                    || self.is_explicit_cast_pair(&source_ty, &target_ty)
                {
                    return target;
                }

                self.diagnostics.push(
                    Diagnostic::error(
                        "E_CAST_INVALID",
                        format!("invalid cast from {:?} to {:?}", source_ty, target_ty),
                    )
                    .with_obligations(&self.obligation_stack)
                    .with_hint("check cast matrix or change source/target types"),
                );
                self.interner.intern(Ty::Any)
            }
            Expr::MacroApply {
                macro_name,
                operand,
                static_args,
            } if macro_name == "if" => self.infer_if_macro(operand),
            Expr::MacroApply {
                macro_name,
                operand,
                static_args,
            } if macro_name == "cases" => self.infer_cases_macro(operand),
            Expr::MacroApply {
                macro_name,
                operand,
                static_args,
            } if macro_name == "return" => self.infer_expr(operand),
            Expr::MacroApply {
                macro_name,
                operand,
                static_args,
            } if macro_name == "break" => {
                if let Expr::List(items) = operand.as_ref() {
                    if let Some(v) = items.first() {
                        return self.infer_expr(v);
                    }
                }
                self.interner.intern(Ty::Void)
            }
            Expr::MacroApply {
                macro_name,
                operand,
                static_args,
            } if macro_name == "continue" => self.interner.intern(Ty::Void),
            Expr::MacroApply {
                macro_name,
                operand,
                static_args,
            } => {
                if macro_name == "add"
                    || macro_name == "sub"
                    || macro_name == "mul"
                    || macro_name == "div"
                {
                    return self.infer_numeric_operator(macro_name, operand, static_args);
                }
                self.diagnostics.push(
                    Diagnostic::warning(
                        "W_MACRO_UNTYPED",
                        format!("macro '{macro_name}' has no typing rule yet"),
                    )
                    .with_obligations(&self.obligation_stack)
                    .with_hint("add a typing rule for this macro before backend lowering"),
                );
                self.interner.intern(Ty::Any)
            }
        }
    }

    fn infer_numeric_operator(
        &mut self,
        op: &str,
        operand: &Expr,
        _static_args: &[StaticArg],
    ) -> TyId {
        let (lhs_expr, rhs_expr) = match operand {
            Expr::List(items) if items.len() == 2 => (&items[0], &items[1]),
            _ => {
                self.diagnostics.push(
                    Diagnostic::error(
                        "E_OP_ARITY",
                        format!("operator macro '{op}' expects exactly two operands"),
                    )
                    .with_obligations(&self.obligation_stack)
                    .with_hint("use form like add [lhs, rhs]"),
                );
                return self.interner.intern(Ty::Any);
            }
        };

        let lhs_ty = self.infer_expr(lhs_expr);
        let rhs_ty = self.infer_expr(rhs_expr);

        self.require_assignable(lhs_ty, rhs_ty, "numeric operator");
        let result = self.unifier.resolve(lhs_ty);
        let Some(result_ty) = self.interner.get(result).cloned() else {
            return self.interner.intern(Ty::Any);
        };

        if is_numeric_ty(&result_ty) {
            return result;
        }

        self.diagnostics.push(
            Diagnostic::error(
                "E_OP_NON_NUMERIC",
                format!(
                    "operator '{op}' requires numeric operands, got {:?}",
                    result_ty
                ),
            )
            .with_obligations(&self.obligation_stack)
            .with_hint("cast operands to numeric types before applying arithmetic operators"),
        );
        self.interner.intern(Ty::Any)
    }

    fn infer_if_macro(&mut self, operand: &Expr) -> TyId {
        let Expr::List(items) = operand else {
            self.diagnostics.push(
                Diagnostic::error(
                    "E_IF_FORM",
                    "if expects list operand [condition, then, else?]",
                )
                .with_obligations(&self.obligation_stack)
                .with_hint("use form: if [condition, then_branch, else_branch]"),
            );
            return self.interner.intern(Ty::Any);
        };

        if items.len() < 2 || items.len() > 3 {
            self.diagnostics.push(
                Diagnostic::error("E_IF_ARITY", "if expects 2 or 3 operands")
                    .with_obligations(&self.obligation_stack)
                    .with_hint(
                        "if [condition, then_branch] or if [condition, then_branch, else_branch]",
                    ),
            );
            return self.interner.intern(Ty::Any);
        }

        let cond_ty = self.infer_expr(&items[0]);
        let bool_ty = self.interner.intern(Ty::Bool);
        self.require_assignable(bool_ty, cond_ty, "if condition");

        let then_ty = self.infer_expr(&items[1]);
        if items.len() == 2 {
            return then_ty;
        }

        let else_ty = self.infer_expr(&items[2]);
        self.require_assignable(then_ty, else_ty, "if branch join");
        self.unifier.resolve(then_ty)
    }

    fn infer_cases_macro(&mut self, operand: &Expr) -> TyId {
        let Expr::MultiArm(arms) = operand else {
            self.diagnostics.push(
                Diagnostic::error("E_CASES_FORM", "cases expects a multi-arm closure operand")
                    .with_obligations(&self.obligation_stack)
                    .with_hint("use form: cases { ~cond -> expr, ~true -> default }"),
            );
            return self.interner.intern(Ty::Any);
        };

        if arms.is_empty() {
            self.diagnostics.push(
                Diagnostic::error("E_CASES_EMPTY", "cases requires at least one arm")
                    .with_obligations(&self.obligation_stack)
                    .with_hint("add one or more guarded arms"),
            );
            return self.interner.intern(Ty::Any);
        }

        let first_ty = self.infer_expr(&arms[0].body);
        for arm in arms.iter().skip(1) {
            let ty = self.infer_expr(&arm.body);
            self.require_assignable(first_ty, ty, "cases arm join");
        }

        self.unifier.resolve(first_ty)
    }

    fn resolve_type_expr(&mut self, ty: &TypeExpr) -> TyId {
        match ty {
            TypeExpr::Static(inner) => self.resolve_type_expr(inner),
            TypeExpr::Named { name, args } => {
                if let Some(alias) = self.aliases.get(name) {
                    return alias;
                }

                match name.as_str() {
                    "Bool" => self.interner.intern(Ty::Bool),
                    "Char" => self.interner.intern(Ty::Char),
                    "Void" => self.interner.intern(Ty::Void),
                    "Never" => self.interner.intern(Ty::Never),
                    "Any" => self.interner.intern(Ty::Any),
                    "String" => self.interner.intern(Ty::Nominal("String".to_string())),
                    "List" => {
                        let item = args
                            .first()
                            .and_then(|a| self.resolve_static_arg_type(a))
                            .unwrap_or_else(|| self.interner.intern(Ty::Any));
                        self.interner.intern(Ty::List(item))
                    }
                    "Dict" => {
                        let key = args
                            .first()
                            .and_then(|a| self.resolve_static_arg_type(a))
                            .unwrap_or_else(|| self.interner.intern(Ty::Any));
                        let value = args
                            .get(1)
                            .and_then(|a| self.resolve_static_arg_type(a))
                            .unwrap_or_else(|| self.interner.intern(Ty::Any));
                        self.interner.intern(Ty::Dict { key, value })
                    }
                    "Set" => {
                        let item = args
                            .first()
                            .and_then(|a| self.resolve_static_arg_type(a))
                            .unwrap_or_else(|| self.interner.intern(Ty::Any));
                        self.interner.intern(Ty::Set(item))
                    }
                    "Array" => {
                        let item = args
                            .first()
                            .and_then(|a| self.resolve_static_arg_type(a))
                            .unwrap_or_else(|| self.interner.intern(Ty::Any));
                        let size = args
                            .get(1)
                            .and_then(|arg| match arg {
                                StaticArg::Value(StaticValueExpr::Int(raw)) => {
                                    raw.parse::<u64>().ok()
                                }
                                _ => None,
                            })
                            .unwrap_or(0);
                        self.interner.intern(Ty::Array { item, size })
                    }
                    "Func" => {
                        let a = args
                            .first()
                            .and_then(|a| self.resolve_static_arg_type(a))
                            .unwrap_or_else(|| self.interner.intern(Ty::Any));
                        let b = args
                            .get(1)
                            .and_then(|a| self.resolve_static_arg_type(a))
                            .unwrap_or_else(|| self.interner.intern(Ty::Any));
                        self.interner.intern(Ty::Func {
                            params: vec![a],
                            ret: b,
                        })
                    }
                    _ => self.interner.intern(Ty::Nominal(name.clone())),
                }
            }
        }
    }

    fn resolve_static_arg_type(&mut self, arg: &StaticArg) -> Option<TyId> {
        match arg {
            StaticArg::Type(ty) => Some(self.resolve_type_expr(ty)),
            StaticArg::Value(_) => None,
        }
    }

    fn infer_call_expr(&mut self, callee_ty: TyId, args: &[Expr]) -> TyId {
        self.push_obligation("checking call expression".to_string());
        let expected_params: Vec<TyId> = args
            .iter()
            .map(|_| self.interner.fresh_infer_var(&mut self.next_infer_var))
            .collect();
        let expected_ret = self.interner.fresh_infer_var(&mut self.next_infer_var);
        let expected_func = self.interner.intern(Ty::Func {
            params: expected_params.clone(),
            ret: expected_ret,
        });

        self.unify_with_context(callee_ty, expected_func, "callable expression");

        for (idx, arg) in args.iter().enumerate() {
            self.push_obligation(format!("checking call argument #{idx}"));
            let arg_ty = self.infer_expr(arg);
            let expected = expected_params[idx];
            self.require_assignable(expected, arg_ty, "call argument");
            self.pop_obligation();
        }

        let resolved = self.unifier.resolve(expected_ret);
        self.pop_obligation();
        resolved
    }

    fn unify_with_context(&mut self, lhs: TyId, rhs: TyId, context: &str) -> TyId {
        match self.unifier.unify(&mut self.interner, lhs, rhs, context) {
            Ok(id) => id,
            Err(diag) => {
                self.diagnostics
                    .push((*diag).with_obligations(&self.obligation_stack));
                self.interner.intern(Ty::Any)
            }
        }
    }

    fn require_assignable(&mut self, expected: TyId, actual: TyId, context: &str) {
        if expected == actual {
            return;
        }

        let Some(expected_ty) = self.interner.get(expected).cloned() else {
            return;
        };
        let Some(actual_ty) = self.interner.get(actual).cloned() else {
            return;
        };

        if matches!(expected_ty, Ty::Any) || matches!(actual_ty, Ty::Any) {
            return;
        }

        if matches!(expected_ty, Ty::InferVar(_)) || matches!(actual_ty, Ty::InferVar(_)) {
            self.unify_with_context(expected, actual, context);
            return;
        }

        if can_implicitly_widen(&actual_ty, &expected_ty) {
            return;
        }

        self.diagnostics.push(
            Diagnostic::error(
                "E_TYPE_MISMATCH",
                format!(
                    "type mismatch in {context}: expected {:?}, got {:?}",
                    expected_ty, actual_ty
                ),
            )
            .with_related("assignment compatibility check failed", None)
            .with_obligations(&self.obligation_stack)
            .with_hint("use an explicit cast for narrowing or cross-domain numeric conversions"),
        );
    }

    fn coerce_or_cast_for_ir(
        &mut self,
        expected: TyId,
        actual: TyId,
        expr: CheckedExpr,
        context: &str,
    ) -> CheckedExpr {
        if expected == actual {
            return expr;
        }

        let Some(expected_ty) = self.interner.get(expected).cloned() else {
            return expr;
        };
        let Some(actual_ty) = self.interner.get(actual).cloned() else {
            return expr;
        };

        if can_implicitly_widen(&actual_ty, &expected_ty) {
            return CheckedExpr::Coerce {
                from: actual,
                to: expected,
                expr: Box::new(expr),
            };
        }

        if self.is_explicit_cast_pair(&actual_ty, &expected_ty) {
            return CheckedExpr::Cast {
                from: actual,
                to: expected,
                expr: Box::new(expr),
            };
        }

        self.diagnostics.push(
            Diagnostic::error(
                "E_TYPE_MISMATCH",
                format!(
                    "type mismatch in {context}: expected {:?}, got {:?}",
                    expected_ty, actual_ty
                ),
            )
            .with_related("IR coercion/cast decision failed", None)
            .with_obligations(&self.obligation_stack)
            .with_hint("use an explicit cast for narrowing or cross-domain numeric conversions"),
        );
        expr
    }

    fn is_explicit_cast_pair(&self, from: &Ty, to: &Ty) -> bool {
        use Ty::*;
        matches!(
            (from, to),
            (Int8 | Int16 | Int32 | Int64 | Int128, Float32 | Float64)
                | (
                    UInt8 | UInt16 | UInt32 | UInt64 | UInt128,
                    Float32 | Float64
                )
                | (Float32 | Float64, Int8 | Int16 | Int32 | Int64 | Int128)
                | (
                    Float32 | Float64,
                    UInt8 | UInt16 | UInt32 | UInt64 | UInt128
                )
                | (
                    Int8 | Int16 | Int32 | Int64 | Int128,
                    UInt8 | UInt16 | UInt32 | UInt64 | UInt128
                )
                | (
                    UInt8 | UInt16 | UInt32 | UInt64 | UInt128,
                    Int8 | Int16 | Int32 | Int64 | Int128
                )
                | (Int16, Int8)
                | (Int32, Int8 | Int16)
                | (Int64, Int8 | Int16 | Int32)
                | (Int128, Int8 | Int16 | Int32 | Int64)
                | (UInt16, UInt8)
                | (UInt32, UInt8 | UInt16)
                | (UInt64, UInt8 | UInt16 | UInt32)
                | (UInt128, UInt8 | UInt16 | UInt32 | UInt64)
                | (Float64, Float32)
        )
    }

    fn push_obligation(&mut self, obligation: String) {
        self.obligation_stack.push(obligation);
    }

    fn pop_obligation(&mut self) {
        let _ = self.obligation_stack.pop();
    }

    fn lower_expr(&mut self, expr: &Expr) -> CheckedExpr {
        match expr {
            Expr::Ident(v) => CheckedExpr::Ident(v.clone()),
            Expr::Int(v) => CheckedExpr::Int(v.clone()),
            Expr::Float(v) => CheckedExpr::Float(v.clone()),
            Expr::Char(v) => CheckedExpr::Char(v.clone()),
            Expr::String(v) => CheckedExpr::String(v.clone()),
            Expr::DotIdent { name, payload } => CheckedExpr::DotIdent {
                name: name.clone(),
                payload: payload.as_ref().map(|p| Box::new(self.lower_expr(p))),
            },
            Expr::Closure {
                params,
                return_type,
            } => CheckedExpr::Closure {
                params: params.iter().map(|p| p.name.clone()).collect(),
                return_ty: return_type.as_ref().map(|t| self.resolve_type_expr(t)),
            },
            Expr::List(items) => {
                CheckedExpr::List(items.iter().map(|item| self.lower_expr(item)).collect())
            }
            Expr::Dict(entries) => CheckedExpr::Dict(
                entries
                    .iter()
                    .map(|(k, v)| (self.lower_expr(k), self.lower_expr(v)))
                    .collect(),
            ),
            Expr::Call { callee, args, .. } => CheckedExpr::Call {
                callee: Box::new(self.lower_expr(callee)),
                args: args.iter().map(|a| self.lower_expr(a)).collect(),
            },
            Expr::MacroApply {
                macro_name,
                operand,
                static_args,
            } if macro_name == "if" => {
                if let Expr::List(items) = operand.as_ref() {
                    if items.len() >= 2 {
                        let condition = self.lower_expr(&items[0]);
                        let then_branch = self.lower_expr(&items[1]);
                        let else_branch = items.get(2).map(|e| Box::new(self.lower_expr(e)));
                        return CheckedExpr::If {
                            condition: Box::new(condition),
                            then_branch: Box::new(then_branch),
                            else_branch,
                        };
                    }
                }
                CheckedExpr::Any
            }
            Expr::MacroApply {
                macro_name,
                operand,
                static_args,
            } if macro_name == "cases" => {
                if let Expr::MultiArm(arms) = operand.as_ref() {
                    return CheckedExpr::Cases {
                        arms: arms.iter().map(|a| self.lower_expr(&a.body)).collect(),
                    };
                }
                CheckedExpr::Any
            }
            Expr::MacroApply {
                macro_name,
                operand,
                static_args,
            } if macro_name == "cast" => {
                let source_ty = self.preview_expr_ty(operand);
                let target_ty = static_args
                    .first()
                    .and_then(|a| self.resolve_static_arg_type(a))
                    .unwrap_or_else(|| self.interner.intern(Ty::Any));
                CheckedExpr::Cast {
                    from: source_ty,
                    to: target_ty,
                    expr: Box::new(self.lower_expr(operand)),
                }
            }
            Expr::MacroApply {
                macro_name,
                operand,
                static_args,
            } if macro_name == "return" => CheckedExpr::Return {
                value: Box::new(self.lower_expr(operand)),
            },
            Expr::MacroApply {
                macro_name,
                operand,
                static_args,
            } if macro_name == "break" => {
                if let Expr::List(items) = operand.as_ref() {
                    let value = items.first().map(|v| Box::new(self.lower_expr(v)));
                    CheckedExpr::Break { value }
                } else {
                    CheckedExpr::Break {
                        value: Some(Box::new(self.lower_expr(operand))),
                    }
                }
            }
            Expr::MacroApply {
                macro_name,
                operand,
                static_args,
            } if macro_name == "continue" => CheckedExpr::Continue,
            Expr::MacroApply {
                macro_name,
                operand,
                static_args,
            } => CheckedExpr::MacroApply {
                macro_name: macro_name.clone(),
                static_args: static_args
                    .iter()
                    .map(|arg| match arg {
                        StaticArg::Type(ty) => CheckedStaticArg::Type(format!("{:?}", ty)),
                        StaticArg::Value(value) => CheckedStaticArg::Value(format!("{:?}", value)),
                    })
                    .collect(),
                operand: Box::new(self.lower_expr(operand)),
            },
            Expr::Label { label, expr } => CheckedExpr::Label {
                label: label.clone(),
                expr: Box::new(self.lower_expr(expr)),
            },
            Expr::MultiArm(arms) => CheckedExpr::MultiArm(
                arms.iter()
                    .map(|arm| self.lower_expr(&arm.body))
                    .collect::<Vec<_>>(),
            ),
        }
    }

    fn preview_expr_ty(&mut self, expr: &Expr) -> TyId {
        match expr {
            Expr::Ident(name) => self.value_env.get(name).copied().unwrap_or_else(|| {
                if name == "true" || name == "false" {
                    self.interner.intern(Ty::Bool)
                } else {
                    self.interner.intern(Ty::Any)
                }
            }),
            Expr::Int(_) => self
                .aliases
                .get("Int")
                .unwrap_or_else(|| self.interner.intern(Ty::Int32)),
            Expr::Float(_) => self
                .aliases
                .get("Float")
                .unwrap_or_else(|| self.interner.intern(Ty::Float32)),
            Expr::Char(_) => self.interner.intern(Ty::Char),
            Expr::String(_) => self.interner.intern(Ty::Nominal("String".to_string())),
            Expr::Closure {
                params,
                return_type,
            } => {
                let param_tys = params
                    .iter()
                    .map(|p| self.resolve_type_expr(&p.ty))
                    .collect::<Vec<_>>();
                let ret = return_type
                    .as_ref()
                    .map(|t| self.resolve_type_expr(t))
                    .unwrap_or_else(|| self.interner.intern(Ty::Any));
                self.interner.intern(Ty::Func {
                    params: param_tys,
                    ret,
                })
            }
            _ => self.infer_expr(expr),
        }
    }
}

fn is_numeric_ty(ty: &Ty) -> bool {
    matches!(
        ty,
        Ty::Int8
            | Ty::Int16
            | Ty::Int32
            | Ty::Int64
            | Ty::Int128
            | Ty::ISize
            | Ty::UInt8
            | Ty::UInt16
            | Ty::UInt32
            | Ty::UInt64
            | Ty::UInt128
            | Ty::USize
            | Ty::Float32
            | Ty::Float64
    )
}

impl Default for TypeChecker {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use crate::checked_ir::CheckedExpr;
    use aura_frontend::ast::{Decl, Expr, FunctionDecl, Pattern, Program, TypeExpr};
    use aura_frontend::ast::{StaticArg, StaticValueExpr};

    use crate::check_module;

    #[test]
    fn allows_implicit_numeric_widening_on_reassignment() {
        let program = Program {
            declarations: vec![
                Decl::Assign {
                    name: "x".to_string(),
                    value: Expr::Int("1".to_string()),
                },
                Decl::Assign {
                    name: "x".to_string(),
                    value: Expr::Int("2".to_string()),
                },
            ],
        };

        let checked = check_module(&program);
        assert!(checked.module.is_none()); // duplicate symbol from resolver in same scope
    }

    #[test]
    fn multi_arm_without_fallback_reports_non_exhaustive() {
        let program = Program {
            declarations: vec![Decl::Function(FunctionDecl {
                static_params: Vec::new(),
                receiver: Some(TypeExpr::Named {
                    name: "Result".to_string(),
                    args: Vec::new(),
                }),
                name: "map".to_string(),
                params: Vec::new(),
                return_type: TypeExpr::Named {
                    name: "Result".to_string(),
                    args: Vec::new(),
                },
                body: Expr::MultiArm(vec![aura_frontend::ast::Arm {
                    patterns: vec![Pattern::DotVariant {
                        name: "ok".to_string(),
                        payload: None,
                    }],
                    body: Expr::Ident("x".to_string()),
                }]),
            })],
        };

        let checked = check_module(&program);
        assert!(checked.module.is_none());
        assert!(checked
            .diagnostics
            .iter()
            .any(|d| d.code == "E_PATTERN_NON_EXHAUSTIVE"));
    }

    #[test]
    fn wildcard_then_extra_arm_reports_unreachable() {
        let program = Program {
            declarations: vec![Decl::Function(FunctionDecl {
                static_params: Vec::new(),
                receiver: Some(TypeExpr::Named {
                    name: "Result".to_string(),
                    args: Vec::new(),
                }),
                name: "map".to_string(),
                params: Vec::new(),
                return_type: TypeExpr::Named {
                    name: "Result".to_string(),
                    args: Vec::new(),
                },
                body: Expr::MultiArm(vec![
                    aura_frontend::ast::Arm {
                        patterns: vec![Pattern::Wildcard],
                        body: Expr::Ident("x".to_string()),
                    },
                    aura_frontend::ast::Arm {
                        patterns: vec![Pattern::Ident("later".to_string())],
                        body: Expr::Ident("y".to_string()),
                    },
                ]),
            })],
        };

        let checked = check_module(&program);
        assert!(checked.module.is_none());
        assert!(checked
            .diagnostics
            .iter()
            .any(|d| d.code == "E_PATTERN_UNREACHABLE_ARM"));
    }

    #[test]
    fn string_is_not_primitive_and_is_nominal() {
        let program = Program {
            declarations: vec![Decl::Assign {
                name: "s".to_string(),
                value: Expr::String("ok".to_string()),
            }],
        };

        let checked = check_module(&program);
        assert!(checked.module.is_some());
        let module = checked.module.expect("module should exist");
        let ty_id = module.value_types.get("s").expect("type should exist");
        let ty = module
            .types
            .get(*ty_id)
            .expect("interned type should exist");
        assert!(matches!(ty, crate::types::Ty::Nominal(name) if name == "String"));
    }

    #[test]
    fn checked_ir_is_emitted_for_assignments() {
        let program = Program {
            declarations: vec![Decl::Assign {
                name: "x".to_string(),
                value: Expr::Int("1".to_string()),
            }],
        };

        let checked = check_module(&program);
        let module = checked.module.expect("checked module should exist");
        assert_eq!(module.ir.declarations.len(), 1);
        assert_eq!(module.ir.declarations[0].name, "x");
        assert!(matches!(
            module.ir.declarations[0].value,
            CheckedExpr::Int(_)
        ));
    }

    #[test]
    fn checked_ir_preserves_call_shape() {
        let program = Program {
            declarations: vec![Decl::Assign {
                name: "v".to_string(),
                value: Expr::Call {
                    callee: Box::new(Expr::Ident("f".to_string())),
                    static_args: Vec::new(),
                    args: vec![Expr::Int("1".to_string())],
                },
            }],
        };

        let checked = check_module(&program);
        let module = checked.module.expect("module should exist");
        assert!(matches!(
            module.ir.declarations[0].value,
            CheckedExpr::Call { .. }
        ));
    }

    #[test]
    fn checked_ir_emits_coerce_for_widening_assignment() {
        let program = Program {
            declarations: vec![
                Decl::Assign {
                    name: "x".to_string(),
                    value: Expr::Int("1".to_string()),
                },
                Decl::Assign {
                    name: "x".to_string(),
                    value: Expr::Float("2.0".to_string()),
                },
            ],
        };

        let checked = check_module(&program);
        assert!(checked.module.is_none());
    }

    #[test]
    fn function_return_mismatch_produces_diagnostic() {
        let program = Program {
            declarations: vec![Decl::Function(FunctionDecl {
                static_params: Vec::new(),
                receiver: Some(TypeExpr::Named {
                    name: "Example".to_string(),
                    args: Vec::new(),
                }),
                name: "f".to_string(),
                params: Vec::new(),
                return_type: TypeExpr::Named {
                    name: "Int".to_string(),
                    args: Vec::new(),
                },
                body: Expr::String("oops".to_string()),
            })],
        };

        let checked = check_module(&program);
        assert!(checked.module.is_none());
        assert!(checked
            .diagnostics
            .iter()
            .any(|d| d.code == "E_TYPE_MISMATCH"));
    }

    #[test]
    fn multi_arm_result_type_mismatch_produces_diagnostic() {
        let program = Program {
            declarations: vec![Decl::Function(FunctionDecl {
                static_params: Vec::new(),
                receiver: Some(TypeExpr::Named {
                    name: "Example".to_string(),
                    args: Vec::new(),
                }),
                name: "g".to_string(),
                params: Vec::new(),
                return_type: TypeExpr::Named {
                    name: "Any".to_string(),
                    args: Vec::new(),
                },
                body: Expr::MultiArm(vec![
                    aura_frontend::ast::Arm {
                        patterns: vec![Pattern::Ident("a".to_string())],
                        body: Expr::Int("1".to_string()),
                    },
                    aura_frontend::ast::Arm {
                        patterns: vec![Pattern::Wildcard],
                        body: Expr::String("bad".to_string()),
                    },
                ]),
            })],
        };

        let checked = check_module(&program);
        assert!(checked.module.is_none());
        assert!(checked
            .diagnostics
            .iter()
            .any(|d| d.code == "E_TYPE_MISMATCH"));
    }

    #[test]
    fn duplicate_use_targets_fail_typecheck_pipeline() {
        let program = Program {
            declarations: vec![
                Decl::Use(aura_frontend::ast::UseDecl {
                    target: "io".to_string(),
                }),
                Decl::Use(aura_frontend::ast::UseDecl {
                    target: "io".to_string(),
                }),
            ],
        };

        let checked = check_module(&program);
        assert!(checked.module.is_none());
        assert!(checked
            .diagnostics
            .iter()
            .any(|d| d.code == "E_USE_DUPLICATE"));
    }

    #[test]
    fn unknown_builtin_symbol_reports_diagnostic() {
        let program = Program {
            declarations: vec![Decl::Assign {
                name: "x".to_string(),
                value: Expr::MacroApply {
                    macro_name: "builtin".to_string(),
                    static_args: Vec::new(),
                    operand: Box::new(Expr::Ident("missing_builtin".to_string())),
                },
            }],
        };

        let checked = check_module(&program);
        assert!(checked.module.is_none());
        assert!(checked
            .diagnostics
            .iter()
            .any(|d| d.code == "E_BUILTIN_UNKNOWN"));
    }

    #[test]
    fn type_mismatch_diagnostic_contains_related_context() {
        let program = Program {
            declarations: vec![
                Decl::Assign {
                    name: "x".to_string(),
                    value: Expr::List(vec![Expr::Int("1".to_string())]),
                },
                Decl::Assign {
                    name: "x".to_string(),
                    value: Expr::Dict(vec![(
                        Expr::Int("1".to_string()),
                        Expr::Int("2".to_string()),
                    )]),
                },
            ],
        };

        let checked = check_module(&program);
        assert!(checked.module.is_none());
        let diag = checked
            .diagnostics
            .iter()
            .find(|d| d.code == "E_TYPE_MISMATCH")
            .expect("expected mismatch diagnostic");
        assert!(!diag.related.is_empty());
    }

    #[test]
    fn call_inference_uses_function_signature_shape() {
        let program = Program {
            declarations: vec![
                Decl::Assign {
                    name: "f".to_string(),
                    value: Expr::Ident("unknown_callable".to_string()),
                },
                Decl::Assign {
                    name: "y".to_string(),
                    value: Expr::Call {
                        callee: Box::new(Expr::Ident("f".to_string())),
                        static_args: Vec::new(),
                        args: vec![Expr::Int("1".to_string())],
                    },
                },
            ],
        };

        let checked = check_module(&program);
        let has_unify_error = checked
            .diagnostics
            .iter()
            .any(|d| d.code == "E_UNIFY_MISMATCH");
        assert!(!has_unify_error);
    }

    #[test]
    fn unify_mismatch_includes_obligation_trace() {
        let program = Program {
            declarations: vec![Decl::Assign {
                name: "x".to_string(),
                value: Expr::Call {
                    callee: Box::new(Expr::Int("1".to_string())),
                    static_args: Vec::new(),
                    args: vec![Expr::Int("2".to_string())],
                },
            }],
        };

        let checked = check_module(&program);
        assert!(checked.module.is_none());
        let diag = checked
            .diagnostics
            .iter()
            .find(|d| d.code == "E_UNIFY_MISMATCH")
            .expect("expected unify mismatch diagnostic");
        assert!(!diag.obligations.is_empty());
    }

    #[test]
    fn numeric_operator_macro_requires_numeric_operands() {
        let program = Program {
            declarations: vec![Decl::Assign {
                name: "x".to_string(),
                value: Expr::MacroApply {
                    macro_name: "add".to_string(),
                    static_args: Vec::new(),
                    operand: Box::new(Expr::List(vec![
                        Expr::String("a".to_string()),
                        Expr::Int("1".to_string()),
                    ])),
                },
            }],
        };

        let checked = check_module(&program);
        assert!(checked.module.is_none());
        assert!(checked
            .diagnostics
            .iter()
            .any(|d| d.code == "E_OP_NON_NUMERIC"));
    }

    #[test]
    fn lower_macro_apply_keeps_static_args_in_ir() {
        let program = Program {
            declarations: vec![Decl::Assign {
                name: "x".to_string(),
                value: Expr::MacroApply {
                    macro_name: "m".to_string(),
                    static_args: vec![StaticArg::Value(StaticValueExpr::Int("4".to_string()))],
                    operand: Box::new(Expr::Ident("node".to_string())),
                },
            }],
        };

        let checked = check_module(&program);
        let module = checked.module.expect("module should exist");
        let CheckedExpr::MacroApply { static_args, .. } = &module.ir.declarations[0].value else {
            panic!("expected macro apply in IR")
        };
        assert_eq!(static_args.len(), 1);
    }

    #[test]
    fn if_macro_typechecks_and_lowers_to_if_ir() {
        let program = Program {
            declarations: vec![Decl::Assign {
                name: "x".to_string(),
                value: Expr::MacroApply {
                    macro_name: "if".to_string(),
                    static_args: Vec::new(),
                    operand: Box::new(Expr::List(vec![
                        Expr::Ident("true".to_string()),
                        Expr::Int("1".to_string()),
                        Expr::Int("2".to_string()),
                    ])),
                },
            }],
        };

        let checked = check_module(&program);
        let module = checked.module.expect("module should exist");
        assert!(matches!(
            module.ir.declarations[0].value,
            CheckedExpr::If { .. }
        ));
    }

    #[test]
    fn cases_macro_lowers_to_cases_ir() {
        let program = Program {
            declarations: vec![Decl::Assign {
                name: "x".to_string(),
                value: Expr::MacroApply {
                    macro_name: "cases".to_string(),
                    static_args: Vec::new(),
                    operand: Box::new(Expr::MultiArm(vec![
                        aura_frontend::ast::Arm {
                            patterns: vec![Pattern::Ident("a".to_string())],
                            body: Expr::Int("1".to_string()),
                        },
                        aura_frontend::ast::Arm {
                            patterns: vec![Pattern::Wildcard],
                            body: Expr::Int("2".to_string()),
                        },
                    ])),
                },
            }],
        };

        let checked = check_module(&program);
        let module = checked.module.expect("module should exist");
        assert!(matches!(
            module.ir.declarations[0].value,
            CheckedExpr::Cases { .. }
        ));
    }

    #[test]
    fn return_break_continue_lower_to_control_flow_ir() {
        let program = Program {
            declarations: vec![
                Decl::Assign {
                    name: "r".to_string(),
                    value: Expr::MacroApply {
                        macro_name: "return".to_string(),
                        static_args: Vec::new(),
                        operand: Box::new(Expr::Int("1".to_string())),
                    },
                },
                Decl::Assign {
                    name: "b".to_string(),
                    value: Expr::MacroApply {
                        macro_name: "break".to_string(),
                        static_args: Vec::new(),
                        operand: Box::new(Expr::List(vec![Expr::Int("9".to_string())])),
                    },
                },
                Decl::Assign {
                    name: "c".to_string(),
                    value: Expr::MacroApply {
                        macro_name: "continue".to_string(),
                        static_args: Vec::new(),
                        operand: Box::new(Expr::Ident("unit".to_string())),
                    },
                },
            ],
        };

        let checked = check_module(&program);
        let module = checked.module.expect("module should exist");
        assert!(matches!(
            module.ir.declarations[0].value,
            CheckedExpr::Return { .. }
        ));
        assert!(matches!(
            module.ir.declarations[1].value,
            CheckedExpr::Break { .. }
        ));
        assert!(matches!(
            module.ir.declarations[2].value,
            CheckedExpr::Continue
        ));
    }

    #[test]
    fn cast_macro_lowers_to_explicit_cast_ir() {
        let program = Program {
            declarations: vec![Decl::Assign {
                name: "x".to_string(),
                value: Expr::MacroApply {
                    macro_name: "cast".to_string(),
                    static_args: vec![StaticArg::Type(TypeExpr::Named {
                        name: "Float".to_string(),
                        args: Vec::new(),
                    })],
                    operand: Box::new(Expr::Int("1".to_string())),
                },
            }],
        };

        let checked = check_module(&program);
        let module = checked.module.expect("module should exist");
        assert!(matches!(
            module.ir.declarations[0].value,
            CheckedExpr::Cast { .. }
        ));
    }

    #[test]
    fn unresolved_identifier_reports_diagnostic() {
        let program = Program {
            declarations: vec![Decl::Assign {
                name: "x".to_string(),
                value: Expr::Ident("missing".to_string()),
            }],
        };

        let checked = check_module(&program);
        assert!(checked.module.is_some());
        assert!(checked
            .diagnostics
            .iter()
            .any(|d| d.code == "W_UNRESOLVED_IDENT"));
    }

    #[test]
    fn closure_lowers_to_typed_closure_ir() {
        let program = Program {
            declarations: vec![Decl::Assign {
                name: "f".to_string(),
                value: Expr::Closure {
                    params: vec![aura_frontend::ast::Param {
                        name: "x".to_string(),
                        ty: TypeExpr::Named {
                            name: "Int".to_string(),
                            args: Vec::new(),
                        },
                    }],
                    return_type: Some(TypeExpr::Named {
                        name: "Int".to_string(),
                        args: Vec::new(),
                    }),
                },
            }],
        };

        let checked = check_module(&program);
        let module = checked.module.expect("module should exist");
        assert!(matches!(
            module.ir.declarations[0].value,
            CheckedExpr::Closure { .. }
        ));
    }
}
