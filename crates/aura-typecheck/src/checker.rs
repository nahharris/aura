use std::collections::HashMap;

use aura_diagnostics::{Diagnostic, Stage};
use aura_frontend::ast::{
    BinaryOp as ParsedBinaryOp, Decl, Expr, LabeledClosureArg, Pattern, Program, StaticArg,
    StaticParam, StaticParamKind, StaticValueExpr, TypeExpr,
};

use crate::aliases::TypeAliases;
use crate::builtins::BuiltinRegistry;
use crate::checked_ir::{
    BinaryOpKind, CheckedDecl, CheckedExpr, CheckedIr, CheckedStaticArg, CheckedStaticValue,
    CheckedTypeExpr,
};
use crate::interfaces::InterfaceRegistry;
use crate::modules::ModuleChecker;
use crate::numeric::can_implicitly_widen;
use crate::patterns::PatternChecker;
use crate::types::{Ty, TyId, TyInterner};
use crate::unify::Unifier;

use crate::generics::GenericConstraint;

#[derive(Debug, Clone)]
pub struct TypeChecker {
    interner: TyInterner,
    aliases: TypeAliases,
    builtins: BuiltinRegistry,
    module_checker: ModuleChecker,
    pattern_checker: PatternChecker,
    interfaces: InterfaceRegistry,
    unifier: Unifier,
    next_infer_var: u32,
    obligation_stack: Vec<String>,
    value_env_scopes: Vec<HashMap<String, TyId>>,
    generic_env_scopes: Vec<HashMap<String, TyId>>,
    function_generics: HashMap<String, Vec<FunctionGenericInfo>>,
    pending_constraints: Vec<TypeConstraint>,
    solving_constraints: bool,
    current_expr_span: Option<aura_diagnostics::Span>,
    diagnostics: Vec<Diagnostic>,
    ir: CheckedIr,
}

#[derive(Debug, Clone)]
enum TypeConstraint {
    Equal {
        lhs: TyId,
        rhs: TyId,
        context: String,
        obligations: Vec<String>,
        span: Option<aura_diagnostics::Span>,
    },
    Assignable {
        expected: TyId,
        actual: TyId,
        context: String,
        obligations: Vec<String>,
        span: Option<aura_diagnostics::Span>,
    },
    InterfaceBound {
        ty: TyId,
        interface: String,
        context: String,
        obligations: Vec<String>,
        span: Option<aura_diagnostics::Span>,
    },
    InterfaceExists {
        interface: String,
        context: String,
        obligations: Vec<String>,
        span: Option<aura_diagnostics::Span>,
    },
    StaticBound {
        arg: Option<StaticArg>,
        param: String,
        expected: TypeExpr,
        context: String,
        obligations: Vec<String>,
        span: Option<aura_diagnostics::Span>,
    },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ConversionMode {
    ImplicitOnly,
    ExplicitCastAllowed,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ConversionDecision {
    Identity,
    Coerce,
    Cast,
    Incompatible,
}

#[derive(Debug, Clone)]
struct FunctionGenericInfo {
    name: String,
    constraints: Vec<GenericConstraint>,
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
            interfaces: InterfaceRegistry::with_prelude(),
            unifier: Unifier::new(),
            next_infer_var: 0,
            obligation_stack: Vec::new(),
            value_env_scopes: vec![HashMap::new()],
            generic_env_scopes: vec![HashMap::new()],
            function_generics: HashMap::new(),
            pending_constraints: Vec::new(),
            solving_constraints: false,
            current_expr_span: None,
            diagnostics: Vec::new(),
            ir: CheckedIr::empty(),
        }
    }

    fn base_expr(expr: &Expr) -> &Expr {
        let mut cur = expr;
        while let Expr::Spanned { expr, .. } = cur {
            cur = expr.as_ref();
        }
        cur
    }

    pub fn check_program(&mut self, program: &Program) -> HashMap<String, TyId> {
        let mut values = HashMap::new();
        self.module_checker.check_program(program);

        for decl in &program.declarations {
            if let Decl::Assign { name, value } = decl {
                let prev_span = self.current_expr_span;
                self.current_expr_span = Expr::span(value);
                self.push_obligation(format!("checking declaration '{name}'"));
                self.pending_constraints.clear();
                let ty = self.infer_expr(value);
                self.solve_constraints();
                if let Some(existing) = values.get(name).copied() {
                    self.require_assignable(existing, ty, "reassignment");
                    self.solve_constraints();
                    let lowered = self.lower_expr(value);
                    let coerced = self.coerce_or_cast_for_ir(
                        existing,
                        ty,
                        lowered,
                        "reassignment",
                        ConversionMode::ImplicitOnly,
                    );
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
                self.insert_value(name.clone(), ty);
                self.pop_obligation();
                self.current_expr_span = prev_span;
            }

            if let Decl::Function(function) = decl {
                let prev_span = self.current_expr_span;
                self.current_expr_span = Expr::span(&function.body);
                self.push_obligation(format!("checking function '{}'", function.name));
                self.pending_constraints.clear();
                self.push_generic_scope();
                for p in &function.static_params {
                    let t = self.interner.intern(Ty::GenericParam(p.name.clone()));
                    self.insert_generic(p.name.clone(), t);
                }
                self.push_scope();
                for param in &function.params {
                    let param_ty = self.resolve_type_expr(&param.ty);
                    self.insert_value(param.name.clone(), param_ty);
                }
                if let Expr::MultiArm(arms) = TypeChecker::base_expr(&function.body) {
                    self.diagnostics
                        .extend(self.pattern_checker.validate_multi_arm_exhaustiveness(arms));
                    self.diagnostics
                        .extend(self.pattern_checker.validate_redundancy(arms));
                }

                let expected_ret = self.resolve_type_expr(&function.return_type);
                let actual_ret = self.infer_expr_with_expected(&function.body, expected_ret);
                self.require_assignable(expected_ret, actual_ret, "function return");
                self.solve_constraints();
                let lowered_function_body = self.lower_expr(&function.body);
                let lowered_body = self.coerce_or_cast_for_ir(
                    expected_ret,
                    actual_ret,
                    lowered_function_body,
                    "function return",
                    ConversionMode::ImplicitOnly,
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
                self.pop_scope();
                self.pop_generic_scope();
                self.insert_value(function.name.clone(), func_ty);
                if !function.static_params.is_empty() {
                    self.function_generics.insert(
                        function.name.clone(),
                        function
                            .static_params
                            .iter()
                            .map(|p| self.to_function_generic_info(p))
                            .collect(),
                    );
                }
                self.pop_obligation();
                self.current_expr_span = prev_span;
            }

            if let Decl::Macro(macro_decl) = decl {
                let prev_span = self.current_expr_span;
                self.current_expr_span = Expr::span(&macro_decl.body);
                self.push_obligation(format!("checking macro '{}'", macro_decl.name));
                self.pending_constraints.clear();
                self.push_scope();
                for param in &macro_decl.params {
                    let param_ty = self.resolve_type_expr(&param.ty);
                    self.insert_value(param.name.clone(), param_ty);
                }
                if let Expr::MultiArm(arms) = TypeChecker::base_expr(&macro_decl.body) {
                    self.diagnostics
                        .extend(self.pattern_checker.validate_multi_arm_exhaustiveness(arms));
                    self.diagnostics
                        .extend(self.pattern_checker.validate_redundancy(arms));
                }

                let expected_ret = self.resolve_type_expr(&macro_decl.return_type);
                let actual_ret = self.infer_expr_with_expected(&macro_decl.body, expected_ret);
                self.require_assignable(expected_ret, actual_ret, "macro return");
                self.solve_constraints();
                let lowered_macro_body = self.lower_expr(&macro_decl.body);
                let lowered_body = self.coerce_or_cast_for_ir(
                    expected_ret,
                    actual_ret,
                    lowered_macro_body,
                    "macro return",
                    ConversionMode::ImplicitOnly,
                );
                self.ir.declarations.push(CheckedDecl {
                    name: macro_decl.name.clone(),
                    ty: expected_ret,
                    value: lowered_body,
                });
                self.pop_scope();
                self.pop_obligation();
                self.current_expr_span = prev_span;
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
            Expr::Spanned { span, expr } => {
                let prev = self.current_expr_span;
                self.current_expr_span = Some(*span);
                let ty = self.infer_expr(expr);
                self.current_expr_span = prev;
                ty
            }
            Expr::Ident(name) => {
                if let Some(ty) = self.lookup_value(name) {
                    ty
                } else if name == "true" || name == "false" {
                    self.interner.intern(Ty::Bool)
                } else {
                    self.diagnostics.push(
                        self.typecheck_warning(
                            "W_UNRESOLVED_IDENT",
                            format!("unresolved identifier '{name}'"),
                        )
                        .with_stage(Stage::Typecheck)
                        .with_hint("declare the identifier in scope before use"),
                    );
                    self.unknown_ty()
                }
            }
            Expr::Int(_) => self.aliases.get("Int").expect("Int alias must exist"),
            Expr::Float(_) => self.aliases.get("Float").expect("Float alias must exist"),
            Expr::Char(_) => self.interner.intern(Ty::Char),
            Expr::String(_) => self.interner.intern(Ty::Nominal("String".to_string())),
            Expr::DotIdent { payload, .. } => {
                if let Some(inner) = payload {
                    self.infer_expr(inner)
                } else {
                    self.interner.intern(Ty::Void)
                }
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
                    .unwrap_or_else(|| self.interner.fresh_infer_var(&mut self.next_infer_var));
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
                    let any_key = self.unknown_ty();
                    let any_value = self.unknown_ty();
                    self.interner.intern(Ty::Dict {
                        key: any_key,
                        value: any_value,
                    })
                }
            }
            Expr::Call {
                callee,
                static_args,
                args,
                trailing,
                ..
            } => {
                let callee_name = match TypeChecker::base_expr(callee.as_ref()) {
                    Expr::Ident(name) => Some(name.clone()),
                    _ => None,
                };
                if matches!(callee_name.as_deref(), Some("if")) {
                    return self.infer_if_call_with_expected(args, trailing, None);
                }
                if matches!(callee_name.as_deref(), Some("cases")) {
                    return self.infer_cases_call_with_expected(args, trailing, None);
                }
                let callee_ty = self.infer_expr(callee);
                self.infer_call_expr(
                    callee_ty,
                    callee_name.as_deref(),
                    static_args,
                    args,
                    trailing,
                    None,
                )
            }
            Expr::Cast { expr, ty } => {
                let source = self.infer_expr(expr);
                let target = self.resolve_type_expr(ty);
                let source_ty = self
                    .interner
                    .get(source)
                    .cloned()
                    .unwrap_or_else(|| self.missing_ty_fallback());
                let target_ty = self
                    .interner
                    .get(target)
                    .cloned()
                    .unwrap_or_else(|| self.missing_ty_fallback());
                match self.conversion_decision(
                    target,
                    source,
                    ConversionMode::ExplicitCastAllowed,
                    "cast expression",
                ) {
                    ConversionDecision::Identity
                    | ConversionDecision::Coerce
                    | ConversionDecision::Cast => target,
                    ConversionDecision::Incompatible => {
                        self.diagnostics.push(
                            self.typecheck_error(
                                "E_CAST_INVALID",
                                format!("invalid cast from {:?} to {:?}", source_ty, target_ty),
                            )
                            .with_hint("check cast matrix or change source/target types"),
                        );
                        self.unknown_ty()
                    }
                }
            }
            Expr::Binary { op, lhs, rhs } => self.infer_binary_expr(*op, lhs, rhs),
            Expr::Member { object, .. } => {
                let _ = self.infer_expr(object);
                self.unknown_ty()
            }
            Expr::TypeExpr(_) => self.unknown_ty(),
            Expr::MultiArm(arms) => {
                if let Some(first) = arms.first() {
                    self.push_scope();
                    self.bind_arm_patterns(first.patterns.as_slice());
                    self.infer_arm_guard(first.guard.as_ref());
                    let first_ty = self.infer_expr(&first.body);
                    self.pop_scope();
                    for arm in arms.iter().skip(1) {
                        self.push_scope();
                        self.bind_arm_patterns(arm.patterns.as_slice());
                        self.infer_arm_guard(arm.guard.as_ref());
                        let arm_ty = self.infer_expr(&arm.body);
                        self.pop_scope();
                        self.join_types(first_ty, arm_ty, "multi-arm result");
                    }
                    self.unifier.resolve(first_ty)
                } else {
                    self.diagnostics.push(
                        self.typecheck_error(
                            "E_PATTERN_EMPTY_ARMS",
                            "multi-arm expression must contain at least one arm",
                        )
                        .with_stage(Stage::Typecheck)
                        .with_hint("add at least one pattern arm"),
                    );
                    self.unknown_ty()
                }
            }
            Expr::MacroApply {
                macro_name,
                operand,
                static_args,
            } if macro_name == "builtin" => {
                if let Expr::Ident(name) = TypeChecker::base_expr(operand.as_ref()) {
                    if let Some(sig) = self.builtins.get(name).cloned() {
                        let param_tys = sig
                            .params
                            .iter()
                            .map(|ty| self.intern_ty(ty))
                            .collect::<Vec<_>>();
                        let ret = self.intern_ty(&sig.ret);
                        return self.interner.intern(Ty::Func {
                            params: param_tys,
                            ret,
                        });
                    } else {
                        self.diagnostics.push(
                            self.typecheck_error(
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
                        self.typecheck_error(
                            "E_BUILTIN_FORM",
                            "builtin expects an identifier operand",
                        )
                        .with_hint("use form: builtin io_write"),
                    );
                }
                self.unknown_ty()
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
                        self.typecheck_error(
                            "E_CAST_TARGET",
                            "cast requires one target type static argument",
                        )
                        .with_hint("use form like cast[Int] value"),
                    );
                    return self.unknown_ty();
                };

                let Some(source_ty) = self.interner.get(source).cloned() else {
                    return self.unknown_ty();
                };
                let Some(target_ty) = self.interner.get(target).cloned() else {
                    return self.unknown_ty();
                };

                match self.conversion_decision(
                    target,
                    source,
                    ConversionMode::ExplicitCastAllowed,
                    "cast expression",
                ) {
                    ConversionDecision::Identity
                    | ConversionDecision::Coerce
                    | ConversionDecision::Cast => return target,
                    ConversionDecision::Incompatible => {}
                }

                self.diagnostics.push(
                    self.typecheck_error(
                        "E_CAST_INVALID",
                        format!("invalid cast from {:?} to {:?}", source_ty, target_ty),
                    )
                    .with_hint("check cast matrix or change source/target types"),
                );
                self.unknown_ty()
            }
            Expr::MacroApply {
                macro_name,
                operand,
                static_args,
            } if macro_name == "if" => {
                self.diagnostics.push(
                    self.typecheck_error(
                        "E_IF_FORM",
                        "if is an inline function call and no longer a macro application",
                    )
                    .with_hint("use form: if (condition) then { ... } else { ... }"),
                );
                self.unknown_ty()
            }
            Expr::MacroApply {
                macro_name,
                operand,
                static_args,
            } if macro_name == "cases" => {
                self.diagnostics.push(
                    self.typecheck_error(
                        "E_CASES_FORM",
                        "cases is an inline function call and no longer a macro application",
                    )
                    .with_hint("use form: cases when { ... }"),
                );
                self.unknown_ty()
            }
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
                if let Expr::List(items) = TypeChecker::base_expr(operand.as_ref()) {
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
                static_args: _,
            } => {
                self.diagnostics.push(
                    self.typecheck_error(
                        "E_MACRO_UNTYPED",
                        format!("macro '{macro_name}' has no typing rule yet"),
                    )
                    .with_hint("add a typing rule for this macro before backend lowering"),
                );
                self.infer_expr(operand)
            }
        }
    }

    fn infer_expr_with_expected(&mut self, expr: &Expr, expected: TyId) -> TyId {
        if let Expr::Spanned { span, expr: inner } = expr {
            let prev = self.current_expr_span;
            self.current_expr_span = Some(*span);
            let ty = self.infer_expr_with_expected(inner, expected);
            self.current_expr_span = prev;
            return ty;
        }
        let expected = self.unifier.resolve(expected);
        let expected_ty = self.interner.get(expected).cloned();

        match (Self::base_expr(expr), expected_ty) {
            (
                Expr::Call {
                    callee,
                    static_args,
                    args,
                    trailing,
                    ..
                },
                _,
            ) => {
                let callee_name = match TypeChecker::base_expr(callee.as_ref()) {
                    Expr::Ident(name) => Some(name.clone()),
                    _ => None,
                };
                if matches!(callee_name.as_deref(), Some("if")) {
                    let actual = self.infer_if_call_with_expected(args, trailing, Some(expected));
                    self.require_assignable(expected, actual, "bidirectional expected type");
                    return actual;
                }
                if matches!(callee_name.as_deref(), Some("cases")) {
                    let actual =
                        self.infer_cases_call_with_expected(args, trailing, Some(expected));
                    self.require_assignable(expected, actual, "bidirectional expected type");
                    return actual;
                }
                let callee_ty = self.infer_expr(callee);
                let actual = self.infer_call_expr(
                    callee_ty,
                    callee_name.as_deref(),
                    static_args,
                    args,
                    trailing,
                    Some(expected),
                );
                self.require_assignable(expected, actual, "bidirectional expected type");
                actual
            }
            (Expr::Label { expr, .. }, _) => {
                let actual = self.infer_expr_with_expected(expr, expected);
                self.require_assignable(expected, actual, "bidirectional expected type");
                actual
            }
            (Expr::Cast { expr, ty }, _) => {
                let source = self.infer_expr(expr);
                let target = self.resolve_type_expr(ty);
                let actual = match self.conversion_decision(
                    target,
                    source,
                    ConversionMode::ExplicitCastAllowed,
                    "cast expression",
                ) {
                    ConversionDecision::Identity
                    | ConversionDecision::Coerce
                    | ConversionDecision::Cast => target,
                    ConversionDecision::Incompatible => {
                        self.emit_type_mismatch(
                            target,
                            source,
                            "cast expression",
                            "explicit cast decision failed",
                        );
                        self.unknown_ty()
                    }
                };
                self.require_assignable(expected, actual, "bidirectional expected type");
                actual
            }
            (
                Expr::DotIdent {
                    payload: Some(inner),
                    ..
                },
                _,
            ) => {
                let actual = self.infer_expr_with_expected(inner, expected);
                self.require_assignable(expected, actual, "bidirectional expected type");
                actual
            }
            (
                Expr::MacroApply {
                    macro_name,
                    operand,
                    static_args: _,
                },
                _,
            ) if macro_name == "if" => {
                self.diagnostics.push(
                    self.typecheck_error(
                        "E_IF_FORM",
                        "if is an inline function call and no longer a macro application",
                    )
                    .with_hint("use form: if (condition) then { ... } else { ... }"),
                );
                self.unknown_ty()
            }
            (
                Expr::MacroApply {
                    macro_name,
                    operand,
                    static_args: _,
                },
                _,
            ) if macro_name == "return" => {
                let actual = self.infer_expr_with_expected(operand, expected);
                self.require_assignable(expected, actual, "bidirectional expected type");
                actual
            }
            (
                Expr::MacroApply {
                    macro_name,
                    operand,
                    static_args: _,
                },
                _,
            ) if macro_name == "cases" => {
                self.diagnostics.push(
                    self.typecheck_error(
                        "E_CASES_FORM",
                        "cases is an inline function call and no longer a macro application",
                    )
                    .with_hint("use form: cases when { ... }"),
                );
                self.unknown_ty()
            }
            (Expr::MultiArm(arms), _) => {
                let actual = self.infer_multi_arm_with_expected(arms, Some(expected));
                self.require_assignable(expected, actual, "bidirectional expected type");
                actual
            }
            (Expr::List(items), Some(Ty::List(expected_item))) => {
                for item in items {
                    let item_ty = self.infer_expr_with_expected(item, expected_item);
                    self.require_assignable(expected_item, item_ty, "list element");
                }
                self.interner.intern(Ty::List(expected_item))
            }
            (
                Expr::Dict(entries),
                Some(Ty::Dict {
                    key: expected_key,
                    value: expected_value,
                }),
            ) => {
                for (k, v) in entries {
                    let key_ty = self.infer_expr_with_expected(k, expected_key);
                    let value_ty = self.infer_expr_with_expected(v, expected_value);
                    self.require_assignable(expected_key, key_ty, "dict key");
                    self.require_assignable(expected_value, value_ty, "dict value");
                }
                self.interner.intern(Ty::Dict {
                    key: expected_key,
                    value: expected_value,
                })
            }
            (
                Expr::Closure {
                    params,
                    return_type,
                },
                Some(Ty::Func {
                    params: expected_params,
                    ret: expected_ret,
                }),
            ) => {
                if params.len() != expected_params.len() {
                    self.diagnostics.push(
                        self.typecheck_error(
                            "E_CLOSURE_ARITY",
                            format!(
                                "closure parameter count {} does not match expected {}",
                                params.len(),
                                expected_params.len()
                            ),
                        )
                        .with_hint("adjust closure parameter list to match expected function type"),
                    );
                }

                let param_tys = params
                    .iter()
                    .map(|p| self.resolve_type_expr(&p.ty))
                    .collect::<Vec<_>>();

                for (declared, expected_param) in param_tys.iter().zip(expected_params.iter()) {
                    self.require_assignable(*expected_param, *declared, "closure parameter");
                }

                let ret = return_type
                    .as_ref()
                    .map(|t| self.resolve_type_expr(t))
                    .unwrap_or(expected_ret);
                self.interner.intern(Ty::Func {
                    params: param_tys,
                    ret,
                })
            }
            _ => {
                let actual = self.infer_expr(expr);
                self.require_assignable(expected, actual, "bidirectional expected type");
                actual
            }
        }
    }

    fn intern_ty(&mut self, ty: &Ty) -> TyId {
        match ty {
            Ty::Nominal(name) => self.interner.intern(Ty::Nominal(name.clone())),
            Ty::List(item) => {
                let item_ty = self
                    .interner
                    .get(*item)
                    .cloned()
                    .unwrap_or_else(|| self.missing_ty_fallback());
                let lowered_item = self.intern_ty(&item_ty);
                self.interner.intern(Ty::List(lowered_item))
            }
            Ty::Dict { key, value } => {
                let k = self
                    .interner
                    .get(*key)
                    .cloned()
                    .unwrap_or_else(|| self.missing_ty_fallback());
                let v = self
                    .interner
                    .get(*value)
                    .cloned()
                    .unwrap_or_else(|| self.missing_ty_fallback());
                let lowered_k = self.intern_ty(&k);
                let lowered_v = self.intern_ty(&v);
                self.interner.intern(Ty::Dict {
                    key: lowered_k,
                    value: lowered_v,
                })
            }
            Ty::Set(item) => {
                let item_ty = self
                    .interner
                    .get(*item)
                    .cloned()
                    .unwrap_or_else(|| self.missing_ty_fallback());
                let lowered_item = self.intern_ty(&item_ty);
                self.interner.intern(Ty::Set(lowered_item))
            }
            Ty::Array { item, size } => {
                let item_ty = self
                    .interner
                    .get(*item)
                    .cloned()
                    .unwrap_or_else(|| self.missing_ty_fallback());
                let lowered_item = self.intern_ty(&item_ty);
                self.interner.intern(Ty::Array {
                    item: lowered_item,
                    size: *size,
                })
            }
            Ty::Func { params, ret } => {
                let lowered_params = params
                    .iter()
                    .map(|p| {
                        let t = self
                            .interner
                            .get(*p)
                            .cloned()
                            .unwrap_or_else(|| self.missing_ty_fallback());
                        self.intern_ty(&t)
                    })
                    .collect();
                let ret_ty = self
                    .interner
                    .get(*ret)
                    .cloned()
                    .unwrap_or_else(|| self.missing_ty_fallback());
                let lowered_ret = self.intern_ty(&ret_ty);
                self.interner.intern(Ty::Func {
                    params: lowered_params,
                    ret: lowered_ret,
                })
            }
            Ty::Tuple(items) => {
                let lowered = items
                    .iter()
                    .map(|i| {
                        let t = self
                            .interner
                            .get(*i)
                            .cloned()
                            .unwrap_or_else(|| self.missing_ty_fallback());
                        self.intern_ty(&t)
                    })
                    .collect();
                self.interner.intern(Ty::Tuple(lowered))
            }
            Ty::Struct(fields) => {
                let lowered = fields
                    .iter()
                    .map(|(n, t)| {
                        let ty = self
                            .interner
                            .get(*t)
                            .cloned()
                            .unwrap_or_else(|| self.missing_ty_fallback());
                        (n.clone(), self.intern_ty(&ty))
                    })
                    .collect();
                self.interner.intern(Ty::Struct(lowered))
            }
            other => self.interner.intern(other.clone()),
        }
    }

    fn infer_binary_expr(&mut self, op: ParsedBinaryOp, lhs: &Expr, rhs: &Expr) -> TyId {
        match op {
            ParsedBinaryOp::Add
            | ParsedBinaryOp::Sub
            | ParsedBinaryOp::Mul
            | ParsedBinaryOp::Div
            | ParsedBinaryOp::Mod => {
                let lhs_ty = self.infer_expr(lhs);
                let rhs_ty = self.infer_expr(rhs);
                self.require_assignable(lhs_ty, rhs_ty, "numeric operator");
                let result = self.unifier.resolve(lhs_ty);
                let Some(result_ty) = self.interner.get(result).cloned() else {
                    return self.unknown_ty();
                };
                if is_numeric_ty(&result_ty) {
                    return result;
                }
                self.diagnostics.push(
                    self.typecheck_error(
                        "E_OP_NON_NUMERIC",
                        format!(
                            "numeric operator requires numeric operands, got {:?}",
                            result_ty
                        ),
                    )
                    .with_related("numeric operator operands are not numeric", None)
                    .with_hint(
                        "cast operands to numeric types before applying arithmetic operators",
                    ),
                );
                self.unknown_ty()
            }
            ParsedBinaryOp::Lt | ParsedBinaryOp::Le | ParsedBinaryOp::Gt | ParsedBinaryOp::Ge => {
                let lhs_ty = self.infer_expr(lhs);
                let rhs_ty = self.infer_expr(rhs);
                self.require_assignable(lhs_ty, rhs_ty, "comparison operator");
                self.require_assignable(rhs_ty, lhs_ty, "comparison operator");
                let result = self.unifier.resolve(lhs_ty);
                let Some(result_ty) = self.interner.get(result).cloned() else {
                    return self.unknown_ty();
                };
                if is_numeric_ty(&result_ty) {
                    return self.interner.intern(Ty::Bool);
                }
                self.diagnostics.push(
                    self.typecheck_error(
                        "E_OP_NON_NUMERIC",
                        format!(
                            "comparison operator requires numeric operands, got {:?}",
                            result_ty
                        ),
                    )
                    .with_related("comparison operator operands are not numeric", None)
                    .with_hint(
                        "cast operands to numeric types before applying comparison operators",
                    ),
                );
                self.unknown_ty()
            }
            ParsedBinaryOp::Eq | ParsedBinaryOp::Neq => {
                let lhs_ty = self.infer_expr(lhs);
                let rhs_ty = self.infer_expr(rhs);
                self.require_assignable(lhs_ty, rhs_ty, "equality operator");
                self.require_assignable(rhs_ty, lhs_ty, "equality operator");
                self.interner.intern(Ty::Bool)
            }
            ParsedBinaryOp::And | ParsedBinaryOp::Or => {
                let bool_ty = self.interner.intern(Ty::Bool);
                let lhs_ty = self.infer_expr_with_expected(lhs, bool_ty);
                let rhs_ty = self.infer_expr_with_expected(rhs, bool_ty);
                self.require_assignable(bool_ty, lhs_ty, "logical operator");
                self.require_assignable(bool_ty, rhs_ty, "logical operator");
                bool_ty
            }
            ParsedBinaryOp::Colon => {
                let source = self.infer_expr(lhs);
                let Expr::TypeExpr(ty) = rhs else {
                    self.diagnostics.push(
                        self.typecheck_error(
                            "E_CAST_TARGET",
                            "cast ':' expects a type expression on RHS",
                        )
                        .with_hint("use form like value: Int"),
                    );
                    return self.unknown_ty();
                };
                let target = self.resolve_type_expr(ty);
                let source_ty = self
                    .interner
                    .get(source)
                    .cloned()
                    .unwrap_or_else(|| self.missing_ty_fallback());
                let target_ty = self
                    .interner
                    .get(target)
                    .cloned()
                    .unwrap_or_else(|| self.missing_ty_fallback());
                match self.conversion_decision(
                    target,
                    source,
                    ConversionMode::ExplicitCastAllowed,
                    "cast expression",
                ) {
                    ConversionDecision::Identity
                    | ConversionDecision::Coerce
                    | ConversionDecision::Cast => target,
                    ConversionDecision::Incompatible => {
                        self.diagnostics.push(
                            self.typecheck_error(
                                "E_CAST_INVALID",
                                format!("invalid cast from {:?} to {:?}", source_ty, target_ty),
                            )
                            .with_hint("check cast matrix or change source/target types"),
                        );
                        self.unknown_ty()
                    }
                }
            }
            ParsedBinaryOp::Elvis | ParsedBinaryOp::Range => {
                let lhs_ty = self.infer_expr(lhs);
                let rhs_ty = self.infer_expr(rhs);
                self.join_types(lhs_ty, rhs_ty, "binary operator")
            }
        }
    }

    fn parsed_binary_op_kind(&self, op: ParsedBinaryOp) -> Option<BinaryOpKind> {
        match op {
            ParsedBinaryOp::Add => Some(BinaryOpKind::Add),
            ParsedBinaryOp::Sub => Some(BinaryOpKind::Sub),
            ParsedBinaryOp::Mul => Some(BinaryOpKind::Mul),
            ParsedBinaryOp::Div => Some(BinaryOpKind::Div),
            ParsedBinaryOp::Mod => Some(BinaryOpKind::Mod),
            ParsedBinaryOp::Lt => Some(BinaryOpKind::Lt),
            ParsedBinaryOp::Le => Some(BinaryOpKind::Le),
            ParsedBinaryOp::Gt => Some(BinaryOpKind::Gt),
            ParsedBinaryOp::Ge => Some(BinaryOpKind::Ge),
            ParsedBinaryOp::Eq => Some(BinaryOpKind::Eq),
            ParsedBinaryOp::Neq => Some(BinaryOpKind::Neq),
            ParsedBinaryOp::And => Some(BinaryOpKind::And),
            ParsedBinaryOp::Or => Some(BinaryOpKind::Or),
            ParsedBinaryOp::Elvis | ParsedBinaryOp::Range | ParsedBinaryOp::Colon => None,
        }
    }

    fn lower_static_arg(&mut self, arg: &StaticArg) -> CheckedStaticArg {
        match arg {
            StaticArg::Type(ty) => CheckedStaticArg::Type(self.lower_type_expr(ty)),
            StaticArg::Value(v) => CheckedStaticArg::Value(self.lower_static_value(v)),
        }
    }

    fn lower_type_expr(&mut self, ty: &TypeExpr) -> CheckedTypeExpr {
        match ty {
            TypeExpr::Named { name, args } => CheckedTypeExpr::Named {
                name: name.clone(),
                args: args.iter().map(|a| self.lower_static_arg(a)).collect(),
            },
            TypeExpr::Static(inner) => {
                CheckedTypeExpr::Static(Box::new(self.lower_type_expr(inner)))
            }
            TypeExpr::InferHole => CheckedTypeExpr::InferHole,
        }
    }

    fn lower_static_value(&self, value: &StaticValueExpr) -> CheckedStaticValue {
        match value {
            StaticValueExpr::Int(v) => CheckedStaticValue::Int(v.clone()),
            StaticValueExpr::Float(v) => CheckedStaticValue::Float(v.clone()),
            StaticValueExpr::Ident(v) => CheckedStaticValue::Ident(v.clone()),
            StaticValueExpr::String(v) => CheckedStaticValue::String(v.clone()),
            StaticValueExpr::Char(v) => CheckedStaticValue::Char(v.clone()),
        }
    }

    fn infer_multi_arm_with_expected(
        &mut self,
        arms: &[aura_frontend::ast::Arm],
        expected: Option<TyId>,
    ) -> TyId {
        if arms.is_empty() {
            self.diagnostics.push(
                self.typecheck_error("E_CASES_EMPTY", "cases requires at least one arm")
                    .with_hint("add one or more guarded arms"),
            );
            return self.unknown_ty();
        }

        self.push_scope();
        self.bind_arm_patterns(arms[0].patterns.as_slice());
        self.infer_arm_guard(arms[0].guard.as_ref());
        let first_ty = if let Some(exp) = expected {
            self.infer_expr_with_expected(&arms[0].body, exp)
        } else {
            self.infer_expr(&arms[0].body)
        };
        self.pop_scope();

        for arm in arms.iter().skip(1) {
            self.push_scope();
            self.bind_arm_patterns(arm.patterns.as_slice());
            self.infer_arm_guard(arm.guard.as_ref());
            let ty = if let Some(exp) = expected {
                self.infer_expr_with_expected(&arm.body, exp)
            } else {
                self.infer_expr(&arm.body)
            };
            self.pop_scope();
            self.join_types(first_ty, ty, "cases arm join");
        }

        self.unifier.resolve(first_ty)
    }

    fn join_types(&mut self, lhs: TyId, rhs: TyId, context: &str) -> TyId {
        let lhs = self.unifier.resolve(lhs);
        let rhs = self.unifier.resolve(rhs);
        if lhs == rhs {
            return lhs;
        }

        let Some(lhs_ty) = self.interner.get(lhs).cloned() else {
            return self.unknown_ty();
        };
        let Some(rhs_ty) = self.interner.get(rhs).cloned() else {
            return self.unknown_ty();
        };

        if matches!(lhs_ty, Ty::Any) {
            return rhs;
        }
        if matches!(rhs_ty, Ty::Any) {
            return lhs;
        }

        if matches!(
            self.conversion_decision(lhs, rhs, ConversionMode::ImplicitOnly, context),
            ConversionDecision::Identity | ConversionDecision::Coerce
        ) {
            return lhs;
        }
        if matches!(
            self.conversion_decision(rhs, lhs, ConversionMode::ImplicitOnly, context),
            ConversionDecision::Identity | ConversionDecision::Coerce
        ) {
            return rhs;
        }

        self.emit_type_mismatch(lhs, rhs, context, "branch join compatibility check failed");

        self.unify_with_context(lhs, rhs, context)
    }

    fn resolve_type_expr(&mut self, ty: &TypeExpr) -> TyId {
        match ty {
            TypeExpr::Static(inner) => self.resolve_type_expr(inner),
            TypeExpr::InferHole => self.unknown_ty(),
            TypeExpr::Named { name, args } => {
                if let Some(alias) = self.aliases.get(name) {
                    return alias;
                }

                match name.as_str() {
                    "Bool" => {
                        self.enforce_exact_type_arity("Bool", args, 0);
                        self.interner.intern(Ty::Bool)
                    }
                    "Char" => {
                        self.enforce_exact_type_arity("Char", args, 0);
                        self.interner.intern(Ty::Char)
                    }
                    "Void" => {
                        self.enforce_exact_type_arity("Void", args, 0);
                        self.interner.intern(Ty::Void)
                    }
                    "Never" => {
                        self.enforce_exact_type_arity("Never", args, 0);
                        self.interner.intern(Ty::Never)
                    }
                    "Any" => {
                        self.enforce_exact_type_arity("Any", args, 0);
                        self.interner.intern(Ty::Any)
                    }
                    "String" => {
                        self.enforce_exact_type_arity("String", args, 0);
                        self.interner.intern(Ty::Nominal("String".to_string()))
                    }
                    "List" => {
                        self.enforce_exact_type_arity("List", args, 1);
                        let item = self.resolve_required_type_arg(args, 0, "List", "item");
                        self.interner.intern(Ty::List(item))
                    }
                    "Dict" => {
                        self.enforce_exact_type_arity("Dict", args, 2);
                        let key = self.resolve_required_type_arg(args, 0, "Dict", "key");
                        let value = self.resolve_required_type_arg(args, 1, "Dict", "value");
                        self.interner.intern(Ty::Dict { key, value })
                    }
                    "Set" => {
                        self.enforce_exact_type_arity("Set", args, 1);
                        let item = self.resolve_required_type_arg(args, 0, "Set", "item");
                        self.interner.intern(Ty::Set(item))
                    }
                    "Array" => {
                        self.enforce_exact_type_arity("Array", args, 2);
                        let item = self.resolve_required_type_arg(args, 0, "Array", "item");
                        let size = self.resolve_required_array_size_arg(args, "Array", "size");
                        self.interner.intern(Ty::Array { item, size })
                    }
                    "Func" => {
                        self.enforce_exact_type_arity("Func", args, 2);
                        let a = self.resolve_required_type_arg(args, 0, "Func", "param0");
                        let b = self.resolve_required_type_arg(args, 1, "Func", "ret");
                        self.interner.intern(Ty::Func {
                            params: vec![a],
                            ret: b,
                        })
                    }
                    _ => self
                        .lookup_generic(name)
                        .unwrap_or_else(|| self.interner.intern(Ty::Nominal(name.clone()))),
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

    fn enforce_exact_type_arity(&mut self, ty_name: &str, args: &[StaticArg], expected: usize) {
        if args.len() != expected {
            self.diagnostics.push(
                self.typecheck_error(
                    "E_TYPE_ARG_ARITY",
                    format!(
                        "{ty_name} expects exactly {expected} static argument(s), got {}",
                        args.len()
                    ),
                )
                .with_hint(
                    "adjust the number of static arguments to match the type constructor arity",
                ),
            );
        }
    }

    fn resolve_required_type_arg(
        &mut self,
        args: &[StaticArg],
        index: usize,
        ty_name: &str,
        slot: &str,
    ) -> TyId {
        match args.get(index) {
            Some(StaticArg::Type(ty)) => self.resolve_type_expr(ty),
            Some(StaticArg::Value(_)) => {
                self.diagnostics.push(
                    self.typecheck_error(
                        "E_TYPE_ARG_KIND",
                        format!(
                            "{ty_name} type argument '{slot}' at index {index} expects a type, got a value"
                        ),
                    )

                    .with_hint("replace the static value with a type argument"),
                );
                self.unknown_ty()
            }
            None => {
                self.diagnostics.push(
                    self.typecheck_error(
                        "E_TYPE_ARG_MISSING",
                        format!(
                            "{ty_name} is missing required type argument '{slot}' at index {index}"
                        ),
                    )
                    .with_hint("provide all required type arguments"),
                );
                self.unknown_ty()
            }
        }
    }

    fn resolve_required_array_size_arg(
        &mut self,
        args: &[StaticArg],
        ty_name: &str,
        slot: &str,
    ) -> u64 {
        match args.get(1) {
            Some(StaticArg::Value(StaticValueExpr::Int(raw))) => match raw.parse::<u64>() {
                Ok(v) => v,
                Err(_) => {
                    self.diagnostics.push(
                        self.typecheck_error(
                            "E_ARRAY_SIZE_INVALID",
                            format!(
                                "{ty_name} {slot} argument must be a valid non-negative integer literal"
                            ),
                        )

                        .with_hint("use an integer literal for array size"),
                    );
                    0
                }
            },
            Some(StaticArg::Value(_)) => {
                self.diagnostics.push(
                    self.typecheck_error(
                        "E_ARRAY_SIZE_KIND",
                        format!("{ty_name} {slot} argument must be an integer literal"),
                    )
                    .with_hint("use form like Array[Int, 4]"),
                );
                0
            }
            Some(StaticArg::Type(_)) => {
                self.diagnostics.push(
                    self.typecheck_error(
                        "E_ARRAY_SIZE_KIND",
                        format!("{ty_name} {slot} argument expects a value, got a type"),
                    )
                    .with_hint("use form like Array[Int, 4]"),
                );
                0
            }
            None => {
                self.diagnostics.push(
                    self.typecheck_error(
                        "E_ARRAY_SIZE_MISSING",
                        format!("{ty_name} is missing required {slot} argument at index 1"),
                    )
                    .with_hint("provide an array size static value"),
                );
                0
            }
        }
    }

    fn infer_call_expr(
        &mut self,
        callee_ty: TyId,
        callee_name: Option<&str>,
        static_args: &[StaticArg],
        args: &[Expr],
        trailing: &[LabeledClosureArg],
        expected_ret: Option<TyId>,
    ) -> TyId {
        self.push_obligation("checking call expression".to_string());
        let callee_ty = self.instantiate_call_callee(callee_ty, callee_name, static_args);
        let total_args = args.len() + trailing.len();
        let expected_params: Vec<TyId> = (0..total_args)
            .map(|_| self.interner.fresh_infer_var(&mut self.next_infer_var))
            .collect();
        let expected_ret = expected_ret
            .map(|t| self.unifier.resolve(t))
            .unwrap_or_else(|| self.interner.fresh_infer_var(&mut self.next_infer_var));
        let expected_func = self.interner.intern(Ty::Func {
            params: expected_params.clone(),
            ret: expected_ret,
        });

        self.unify_with_context(callee_ty, expected_func, "callable expression");

        for (idx, arg) in args.iter().enumerate() {
            self.push_obligation(format!("checking call argument #{idx}"));
            let expected = expected_params[idx];
            let arg_ty = self.infer_expr_with_expected(arg, expected);
            self.require_assignable(expected, arg_ty, "call argument");
            self.pop_obligation();
        }

        for (idx, closure) in trailing.iter().enumerate() {
            let param_idx = args.len() + idx;
            self.push_obligation(format!(
                "checking trailing closure argument '{}' #{}",
                closure.label, idx
            ));
            let expected = expected_params[param_idx];
            let arg_ty = self.infer_expr_with_expected(&closure.body, expected);
            self.require_assignable(expected, arg_ty, "trailing closure argument");
            self.pop_obligation();
        }

        let resolved = self.unifier.resolve(expected_ret);
        self.pop_obligation();
        resolved
    }

    fn infer_if_call_with_expected(
        &mut self,
        args: &[Expr],
        trailing: &[LabeledClosureArg],
        expected: Option<TyId>,
    ) -> TyId {
        if args.len() != 1 {
            self.diagnostics.push(
                self.typecheck_error("E_IF_ARITY", "if expects one runtime argument: condition")
                    .with_hint("use form: if (condition) then { ... } else { ... }"),
            );
            return self.unknown_ty();
        }

        let then_branch = trailing.iter().find(|c| c.label == "then");
        let else_branch = trailing.iter().find(|c| c.label == "else");

        let Some(then_branch) = then_branch else {
            self.diagnostics.push(
                self.typecheck_error("E_IF_FORM", "if requires a labeled 'then' closure")
                    .with_hint("use form: if (condition) then { ... } else { ... }"),
            );
            return self.unknown_ty();
        };

        let cond_ty = self.infer_expr(&args[0]);
        let bool_ty = self.interner.intern(Ty::Bool);
        self.require_assignable(bool_ty, cond_ty, "if condition");

        let then_ty = if let Some(exp) = expected {
            self.infer_expr_with_expected(&then_branch.body, exp)
        } else {
            self.infer_expr(&then_branch.body)
        };

        let Some(else_branch) = else_branch else {
            return then_ty;
        };

        let else_ty = if let Some(exp) = expected {
            self.infer_expr_with_expected(&else_branch.body, exp)
        } else {
            self.infer_expr(&else_branch.body)
        };

        self.join_types(then_ty, else_ty, "if branch join")
    }

    fn infer_cases_call_with_expected(
        &mut self,
        args: &[Expr],
        trailing: &[LabeledClosureArg],
        expected: Option<TyId>,
    ) -> TyId {
        if !args.is_empty() {
            self.diagnostics.push(
                self.typecheck_error("E_CASES_FORM", "cases does not accept runtime arguments")
                    .with_hint("use form: cases when { ... }"),
            );
            return self.unknown_ty();
        }

        let Some(when) = trailing.iter().find(|c| c.label == "when") else {
            self.diagnostics.push(
                self.typecheck_error("E_CASES_FORM", "cases requires labeled 'when' closure")
                    .with_hint("use form: cases when { ... }"),
            );
            return self.unknown_ty();
        };

        let Expr::MultiArm(arms) = TypeChecker::base_expr(&when.body) else {
            self.diagnostics.push(
                self.typecheck_error("E_CASES_FORM", "cases 'when' closure must be multi-arm")
                    .with_hint("use form: cases when { ~cond -> expr, ~true -> default }"),
            );
            return self.unknown_ty();
        };

        self.infer_multi_arm_with_expected(arms, expected)
    }

    fn instantiate_call_callee(
        &mut self,
        callee_ty: TyId,
        callee_name: Option<&str>,
        static_args: &[StaticArg],
    ) -> TyId {
        let Some(name) = callee_name else {
            if !static_args.is_empty() {
                self.diagnostics.push(
                    self.typecheck_error(
                        "E_CALL_STATIC_UNSUPPORTED",
                        "static call arguments require a directly named generic callee",
                    )
                    .with_hint("call a named generic function directly, e.g. f[Int](x)"),
                );
            }
            return callee_ty;
        };

        let Some(generic_params) = self.function_generics.get(name).cloned() else {
            if !static_args.is_empty() {
                self.diagnostics.push(
                    self.typecheck_error(
                        "E_CALL_STATIC_UNEXPECTED",
                        format!(
                            "call provides static arguments, but '{name}' is not a generic function"
                        ),
                    )
                    .with_hint("remove static arguments or call a generic function"),
                );
            }
            return callee_ty;
        };

        if !static_args.is_empty() && static_args.len() != generic_params.len() {
            self.diagnostics.push(
                self.typecheck_error(
                    "E_CALL_STATIC_ARITY",
                    format!(
                        "generic call static-arg arity mismatch for '{name}': expected {} when explicit, got {}",
                        generic_params.len(),
                        static_args.len()
                    ),
                )

                .with_hint("either omit all static args for inference, or provide one per generic parameter"),
            );
        }

        let mut subst = HashMap::new();
        for (idx, param) in generic_params.iter().enumerate() {
            let mapped = static_args
                .get(idx)
                .and_then(|a| self.resolve_static_arg_type(a))
                .unwrap_or_else(|| self.interner.fresh_infer_var(&mut self.next_infer_var));

            for c in &param.constraints {
                match c {
                    GenericConstraint::Interface(interface) => {
                        self.pending_constraints
                            .push(TypeConstraint::InterfaceExists {
                                interface: interface.clone(),
                                context: format!("generic call '{name}' for '{}'", param.name),
                                obligations: self.obligation_stack.clone(),
                                span: self.current_expr_span,
                            });
                        self.pending_constraints
                            .push(TypeConstraint::InterfaceBound {
                                ty: mapped,
                                interface: interface.clone(),
                                context: format!("generic call '{name}' for '{}'", param.name),
                                obligations: self.obligation_stack.clone(),
                                span: self.current_expr_span,
                            });
                    }
                    GenericConstraint::Static(expected) => {
                        self.pending_constraints.push(TypeConstraint::StaticBound {
                            arg: static_args.get(idx).cloned(),
                            param: param.name.clone(),
                            expected: expected.clone(),
                            context: format!("generic call '{name}' for '{}'", param.name),
                            obligations: self.obligation_stack.clone(),
                            span: self.current_expr_span,
                        });
                    }
                }
            }

            subst.insert(param.name.clone(), mapped);
        }

        self.substitute_ty_id(callee_ty, &subst)
    }

    fn substitute_ty_id(&mut self, ty_id: TyId, subst: &HashMap<String, TyId>) -> TyId {
        let resolved = self.unifier.resolve(ty_id);
        let Some(ty) = self.interner.get(resolved).cloned() else {
            return self.unknown_ty();
        };

        match ty {
            Ty::GenericParam(name) => subst
                .get(&name)
                .copied()
                .unwrap_or_else(|| self.interner.intern(Ty::GenericParam(name))),
            Ty::Nominal(name) => subst
                .get(&name)
                .copied()
                .unwrap_or_else(|| self.interner.intern(Ty::Nominal(name))),
            Ty::List(item) => {
                let i = self.substitute_ty_id(item, subst);
                self.interner.intern(Ty::List(i))
            }
            Ty::Dict { key, value } => {
                let k = self.substitute_ty_id(key, subst);
                let v = self.substitute_ty_id(value, subst);
                self.interner.intern(Ty::Dict { key: k, value: v })
            }
            Ty::Set(item) => {
                let i = self.substitute_ty_id(item, subst);
                self.interner.intern(Ty::Set(i))
            }
            Ty::Array { item, size } => {
                let i = self.substitute_ty_id(item, subst);
                self.interner.intern(Ty::Array { item: i, size })
            }
            Ty::Func { params, ret } => {
                let p = params
                    .iter()
                    .map(|x| self.substitute_ty_id(*x, subst))
                    .collect();
                let r = self.substitute_ty_id(ret, subst);
                self.interner.intern(Ty::Func { params: p, ret: r })
            }
            Ty::Tuple(items) => {
                let out = items
                    .iter()
                    .map(|x| self.substitute_ty_id(*x, subst))
                    .collect();
                self.interner.intern(Ty::Tuple(out))
            }
            Ty::Struct(fields) => {
                let out = fields
                    .iter()
                    .map(|(n, t)| (n.clone(), self.substitute_ty_id(*t, subst)))
                    .collect();
                self.interner.intern(Ty::Struct(out))
            }
            other => self.interner.intern(other),
        }
    }

    fn unify_with_context(&mut self, lhs: TyId, rhs: TyId, context: &str) -> TyId {
        if !self.solving_constraints
            && (matches!(
                self.interner.get(lhs),
                Some(Ty::InferVar(_)) | Some(Ty::GenericParam(_))
            ) || matches!(
                self.interner.get(rhs),
                Some(Ty::InferVar(_)) | Some(Ty::GenericParam(_))
            ))
        {
            self.pending_constraints.push(TypeConstraint::Equal {
                lhs,
                rhs,
                context: context.to_string(),
                obligations: self.obligation_stack.clone(),
                span: self.current_expr_span,
            });
        }
        match self.unifier.unify(&mut self.interner, lhs, rhs, context) {
            Ok(id) => id,
            Err(diag) => {
                self.diagnostics
                    .push((*diag).with_obligations(&self.obligation_stack));
                self.unknown_ty()
            }
        }
    }

    fn require_assignable(&mut self, expected: TyId, actual: TyId, context: &str) {
        self.pending_constraints.push(TypeConstraint::Assignable {
            expected,
            actual,
            context: context.to_string(),
            obligations: self.obligation_stack.clone(),
            span: self.current_expr_span,
        });
        if matches!(
            self.conversion_decision(expected, actual, ConversionMode::ImplicitOnly, context),
            ConversionDecision::Identity | ConversionDecision::Coerce
        ) {
            return;
        }

        self.emit_type_mismatch(
            expected,
            actual,
            context,
            "assignment compatibility check failed",
        );
    }

    fn solve_constraints(&mut self) {
        let constraints = std::mem::take(&mut self.pending_constraints);
        self.solving_constraints = true;
        for c in constraints {
            match c {
                TypeConstraint::Equal {
                    lhs,
                    rhs,
                    context,
                    obligations,
                    span,
                } => {
                    let prev_obligations = self.obligation_stack.clone();
                    let prev_span = self.current_expr_span;
                    self.obligation_stack = obligations;
                    self.current_expr_span = span;
                    let _ = self.unify_with_context(lhs, rhs, &context);
                    self.obligation_stack = prev_obligations;
                    self.current_expr_span = prev_span;
                }
                TypeConstraint::InterfaceExists {
                    interface,
                    context,
                    obligations,
                    span,
                } => {
                    if !self.interfaces.contains(&interface) {
                        let prev_obligations = self.obligation_stack.clone();
                        let prev_span = self.current_expr_span;
                        self.obligation_stack = obligations;
                        self.current_expr_span = span;
                        self.diagnostics.push(
                            self.typecheck_error(
                                "E_UNKNOWN_INTERFACE",
                                format!(
                                    "unknown interface constraint '{}' referenced in {}",
                                    interface, context
                                ),
                            )
                            .with_hint("declare the interface or use a known prelude interface"),
                        );
                        self.obligation_stack = prev_obligations;
                        self.current_expr_span = prev_span;
                    }
                }
                TypeConstraint::Assignable {
                    expected,
                    actual,
                    context,
                    obligations,
                    span,
                } => {
                    let prev_obligations = self.obligation_stack.clone();
                    let prev_span = self.current_expr_span;
                    self.obligation_stack = obligations;
                    self.current_expr_span = span;
                    if matches!(
                        self.conversion_decision(
                            expected,
                            actual,
                            ConversionMode::ImplicitOnly,
                            &context,
                        ),
                        ConversionDecision::Identity | ConversionDecision::Coerce
                    ) {
                        self.obligation_stack = prev_obligations;
                        self.current_expr_span = prev_span;
                        continue;
                    }
                    if !self
                        .diagnostics
                        .iter()
                        .any(|d| d.code == "E_TYPE_MISMATCH" && d.message.contains(&context))
                    {
                        self.emit_type_mismatch(
                            expected,
                            actual,
                            &context,
                            "assignment compatibility check failed",
                        );
                    }
                    self.obligation_stack = prev_obligations;
                    self.current_expr_span = prev_span;
                }
                TypeConstraint::InterfaceBound {
                    ty,
                    interface,
                    context,
                    obligations,
                    span,
                } => {
                    let prev_obligations = self.obligation_stack.clone();
                    let prev_span = self.current_expr_span;
                    self.obligation_stack = obligations;
                    self.current_expr_span = span;
                    let ty = self.unifier.resolve(ty);
                    let Some(resolved) = self.interner.get(ty).cloned() else {
                        self.obligation_stack = prev_obligations;
                        self.current_expr_span = prev_span;
                        continue;
                    };

                    if matches!(resolved, Ty::InferVar(_)) {
                        self.obligation_stack = prev_obligations;
                        self.current_expr_span = prev_span;
                        continue;
                    }

                    if !self.satisfies_interface(&resolved, &interface) {
                        self.diagnostics.push(
                            self.typecheck_error(
                                "E_INTERFACE_BOUND_UNSAT",
                                format!(
                                    "type {:?} does not satisfy interface bound '{}' in {}",
                                    resolved, interface, context
                                ),
                            )
                            .with_hint(
                                "provide a type that satisfies the declared interface bound",
                            ),
                        );
                    }
                    self.obligation_stack = prev_obligations;
                    self.current_expr_span = prev_span;
                }
                TypeConstraint::StaticBound {
                    arg,
                    param,
                    expected,
                    context,
                    obligations,
                    span,
                } => match arg {
                    None => {
                        let prev_obligations = self.obligation_stack.clone();
                        let prev_span = self.current_expr_span;
                        self.obligation_stack = obligations;
                        self.current_expr_span = span;
                        self.diagnostics.push(
                            self.typecheck_error(
                                "E_STATIC_ARG_MISSING",
                                format!(
                                    "missing static argument for constrained generic parameter '{}' in {}",
                                    param, context
                                ),
                            )

                            .with_hint("provide a compile-time value for the static constrained parameter"),
                        );
                        self.obligation_stack = prev_obligations;
                        self.current_expr_span = prev_span;
                    }
                    Some(StaticArg::Value(_)) => {}
                    Some(StaticArg::Type(_)) => {
                        let prev_obligations = self.obligation_stack.clone();
                        let prev_span = self.current_expr_span;
                        self.obligation_stack = obligations;
                        self.current_expr_span = span;
                        self.diagnostics.push(
                            self.typecheck_error(
                                "E_STATIC_ARG_KIND",
                                format!(
                                    "expected compile-time static value for constraint {:?} in {}",
                                    expected, context
                                ),
                            )
                            .with_hint("replace type argument with compile-time value"),
                        );
                        self.obligation_stack = prev_obligations;
                        self.current_expr_span = prev_span;
                    }
                },
            }
        }
        self.solving_constraints = false;
    }

    fn to_function_generic_info(&self, param: &StaticParam) -> FunctionGenericInfo {
        let constraints = match &param.kind {
            StaticParamKind::Type => Vec::new(),
            StaticParamKind::Constraint(TypeExpr::Static(inner)) => {
                vec![GenericConstraint::Static((**inner).clone())]
            }
            StaticParamKind::Constraint(TypeExpr::Named { name, args: _ }) => {
                vec![GenericConstraint::Interface(name.clone())]
            }
            StaticParamKind::Constraint(other) => {
                vec![GenericConstraint::Interface(format!("{:?}", other))]
            }
        };
        FunctionGenericInfo {
            name: param.name.clone(),
            constraints,
        }
    }

    fn satisfies_interface(&self, ty: &Ty, interface: &str) -> bool {
        match interface {
            "Eq" => matches!(
                ty,
                Ty::Bool
                    | Ty::Char
                    | Ty::Int8
                    | Ty::Int16
                    | Ty::Int32
                    | Ty::Int64
                    | Ty::Int128
                    | Ty::UInt8
                    | Ty::UInt16
                    | Ty::UInt32
                    | Ty::UInt64
                    | Ty::UInt128
                    | Ty::Nominal(_)
            ),
            "Show" | "ToStr" => !matches!(ty, Ty::Never),
            "Hash" | "Hasheable" => matches!(
                ty,
                Ty::Bool
                    | Ty::Char
                    | Ty::Int8
                    | Ty::Int16
                    | Ty::Int32
                    | Ty::Int64
                    | Ty::Int128
                    | Ty::UInt8
                    | Ty::UInt16
                    | Ty::UInt32
                    | Ty::UInt64
                    | Ty::UInt128
                    | Ty::Nominal(_)
            ),
            "Iterable" => matches!(ty, Ty::List(_) | Ty::Array { .. } | Ty::Set(_)),
            "From" => matches!(ty, Ty::Func { .. } | Ty::Nominal(_)),
            _ => false,
        }
    }

    fn coerce_or_cast_for_ir(
        &mut self,
        expected: TyId,
        actual: TyId,
        expr: CheckedExpr,
        context: &str,
        mode: ConversionMode,
    ) -> CheckedExpr {
        match self.conversion_decision(expected, actual, mode, context) {
            ConversionDecision::Identity => expr,
            ConversionDecision::Coerce => CheckedExpr::Coerce {
                from: actual,
                to: expected,
                expr: Box::new(expr),
            },
            ConversionDecision::Cast => CheckedExpr::Cast {
                from: actual,
                to: expected,
                expr: Box::new(expr),
            },
            ConversionDecision::Incompatible => {
                self.emit_type_mismatch(
                    expected,
                    actual,
                    context,
                    "IR coercion/cast decision failed",
                );
                expr
            }
        }
    }

    fn conversion_decision(
        &mut self,
        expected: TyId,
        actual: TyId,
        mode: ConversionMode,
        context: &str,
    ) -> ConversionDecision {
        let expected = self.unifier.resolve(expected);
        let actual = self.unifier.resolve(actual);
        if expected == actual {
            return ConversionDecision::Identity;
        }

        let Some(expected_ty) = self.interner.get(expected).cloned() else {
            return ConversionDecision::Incompatible;
        };
        let Some(actual_ty) = self.interner.get(actual).cloned() else {
            return ConversionDecision::Incompatible;
        };

        if matches!(expected_ty, Ty::Any) || matches!(actual_ty, Ty::Any) {
            return ConversionDecision::Identity;
        }

        if matches!(expected_ty, Ty::InferVar(_)) || matches!(actual_ty, Ty::InferVar(_)) {
            let _ = self.unify_with_context(expected, actual, context);
            return ConversionDecision::Identity;
        }

        if matches!(mode, ConversionMode::ImplicitOnly)
            && matches!(
                (&expected_ty, &actual_ty),
                (
                    Ty::Float32 | Ty::Float64,
                    Ty::Int8 | Ty::Int16 | Ty::Int32 | Ty::Int64 | Ty::Int128
                ) | (
                    Ty::Float32 | Ty::Float64,
                    Ty::UInt8 | Ty::UInt16 | Ty::UInt32 | Ty::UInt64 | Ty::UInt128
                )
            )
        {
            return ConversionDecision::Incompatible;
        }

        if can_implicitly_widen(&actual_ty, &expected_ty) {
            return ConversionDecision::Coerce;
        }

        if matches!(mode, ConversionMode::ExplicitCastAllowed)
            && self.is_explicit_cast_pair(&actual_ty, &expected_ty)
        {
            return ConversionDecision::Cast;
        }

        ConversionDecision::Incompatible
    }

    fn emit_type_mismatch(&mut self, expected: TyId, actual: TyId, context: &str, related: &str) {
        let expected = self.unifier.resolve(expected);
        let actual = self.unifier.resolve(actual);
        let Some(expected_ty) = self.interner.get(expected).cloned() else {
            return;
        };
        let Some(actual_ty) = self.interner.get(actual).cloned() else {
            return;
        };
        let mut diag = self.typecheck_error(
            "E_TYPE_MISMATCH",
            format!(
                "type mismatch in {context}: expected {:?}, got {:?}",
                expected_ty, actual_ty
            ),
        );
        diag = diag.with_related(related, None);
        self.diagnostics.push(
            diag.with_hint(
                "use an explicit cast for narrowing or cross-domain numeric conversions",
            ),
        );
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

    fn typecheck_error(&self, code: &'static str, message: impl Into<String>) -> Diagnostic {
        Diagnostic::error(code, message)
            .with_stage(Stage::Typecheck)
            .with_span_opt(self.current_expr_span)
            .with_obligations(&self.obligation_stack)
    }

    fn typecheck_warning(&self, code: &'static str, message: impl Into<String>) -> Diagnostic {
        Diagnostic::warning(code, message)
            .with_stage(Stage::Typecheck)
            .with_span_opt(self.current_expr_span)
            .with_obligations(&self.obligation_stack)
    }

    fn unknown_ty(&mut self) -> TyId {
        self.interner.fresh_infer_var(&mut self.next_infer_var)
    }

    fn missing_ty_fallback(&mut self) -> Ty {
        let idx = self.next_infer_var;
        self.next_infer_var += 1;
        Ty::InferVar(idx)
    }

    fn push_scope(&mut self) {
        self.value_env_scopes.push(HashMap::new());
    }

    fn push_generic_scope(&mut self) {
        self.generic_env_scopes.push(HashMap::new());
    }

    fn pop_scope(&mut self) {
        if self.value_env_scopes.len() > 1 {
            let _ = self.value_env_scopes.pop();
        }
    }

    fn pop_generic_scope(&mut self) {
        if self.generic_env_scopes.len() > 1 {
            let _ = self.generic_env_scopes.pop();
        }
    }

    fn insert_value(&mut self, name: String, ty: TyId) {
        if let Some(scope) = self.value_env_scopes.last_mut() {
            scope.insert(name, ty);
        }
    }

    fn insert_generic(&mut self, name: String, ty: TyId) {
        if let Some(scope) = self.generic_env_scopes.last_mut() {
            scope.insert(name, ty);
        }
    }

    fn bind_arm_patterns(&mut self, patterns: &[Pattern]) {
        for pattern in patterns {
            self.bind_pattern(pattern);
        }
    }

    fn infer_arm_guard(&mut self, guard: Option<&Expr>) {
        let Some(guard) = guard else {
            return;
        };
        let bool_ty = self.interner.intern(Ty::Bool);
        let guard_ty = self.infer_expr_with_expected(guard, bool_ty);
        self.require_assignable(bool_ty, guard_ty, "arm guard");
    }

    fn bind_pattern(&mut self, pattern: &Pattern) {
        match pattern {
            Pattern::Ident(name) if name != "true" && name != "false" => {
                let ty = self.interner.fresh_infer_var(&mut self.next_infer_var);
                self.insert_value(name.clone(), ty);
            }
            Pattern::DotVariant { payload, .. } => {
                if let Some(inner) = payload.as_ref() {
                    self.bind_pattern(inner);
                }
            }
            _ => {}
        }
    }

    fn lookup_value(&self, name: &str) -> Option<TyId> {
        self.value_env_scopes
            .iter()
            .rev()
            .find_map(|scope| scope.get(name).copied())
    }

    fn lookup_generic(&self, name: &str) -> Option<TyId> {
        self.generic_env_scopes
            .iter()
            .rev()
            .find_map(|scope| scope.get(name).copied())
    }

    fn lower_expr(&mut self, expr: &Expr) -> CheckedExpr {
        match expr {
            Expr::Spanned { expr, .. } => self.lower_expr(expr),
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
            Expr::Cast { expr, ty } => {
                let source_ty = self.preview_expr_ty(expr);
                let target_ty = self.resolve_type_expr(ty);
                match self.conversion_decision(
                    target_ty,
                    source_ty,
                    ConversionMode::ExplicitCastAllowed,
                    "cast expression",
                ) {
                    ConversionDecision::Identity => self.lower_expr(expr),
                    ConversionDecision::Coerce => CheckedExpr::Coerce {
                        from: source_ty,
                        to: target_ty,
                        expr: Box::new(self.lower_expr(expr)),
                    },
                    ConversionDecision::Cast | ConversionDecision::Incompatible => {
                        CheckedExpr::Cast {
                            from: source_ty,
                            to: target_ty,
                            expr: Box::new(self.lower_expr(expr)),
                        }
                    }
                }
            }
            Expr::MacroApply {
                macro_name,
                operand,
                static_args,
            } if macro_name == "if" => {
                if let Expr::List(items) = TypeChecker::base_expr(operand.as_ref()) {
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
                CheckedExpr::MacroApply {
                    macro_name: macro_name.clone(),
                    static_args: static_args
                        .iter()
                        .map(|arg| self.lower_static_arg(arg))
                        .collect(),
                    operand: Box::new(self.lower_expr(operand)),
                }
            }
            Expr::MacroApply {
                macro_name,
                operand,
                static_args,
            } if macro_name == "cases" => {
                if let Expr::MultiArm(arms) = TypeChecker::base_expr(operand.as_ref()) {
                    return CheckedExpr::Cases {
                        arms: arms.iter().map(|a| self.lower_expr(&a.body)).collect(),
                    };
                }
                CheckedExpr::MacroApply {
                    macro_name: macro_name.clone(),
                    static_args: static_args
                        .iter()
                        .map(|arg| self.lower_static_arg(arg))
                        .collect(),
                    operand: Box::new(self.lower_expr(operand)),
                }
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
                    .unwrap_or_else(|| self.unknown_ty());
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
                if let Expr::List(items) = TypeChecker::base_expr(operand.as_ref()) {
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
                    .map(|arg| self.lower_static_arg(arg))
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
            Expr::Member { object, field } => CheckedExpr::DotIdent {
                name: field.clone(),
                payload: Some(Box::new(self.lower_expr(object))),
            },
            Expr::Binary { op, lhs, rhs } => {
                if let Some(kind) = self.parsed_binary_op_kind(*op) {
                    let lhs_lowered = self.lower_expr(lhs);
                    let rhs_lowered = self.lower_expr(rhs);
                    let ty = self.preview_expr_ty(expr);
                    CheckedExpr::BinaryOp {
                        op: kind,
                        lhs: Box::new(lhs_lowered),
                        rhs: Box::new(rhs_lowered),
                        ty,
                    }
                } else if matches!(op, ParsedBinaryOp::Colon) {
                    let from = self.preview_expr_ty(lhs);
                    if let Expr::TypeExpr(target_ty_expr) = TypeChecker::base_expr(rhs.as_ref()) {
                        let to = self.resolve_type_expr(target_ty_expr);
                        let lowered_expr = self.lower_expr(lhs);
                        CheckedExpr::Cast {
                            from,
                            to,
                            expr: Box::new(lowered_expr),
                        }
                    } else {
                        CheckedExpr::MacroApply {
                            macro_name: "binary".to_string(),
                            static_args: Vec::new(),
                            operand: Box::new(CheckedExpr::List(vec![
                                self.lower_expr(lhs),
                                self.lower_expr(rhs),
                            ])),
                        }
                    }
                } else {
                    CheckedExpr::MacroApply {
                        macro_name: "binary".to_string(),
                        static_args: Vec::new(),
                        operand: Box::new(CheckedExpr::List(vec![
                            self.lower_expr(lhs),
                            self.lower_expr(rhs),
                        ])),
                    }
                }
            }
            Expr::TypeExpr(_) => CheckedExpr::Any,
        }
    }

    fn preview_expr_ty(&mut self, expr: &Expr) -> TyId {
        match expr {
            Expr::Spanned { expr, .. } => self.preview_expr_ty(expr),
            Expr::Ident(name) => self.lookup_value(name).unwrap_or_else(|| {
                if name == "true" || name == "false" {
                    self.interner.intern(Ty::Bool)
                } else {
                    self.unknown_ty()
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
                    .unwrap_or_else(|| self.interner.fresh_infer_var(&mut self.next_infer_var));
                self.interner.intern(Ty::Func {
                    params: param_tys,
                    ret,
                })
            }
            Expr::Cast { expr, ty } => {
                let source = self.preview_expr_ty(expr);
                let target = self.resolve_type_expr(ty);
                match self.conversion_decision(
                    target,
                    source,
                    ConversionMode::ExplicitCastAllowed,
                    "cast expression",
                ) {
                    ConversionDecision::Identity
                    | ConversionDecision::Coerce
                    | ConversionDecision::Cast => target,
                    ConversionDecision::Incompatible => self.unknown_ty(),
                }
            }
            Expr::Member { object, .. } => self.preview_expr_ty(object),
            Expr::Binary { op, lhs, rhs } => self.infer_binary_expr(*op, lhs, rhs),
            Expr::TypeExpr(_) => self.unknown_ty(),
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
    use super::TypeChecker;
    use crate::checked_ir::{CheckedExpr, CheckedStaticArg, CheckedStaticValue};
    use crate::types::Ty;
    use aura_frontend::ast::{
        BinaryOp as ParsedBinaryOp, Decl, Expr, FunctionDecl, LabeledClosureArg, Pattern, Program,
        StaticArg, StaticParam, StaticParamKind, StaticValueExpr, TypeExpr,
    };

    fn ty_param(name: &str) -> StaticParam {
        StaticParam {
            name: name.to_string(),
            kind: StaticParamKind::Type,
        }
    }

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
                    guard: None,
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
                        guard: None,
                        body: Expr::Ident("x".to_string()),
                    },
                    aura_frontend::ast::Arm {
                        patterns: vec![Pattern::Ident("later".to_string())],
                        guard: None,
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

                    trailing: Vec::new(),
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
                        guard: None,
                        body: Expr::Int("1".to_string()),
                    },
                    aura_frontend::ast::Arm {
                        patterns: vec![Pattern::Wildcard],
                        guard: None,
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

                        trailing: Vec::new(),
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

                    trailing: Vec::new(),
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
    fn numeric_operator_requires_numeric_operands() {
        let program = Program {
            declarations: vec![Decl::Assign {
                name: "x".to_string(),
                value: Expr::Binary {
                    op: ParsedBinaryOp::Add,
                    lhs: Box::new(Expr::String("a".to_string())),
                    rhs: Box::new(Expr::Int("1".to_string())),
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
                name: "y".to_string(),
                value: Expr::MacroApply {
                    macro_name: "builtin".to_string(),
                    static_args: vec![StaticArg::Value(StaticValueExpr::Int("4".to_string()))],
                    operand: Box::new(Expr::Ident("io_write".to_string())),
                },
            }],
        };

        let checked = check_module(&program);
        let module = checked.module.expect("module should exist");
        let CheckedExpr::MacroApply { static_args, .. } = &module.ir.declarations[0].value else {
            panic!("expected macro apply in IR")
        };
        assert_eq!(static_args.len(), 1);
        assert!(matches!(
            static_args[0],
            CheckedStaticArg::Value(CheckedStaticValue::Int(ref v)) if v == "4"
        ));
    }

    #[test]
    fn if_call_typechecks_with_labeled_closures() {
        let program = Program {
            declarations: vec![Decl::Assign {
                name: "x".to_string(),
                value: Expr::Call {
                    callee: Box::new(Expr::Ident("if".to_string())),
                    static_args: Vec::new(),
                    args: vec![Expr::Ident("true".to_string())],
                    trailing: vec![
                        LabeledClosureArg {
                            label: "then".to_string(),
                            body: Expr::Int("1".to_string()),
                        },
                        LabeledClosureArg {
                            label: "else".to_string(),
                            body: Expr::Int("2".to_string()),
                        },
                    ],
                },
            }],
        };

        let checked = check_module(&program);
        let module = checked.module.expect("module should exist");
        assert!(matches!(
            module.ir.declarations[0].value,
            CheckedExpr::Call { .. }
        ));
        let x_ty = module.value_types.get("x").expect("x should exist");
        assert!(matches!(module.types.get(*x_ty), Some(Ty::Int32)));
    }

    #[test]
    fn cases_call_typechecks_with_when_closure() {
        let program = Program {
            declarations: vec![Decl::Assign {
                name: "x".to_string(),
                value: Expr::Call {
                    callee: Box::new(Expr::Ident("cases".to_string())),
                    static_args: Vec::new(),
                    args: Vec::new(),
                    trailing: vec![LabeledClosureArg {
                        label: "when".to_string(),
                        body: Expr::MultiArm(vec![
                            aura_frontend::ast::Arm {
                                patterns: vec![Pattern::Ident("true".to_string())],
                                guard: None,
                                body: Expr::Int("1".to_string()),
                            },
                            aura_frontend::ast::Arm {
                                patterns: vec![Pattern::Wildcard],
                                guard: None,
                                body: Expr::Int("2".to_string()),
                            },
                        ]),
                    }],
                },
            }],
        };

        let checked = check_module(&program);
        let module = checked.module.expect("module should exist");
        assert!(matches!(
            module.ir.declarations[0].value,
            CheckedExpr::Call { .. }
        ));
        let x_ty = module.value_types.get("x").expect("x should exist");
        assert!(matches!(module.types.get(*x_ty), Some(Ty::Int32)));
    }

    #[test]
    fn if_macro_form_is_rejected() {
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
        assert!(checked.module.is_none());
        assert!(checked.diagnostics.iter().any(|d| d.code == "E_IF_FORM"));
    }

    #[test]
    fn cases_macro_form_is_rejected() {
        let program = Program {
            declarations: vec![Decl::Assign {
                name: "x".to_string(),
                value: Expr::MacroApply {
                    macro_name: "cases".to_string(),
                    static_args: Vec::new(),
                    operand: Box::new(Expr::MultiArm(vec![
                        aura_frontend::ast::Arm {
                            patterns: vec![Pattern::Ident("a".to_string())],
                            guard: None,
                            body: Expr::Int("1".to_string()),
                        },
                        aura_frontend::ast::Arm {
                            patterns: vec![Pattern::Wildcard],
                            guard: None,
                            body: Expr::Int("2".to_string()),
                        },
                    ])),
                },
            }],
        };

        let checked = check_module(&program);
        assert!(checked.module.is_none());
        assert!(checked.diagnostics.iter().any(|d| d.code == "E_CASES_FORM"));
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

    #[test]
    fn builtin_macro_produces_function_type() {
        let program = Program {
            declarations: vec![Decl::Assign {
                name: "w".to_string(),
                value: Expr::MacroApply {
                    macro_name: "builtin".to_string(),
                    static_args: Vec::new(),
                    operand: Box::new(Expr::Ident("io_write".to_string())),
                },
            }],
        };

        let checked = check_module(&program);
        let module = checked.module.expect("module should exist");
        let ty_id = module
            .value_types
            .get("w")
            .expect("value type should exist");
        let ty = module.types.get(*ty_id).expect("type should exist");
        assert!(matches!(ty, Ty::Func { .. }));
    }

    #[test]
    fn dot_identifier_without_payload_is_void_typed() {
        let program = Program {
            declarations: vec![Decl::Assign {
                name: "v".to_string(),
                value: Expr::DotIdent {
                    name: "null".to_string(),
                    payload: None,
                },
            }],
        };

        let checked = check_module(&program);
        let module = checked.module.expect("module should exist");
        let ty_id = module
            .value_types
            .get("v")
            .expect("value type should exist");
        let ty = module.types.get(*ty_id).expect("type should exist");
        assert!(matches!(ty, Ty::Void));
    }

    #[test]
    fn function_params_are_available_in_body_scope() {
        let program = Program {
            declarations: vec![Decl::Function(FunctionDecl {
                static_params: Vec::new(),
                receiver: None,
                name: "id".to_string(),
                params: vec![aura_frontend::ast::Param {
                    name: "x".to_string(),
                    ty: TypeExpr::Named {
                        name: "Int".to_string(),
                        args: Vec::new(),
                    },
                }],
                return_type: TypeExpr::Named {
                    name: "Int".to_string(),
                    args: Vec::new(),
                },
                body: Expr::Ident("x".to_string()),
            })],
        };

        let checked = check_module(&program);
        assert!(checked.module.is_some());
        assert!(!checked
            .diagnostics
            .iter()
            .any(|d| d.code == "W_UNRESOLVED_IDENT"));
    }

    #[test]
    fn function_param_scope_does_not_leak_to_global() {
        let program = Program {
            declarations: vec![
                Decl::Function(FunctionDecl {
                    static_params: Vec::new(),
                    receiver: None,
                    name: "id".to_string(),
                    params: vec![aura_frontend::ast::Param {
                        name: "x".to_string(),
                        ty: TypeExpr::Named {
                            name: "Int".to_string(),
                            args: Vec::new(),
                        },
                    }],
                    return_type: TypeExpr::Named {
                        name: "Int".to_string(),
                        args: Vec::new(),
                    },
                    body: Expr::Ident("x".to_string()),
                }),
                Decl::Assign {
                    name: "z".to_string(),
                    value: Expr::Ident("x".to_string()),
                },
            ],
        };

        let checked = check_module(&program);
        assert!(checked.module.is_some());
        assert!(checked
            .diagnostics
            .iter()
            .any(|d| d.code == "W_UNRESOLVED_IDENT"));
    }

    #[test]
    fn multi_arm_pattern_identifier_is_scoped_to_arm_body() {
        let program = Program {
            declarations: vec![Decl::Assign {
                name: "m".to_string(),
                value: Expr::MultiArm(vec![
                    aura_frontend::ast::Arm {
                        patterns: vec![Pattern::Ident("v".to_string())],
                        guard: None,
                        body: Expr::Ident("v".to_string()),
                    },
                    aura_frontend::ast::Arm {
                        patterns: vec![Pattern::Wildcard],
                        guard: None,
                        body: Expr::Int("1".to_string()),
                    },
                ]),
            }],
        };

        let checked = check_module(&program);
        assert!(checked.module.is_some());
        assert!(!checked
            .diagnostics
            .iter()
            .any(|d| d.code == "W_UNRESOLVED_IDENT"));
    }

    #[test]
    fn pattern_identifier_does_not_leak_outside_multi_arm() {
        let program = Program {
            declarations: vec![
                Decl::Assign {
                    name: "m".to_string(),
                    value: Expr::MultiArm(vec![
                        aura_frontend::ast::Arm {
                            patterns: vec![Pattern::Ident("v".to_string())],
                            guard: None,
                            body: Expr::Ident("v".to_string()),
                        },
                        aura_frontend::ast::Arm {
                            patterns: vec![Pattern::Wildcard],
                            guard: None,
                            body: Expr::Int("1".to_string()),
                        },
                    ]),
                },
                Decl::Assign {
                    name: "z".to_string(),
                    value: Expr::Ident("v".to_string()),
                },
            ],
        };

        let checked = check_module(&program);
        assert!(checked.module.is_some());
        assert!(checked
            .diagnostics
            .iter()
            .any(|d| d.code == "W_UNRESOLVED_IDENT"));
    }

    #[test]
    fn generic_function_call_static_arg_instantiates_signature() {
        let program = Program {
            declarations: vec![
                Decl::Function(FunctionDecl {
                    static_params: vec![ty_param("T")],
                    receiver: None,
                    name: "id".to_string(),
                    params: vec![aura_frontend::ast::Param {
                        name: "x".to_string(),
                        ty: TypeExpr::Named {
                            name: "T".to_string(),
                            args: Vec::new(),
                        },
                    }],
                    return_type: TypeExpr::Named {
                        name: "T".to_string(),
                        args: Vec::new(),
                    },
                    body: Expr::Ident("x".to_string()),
                }),
                Decl::Assign {
                    name: "y".to_string(),
                    value: Expr::Call {
                        callee: Box::new(Expr::Ident("id".to_string())),
                        static_args: vec![StaticArg::Type(TypeExpr::Named {
                            name: "Int".to_string(),
                            args: Vec::new(),
                        })],
                        args: vec![Expr::Int("1".to_string())],

                        trailing: Vec::new(),
                    },
                },
            ],
        };

        let checked = check_module(&program);
        assert!(checked.module.is_some());
        let module = checked.module.expect("module should exist");
        let ty_id = module
            .value_types
            .get("y")
            .expect("value type should exist");
        let ty = module.types.get(*ty_id).expect("type should exist");
        assert!(matches!(ty, Ty::Int32));
    }

    #[test]
    fn static_args_on_non_generic_call_report_diagnostic() {
        let program = Program {
            declarations: vec![
                Decl::Function(FunctionDecl {
                    static_params: Vec::new(),
                    receiver: None,
                    name: "f".to_string(),
                    params: vec![aura_frontend::ast::Param {
                        name: "x".to_string(),
                        ty: TypeExpr::Named {
                            name: "Int".to_string(),
                            args: Vec::new(),
                        },
                    }],
                    return_type: TypeExpr::Named {
                        name: "Int".to_string(),
                        args: Vec::new(),
                    },
                    body: Expr::Ident("x".to_string()),
                }),
                Decl::Assign {
                    name: "y".to_string(),
                    value: Expr::Call {
                        callee: Box::new(Expr::Ident("f".to_string())),
                        static_args: vec![StaticArg::Type(TypeExpr::Named {
                            name: "Int".to_string(),
                            args: Vec::new(),
                        })],
                        args: vec![Expr::Int("1".to_string())],

                        trailing: Vec::new(),
                    },
                },
            ],
        };

        let checked = check_module(&program);
        assert!(checked.module.is_none());
        assert!(checked
            .diagnostics
            .iter()
            .any(|d| d.code == "E_CALL_STATIC_UNEXPECTED"));
    }

    #[test]
    fn generic_call_with_missing_static_arg_reports_arity_error() {
        let program = Program {
            declarations: vec![
                Decl::Function(FunctionDecl {
                    static_params: vec![ty_param("T")],
                    receiver: None,
                    name: "id".to_string(),
                    params: vec![aura_frontend::ast::Param {
                        name: "x".to_string(),
                        ty: TypeExpr::Named {
                            name: "T".to_string(),
                            args: Vec::new(),
                        },
                    }],
                    return_type: TypeExpr::Named {
                        name: "T".to_string(),
                        args: Vec::new(),
                    },
                    body: Expr::Ident("x".to_string()),
                }),
                Decl::Assign {
                    name: "y".to_string(),
                    value: Expr::Call {
                        callee: Box::new(Expr::Ident("id".to_string())),
                        static_args: vec![StaticArg::Type(TypeExpr::Named {
                            name: "Int".to_string(),
                            args: Vec::new(),
                        })],
                        args: vec![Expr::Int("1".to_string())],

                        trailing: Vec::new(),
                    },
                },
                Decl::Assign {
                    name: "z".to_string(),
                    value: Expr::Call {
                        callee: Box::new(Expr::Ident("id".to_string())),
                        static_args: Vec::new(),
                        args: vec![Expr::Int("2".to_string())],

                        trailing: Vec::new(),
                    },
                },
            ],
        };

        let checked = check_module(&program);
        assert!(checked.module.is_some());
        assert!(!checked
            .diagnostics
            .iter()
            .any(|d| d.code == "E_CALL_STATIC_ARITY"));
    }

    #[test]
    fn generic_call_partial_explicit_args_report_arity_error() {
        let program = Program {
            declarations: vec![
                Decl::Function(FunctionDecl {
                    static_params: vec![ty_param("T"), ty_param("U")],
                    receiver: None,
                    name: "pair_first".to_string(),
                    params: vec![aura_frontend::ast::Param {
                        name: "x".to_string(),
                        ty: TypeExpr::Named {
                            name: "T".to_string(),
                            args: Vec::new(),
                        },
                    }],
                    return_type: TypeExpr::Named {
                        name: "T".to_string(),
                        args: Vec::new(),
                    },
                    body: Expr::Ident("x".to_string()),
                }),
                Decl::Assign {
                    name: "y".to_string(),
                    value: Expr::Call {
                        callee: Box::new(Expr::Ident("pair_first".to_string())),
                        static_args: vec![StaticArg::Type(TypeExpr::Named {
                            name: "Int".to_string(),
                            args: Vec::new(),
                        })],
                        args: vec![Expr::Int("1".to_string())],

                        trailing: Vec::new(),
                    },
                },
            ],
        };

        let checked = check_module(&program);
        assert!(checked.module.is_none());
        assert!(checked
            .diagnostics
            .iter()
            .any(|d| d.code == "E_CALL_STATIC_ARITY"));
    }

    #[test]
    fn empty_list_in_call_argument_uses_expected_element_type() {
        let program = Program {
            declarations: vec![
                Decl::Function(FunctionDecl {
                    static_params: Vec::new(),
                    receiver: None,
                    name: "takes_list".to_string(),
                    params: vec![aura_frontend::ast::Param {
                        name: "xs".to_string(),
                        ty: TypeExpr::Named {
                            name: "List".to_string(),
                            args: vec![StaticArg::Type(TypeExpr::Named {
                                name: "Int".to_string(),
                                args: Vec::new(),
                            })],
                        },
                    }],
                    return_type: TypeExpr::Named {
                        name: "Int".to_string(),
                        args: Vec::new(),
                    },
                    body: Expr::Int("0".to_string()),
                }),
                Decl::Assign {
                    name: "y".to_string(),
                    value: Expr::Call {
                        callee: Box::new(Expr::Ident("takes_list".to_string())),
                        static_args: Vec::new(),
                        args: vec![Expr::List(Vec::new())],

                        trailing: Vec::new(),
                    },
                },
            ],
        };

        let checked = check_module(&program);
        assert!(checked.module.is_some());
        assert!(!checked
            .diagnostics
            .iter()
            .any(|d| d.code == "E_TYPE_MISMATCH"));
    }

    #[test]
    fn empty_dict_in_call_argument_uses_expected_key_value_types() {
        let program = Program {
            declarations: vec![
                Decl::Function(FunctionDecl {
                    static_params: Vec::new(),
                    receiver: None,
                    name: "takes_dict".to_string(),
                    params: vec![aura_frontend::ast::Param {
                        name: "m".to_string(),
                        ty: TypeExpr::Named {
                            name: "Dict".to_string(),
                            args: vec![
                                StaticArg::Type(TypeExpr::Named {
                                    name: "Int".to_string(),
                                    args: Vec::new(),
                                }),
                                StaticArg::Type(TypeExpr::Named {
                                    name: "Float".to_string(),
                                    args: Vec::new(),
                                }),
                            ],
                        },
                    }],
                    return_type: TypeExpr::Named {
                        name: "Int".to_string(),
                        args: Vec::new(),
                    },
                    body: Expr::Int("0".to_string()),
                }),
                Decl::Assign {
                    name: "y".to_string(),
                    value: Expr::Call {
                        callee: Box::new(Expr::Ident("takes_dict".to_string())),
                        static_args: Vec::new(),
                        args: vec![Expr::Dict(Vec::new())],

                        trailing: Vec::new(),
                    },
                },
            ],
        };

        let checked = check_module(&program);
        assert!(checked.module.is_some());
        assert!(!checked
            .diagnostics
            .iter()
            .any(|d| d.code == "E_TYPE_MISMATCH"));
    }

    #[test]
    fn expected_type_guides_if_macro_branches() {
        let program = Program {
            declarations: vec![Decl::Function(FunctionDecl {
                static_params: Vec::new(),
                receiver: None,
                name: "pick".to_string(),
                params: vec![aura_frontend::ast::Param {
                    name: "cond".to_string(),
                    ty: TypeExpr::Named {
                        name: "Bool".to_string(),
                        args: Vec::new(),
                    },
                }],
                return_type: TypeExpr::Named {
                    name: "List".to_string(),
                    args: vec![StaticArg::Type(TypeExpr::Named {
                        name: "Int".to_string(),
                        args: Vec::new(),
                    })],
                },
                body: Expr::Call {
                    callee: Box::new(Expr::Ident("if".to_string())),
                    static_args: Vec::new(),
                    args: vec![Expr::Ident("cond".to_string())],
                    trailing: vec![
                        LabeledClosureArg {
                            label: "then".to_string(),
                            body: Expr::List(Vec::new()),
                        },
                        LabeledClosureArg {
                            label: "else".to_string(),
                            body: Expr::List(vec![Expr::Int("1".to_string())]),
                        },
                    ],
                },
            })],
        };

        let checked = check_module(&program);
        assert!(checked.module.is_some());
        assert!(!checked
            .diagnostics
            .iter()
            .any(|d| d.code == "E_TYPE_MISMATCH"));
    }

    #[test]
    fn expected_type_guides_cases_arm_bodies() {
        let program = Program {
            declarations: vec![Decl::Function(FunctionDecl {
                static_params: Vec::new(),
                receiver: None,
                name: "pick_case".to_string(),
                params: vec![aura_frontend::ast::Param {
                    name: "cond".to_string(),
                    ty: TypeExpr::Named {
                        name: "Bool".to_string(),
                        args: Vec::new(),
                    },
                }],
                return_type: TypeExpr::Named {
                    name: "Dict".to_string(),
                    args: vec![
                        StaticArg::Type(TypeExpr::Named {
                            name: "Int".to_string(),
                            args: Vec::new(),
                        }),
                        StaticArg::Type(TypeExpr::Named {
                            name: "Float".to_string(),
                            args: Vec::new(),
                        }),
                    ],
                },
                body: Expr::Call {
                    callee: Box::new(Expr::Ident("cases".to_string())),
                    static_args: Vec::new(),
                    args: Vec::new(),
                    trailing: vec![LabeledClosureArg {
                        label: "when".to_string(),
                        body: Expr::MultiArm(vec![
                            aura_frontend::ast::Arm {
                                patterns: vec![Pattern::Ident("true".to_string())],
                                guard: None,
                                body: Expr::Dict(Vec::new()),
                            },
                            aura_frontend::ast::Arm {
                                patterns: vec![Pattern::Wildcard],
                                guard: None,
                                body: Expr::Dict(vec![(
                                    Expr::Int("1".to_string()),
                                    Expr::Float("1.0".to_string()),
                                )]),
                            },
                        ]),
                    }],
                },
            })],
        };

        let checked = check_module(&program);
        assert!(checked.module.is_some());
        assert!(!checked
            .diagnostics
            .iter()
            .any(|d| d.code == "E_TYPE_MISMATCH"));
    }

    #[test]
    fn arm_guard_must_typecheck_as_bool() {
        let program = Program {
            declarations: vec![Decl::Assign {
                name: "m".to_string(),
                value: Expr::MultiArm(vec![
                    aura_frontend::ast::Arm {
                        patterns: vec![Pattern::Ident("x".to_string())],
                        guard: Some(Expr::Int("1".to_string())),
                        body: Expr::Int("1".to_string()),
                    },
                    aura_frontend::ast::Arm {
                        patterns: vec![],
                        guard: None,
                        body: Expr::Int("2".to_string()),
                    },
                ]),
            }],
        };

        let checked = check_module(&program);
        assert!(checked.module.is_none());
        assert!(checked
            .diagnostics
            .iter()
            .any(|d| d.code == "E_TYPE_MISMATCH"));
    }

    #[test]
    fn expected_list_type_guides_nested_elements() {
        let program = Program {
            declarations: vec![
                Decl::Function(FunctionDecl {
                    static_params: Vec::new(),
                    receiver: None,
                    name: "sum_list".to_string(),
                    params: vec![aura_frontend::ast::Param {
                        name: "xs".to_string(),
                        ty: TypeExpr::Named {
                            name: "List".to_string(),
                            args: vec![StaticArg::Type(TypeExpr::Named {
                                name: "Int".to_string(),
                                args: Vec::new(),
                            })],
                        },
                    }],
                    return_type: TypeExpr::Named {
                        name: "Int".to_string(),
                        args: Vec::new(),
                    },
                    body: Expr::Int("0".to_string()),
                }),
                Decl::Assign {
                    name: "y".to_string(),
                    value: Expr::Call {
                        callee: Box::new(Expr::Ident("sum_list".to_string())),
                        static_args: Vec::new(),
                        args: vec![Expr::List(vec![Expr::Int("1".to_string())])],

                        trailing: Vec::new(),
                    },
                },
            ],
        };

        let checked = check_module(&program);
        assert!(checked.module.is_some());
        assert!(!checked
            .diagnostics
            .iter()
            .any(|d| d.code == "E_TYPE_MISMATCH"));
    }

    #[test]
    fn expected_dict_type_guides_nested_entries() {
        let program = Program {
            declarations: vec![
                Decl::Function(FunctionDecl {
                    static_params: Vec::new(),
                    receiver: None,
                    name: "takes_dict".to_string(),
                    params: vec![aura_frontend::ast::Param {
                        name: "m".to_string(),
                        ty: TypeExpr::Named {
                            name: "Dict".to_string(),
                            args: vec![
                                StaticArg::Type(TypeExpr::Named {
                                    name: "Int".to_string(),
                                    args: Vec::new(),
                                }),
                                StaticArg::Type(TypeExpr::Named {
                                    name: "Float".to_string(),
                                    args: Vec::new(),
                                }),
                            ],
                        },
                    }],
                    return_type: TypeExpr::Named {
                        name: "Int".to_string(),
                        args: Vec::new(),
                    },
                    body: Expr::Int("0".to_string()),
                }),
                Decl::Assign {
                    name: "y".to_string(),
                    value: Expr::Call {
                        callee: Box::new(Expr::Ident("takes_dict".to_string())),
                        static_args: Vec::new(),
                        args: vec![Expr::Dict(vec![(
                            Expr::Int("1".to_string()),
                            Expr::Float("2.0".to_string()),
                        )])],

                        trailing: Vec::new(),
                    },
                },
            ],
        };

        let checked = check_module(&program);
        assert!(checked.module.is_some());
        assert!(!checked
            .diagnostics
            .iter()
            .any(|d| d.code == "E_TYPE_MISMATCH"));
    }

    #[test]
    fn expected_list_type_rejects_incompatible_element() {
        let program = Program {
            declarations: vec![
                Decl::Function(FunctionDecl {
                    static_params: Vec::new(),
                    receiver: None,
                    name: "sum_list".to_string(),
                    params: vec![aura_frontend::ast::Param {
                        name: "xs".to_string(),
                        ty: TypeExpr::Named {
                            name: "List".to_string(),
                            args: vec![StaticArg::Type(TypeExpr::Named {
                                name: "Int".to_string(),
                                args: Vec::new(),
                            })],
                        },
                    }],
                    return_type: TypeExpr::Named {
                        name: "Int".to_string(),
                        args: Vec::new(),
                    },
                    body: Expr::Int("0".to_string()),
                }),
                Decl::Assign {
                    name: "y".to_string(),
                    value: Expr::Call {
                        callee: Box::new(Expr::Ident("sum_list".to_string())),
                        static_args: Vec::new(),
                        args: vec![Expr::List(vec![Expr::String("oops".to_string())])],

                        trailing: Vec::new(),
                    },
                },
            ],
        };

        let checked = check_module(&program);
        assert!(checked.module.is_none());
        assert!(checked
            .diagnostics
            .iter()
            .any(|d| d.code == "E_TYPE_MISMATCH"));
    }

    #[test]
    fn expected_return_type_guides_nested_call_inference() {
        let program = Program {
            declarations: vec![
                Decl::Function(FunctionDecl {
                    static_params: Vec::new(),
                    receiver: None,
                    name: "id_int".to_string(),
                    params: vec![aura_frontend::ast::Param {
                        name: "x".to_string(),
                        ty: TypeExpr::Named {
                            name: "Int".to_string(),
                            args: Vec::new(),
                        },
                    }],
                    return_type: TypeExpr::Named {
                        name: "Int".to_string(),
                        args: Vec::new(),
                    },
                    body: Expr::Ident("x".to_string()),
                }),
                Decl::Function(FunctionDecl {
                    static_params: Vec::new(),
                    receiver: None,
                    name: "outer".to_string(),
                    params: vec![aura_frontend::ast::Param {
                        name: "x".to_string(),
                        ty: TypeExpr::Named {
                            name: "Int".to_string(),
                            args: Vec::new(),
                        },
                    }],
                    return_type: TypeExpr::Named {
                        name: "Int".to_string(),
                        args: Vec::new(),
                    },
                    body: Expr::Call {
                        callee: Box::new(Expr::Ident("id_int".to_string())),
                        static_args: Vec::new(),
                        args: vec![Expr::Ident("x".to_string())],

                        trailing: Vec::new(),
                    },
                }),
            ],
        };

        let checked = check_module(&program);
        assert!(checked.module.is_some());
        assert!(!checked
            .diagnostics
            .iter()
            .any(|d| d.code == "E_TYPE_MISMATCH" || d.code == "E_UNIFY_MISMATCH"));
    }

    #[test]
    fn label_expression_propagates_expected_type() {
        let program = Program {
            declarations: vec![Decl::Function(FunctionDecl {
                static_params: Vec::new(),
                receiver: None,
                name: "f".to_string(),
                params: Vec::new(),
                return_type: TypeExpr::Named {
                    name: "Int".to_string(),
                    args: Vec::new(),
                },
                body: Expr::Label {
                    label: "dbg".to_string(),
                    expr: Box::new(Expr::Int("1".to_string())),
                },
            })],
        };

        let checked = check_module(&program);
        assert!(checked.module.is_some());
        assert!(!checked
            .diagnostics
            .iter()
            .any(|d| d.code == "E_TYPE_MISMATCH"));
    }

    #[test]
    fn dot_ident_payload_propagates_expected_type() {
        let program = Program {
            declarations: vec![Decl::Function(FunctionDecl {
                static_params: Vec::new(),
                receiver: None,
                name: "f".to_string(),
                params: Vec::new(),
                return_type: TypeExpr::Named {
                    name: "Int".to_string(),
                    args: Vec::new(),
                },
                body: Expr::DotIdent {
                    name: "ok".to_string(),
                    payload: Some(Box::new(Expr::Int("1".to_string()))),
                },
            })],
        };

        let checked = check_module(&program);
        assert!(checked.module.is_some());
        assert!(!checked
            .diagnostics
            .iter()
            .any(|d| d.code == "E_TYPE_MISMATCH"));
    }

    #[test]
    fn untyped_macro_rule_is_error() {
        let program = Program {
            declarations: vec![Decl::Assign {
                name: "x".to_string(),
                value: Expr::MacroApply {
                    macro_name: "unknown_macro".to_string(),
                    static_args: Vec::new(),
                    operand: Box::new(Expr::Int("1".to_string())),
                },
            }],
        };

        let checked = check_module(&program);
        assert!(checked.module.is_none());
        assert!(checked
            .diagnostics
            .iter()
            .any(|d| d.code == "E_MACRO_UNTYPED"));
    }

    #[test]
    fn malformed_if_lowering_uses_macro_apply_fallback_not_any() {
        let program = Program {
            declarations: vec![Decl::Assign {
                name: "x".to_string(),
                value: Expr::MacroApply {
                    macro_name: "if".to_string(),
                    static_args: Vec::new(),
                    operand: Box::new(Expr::Int("1".to_string())),
                },
            }],
        };

        let checked = check_module(&program);
        assert!(checked.module.is_none());
        assert!(checked.diagnostics.iter().any(|d| d.code == "E_IF_FORM"));
    }

    #[test]
    fn malformed_cases_lowering_uses_macro_apply_fallback_not_any() {
        let program = Program {
            declarations: vec![Decl::Assign {
                name: "x".to_string(),
                value: Expr::MacroApply {
                    macro_name: "cases".to_string(),
                    static_args: Vec::new(),
                    operand: Box::new(Expr::Int("1".to_string())),
                },
            }],
        };

        let checked = check_module(&program);
        assert!(checked.module.is_none());
        assert!(checked.diagnostics.iter().any(|d| d.code == "E_CASES_FORM"));
    }

    #[test]
    fn list_type_expr_without_item_arg_reports_missing_type_arg() {
        let program = Program {
            declarations: vec![Decl::Function(FunctionDecl {
                static_params: Vec::new(),
                receiver: None,
                name: "f".to_string(),
                params: vec![aura_frontend::ast::Param {
                    name: "xs".to_string(),
                    ty: TypeExpr::Named {
                        name: "List".to_string(),
                        args: Vec::new(),
                    },
                }],
                return_type: TypeExpr::Named {
                    name: "Int".to_string(),
                    args: Vec::new(),
                },
                body: Expr::Int("0".to_string()),
            })],
        };

        let checked = check_module(&program);
        assert!(checked.module.is_none());
        assert!(checked
            .diagnostics
            .iter()
            .any(|d| d.code == "E_TYPE_ARG_MISSING"));
    }

    #[test]
    fn dict_type_expr_with_value_in_type_slot_reports_kind_error() {
        let program = Program {
            declarations: vec![Decl::Function(FunctionDecl {
                static_params: Vec::new(),
                receiver: None,
                name: "f".to_string(),
                params: vec![aura_frontend::ast::Param {
                    name: "m".to_string(),
                    ty: TypeExpr::Named {
                        name: "Dict".to_string(),
                        args: vec![
                            StaticArg::Type(TypeExpr::Named {
                                name: "Int".to_string(),
                                args: Vec::new(),
                            }),
                            StaticArg::Value(StaticValueExpr::Int("1".to_string())),
                        ],
                    },
                }],
                return_type: TypeExpr::Named {
                    name: "Int".to_string(),
                    args: Vec::new(),
                },
                body: Expr::Int("0".to_string()),
            })],
        };

        let checked = check_module(&program);
        assert!(checked.module.is_none());
        assert!(checked
            .diagnostics
            .iter()
            .any(|d| d.code == "E_TYPE_ARG_KIND"));
    }

    #[test]
    fn array_type_expr_without_size_reports_missing_size_error() {
        let program = Program {
            declarations: vec![Decl::Function(FunctionDecl {
                static_params: Vec::new(),
                receiver: None,
                name: "f".to_string(),
                params: vec![aura_frontend::ast::Param {
                    name: "arr".to_string(),
                    ty: TypeExpr::Named {
                        name: "Array".to_string(),
                        args: vec![StaticArg::Type(TypeExpr::Named {
                            name: "Int".to_string(),
                            args: Vec::new(),
                        })],
                    },
                }],
                return_type: TypeExpr::Named {
                    name: "Int".to_string(),
                    args: Vec::new(),
                },
                body: Expr::Int("0".to_string()),
            })],
        };

        let checked = check_module(&program);
        assert!(checked.module.is_none());
        assert!(checked
            .diagnostics
            .iter()
            .any(|d| d.code == "E_ARRAY_SIZE_MISSING"));
    }

    #[test]
    fn list_type_expr_with_extra_arg_reports_arity_error() {
        let program = Program {
            declarations: vec![Decl::Function(FunctionDecl {
                static_params: Vec::new(),
                receiver: None,
                name: "f".to_string(),
                params: vec![aura_frontend::ast::Param {
                    name: "xs".to_string(),
                    ty: TypeExpr::Named {
                        name: "List".to_string(),
                        args: vec![
                            StaticArg::Type(TypeExpr::Named {
                                name: "Int".to_string(),
                                args: Vec::new(),
                            }),
                            StaticArg::Type(TypeExpr::Named {
                                name: "Int".to_string(),
                                args: Vec::new(),
                            }),
                        ],
                    },
                }],
                return_type: TypeExpr::Named {
                    name: "Int".to_string(),
                    args: Vec::new(),
                },
                body: Expr::Int("0".to_string()),
            })],
        };

        let checked = check_module(&program);
        assert!(checked.module.is_none());
        assert!(checked
            .diagnostics
            .iter()
            .any(|d| d.code == "E_TYPE_ARG_ARITY"));
    }

    #[test]
    fn bool_type_expr_with_any_arg_reports_arity_error() {
        let program = Program {
            declarations: vec![Decl::Function(FunctionDecl {
                static_params: Vec::new(),
                receiver: None,
                name: "f".to_string(),
                params: vec![aura_frontend::ast::Param {
                    name: "b".to_string(),
                    ty: TypeExpr::Named {
                        name: "Bool".to_string(),
                        args: vec![StaticArg::Type(TypeExpr::Named {
                            name: "Int".to_string(),
                            args: Vec::new(),
                        })],
                    },
                }],
                return_type: TypeExpr::Named {
                    name: "Int".to_string(),
                    args: Vec::new(),
                },
                body: Expr::Int("0".to_string()),
            })],
        };

        let checked = check_module(&program);
        assert!(checked.module.is_none());
        assert!(checked
            .diagnostics
            .iter()
            .any(|d| d.code == "E_TYPE_ARG_ARITY"));
    }

    #[test]
    fn generic_param_type_resolves_inside_generic_function_signature() {
        let program = Program {
            declarations: vec![
                Decl::Function(FunctionDecl {
                    static_params: vec![ty_param("T")],
                    receiver: None,
                    name: "id".to_string(),
                    params: vec![aura_frontend::ast::Param {
                        name: "x".to_string(),
                        ty: TypeExpr::Named {
                            name: "T".to_string(),
                            args: Vec::new(),
                        },
                    }],
                    return_type: TypeExpr::Named {
                        name: "T".to_string(),
                        args: Vec::new(),
                    },
                    body: Expr::Ident("x".to_string()),
                }),
                Decl::Assign {
                    name: "f".to_string(),
                    value: Expr::Ident("id".to_string()),
                },
            ],
        };

        let checked = check_module(&program);
        assert!(checked.module.is_some());
        let module = checked.module.expect("module should exist");
        let ty_id = module.value_types.get("f").expect("f type should exist");
        let ty = module.types.get(*ty_id).expect("type should exist");
        let Ty::Func { params, ret } = ty else {
            panic!("id should be function typed")
        };

        let p0 = module
            .types
            .get(params[0])
            .expect("param type should exist");
        let r = module.types.get(*ret).expect("return type should exist");
        assert!(matches!(p0, Ty::GenericParam(name) if name == "T"));
        assert!(matches!(r, Ty::GenericParam(name) if name == "T"));
    }

    #[test]
    fn infer_hole_type_expr_resolves_to_infer_var() {
        let program = Program {
            declarations: vec![
                Decl::Function(FunctionDecl {
                    static_params: Vec::new(),
                    receiver: None,
                    name: "f".to_string(),
                    params: vec![aura_frontend::ast::Param {
                        name: "x".to_string(),
                        ty: TypeExpr::Named {
                            name: "List".to_string(),
                            args: vec![StaticArg::Type(TypeExpr::InferHole)],
                        },
                    }],
                    return_type: TypeExpr::Named {
                        name: "Int".to_string(),
                        args: Vec::new(),
                    },
                    body: Expr::Int("0".to_string()),
                }),
                Decl::Assign {
                    name: "g".to_string(),
                    value: Expr::Ident("f".to_string()),
                },
            ],
        };

        let checked = check_module(&program);
        assert!(checked.module.is_some());
        let module = checked.module.expect("module should exist");
        let g_ty = module.value_types.get("g").expect("g type should exist");
        let Ty::Func { params, .. } = module.types.get(*g_ty).expect("func type expected") else {
            panic!("expected function type")
        };
        let list_ty = module.types.get(params[0]).expect("param type expected");
        let Ty::List(item) = list_ty else {
            panic!("expected list type")
        };
        assert!(matches!(module.types.get(*item), Some(Ty::InferVar(_))));
    }

    #[test]
    fn explicit_generic_call_accepts_infer_hole_slots() {
        let program = Program {
            declarations: vec![
                Decl::Function(FunctionDecl {
                    static_params: vec![ty_param("T"), ty_param("U")],
                    receiver: None,
                    name: "first".to_string(),
                    params: vec![aura_frontend::ast::Param {
                        name: "x".to_string(),
                        ty: TypeExpr::Named {
                            name: "T".to_string(),
                            args: Vec::new(),
                        },
                    }],
                    return_type: TypeExpr::Named {
                        name: "T".to_string(),
                        args: Vec::new(),
                    },
                    body: Expr::Ident("x".to_string()),
                }),
                Decl::Assign {
                    name: "y".to_string(),
                    value: Expr::Call {
                        callee: Box::new(Expr::Ident("first".to_string())),
                        static_args: vec![
                            StaticArg::Type(TypeExpr::InferHole),
                            StaticArg::Type(TypeExpr::Named {
                                name: "Int".to_string(),
                                args: Vec::new(),
                            }),
                        ],
                        args: vec![Expr::Int("1".to_string())],

                        trailing: Vec::new(),
                    },
                },
            ],
        };

        let checked = check_module(&program);
        assert!(checked.module.is_some());
        let module = checked.module.expect("module should exist");
        let y_ty = module.value_types.get("y").expect("y type should exist");
        assert!(matches!(module.types.get(*y_ty), Some(Ty::Int32)));
    }

    #[test]
    fn interface_bound_failure_reports_diagnostic() {
        let program = Program {
            declarations: vec![
                Decl::Function(FunctionDecl {
                    static_params: vec![StaticParam {
                        name: "T".to_string(),
                        kind: StaticParamKind::Constraint(TypeExpr::Named {
                            name: "Iterable".to_string(),
                            args: Vec::new(),
                        }),
                    }],
                    receiver: None,
                    name: "requires_iter".to_string(),
                    params: vec![aura_frontend::ast::Param {
                        name: "x".to_string(),
                        ty: TypeExpr::Named {
                            name: "T".to_string(),
                            args: Vec::new(),
                        },
                    }],
                    return_type: TypeExpr::Named {
                        name: "T".to_string(),
                        args: Vec::new(),
                    },
                    body: Expr::Ident("x".to_string()),
                }),
                Decl::Assign {
                    name: "y".to_string(),
                    value: Expr::Call {
                        callee: Box::new(Expr::Ident("requires_iter".to_string())),
                        static_args: vec![StaticArg::Type(TypeExpr::Named {
                            name: "Int".to_string(),
                            args: Vec::new(),
                        })],
                        args: vec![Expr::Int("1".to_string())],

                        trailing: Vec::new(),
                    },
                },
            ],
        };

        let checked = check_module(&program);
        assert!(checked.module.is_none());
        assert!(checked
            .diagnostics
            .iter()
            .any(|d| d.code == "E_INTERFACE_BOUND_UNSAT"));
        assert!(checked
            .diagnostics
            .iter()
            .any(|d| !d.obligations.is_empty()));
    }

    #[test]
    fn static_bound_with_type_arg_reports_kind_error() {
        let program = Program {
            declarations: vec![
                Decl::Function(FunctionDecl {
                    static_params: vec![StaticParam {
                        name: "n".to_string(),
                        kind: StaticParamKind::Constraint(TypeExpr::Static(Box::new(
                            TypeExpr::Named {
                                name: "Int".to_string(),
                                args: Vec::new(),
                            },
                        ))),
                    }],
                    receiver: None,
                    name: "requires_static".to_string(),
                    params: vec![aura_frontend::ast::Param {
                        name: "x".to_string(),
                        ty: TypeExpr::Named {
                            name: "Int".to_string(),
                            args: Vec::new(),
                        },
                    }],
                    return_type: TypeExpr::Named {
                        name: "Int".to_string(),
                        args: Vec::new(),
                    },
                    body: Expr::Ident("x".to_string()),
                }),
                Decl::Assign {
                    name: "y".to_string(),
                    value: Expr::Call {
                        callee: Box::new(Expr::Ident("requires_static".to_string())),
                        static_args: vec![StaticArg::Type(TypeExpr::Named {
                            name: "Int".to_string(),
                            args: Vec::new(),
                        })],
                        args: vec![Expr::Int("1".to_string())],

                        trailing: Vec::new(),
                    },
                },
            ],
        };

        let checked = check_module(&program);
        assert!(checked.module.is_none());
        assert!(checked
            .diagnostics
            .iter()
            .any(|d| d.code == "E_STATIC_ARG_KIND"));
        assert!(checked
            .diagnostics
            .iter()
            .any(|d| !d.obligations.is_empty()));
    }

    #[test]
    fn static_bound_missing_arg_reports_diagnostic_on_omitted_static_args() {
        let program = Program {
            declarations: vec![
                Decl::Function(FunctionDecl {
                    static_params: vec![StaticParam {
                        name: "n".to_string(),
                        kind: StaticParamKind::Constraint(TypeExpr::Static(Box::new(
                            TypeExpr::Named {
                                name: "Int".to_string(),
                                args: Vec::new(),
                            },
                        ))),
                    }],
                    receiver: None,
                    name: "requires_static".to_string(),
                    params: vec![aura_frontend::ast::Param {
                        name: "x".to_string(),
                        ty: TypeExpr::Named {
                            name: "Int".to_string(),
                            args: Vec::new(),
                        },
                    }],
                    return_type: TypeExpr::Named {
                        name: "Int".to_string(),
                        args: Vec::new(),
                    },
                    body: Expr::Ident("x".to_string()),
                }),
                Decl::Assign {
                    name: "y".to_string(),
                    value: Expr::Call {
                        callee: Box::new(Expr::Ident("requires_static".to_string())),
                        static_args: Vec::new(),
                        args: vec![Expr::Int("1".to_string())],

                        trailing: Vec::new(),
                    },
                },
            ],
        };

        let checked = check_module(&program);
        assert!(checked.module.is_none());
        assert!(checked
            .diagnostics
            .iter()
            .any(|d| d.code == "E_STATIC_ARG_MISSING"));
    }

    #[test]
    fn unknown_interface_constraint_reports_diagnostic_in_solver_path() {
        let program = Program {
            declarations: vec![
                Decl::Function(FunctionDecl {
                    static_params: vec![StaticParam {
                        name: "T".to_string(),
                        kind: StaticParamKind::Constraint(TypeExpr::Named {
                            name: "Mystery".to_string(),
                            args: Vec::new(),
                        }),
                    }],
                    receiver: None,
                    name: "f".to_string(),
                    params: vec![aura_frontend::ast::Param {
                        name: "x".to_string(),
                        ty: TypeExpr::Named {
                            name: "T".to_string(),
                            args: Vec::new(),
                        },
                    }],
                    return_type: TypeExpr::Named {
                        name: "T".to_string(),
                        args: Vec::new(),
                    },
                    body: Expr::Ident("x".to_string()),
                }),
                Decl::Assign {
                    name: "y".to_string(),
                    value: Expr::Call {
                        callee: Box::new(Expr::Ident("f".to_string())),
                        static_args: vec![StaticArg::Type(TypeExpr::Named {
                            name: "Int".to_string(),
                            args: Vec::new(),
                        })],
                        args: vec![Expr::Int("1".to_string())],

                        trailing: Vec::new(),
                    },
                },
            ],
        };

        let checked = check_module(&program);
        assert!(checked.module.is_none());
        assert!(checked
            .diagnostics
            .iter()
            .any(|d| d.code == "E_UNKNOWN_INTERFACE"));
    }

    #[test]
    fn ir_wrapping_uses_central_conversion_decision_for_widening() {
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

        let mut checker = TypeChecker::new();
        let _ = checker.check_program(&program);
        let (_types, _diagnostics, ir) = checker.into_parts();
        assert!(ir
            .declarations
            .iter()
            .any(|d| d.name == "x" && matches!(&d.value, CheckedExpr::Int(_))));
    }

    #[test]
    fn implicit_assignability_rejects_explicit_only_cast_pair() {
        let program = Program {
            declarations: vec![
                Decl::Assign {
                    name: "x".to_string(),
                    value: Expr::Float("1.5".to_string()),
                },
                Decl::Assign {
                    name: "x".to_string(),
                    value: Expr::Int("1".to_string()),
                },
            ],
        };

        let checked = check_module(&program);
        assert!(checked.module.is_none());
        assert!(checked
            .diagnostics
            .iter()
            .any(|d| d.code == "E_TYPE_MISMATCH"));
    }

    #[test]
    fn comparison_operator_returns_bool() {
        let program = Program {
            declarations: vec![Decl::Assign {
                name: "x".to_string(),
                value: Expr::Binary {
                    op: ParsedBinaryOp::Gt,
                    lhs: Box::new(Expr::Float("1.0".to_string())),
                    rhs: Box::new(Expr::Float("2.0".to_string())),
                },
            }],
        };

        let checked = check_module(&program);
        assert!(checked.module.is_some());
        let module = checked.module.expect("module should exist");
        let x_ty = module.value_types.get("x").expect("x should exist");
        assert!(matches!(module.types.get(*x_ty), Some(Ty::Bool)));
    }

    #[test]
    fn logical_operator_requires_bool_operands() {
        let program = Program {
            declarations: vec![Decl::Assign {
                name: "x".to_string(),
                value: Expr::Binary {
                    op: ParsedBinaryOp::And,
                    lhs: Box::new(Expr::Int("1".to_string())),
                    rhs: Box::new(Expr::Int("2".to_string())),
                },
            }],
        };

        let checked = check_module(&program);
        assert!(checked.module.is_none());
        assert!(checked
            .diagnostics
            .iter()
            .any(|d| d.code == "E_TYPE_MISMATCH"));
    }

    #[test]
    fn mod_operator_is_typed_as_numeric_operator() {
        let program = Program {
            declarations: vec![Decl::Assign {
                name: "x".to_string(),
                value: Expr::Binary {
                    op: ParsedBinaryOp::Mod,
                    lhs: Box::new(Expr::Int("7".to_string())),
                    rhs: Box::new(Expr::Int("3".to_string())),
                },
            }],
        };

        let checked = check_module(&program);
        assert!(checked.module.is_some());
        let module = checked.module.expect("module should exist");
        let x_ty = module.value_types.get("x").expect("x should exist");
        assert!(matches!(module.types.get(*x_ty), Some(Ty::Int32)));
    }

    #[test]
    fn parsed_cast_expression_typechecks_and_lowers_to_cast_ir() {
        let program = Program {
            declarations: vec![Decl::Assign {
                name: "x".to_string(),
                value: Expr::Cast {
                    expr: Box::new(Expr::Int("1".to_string())),
                    ty: TypeExpr::Named {
                        name: "Float".to_string(),
                        args: Vec::new(),
                    },
                },
            }],
        };

        let checked = check_module(&program);
        let module = checked.module.expect("module should exist");
        let decl = module
            .ir
            .declarations
            .iter()
            .find(|d| d.name == "x")
            .expect("x declaration should exist");
        assert!(matches!(decl.value, CheckedExpr::Cast { .. }));
    }
}
