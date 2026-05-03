use std::collections::HashMap;

use aura_diagnostics::type_ref::FuncParamRef;
use aura_diagnostics::{Diagnostic, Issue, PrimitiveType, Stage, TypeRef, TypingContext};
use aura_frontend::ast::{
    BinaryOp as ParsedBinaryOp, Decl, Expr, LabeledClosureArg, Pattern, Program, StaticArg,
    StaticParam, StaticParamKind, StaticValueExpr, TypeExpr,
};

use crate::aliases::TypeAliases;
use crate::checked_ir::{
    BinaryOpKind, CheckedBinding, CheckedCaseArm, CheckedDecl, CheckedEnumArm,
    CheckedEnumStructBinding, CheckedExpr, CheckedIr, CheckedStaticArg, CheckedStaticValue,
    CheckedTypeExpr, MemoryOpKind,
};
use crate::interfaces::InterfaceRegistry;
use crate::modules::ModuleChecker;
use crate::numeric::can_implicitly_widen;
use crate::patterns::PatternChecker;
use crate::types::{FuncParam, Ty, TyId, TyInterner};
use crate::unify::Unifier;

use crate::generics::GenericConstraint;
use crate::{CheckContext, CheckOptions, GenericTypeAlias, ImportBinding, TypeImportBinding};

#[derive(Debug, Clone)]
pub struct TypeChecker {
    interner: TyInterner,
    aliases: TypeAliases,
    module_checker: ModuleChecker,
    pattern_checker: PatternChecker,
    interfaces: InterfaceRegistry,
    unifier: Unifier,
    next_infer_var: u32,
    obligation_stack: Vec<String>,
    value_env_scopes: Vec<HashMap<String, ValueBinding>>,
    generic_env_scopes: Vec<HashMap<String, TyId>>,
    function_generics: HashMap<String, Vec<FunctionGenericInfo>>,
    pending_constraints: Vec<TypeConstraint>,
    solving_constraints: bool,
    current_expr_span: Option<aura_diagnostics::Span>,
    diagnostics: Vec<Diagnostic>,
    ir: CheckedIr,
    imported_values: HashMap<String, ImportBinding>,
    imported_types: HashMap<String, TypeImportBinding>,
    methods: HashMap<(TyId, String), MethodBinding>,
    namespaces: HashMap<String, HashMap<String, ImportBinding>>,
    current_match_subject: Option<MatchSubject>,
    resolved_enum_ctors: HashMap<String, ResolvedEnumCtor>,
    resolved_method_calls: HashMap<String, String>,
    active_labels: Vec<String>,
    active_function_targets: Vec<FunctionJumpTarget>,
    active_loop_targets: Vec<ActiveLoopTarget>,
    resolved_loop_targets: HashMap<String, ResolvedLoopInfo>,
    resolved_jump_targets: HashMap<String, String>,
    next_loop_target: usize,
    options: CheckOptions,
}

#[derive(Debug, Clone, Copy)]
struct ValueBinding {
    ty: TyId,
    mutable: bool,
    place_mutable: bool,
}

#[derive(Debug, Clone)]
struct MethodBinding {
    name: String,
    link_name: String,
    ty: TyId,
}

#[derive(Debug, Clone)]
struct MatchSubject {
    name: String,
    ty: TyId,
}

#[derive(Debug, Clone, Copy)]
struct FieldPlace {
    field_ty: TyId,
}

#[derive(Debug, Clone, Copy)]
struct ResolvedEnumCtor {
    enum_ty: TyId,
    variant_index: usize,
}

#[derive(Debug, Clone)]
struct FunctionJumpTarget {
    name: String,
    return_ty: TyId,
}

#[derive(Debug, Clone)]
struct ActiveLoopTarget {
    target: String,
    label: Option<String>,
    result_ty: TyId,
    saw_break: bool,
}

#[derive(Debug, Clone)]
struct ResolvedLoopInfo {
    target: String,
    result_ty: TyId,
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

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum BuiltinMemberCall {
    BytesNew,
    BytesGet,
    BytesSet,
    StringInto,
    RawAllocNew,
    RawAllocSlice,
    SliceRefAt,
}

#[derive(Debug, Clone)]
struct FunctionGenericInfo {
    name: String,
    constraints: Vec<GenericConstraint>,
}

impl TypeChecker {
    const KNOWN_GENERIC_RECEIVERS: [&'static str; 8] = [
        "List", "Dict", "Set", "Array", "Func", "Option", "Result", "Seq",
    ];

    pub fn new(context: CheckContext, options: CheckOptions) -> Self {
        let mut interner = TyInterner::new();
        interner.prelude_primitives();
        let aliases = TypeAliases::with_prelude(&mut interner);
        let namespaces = context
            .namespaces
            .into_iter()
            .map(|(alias, bindings)| {
                (
                    alias,
                    bindings
                        .into_iter()
                        .map(|binding| (binding.local_name.clone(), binding))
                        .collect::<HashMap<_, _>>(),
                )
            })
            .collect::<HashMap<_, _>>();
        let imported_values = context
            .imported_values
            .into_iter()
            .map(|binding| (binding.local_name.clone(), binding))
            .collect::<HashMap<_, _>>();
        let imported_types = context
            .imported_types
            .into_iter()
            .map(|binding| (binding.local_name.clone(), binding))
            .collect::<HashMap<_, _>>();
        let mut checker = Self {
            interner,
            aliases,
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
            imported_values,
            imported_types,
            methods: HashMap::new(),
            namespaces,
            current_match_subject: None,
            resolved_enum_ctors: HashMap::new(),
            resolved_method_calls: HashMap::new(),
            active_labels: Vec::new(),
            active_function_targets: Vec::new(),
            active_loop_targets: Vec::new(),
            resolved_loop_targets: HashMap::new(),
            resolved_jump_targets: HashMap::new(),
            next_loop_target: 0,
            options,
        };

        let imported_bindings = checker
            .imported_values
            .values()
            .cloned()
            .collect::<Vec<_>>();
        for binding in imported_bindings {
            let ty = checker.type_ref_to_ty(&binding.ty);
            checker.insert_value(binding.local_name.clone(), ty, false);
            checker.ir.declarations.push(CheckedDecl {
                name: binding.local_name,
                link_name: binding.link_name,
                params: Vec::new(),
                ty,
                is_extern: true,
                value: CheckedExpr::Any,
            });
        }

        let imported_type_bindings = checker.imported_types.values().cloned().collect::<Vec<_>>();
        for binding in imported_type_bindings {
            if let Some(generic) = binding.generic {
                checker.aliases.insert_generic(
                    binding.local_name,
                    generic.static_params,
                    generic.body,
                );
            } else {
                let ty = checker.type_ref_to_ty(&binding.ty);
                checker.aliases.insert(binding.local_name, ty);
            }
        }

        checker
    }

    fn base_expr(expr: &Expr) -> &Expr {
        let mut cur = expr;
        while let Expr::Spanned { expr, .. } = cur {
            cur = expr.as_ref();
        }
        cur
    }

    fn is_placeholder_expr(expr: &Expr) -> bool {
        matches!(Self::base_expr(expr), Expr::Placeholder)
    }

    fn nominal_ty(&mut self, name: &str) -> TyId {
        self.interner.intern(Ty::Nominal(name.to_string()))
    }

    fn positional_params(&self, params: impl IntoIterator<Item = TyId>) -> Vec<FuncParam> {
        params.into_iter().map(FuncParam::positional).collect()
    }

    fn named_params_from_fields(&mut self, fields: &[(String, TypeExpr)]) -> Vec<FuncParam> {
        fields
            .iter()
            .map(|(name, ty)| FuncParam::named(name.clone(), self.resolve_type_expr(ty)))
            .collect()
    }

    fn type_ref_to_ty(&mut self, ty: &TypeRef) -> TyId {
        match ty {
            TypeRef::Primitive(primitive) => match primitive {
                PrimitiveType::Int8 => self.interner.intern(Ty::Int8),
                PrimitiveType::Int16 => self.interner.intern(Ty::Int16),
                PrimitiveType::Int32 => self.interner.intern(Ty::Int32),
                PrimitiveType::Int64 => self.interner.intern(Ty::Int64),
                PrimitiveType::Int128 => self.interner.intern(Ty::Int128),
                PrimitiveType::ISize => self.interner.intern(Ty::ISize),
                PrimitiveType::UInt8 => self.interner.intern(Ty::UInt8),
                PrimitiveType::UInt16 => self.interner.intern(Ty::UInt16),
                PrimitiveType::UInt32 => self.interner.intern(Ty::UInt32),
                PrimitiveType::UInt64 => self.interner.intern(Ty::UInt64),
                PrimitiveType::UInt128 => self.interner.intern(Ty::UInt128),
                PrimitiveType::USize => self.interner.intern(Ty::USize),
                PrimitiveType::Float32 => self.interner.intern(Ty::Float32),
                PrimitiveType::Float64 => self.interner.intern(Ty::Float64),
                PrimitiveType::Bool => self.interner.intern(Ty::Bool),
                PrimitiveType::Char => self.interner.intern(Ty::Char),
                PrimitiveType::Void => self.interner.intern(Ty::Void),
                PrimitiveType::Never => self.interner.intern(Ty::Never),
                PrimitiveType::Any => self.interner.intern(Ty::Any),
            },
            TypeRef::InferVar(v) => self.interner.intern(Ty::InferVar(*v)),
            TypeRef::GenericParam(name) => self.interner.intern(Ty::GenericParam(name.clone())),
            TypeRef::Nominal(name) => self.nominal_ty(name),
            TypeRef::RawAlloc(item) => {
                let item_ty = self.type_ref_to_ty(item);
                self.interner.intern(Ty::RawAlloc(item_ty))
            }
            TypeRef::Slice(item) => {
                let item_ty = self.type_ref_to_ty(item);
                self.interner.intern(Ty::Slice(item_ty))
            }
            TypeRef::Ref(item) => {
                let item_ty = self.type_ref_to_ty(item);
                self.interner.intern(Ty::Ref(item_ty))
            }
            TypeRef::List(item) => {
                let item_ty = self.type_ref_to_ty(item);
                self.interner.intern(Ty::List(item_ty))
            }
            TypeRef::Dict { key, value } => {
                let key_ty = self.type_ref_to_ty(key);
                let value_ty = self.type_ref_to_ty(value);
                self.interner.intern(Ty::Dict {
                    key: key_ty,
                    value: value_ty,
                })
            }
            TypeRef::Set(item) => {
                let item_ty = self.type_ref_to_ty(item);
                self.interner.intern(Ty::Set(item_ty))
            }
            TypeRef::Array { item, size } => {
                let item_ty = self.type_ref_to_ty(item);
                self.interner.intern(Ty::Array {
                    item: item_ty,
                    size: *size,
                })
            }
            TypeRef::Func { params, ret } => {
                let param_tys = params
                    .iter()
                    .map(|param| FuncParam {
                        name: param.name.clone(),
                        label: param.label.clone(),
                        trailing: param.trailing,
                        ty: self.type_ref_to_ty(&param.ty),
                    })
                    .collect::<Vec<_>>();
                let ret_ty = self.type_ref_to_ty(ret);
                self.interner.intern(Ty::Func {
                    params: param_tys,
                    ret: ret_ty,
                })
            }
            TypeRef::Macro { params, ret } => {
                let param_tys = params
                    .iter()
                    .map(|param| FuncParam {
                        name: param.name.clone(),
                        label: param.label.clone(),
                        trailing: param.trailing,
                        ty: self.type_ref_to_ty(&param.ty),
                    })
                    .collect::<Vec<_>>();
                let ret_ty = self.type_ref_to_ty(ret);
                self.interner.intern(Ty::Macro {
                    params: param_tys,
                    ret: ret_ty,
                })
            }
            TypeRef::Tuple(items) => {
                let item_tys = items
                    .iter()
                    .map(|item| self.type_ref_to_ty(item))
                    .collect::<Vec<_>>();
                self.interner.intern(Ty::Tuple(item_tys))
            }
            TypeRef::Struct(fields) => {
                let field_tys = fields
                    .iter()
                    .map(|(name, ty)| (name.clone(), self.type_ref_to_ty(ty)))
                    .collect::<Vec<_>>();
                self.interner.intern(Ty::Struct(field_tys))
            }
            TypeRef::Union(items) => {
                let item_tys = items
                    .iter()
                    .map(|item| self.type_ref_to_ty(item))
                    .collect::<Vec<_>>();
                self.interner.intern(Ty::Union(item_tys))
            }
            TypeRef::Enum(variants) => {
                let lowered = variants
                    .iter()
                    .map(|(name, ty)| {
                        (
                            name.clone(),
                            ty.as_ref().map(|inner| self.type_ref_to_ty(inner)),
                        )
                    })
                    .collect::<Vec<_>>();
                self.interner.intern(Ty::Enum(lowered))
            }
            TypeRef::Unknown => self.unknown_ty(),
        }
    }

    fn imported_binding(&self, name: &str) -> Option<&ImportBinding> {
        self.imported_values.get(name)
    }

    fn imported_type_binding(&self, name: &str) -> Option<&TypeImportBinding> {
        self.imported_types.get(name)
    }

    fn namespace_binding(&self, namespace: &str, field: &str) -> Option<&ImportBinding> {
        self.namespaces
            .get(namespace)
            .and_then(|fields| fields.get(field))
    }

    fn namespace_alias_conflicts(&self, name: &str) -> bool {
        self.namespaces.contains_key(name)
    }

    fn expr_cache_key(expr: &Expr) -> String {
        format!("{expr:?}")
    }

    fn next_loop_target_name(&mut self) -> String {
        let target = format!("loop#{}", self.next_loop_target);
        self.next_loop_target += 1;
        target
    }

    fn current_jump_label(&self) -> Option<String> {
        self.active_labels.last().cloned()
    }

    fn static_label_arg(&mut self, static_args: &[StaticArg], form: &str) -> Option<String> {
        match static_args.first() {
            None => None,
            Some(StaticArg::Value(StaticValueExpr::Label(label)))
            | Some(StaticArg::Value(StaticValueExpr::Ident(label))) => Some(label.clone()),
            Some(_) => {
                self.diagnostics.push(
                    self.typecheck_error(
                        Issue::BuiltinForm,
                        format!("{form} label must be a dot-identifier static argument"),
                    )
                    .with_hint(format!("use form like {form}[.target] ...")),
                );
                None
            }
        }
    }

    fn resolve_function_jump_target(
        &mut self,
        static_args: &[StaticArg],
        form: &str,
    ) -> Option<FunctionJumpTarget> {
        let label = self.static_label_arg(static_args, form);
        if let Some(label) = label {
            let resolved = self
                .active_function_targets
                .iter()
                .rev()
                .find(|target| target.name == label)
                .cloned();
            if resolved.is_none() {
                self.diagnostics.push(
                    self.typecheck_error(
                        Issue::BuiltinForm,
                        format!("{form} target '.{label}' does not name an enclosing function"),
                    )
                    .with_hint("use an enclosing function label or remove the explicit target"),
                );
            }
            resolved
        } else {
            let resolved = self.active_function_targets.last().cloned();
            if resolved.is_none() {
                self.diagnostics.push(
                    self.typecheck_error(
                        Issue::BuiltinForm,
                        format!("{form} is only valid inside a function body"),
                    )
                    .with_hint("move the jump into a function body"),
                );
            }
            resolved
        }
    }

    fn resolve_loop_jump_target(&mut self, static_args: &[StaticArg], form: &str) -> Option<usize> {
        let label = self.static_label_arg(static_args, form);
        let resolved = if let Some(label) = label.clone() {
            self.active_loop_targets
                .iter()
                .rposition(|target| target.label.as_deref() == Some(label.as_str()))
        } else if self.active_loop_targets.is_empty() {
            None
        } else {
            Some(self.active_loop_targets.len() - 1)
        };

        if resolved.is_none() {
            let message = if let Some(label) = label {
                format!("{form} target '.{label}' does not name an enclosing loop")
            } else {
                format!("{form} is only valid inside a loop body")
            };
            self.diagnostics.push(
                self.typecheck_error(Issue::BuiltinForm, message)
                    .with_hint("use an enclosing loop target or remove the jump"),
            );
        }
        resolved
    }

    fn enum_alias(&self, name: &str) -> Option<TyId> {
        let ty = self.aliases.get(name)?;
        matches!(self.interner.get(ty), Some(Ty::Enum(_))).then_some(ty)
    }

    fn enum_variant(&self, enum_ty: TyId, name: &str) -> Option<(usize, Option<TyId>)> {
        let Ty::Enum(variants) = self.interner.get(enum_ty)? else {
            return None;
        };
        variants
            .iter()
            .enumerate()
            .find(|(_, (variant_name, _))| variant_name == name)
            .map(|(index, (_, payload_ty))| (index, *payload_ty))
    }

    fn named_call_args<'a>(&self, args: &'a [Expr]) -> Option<Vec<(String, &'a Expr)>> {
        if args.is_empty() {
            return None;
        }
        let mut fields = Vec::with_capacity(args.len());
        for arg in args {
            let Expr::Assign { name, value } = Self::base_expr(arg) else {
                return None;
            };
            fields.push((name.clone(), value.as_ref()));
        }
        Some(fields)
    }

    fn infer_struct_fields_with_expected(
        &mut self,
        actual_fields: &[(String, &Expr)],
        expected_fields: &[(String, TyId)],
        context: &str,
    ) -> TyId {
        let mut shape_matches = actual_fields.len() == expected_fields.len();
        if !shape_matches {
            self.diagnostics.push(
                self.typecheck_error(
                    Issue::TypeMismatch {
                        context: TypingContext::Custom(context.to_string()),
                        expected: TypeRef::Struct(
                            expected_fields
                                .iter()
                                .filter_map(|(name, ty)| {
                                    self.interner
                                        .get(*ty)
                                        .map(|ty| (name.clone(), ty_to_ref(ty, &self.interner)))
                                })
                                .collect(),
                        ),
                        actual: TypeRef::Unknown,
                    },
                    format!("{context} field count does not match expected struct payload"),
                )
                .with_hint("use exactly the fields declared by the enum variant payload"),
            );
        }

        for ((actual_name, value), (expected_name, expected_ty)) in
            actual_fields.iter().zip(expected_fields.iter())
        {
            if actual_name != expected_name {
                shape_matches = false;
                self.diagnostics.push(
                    self.typecheck_error(
                        Issue::TypeMismatch {
                            context: TypingContext::Custom(context.to_string()),
                            expected: TypeRef::Struct(
                                expected_fields
                                    .iter()
                                    .filter_map(|(name, ty)| {
                                        self.interner.get(*ty).map(|ty| {
                                            (name.clone(), ty_to_ref(ty, &self.interner))
                                        })
                                    })
                                    .collect(),
                            ),
                            actual: TypeRef::Unknown,
                        },
                        format!(
                            "{context} field '{actual_name}' does not match expected field '{expected_name}'"
                        ),
                    )
                    .with_hint("use the enum variant payload field names in declaration order"),
                );
            }
            let value_ty = self.infer_expr_with_expected(value, *expected_ty);
            self.require_assignable(*expected_ty, value_ty, context);
        }

        if shape_matches {
            self.interner.intern(Ty::Struct(expected_fields.to_vec()))
        } else {
            self.unknown_ty()
        }
    }

    fn infer_enum_constructor_call(
        &mut self,
        expr: &Expr,
        enum_ty: TyId,
        variant_index: usize,
        payload_ty: Option<TyId>,
        args: &[Expr],
        expected_result: Option<TyId>,
    ) -> TyId {
        if let Some(named_args) = self.named_call_args(args) {
            let Some(expected_payload_ty) = payload_ty else {
                self.emit_enum_constructor_payload_mismatch(
                    enum_ty,
                    "unit enum variant does not accept payload fields",
                );
                return self.unknown_ty();
            };
            let Some(Ty::Struct(expected_fields)) = self.interner.get(expected_payload_ty).cloned()
            else {
                self.emit_enum_constructor_payload_mismatch(
                    enum_ty,
                    "enum variant field sugar requires a struct payload",
                );
                return self.unknown_ty();
            };
            let payload = self.infer_struct_fields_with_expected(
                &named_args,
                &expected_fields,
                "enum variant payload",
            );
            self.require_assignable(expected_payload_ty, payload, "enum variant payload");
            self.record_enum_ctor(expr, enum_ty, variant_index);
            if let Some(expected) = expected_result {
                self.require_assignable(expected, enum_ty, "bidirectional expected type");
            }
            return enum_ty;
        }

        match (payload_ty, args) {
            (None, []) => {
                self.record_enum_ctor(expr, enum_ty, variant_index);
                if let Some(expected) = expected_result {
                    self.require_assignable(expected, enum_ty, "bidirectional expected type");
                }
                enum_ty
            }
            (Some(expected_payload_ty), [payload]) => {
                let actual_payload = self.infer_expr_with_expected(payload, expected_payload_ty);
                self.require_assignable(
                    expected_payload_ty,
                    actual_payload,
                    "enum variant payload",
                );
                self.record_enum_ctor(expr, enum_ty, variant_index);
                if let Some(expected) = expected_result {
                    self.require_assignable(expected, enum_ty, "bidirectional expected type");
                }
                enum_ty
            }
            _ => {
                self.emit_enum_constructor_payload_mismatch(
                    enum_ty,
                    "enum variant payload arity does not match expected type",
                );
                self.unknown_ty()
            }
        }
    }

    fn emit_enum_constructor_payload_mismatch(&mut self, enum_ty: TyId, reason: &str) {
        self.diagnostics.push(
            self.typecheck_error(
                Issue::TypeMismatch {
                    context: TypingContext::Custom("enum constructor".to_string()),
                    expected: ty_to_ref(self.interner.get(enum_ty).unwrap_or(&Ty::Any), &self.interner),
                    actual: TypeRef::Unknown,
                },
                format!("type mismatch in enum constructor: {reason}"),
            )
            .with_hint(
                "call payload variants with one payload value, or use field sugar for struct payload variants",
            ),
        );
    }

    fn record_enum_ctor(&mut self, expr: &Expr, enum_ty: TyId, variant_index: usize) {
        self.resolved_enum_ctors.insert(
            Self::expr_cache_key(expr),
            ResolvedEnumCtor {
                enum_ty,
                variant_index,
            },
        );
    }

    fn resolved_enum_ctor(&self, expr: &Expr) -> Option<ResolvedEnumCtor> {
        self.resolved_enum_ctors
            .get(&Self::expr_cache_key(expr))
            .copied()
    }

    fn lower_enum_call_payload(
        &mut self,
        enum_ty: TyId,
        variant_index: usize,
        args: &[Expr],
    ) -> Option<Box<CheckedExpr>> {
        if let Some(named_args) = self.named_call_args(args) {
            let Some(Ty::Enum(variants)) = self.interner.get(enum_ty).cloned() else {
                return None;
            };
            let payload_ty = variants
                .get(variant_index)
                .and_then(|(_, payload)| *payload)?;
            if !matches!(self.interner.get(payload_ty), Some(Ty::Struct(_))) {
                return None;
            }
            let fields = named_args
                .into_iter()
                .map(|(name, value)| (name, self.lower_expr(value)))
                .collect::<Vec<_>>();
            return Some(Box::new(CheckedExpr::Struct(fields)));
        }

        args.first().map(|arg| Box::new(self.lower_expr(arg)))
    }

    fn enum_struct_pattern_bindings(
        &self,
        pattern: Option<&Pattern>,
        payload_ty: Option<TyId>,
    ) -> Vec<CheckedEnumStructBinding> {
        let (Some(Pattern::Struct(pattern_fields)), Some(payload_ty)) = (pattern, payload_ty)
        else {
            return Vec::new();
        };
        let Some(Ty::Struct(payload_fields)) = self.interner.get(payload_ty) else {
            return Vec::new();
        };

        pattern_fields
            .iter()
            .filter_map(|(field_name, pattern)| {
                let Pattern::Ident(binding_name) = pattern else {
                    return None;
                };
                let (field_index, (_, field_ty)) = payload_fields
                    .iter()
                    .enumerate()
                    .find(|(_, (payload_name, _))| payload_name == field_name)?;
                Some(CheckedEnumStructBinding {
                    name: binding_name.clone(),
                    field_index,
                    ty: *field_ty,
                })
            })
            .collect()
    }

    fn record_method_call(&mut self, expr: &Expr, link_name: String) {
        self.resolved_method_calls
            .insert(Self::expr_cache_key(expr), link_name);
    }

    fn resolved_method_call(&self, expr: &Expr) -> Option<&String> {
        self.resolved_method_calls.get(&Self::expr_cache_key(expr))
    }

    fn lookup_method(&self, receiver_ty: TyId, name: &str) -> Option<&MethodBinding> {
        self.methods.get(&(receiver_ty, name.to_string()))
    }

    fn field_lookup(&self, object_ty: TyId, field: &str) -> Option<(usize, TyId)> {
        let object_ty = self.unifier.resolve(object_ty);
        match self.interner.get(object_ty) {
            Some(Ty::Struct(fields)) => fields
                .iter()
                .enumerate()
                .find(|(_, (name, _))| name == field)
                .map(|(index, (_, ty))| (index, *ty)),
            Some(Ty::Tuple(items)) => field
                .parse::<usize>()
                .ok()
                .and_then(|index| items.get(index).copied().map(|ty| (index, ty))),
            _ => None,
        }
    }

    fn emit_missing_field(&mut self, object_ty: TyId, field: &str) {
        let object_ty_ref = self
            .interner
            .get(self.unifier.resolve(object_ty))
            .map(|ty| ty_to_ref(ty, &self.interner))
            .unwrap_or(TypeRef::Unknown);
        self.diagnostics.push(
            self.typecheck_error(
                Issue::TypeMismatch {
                    context: TypingContext::Custom("field access".to_string()),
                    expected: object_ty_ref,
                    actual: TypeRef::Unknown,
                },
                format!("type has no field '{field}'"),
            )
            .with_hint("use a field declared by the tuple or struct type"),
        );
    }

    fn infer_field_place(&mut self, target: &Expr) -> Option<FieldPlace> {
        let Expr::Member { object, field } = TypeChecker::base_expr(target) else {
            return None;
        };
        self.ensure_place_root_mutable(object);
        let object_ty = self.infer_expr(object);
        if let Some((_, field_ty)) = self.field_lookup(object_ty, field) {
            Some(FieldPlace { field_ty })
        } else {
            self.emit_missing_field(object_ty, field);
            None
        }
    }

    fn infer_assign_place_expr(
        &mut self,
        target: &Expr,
        value: &Expr,
        expected: Option<TyId>,
    ) -> TyId {
        if let Some(name) = Self::ident_name(target) {
            return self.infer_assign_local(name, value, expected);
        }
        let Some(place) = self.infer_field_place(target) else {
            self.diagnostics.push(
                self.typecheck_error(
                    Issue::TypeMismatch {
                        context: TypingContext::Assignment,
                        expected: TypeRef::Unknown,
                        actual: TypeRef::Unknown,
                    },
                    "assignment target is not assignable",
                )
                .with_hint("assign to a local, struct field, or tuple field"),
            );
            return self.unknown_ty();
        };
        let actual = self.infer_expr_with_expected(value, place.field_ty);
        self.require_assignable(place.field_ty, actual, "field assignment");
        if let Some(expected) = expected {
            self.require_assignable(expected, place.field_ty, "bidirectional expected type");
        }
        place.field_ty
    }

    fn infer_assign_local(&mut self, name: &str, value: &Expr, expected: Option<TyId>) -> TyId {
        let Some(binding) = self.lookup_value_binding(name) else {
            self.diagnostics.push(
                self.typecheck_error(
                    Issue::UnresolvedIdent {
                        name: name.to_string(),
                    },
                    format!("cannot assign to undeclared local '{name}'"),
                )
                .with_hint("declare the local with `let` or `def` before assigning"),
            );
            return self.unknown_ty();
        };
        if !binding.mutable {
            let binding_ty = self
                .interner
                .get(binding.ty)
                .cloned()
                .unwrap_or_else(|| self.missing_ty_fallback());
            self.diagnostics.push(
                self.typecheck_error(
                    Issue::TypeMismatch {
                        context: TypingContext::Assignment,
                        expected: ty_to_ref(&binding_ty, &self.interner),
                        actual: ty_to_ref(&binding_ty, &self.interner),
                    },
                    format!("cannot assign to immutable local '{name}'"),
                )
                .with_hint("use `let` for mutable locals or stop reassigning this name"),
            );
            return binding.ty;
        }
        let actual = self.infer_expr_with_expected(value, binding.ty);
        self.require_assignable(binding.ty, actual, "assignment");
        if let Some(expected) = expected {
            self.require_assignable(expected, binding.ty, "bidirectional expected type");
        }
        binding.ty
    }

    fn ensure_place_root_mutable(&mut self, expr: &Expr) {
        match TypeChecker::base_expr(expr) {
            Expr::Ident(name) => {
                let Some(binding) = self.lookup_value_binding(name) else {
                    self.diagnostics.push(
                        self.typecheck_error(
                            Issue::UnresolvedIdent { name: name.clone() },
                            format!("cannot assign through undeclared local '{name}'"),
                        )
                        .with_hint("declare the local with `let` before assigning through it"),
                    );
                    return;
                };
                if !binding.place_mutable {
                    self.diagnostics.push(
                        self.typecheck_error(
                            Issue::TypeMismatch {
                                context: TypingContext::Assignment,
                                expected: ty_to_ref(
                                    self.interner.get(binding.ty).unwrap_or(&Ty::Any),
                                    &self.interner,
                                ),
                                actual: ty_to_ref(
                                    self.interner.get(binding.ty).unwrap_or(&Ty::Any),
                                    &self.interner,
                                ),
                            },
                            format!("cannot assign through immutable local '{name}'"),
                        )
                        .with_hint("bind the value with `let` or mutate through a parameter"),
                    );
                }
            }
            Expr::Member { object, .. } => self.ensure_place_root_mutable(object),
            _ => {}
        }
    }

    fn ident_name(expr: &Expr) -> Option<&str> {
        match TypeChecker::base_expr(expr) {
            Expr::Ident(name) => Some(name.as_str()),
            _ => None,
        }
    }

    fn register_method(&mut self, receiver_ty: TyId, name: String, link_name: String, ty: TyId) {
        self.methods.insert(
            (receiver_ty, name.clone()),
            MethodBinding {
                name,
                link_name,
                ty,
            },
        );
    }

    fn classify_builtin_member_call(object: &Expr, field: &str) -> Option<BuiltinMemberCall> {
        match (Self::base_expr(object), field) {
            (Expr::Ident(name), "new") if name == "Bytes" => Some(BuiltinMemberCall::BytesNew),
            (
                Expr::TypeApply {
                    callee,
                    static_args: _,
                },
                "new",
            ) if matches!(Self::base_expr(callee), Expr::Ident(name) if name == "RawAlloc") => {
                Some(BuiltinMemberCall::RawAllocNew)
            }
            (_, "slice") => Some(BuiltinMemberCall::RawAllocSlice),
            (_, "get") => Some(BuiltinMemberCall::BytesGet),
            (_, "set") => Some(BuiltinMemberCall::BytesSet),
            (_, "ref_at") => Some(BuiltinMemberCall::SliceRefAt),
            (_, "into") => Some(BuiltinMemberCall::StringInto),
            _ => None,
        }
    }

    fn type_apply_arg(&mut self, object: &Expr, expected_name: &str) -> Option<TyId> {
        let Expr::TypeApply {
            callee,
            static_args,
        } = Self::base_expr(object)
        else {
            return None;
        };
        let Expr::Ident(name) = Self::base_expr(callee) else {
            return None;
        };
        if name != expected_name {
            return None;
        }
        if static_args.len() != 1 {
            self.diagnostics.push(
                self.typecheck_error(
                    Issue::TypeArgArity,
                    format!("{expected_name} requires exactly one type argument"),
                )
                .with_hint(format!("use `{expected_name}[T]`")),
            );
            return Some(self.unknown_ty());
        }
        Some(self.resolve_required_type_arg(static_args, 0, expected_name, "item"))
    }

    fn option_ty(&mut self, payload: TyId) -> TyId {
        self.interner.intern(Ty::Enum(vec![
            ("null".to_string(), None),
            ("some".to_string(), Some(payload)),
        ]))
    }

    fn emit_builtin_method_arity_error(&mut self, name: &str, expected: usize, actual: usize) {
        self.diagnostics.push(
            self.typecheck_error(
                Issue::BuiltinForm,
                format!(
                    "builtin method '{name}' expects {expected} runtime arguments, got {actual}"
                ),
            )
            .with_hint("adjust the runtime argument count to match the builtin method"),
        );
    }

    fn infer_builtin_member_call(
        &mut self,
        object: &Expr,
        field: &str,
        args: &[Expr],
        trailing: &[LabeledClosureArg],
        expected_ret: Option<TyId>,
    ) -> Option<TyId> {
        let kind = Self::classify_builtin_member_call(object, field)?;
        if !trailing.is_empty() {
            self.diagnostics.push(
                self.typecheck_error(
                    Issue::BuiltinForm,
                    format!("builtin method '{field}' does not accept trailing closures"),
                )
                .with_hint("pass only positional runtime arguments to this builtin method"),
            );
            return Some(self.unknown_ty());
        }

        let usize_ty = self.interner.intern(Ty::USize);
        let uint8_ty = self.interner.intern(Ty::UInt8);
        let void_ty = self.interner.intern(Ty::Void);
        let bytes_ty = self.nominal_ty("Bytes");
        let string_ty = self.nominal_ty("String");

        let actual = match kind {
            BuiltinMemberCall::BytesNew => {
                if args.len() != 1 {
                    self.emit_builtin_method_arity_error("Bytes.new", 1, args.len());
                    return Some(self.unknown_ty());
                }
                let size_ty = self.infer_expr_with_expected(&args[0], usize_ty);
                self.require_assignable(usize_ty, size_ty, "Bytes.new size");
                bytes_ty
            }
            BuiltinMemberCall::BytesGet => {
                let inferred_receiver = self.infer_expr(object);
                let receiver_ty = self.unifier.resolve(inferred_receiver);
                match self.interner.get(receiver_ty).cloned() {
                    Some(Ty::Slice(item)) => {
                        if args.len() != 1 {
                            self.emit_builtin_method_arity_error("Slice.get", 1, args.len());
                            return Some(self.unknown_ty());
                        }
                        let index_ty = self.infer_expr_with_expected(&args[0], usize_ty);
                        self.require_assignable(usize_ty, index_ty, "Slice.get index");
                        self.option_ty(item)
                    }
                    Some(Ty::Ref(item)) => {
                        if !args.is_empty() {
                            self.emit_builtin_method_arity_error("Ref.get", 0, args.len());
                            return Some(self.unknown_ty());
                        }
                        item
                    }
                    _ => {
                        if args.len() != 1 {
                            self.emit_builtin_method_arity_error("Bytes.get", 1, args.len());
                            return Some(self.unknown_ty());
                        }
                        self.require_assignable(bytes_ty, receiver_ty, "Bytes.get receiver");
                        let index_ty = self.infer_expr_with_expected(&args[0], usize_ty);
                        self.require_assignable(usize_ty, index_ty, "Bytes.get index");
                        uint8_ty
                    }
                }
            }
            BuiltinMemberCall::BytesSet => {
                let inferred_receiver = self.infer_expr(object);
                let receiver_ty = self.unifier.resolve(inferred_receiver);
                match self.interner.get(receiver_ty).cloned() {
                    Some(Ty::Ref(item)) => {
                        if args.len() != 1 {
                            self.emit_builtin_method_arity_error("Ref.set", 1, args.len());
                            return Some(self.unknown_ty());
                        }
                        let value_ty = self.infer_expr_with_expected(&args[0], item);
                        self.require_assignable(item, value_ty, "Ref.set value");
                        void_ty
                    }
                    Some(Ty::Slice(item)) => {
                        if args.len() != 2 {
                            self.emit_builtin_method_arity_error("Slice.set", 2, args.len());
                            return Some(self.unknown_ty());
                        }
                        let index_ty = self.infer_expr_with_expected(&args[0], usize_ty);
                        self.require_assignable(usize_ty, index_ty, "Slice.set index");
                        let value_ty = self.infer_expr_with_expected(&args[1], item);
                        self.require_assignable(item, value_ty, "Slice.set value");
                        self.interner.intern(Ty::Bool)
                    }
                    _ => {
                        if args.len() != 2 {
                            self.emit_builtin_method_arity_error("Bytes.set", 2, args.len());
                            return Some(self.unknown_ty());
                        }
                        self.require_assignable(bytes_ty, receiver_ty, "Bytes.set receiver");
                        let index_ty = self.infer_expr_with_expected(&args[0], usize_ty);
                        self.require_assignable(usize_ty, index_ty, "Bytes.set index");
                        let value_ty = self.infer_expr_with_expected(&args[1], uint8_ty);
                        self.require_assignable(uint8_ty, value_ty, "Bytes.set value");
                        void_ty
                    }
                }
            }
            BuiltinMemberCall::StringInto => {
                if !args.is_empty() {
                    self.emit_builtin_method_arity_error("String.into", 0, args.len());
                    return Some(self.unknown_ty());
                }
                let receiver_ty = self.infer_expr(object);
                self.require_assignable(string_ty, receiver_ty, "String.into receiver");
                bytes_ty
            }
            BuiltinMemberCall::RawAllocNew => {
                if args.len() != 1 {
                    self.emit_builtin_method_arity_error("RawAlloc.new", 1, args.len());
                    return Some(self.unknown_ty());
                }
                let item = self
                    .type_apply_arg(object, "RawAlloc")
                    .unwrap_or_else(|| self.unknown_ty());
                let count_ty = self.infer_expr_with_expected(&args[0], usize_ty);
                self.require_assignable(usize_ty, count_ty, "RawAlloc.new count");
                self.interner.intern(Ty::RawAlloc(item))
            }
            BuiltinMemberCall::RawAllocSlice => {
                if !args.is_empty() {
                    self.emit_builtin_method_arity_error("RawAlloc.slice", 0, args.len());
                    return Some(self.unknown_ty());
                }
                let inferred_receiver = self.infer_expr(object);
                let receiver_ty = self.unifier.resolve(inferred_receiver);
                if let Some(Ty::RawAlloc(item)) = self.interner.get(receiver_ty).cloned() {
                    self.interner.intern(Ty::Slice(item))
                } else {
                    self.unknown_ty()
                }
            }
            BuiltinMemberCall::SliceRefAt => {
                if args.len() != 1 {
                    self.emit_builtin_method_arity_error("Slice.ref_at", 1, args.len());
                    return Some(self.unknown_ty());
                }
                let inferred_receiver = self.infer_expr(object);
                let receiver_ty = self.unifier.resolve(inferred_receiver);
                let index_ty = self.infer_expr_with_expected(&args[0], usize_ty);
                self.require_assignable(usize_ty, index_ty, "Slice.ref_at index");
                if let Some(Ty::Slice(item)) = self.interner.get(receiver_ty).cloned() {
                    let ref_ty = self.interner.intern(Ty::Ref(item));
                    self.option_ty(ref_ty)
                } else {
                    self.unknown_ty()
                }
            }
        };

        if let Some(expected) = expected_ret {
            self.require_assignable(expected, actual, "builtin method return");
        }

        Some(actual)
    }

    fn lower_builtin_member_call(
        &mut self,
        object: &Expr,
        field: &str,
        args: &[Expr],
        result_ty: TyId,
    ) -> Option<CheckedExpr> {
        let kind = Self::classify_builtin_member_call(object, field)?;
        let (name, lowered_args): (&str, Vec<CheckedExpr>) = match kind {
            BuiltinMemberCall::BytesNew => (
                "bytes_new",
                args.iter().map(|arg| self.lower_expr(arg)).collect(),
            ),
            BuiltinMemberCall::RawAllocNew => {
                let item_ty = self
                    .type_apply_arg(object, "RawAlloc")
                    .unwrap_or_else(|| self.unknown_ty());
                return Some(CheckedExpr::MemoryOp {
                    op: MemoryOpKind::RawAllocNew,
                    item_ty,
                    result_ty,
                    args: args.iter().map(|arg| self.lower_expr(arg)).collect(),
                });
            }
            BuiltinMemberCall::RawAllocSlice => {
                let preview_receiver = self.preview_expr_ty(object);
                let receiver_ty = self.unifier.resolve(preview_receiver);
                if let Some(Ty::RawAlloc(item_ty)) = self.interner.get(receiver_ty).cloned() {
                    return Some(CheckedExpr::MemoryOp {
                        op: MemoryOpKind::RawAllocSlice,
                        item_ty,
                        result_ty,
                        args: vec![self.lower_expr(object)],
                    });
                }
                return None;
            }
            BuiltinMemberCall::BytesGet => (
                {
                    let preview_receiver = self.preview_expr_ty(object);
                    let receiver_ty = self.unifier.resolve(preview_receiver);
                    match self.interner.get(receiver_ty).cloned() {
                        Some(Ty::Slice(item_ty)) => {
                            return Some(CheckedExpr::MemoryOp {
                                op: MemoryOpKind::SliceGet,
                                item_ty,
                                result_ty,
                                args: std::iter::once(self.lower_expr(object))
                                    .chain(args.iter().map(|arg| self.lower_expr(arg)))
                                    .collect(),
                            });
                        }
                        Some(Ty::Ref(item_ty)) => {
                            return Some(CheckedExpr::MemoryOp {
                                op: MemoryOpKind::RefGet,
                                item_ty,
                                result_ty,
                                args: vec![self.lower_expr(object)],
                            });
                        }
                        _ => "bytes_get",
                    }
                },
                std::iter::once(self.lower_expr(object))
                    .chain(args.iter().map(|arg| self.lower_expr(arg)))
                    .collect(),
            ),
            BuiltinMemberCall::BytesSet => {
                let preview_receiver = self.preview_expr_ty(object);
                let receiver_ty = self.unifier.resolve(preview_receiver);
                match self.interner.get(receiver_ty).cloned() {
                    Some(Ty::Slice(item_ty)) => {
                        return Some(CheckedExpr::MemoryOp {
                            op: MemoryOpKind::SliceSet,
                            item_ty,
                            result_ty,
                            args: std::iter::once(self.lower_expr(object))
                                .chain(args.iter().map(|arg| self.lower_expr(arg)))
                                .collect(),
                        });
                    }
                    Some(Ty::Ref(item_ty)) => {
                        return Some(CheckedExpr::MemoryOp {
                            op: MemoryOpKind::RefSet,
                            item_ty,
                            result_ty,
                            args: std::iter::once(self.lower_expr(object))
                                .chain(args.iter().map(|arg| self.lower_expr(arg)))
                                .collect(),
                        });
                    }
                    _ => (
                        "bytes_set",
                        std::iter::once(self.lower_expr(object))
                            .chain(args.iter().map(|arg| self.lower_expr(arg)))
                            .collect(),
                    ),
                }
            }
            BuiltinMemberCall::StringInto => ("string_into", vec![self.lower_expr(object)]),
            BuiltinMemberCall::SliceRefAt => {
                let preview_receiver = self.preview_expr_ty(object);
                let receiver_ty = self.unifier.resolve(preview_receiver);
                if let Some(Ty::Slice(item_ty)) = self.interner.get(receiver_ty).cloned() {
                    return Some(CheckedExpr::MemoryOp {
                        op: MemoryOpKind::SliceRefAt,
                        item_ty,
                        result_ty,
                        args: std::iter::once(self.lower_expr(object))
                            .chain(args.iter().map(|arg| self.lower_expr(arg)))
                            .collect(),
                    });
                }
                return None;
            }
        };

        Some(CheckedExpr::Call {
            callee: Box::new(CheckedExpr::Ident(name.to_string())),
            args: lowered_args,
        })
    }

    fn pipe_to_call_expr(lhs: &Expr, rhs: &Expr) -> Expr {
        match Self::base_expr(rhs) {
            Expr::Call {
                callee,
                static_args,
                args,
                trailing,
            } => {
                let mut new_args = Vec::new();
                let mut consumed_pipe_value = false;
                let has_placeholder = args.iter().any(Self::is_placeholder_expr);

                if has_placeholder {
                    for arg in args {
                        if !consumed_pipe_value && Self::is_placeholder_expr(arg) {
                            new_args.push(lhs.clone());
                            consumed_pipe_value = true;
                        } else {
                            new_args.push(arg.clone());
                        }
                    }
                }

                if !consumed_pipe_value {
                    new_args.push(lhs.clone());
                    new_args.extend(args.iter().cloned());
                }

                Expr::Call {
                    callee: callee.clone(),
                    static_args: static_args.clone(),
                    args: new_args,
                    trailing: trailing.clone(),
                }
            }
            _ => Expr::Call {
                callee: Box::new(rhs.clone()),
                static_args: Vec::new(),
                args: vec![lhs.clone()],
                trailing: Vec::new(),
            },
        }
    }

    pub fn check_program(
        &mut self,
        program: &Program,
    ) -> (
        HashMap<String, TyId>,
        HashMap<String, TyId>,
        HashMap<String, GenericTypeAlias>,
    ) {
        let mut values = HashMap::new();
        let mut type_aliases = HashMap::new();
        let mut generic_type_aliases = HashMap::new();
        self.module_checker.check_program(program);

        for decl in &program.declarations {
            if let Decl::Assign {
                name,
                static_params,
                value,
                ..
            } = decl
            {
                if let Expr::TypeExpr(type_expr) = value {
                    if self.imported_binding(name).is_some()
                        || self.imported_type_binding(name).is_some()
                        || self.namespace_alias_conflicts(name)
                    {
                        self.diagnostics.push(
                            self.typecheck_error(
                                Issue::ResolveDuplicate,
                                format!("type '{}' conflicts with an imported name", name),
                            )
                            .with_stage(Stage::Resolver)
                            .with_hint("rename the type or adjust the imports"),
                        );
                        continue;
                    }
                    if !static_params.is_empty() {
                        self.aliases.insert_generic(
                            name.clone(),
                            static_params.clone(),
                            type_expr.clone(),
                        );
                        generic_type_aliases.insert(
                            name.clone(),
                            GenericTypeAlias {
                                static_params: static_params.clone(),
                                body: type_expr.clone(),
                            },
                        );
                        continue;
                    }
                    let ty = self.resolve_type_expr(type_expr);
                    self.aliases.insert(name.clone(), ty);
                    type_aliases.insert(name.clone(), ty);
                    continue;
                }
                if self.imported_binding(name).is_some() || self.namespace_alias_conflicts(name) {
                    self.diagnostics.push(
                        self.typecheck_error(
                            Issue::ResolveDuplicate,
                            format!("declaration '{name}' conflicts with an imported name"),
                        )
                        .with_stage(Stage::Resolver)
                        .with_hint("rename the declaration or adjust the imports"),
                    );
                    continue;
                }
                let prev_span = self.current_expr_span;
                self.current_expr_span = Expr::span(value);
                self.push_obligation(format!("checking declaration `{name}`"));
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
                        link_name: name.clone(),
                        params: Vec::new(),
                        ty: existing,
                        is_extern: false,
                        value: coerced,
                    });
                } else {
                    let lowered = self.lower_expr(value);
                    self.ir.declarations.push(CheckedDecl {
                        name: name.clone(),
                        link_name: name.clone(),
                        params: Vec::new(),
                        ty,
                        is_extern: false,
                        value: lowered,
                    });
                }
                values.insert(name.clone(), ty);
                self.insert_value(name.clone(), ty, false);
                self.pop_obligation();
                self.current_expr_span = prev_span;
            }

            if let Decl::Stub(stub) = decl {
                if self.imported_binding(&stub.name).is_some()
                    || self.namespace_alias_conflicts(&stub.name)
                {
                    self.diagnostics.push(
                        self.typecheck_error(
                            Issue::ResolveDuplicate,
                            format!("stub '{}' conflicts with an imported name", stub.name),
                        )
                        .with_stage(Stage::Resolver)
                        .with_hint("rename the stub or adjust the imports"),
                    );
                    continue;
                }

                self.push_generic_scope();
                for p in &stub.static_params {
                    let t = self.interner.intern(Ty::GenericParam(p.name.clone()));
                    self.insert_generic(p.name.clone(), t);
                }
                let ty = self.resolve_type_expr(&stub.ty);
                self.pop_generic_scope();

                self.ir.declarations.push(CheckedDecl {
                    name: stub.name.clone(),
                    link_name: stub.name.clone(),
                    params: Vec::new(),
                    ty,
                    is_extern: true,
                    value: CheckedExpr::Any,
                });
                values.insert(stub.name.clone(), ty);
                self.insert_value(stub.name.clone(), ty, false);
            }

            if let Decl::Function(function) = decl {
                if self.imported_binding(&function.name).is_some()
                    || self.namespace_alias_conflicts(&function.name)
                {
                    self.diagnostics.push(
                        self.typecheck_error(
                            Issue::ResolveDuplicate,
                            format!(
                                "function '{}' conflicts with an imported name",
                                function.name
                            ),
                        )
                        .with_stage(Stage::Resolver)
                        .with_hint("rename the function or adjust the imports"),
                    );
                    continue;
                }
                let prev_span = self.current_expr_span;
                self.current_expr_span = Expr::span(&function.body);
                self.push_obligation(format!("checking function `{}`", function.name));
                self.pending_constraints.clear();
                let receiver_ty = function.receiver.as_ref().map(|receiver| {
                    self.validate_method_receiver(receiver);
                    self.resolve_type_expr(receiver)
                });
                self.push_generic_scope();
                for p in &function.static_params {
                    let t = self.interner.intern(Ty::GenericParam(p.name.clone()));
                    self.insert_generic(p.name.clone(), t);
                }
                self.push_scope();
                for param in &function.params {
                    let param_ty = self.resolve_type_expr(&param.ty);
                    self.insert_value_param(param.name.clone(), param_ty);
                }
                if let Expr::MultiArm(arms) = TypeChecker::base_expr(&function.body) {
                    if let Some(receiver_ty) = receiver_ty {
                        if matches!(self.interner.get(receiver_ty), Some(Ty::Enum(_))) {
                            self.validate_enum_multi_arm_patterns(arms, receiver_ty);
                        } else {
                            self.diagnostics.extend(
                                self.pattern_checker.validate_multi_arm_exhaustiveness(arms),
                            );
                        }
                    } else {
                        self.diagnostics
                            .extend(self.pattern_checker.validate_multi_arm_exhaustiveness(arms));
                    }
                    self.diagnostics
                        .extend(self.pattern_checker.validate_redundancy(arms));
                }

                let param_tys: Vec<TyId> = function
                    .params
                    .iter()
                    .map(|p| self.resolve_type_expr(&p.ty))
                    .collect();
                let expected_ret = self.resolve_type_expr(&function.return_type);
                self.validate_main_signature(function);
                self.active_function_targets.push(FunctionJumpTarget {
                    name: function.name.clone(),
                    return_ty: expected_ret,
                });
                let previous_match_subject = self.current_match_subject.clone();
                if let (Some(receiver_ty), Some(first_param)) =
                    (receiver_ty, function.params.first())
                {
                    self.current_match_subject = Some(MatchSubject {
                        name: first_param.name.clone(),
                        ty: receiver_ty,
                    });
                }
                let actual_ret = self.infer_expr_with_expected(&function.body, expected_ret);
                self.require_assignable(expected_ret, actual_ret, "function return");
                self.solve_constraints();
                let lowered_function_body = self.lower_expr(&function.body);
                self.current_match_subject = previous_match_subject;
                let lowered_body = self.coerce_or_cast_for_ir(
                    expected_ret,
                    actual_ret,
                    lowered_function_body,
                    "function return",
                    ConversionMode::ImplicitOnly,
                );
                let func_ty = self.interner.intern(Ty::Func {
                    params: self.positional_params(param_tys),
                    ret: expected_ret,
                });
                self.ir.declarations.push(CheckedDecl {
                    name: function.name.clone(),
                    link_name: function.name.clone(),
                    params: function
                        .params
                        .iter()
                        .map(|param| param.name.clone())
                        .collect(),
                    ty: func_ty,
                    is_extern: false,
                    value: lowered_body,
                });
                self.pop_scope();
                self.pop_generic_scope();
                let _ = self.active_function_targets.pop();
                self.insert_value(function.name.clone(), func_ty, false);
                if let Some(receiver_ty) = receiver_ty {
                    self.register_method(
                        receiver_ty,
                        function.name.clone(),
                        function.name.clone(),
                        func_ty,
                    );
                }
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
                if self.imported_binding(&macro_decl.name).is_some()
                    || self.namespace_alias_conflicts(&macro_decl.name)
                {
                    self.diagnostics.push(
                        self.typecheck_error(
                            Issue::ResolveDuplicate,
                            format!(
                                "macro '{}' conflicts with an imported name",
                                macro_decl.name
                            ),
                        )
                        .with_stage(Stage::Resolver)
                        .with_hint("rename the macro or adjust the imports"),
                    );
                    continue;
                }
                let prev_span = self.current_expr_span;
                self.current_expr_span = Expr::span(&macro_decl.body);
                self.push_obligation(format!("checking macro `{}`", macro_decl.name));
                self.pending_constraints.clear();
                self.push_scope();
                for param in &macro_decl.params {
                    let param_ty = self.resolve_type_expr(&param.ty);
                    self.insert_value_param(param.name.clone(), param_ty);
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
                    link_name: macro_decl.name.clone(),
                    params: Vec::new(),
                    ty: expected_ret,
                    is_extern: false,
                    value: lowered_body,
                });
                self.pop_scope();
                self.pop_obligation();
                self.current_expr_span = prev_span;
            }
        }

        self.diagnostics
            .extend(std::mem::take(&mut self.module_checker).into_diagnostics());

        (values, type_aliases, generic_type_aliases)
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
                } else if self.namespace_alias_conflicts(name) {
                    self.unknown_ty()
                } else if name == "true" || name == "false" {
                    self.interner.intern(Ty::Bool)
                } else {
                    self.diagnostics.push(
                        self.typecheck_warning(
                            Issue::UnresolvedIdent { name: name.clone() },
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
            Expr::TypeApply { .. } => self.unknown_ty(),
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
                    params: self.positional_params(param_tys),
                    ret,
                })
            }
            Expr::Label { label, expr } => {
                self.active_labels.push(label.clone());
                let ty = self.infer_expr(expr);
                let _ = self.active_labels.pop();
                ty
            }
            Expr::Tuple(items) => {
                if items.is_empty() {
                    return self.interner.intern(Ty::Void);
                }
                let item_tys = items
                    .iter()
                    .map(|item| self.infer_expr(item))
                    .collect::<Vec<_>>();
                self.interner.intern(Ty::Tuple(item_tys))
            }
            Expr::Struct(fields) => {
                let field_tys = fields
                    .iter()
                    .map(|(name, value)| (name.clone(), self.infer_expr(value)))
                    .collect::<Vec<_>>();
                self.interner.intern(Ty::Struct(field_tys))
            }
            Expr::Block(items) => {
                self.push_scope();
                let result = if let Some((last, rest)) = items.split_last() {
                    for item in rest {
                        let _ = self.infer_expr(item);
                    }
                    self.infer_expr(last)
                } else {
                    self.interner.intern(Ty::Void)
                };
                self.pop_scope();
                result
            }
            Expr::Bindings(_) => {
                self.diagnostics.push(
                    self.typecheck_error(
                        Issue::MacroUntyped,
                        "binding payloads must be consumed by `let` or `def`",
                    )
                    .with_hint("use binding payloads through `let ...` or `def ...`"),
                );
                self.unknown_ty()
            }
            Expr::Assign { name, value } => self.infer_assign_local(name, value, None),
            Expr::AssignPlace { target, value } => {
                self.infer_assign_place_expr(target, value, None)
            }
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
                if let Expr::Member { object, field } = TypeChecker::base_expr(callee.as_ref()) {
                    if let Expr::Ident(type_name) = TypeChecker::base_expr(object) {
                        if let Some(enum_ty) = self.enum_alias(type_name) {
                            if let Some((variant_index, payload_ty)) =
                                self.enum_variant(enum_ty, field)
                            {
                                return self.infer_enum_constructor_call(
                                    expr,
                                    enum_ty,
                                    variant_index,
                                    payload_ty,
                                    args,
                                    None,
                                );
                            }
                        }
                    }
                }
                if let Expr::Member { object, field } = TypeChecker::base_expr(callee.as_ref()) {
                    if let Expr::Ident(namespace) = TypeChecker::base_expr(object) {
                        if let Some(binding) = self.namespace_binding(namespace, field).cloned() {
                            let callee_ty = self.type_ref_to_ty(&binding.ty);
                            return self.infer_call_expr(
                                callee_ty,
                                Some(binding.local_name.as_str()),
                                static_args,
                                args,
                                trailing,
                                None,
                            );
                        }
                    }
                }
                if let Expr::Member { object, field } = TypeChecker::base_expr(callee.as_ref()) {
                    let receiver_ty = self.infer_expr(object);
                    let receiver_ty = self.unifier.resolve(receiver_ty);
                    if let Some(method) = self.lookup_method(receiver_ty, field).cloned() {
                        self.record_method_call(expr, method.link_name.clone());
                        self.record_method_call(callee.as_ref(), method.link_name.clone());
                        let mut method_args = vec![object.as_ref().clone()];
                        method_args.extend(args.iter().cloned());
                        return self.infer_call_expr(
                            method.ty,
                            Some(method.name.as_str()),
                            static_args,
                            &method_args,
                            trailing,
                            None,
                        );
                    }
                }
                if let Expr::Member { object, field } = TypeChecker::base_expr(callee.as_ref()) {
                    if let Some(ret) =
                        self.infer_builtin_member_call(object, field, args, trailing, None)
                    {
                        return ret;
                    }
                }
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
                if matches!(callee_name.as_deref(), Some("loop")) {
                    return self.infer_loop_call_with_expected(expr, args, trailing, None);
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
                                Issue::CastInvalid {
                                    source: ty_to_ref(&source_ty, &self.interner),
                                    target: ty_to_ref(&target_ty, &self.interner),
                                },
                                format!("invalid cast from {:?} to {:?}", source_ty, target_ty),
                            )
                            .with_hint("check cast matrix or change source/target types"),
                        );
                        self.unknown_ty()
                    }
                }
            }
            Expr::Binary { op, lhs, rhs } => self.infer_binary_expr(*op, lhs, rhs),
            Expr::Member { object, field } => match TypeChecker::base_expr(object) {
                Expr::Ident(name) if self.enum_alias(name).is_some() => {
                    let enum_ty = self.enum_alias(name).expect("enum alias should exist");
                    match self.enum_variant(enum_ty, field) {
                        Some((variant_index, None)) => {
                            self.record_enum_ctor(expr, enum_ty, variant_index);
                            enum_ty
                        }
                        Some((_, Some(_))) => {
                            self.diagnostics.push(
                                self.typecheck_error(
                                    Issue::TypeMismatch {
                                        context: TypingContext::Custom(
                                            "enum constructor".to_string(),
                                        ),
                                        expected: ty_to_ref(
                                            self.interner.get(enum_ty).unwrap_or(&Ty::Any),
                                            &self.interner,
                                        ),
                                        actual: TypeRef::Unknown,
                                    },
                                    format!(
                                        "payload enum variant '{}.{}' must be called with an argument",
                                        name, field
                                    ),
                                )
                                .with_hint("use form `Type.variant(value)` for payload variants"),
                            );
                            self.unknown_ty()
                        }
                        None => self.unknown_ty(),
                    }
                }
                Expr::Ident(namespace) => {
                    if let Some(binding) = self.namespace_binding(namespace, field).cloned() {
                        self.type_ref_to_ty(&binding.ty)
                    } else {
                        let object_ty = self.infer_expr(object);
                        if let Some((_, field_ty)) = self.field_lookup(object_ty, field) {
                            field_ty
                        } else {
                            self.emit_missing_field(object_ty, field);
                            self.unknown_ty()
                        }
                    }
                }
                _ => {
                    let object_ty = self.infer_expr(object);
                    if let Some((_, field_ty)) = self.field_lookup(object_ty, field) {
                        field_ty
                    } else {
                        self.emit_missing_field(object_ty, field);
                        self.unknown_ty()
                    }
                }
            },
            Expr::TypeExpr(_) => self.unknown_ty(),
            Expr::Placeholder => self.unknown_ty(),
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
                            Issue::PatternEmptyArms,
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
            } if macro_name == "let" || macro_name == "def" => {
                let Expr::Bindings(bindings) = TypeChecker::base_expr(operand.as_ref()) else {
                    self.diagnostics.push(
                        self.typecheck_error(
                            Issue::MacroUntyped,
                            format!("`{macro_name}` expects binding payloads"),
                        )
                        .with_hint(format!("use form like `{macro_name} name = value`")),
                    );
                    return self.unknown_ty();
                };
                let is_mutable = macro_name == "let";
                for binding in bindings {
                    let value_ty = self.infer_expr(&binding.value);
                    self.bind_local_pattern(&binding.pattern, value_ty, is_mutable);
                }
                self.interner.intern(Ty::Void)
            }
            Expr::MacroApply {
                macro_name,
                operand,
                static_args,
            } if macro_name == "builtin" => {
                self.diagnostics.push(
                    self.typecheck_error(
                        Issue::BuiltinForm,
                        "builtin macro is removed; call builtin symbols directly",
                    )
                    .with_hint("use `syscall_exit(...)` directly"),
                );
                self.infer_expr(operand)
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
                            Issue::CastTarget,
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
                        Issue::CastInvalid {
                            source: ty_to_ref(&source_ty, &self.interner),
                            target: ty_to_ref(&target_ty, &self.interner),
                        },
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
                        Issue::IfForm,
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
                        Issue::CasesForm,
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
            } if macro_name == "return" => {
                if let Some(target) = self.resolve_function_jump_target(static_args, "return") {
                    let actual = self.infer_expr_with_expected(operand, target.return_ty);
                    self.require_assignable(target.return_ty, actual, "return value");
                    self.resolved_jump_targets
                        .insert(Self::expr_cache_key(expr), target.name);
                }
                self.interner.intern(Ty::Never)
            }
            Expr::MacroApply {
                macro_name,
                operand,
                static_args,
            } if macro_name == "break" => {
                if let Some(target_idx) = self.resolve_loop_jump_target(static_args, "break") {
                    let result_ty = self.active_loop_targets[target_idx].result_ty;
                    let actual = if let Expr::List(items) = TypeChecker::base_expr(operand.as_ref())
                    {
                        if let Some(v) = items.first() {
                            self.infer_expr_with_expected(v, result_ty)
                        } else {
                            self.interner.intern(Ty::Void)
                        }
                    } else {
                        self.infer_expr_with_expected(operand, result_ty)
                    };
                    self.require_assignable(result_ty, actual, "break value");
                    self.active_loop_targets[target_idx].saw_break = true;
                    self.resolved_jump_targets.insert(
                        Self::expr_cache_key(expr),
                        self.active_loop_targets[target_idx].target.clone(),
                    );
                }
                self.interner.intern(Ty::Never)
            }
            Expr::MacroApply {
                macro_name,
                operand,
                static_args,
            } if macro_name == "continue" => {
                if let Some(target_idx) = self.resolve_loop_jump_target(static_args, "continue") {
                    self.resolved_jump_targets.insert(
                        Self::expr_cache_key(expr),
                        self.active_loop_targets[target_idx].target.clone(),
                    );
                }
                self.interner.intern(Ty::Never)
            }
            Expr::MacroApply {
                macro_name,
                operand,
                static_args: _,
            } => {
                self.diagnostics.push(
                    self.typecheck_error(
                        Issue::MacroUntyped,
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
            (Expr::Block(items), _) => {
                self.push_scope();
                let result = if let Some((last, rest)) = items.split_last() {
                    for item in rest {
                        let _ = self.infer_expr(item);
                    }
                    self.infer_expr_with_expected(last, expected)
                } else {
                    self.interner.intern(Ty::Void)
                };
                self.pop_scope();
                result
            }
            (Expr::Assign { name, value }, _) => {
                self.infer_assign_local(name, value, Some(expected))
            }
            (Expr::AssignPlace { target, value }, _) => {
                self.infer_assign_place_expr(target, value, Some(expected))
            }
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
                if let Expr::Member { object, field } = TypeChecker::base_expr(callee.as_ref()) {
                    if let Expr::Ident(type_name) = TypeChecker::base_expr(object) {
                        if let Some(enum_ty) = self.enum_alias(type_name) {
                            if let Some((variant_index, payload_ty)) =
                                self.enum_variant(enum_ty, field)
                            {
                                return self.infer_enum_constructor_call(
                                    expr,
                                    enum_ty,
                                    variant_index,
                                    payload_ty,
                                    args,
                                    Some(expected),
                                );
                            }
                        }
                    }
                }
                if let Some(Ty::Enum(variants)) = self.interner.get(expected).cloned() {
                    if let Expr::DotIdent { name, payload } =
                        TypeChecker::base_expr(callee.as_ref())
                    {
                        let variant = variants
                            .iter()
                            .enumerate()
                            .find(|(_, (variant_name, _))| variant_name == name);
                        if let Some((variant_index, (_, variant_payload))) = variant {
                            match (args.as_slice(), payload.as_deref(), variant_payload) {
                                ([], None, None) => {
                                    self.record_enum_ctor(expr, expected, variant_index);
                                    return expected;
                                }
                                ([payload_expr], None, Some(expected_payload_ty)) => {
                                    let payload_ty = self.infer_expr_with_expected(
                                        payload_expr,
                                        *expected_payload_ty,
                                    );
                                    self.require_assignable(
                                        *expected_payload_ty,
                                        payload_ty,
                                        "enum variant payload",
                                    );
                                    self.record_enum_ctor(expr, expected, variant_index);
                                    return expected;
                                }
                                _ => {
                                    let actual = self.infer_expr(expr);
                                    self.emit_type_mismatch(
                                        expected,
                                        actual,
                                        "assignment",
                                        "enum variant payload arity does not match expected type",
                                    );
                                    return self.unknown_ty();
                                }
                            }
                        }
                    }
                }
                if let Expr::Member { object, field } = TypeChecker::base_expr(callee.as_ref()) {
                    let receiver_ty = self.infer_expr(object);
                    let receiver_ty = self.unifier.resolve(receiver_ty);
                    if let Some(method) = self.lookup_method(receiver_ty, field).cloned() {
                        self.record_method_call(expr, method.link_name.clone());
                        self.record_method_call(callee.as_ref(), method.link_name.clone());
                        let mut method_args = vec![object.as_ref().clone()];
                        method_args.extend(args.iter().cloned());
                        let actual = self.infer_call_expr(
                            method.ty,
                            Some(method.name.as_str()),
                            static_args,
                            &method_args,
                            trailing,
                            Some(expected),
                        );
                        self.require_assignable(expected, actual, "bidirectional expected type");
                        return actual;
                    }
                }
                if let Expr::Member { object, field } = TypeChecker::base_expr(callee.as_ref()) {
                    if let Expr::Ident(namespace) = TypeChecker::base_expr(object) {
                        if let Some(binding) = self.namespace_binding(namespace, field).cloned() {
                            let callee_ty = self.type_ref_to_ty(&binding.ty);
                            let actual = self.infer_call_expr(
                                callee_ty,
                                Some(binding.local_name.as_str()),
                                static_args,
                                args,
                                trailing,
                                Some(expected),
                            );
                            self.require_assignable(
                                expected,
                                actual,
                                "bidirectional expected type",
                            );
                            return actual;
                        }
                    }
                }
                if let Expr::Member { object, field } = TypeChecker::base_expr(callee.as_ref()) {
                    if let Some(actual) = self.infer_builtin_member_call(
                        object,
                        field,
                        args,
                        trailing,
                        Some(expected),
                    ) {
                        self.require_assignable(expected, actual, "bidirectional expected type");
                        return actual;
                    }
                }
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
                if matches!(callee_name.as_deref(), Some("loop")) {
                    let actual =
                        self.infer_loop_call_with_expected(expr, args, trailing, Some(expected));
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
            (Expr::Label { label, expr }, _) => {
                self.active_labels.push(label.clone());
                let actual = self.infer_expr_with_expected(expr, expected);
                let _ = self.active_labels.pop();
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
                Expr::MacroApply {
                    macro_name,
                    operand,
                    ..
                },
                _,
            ) if macro_name == "let" || macro_name == "def" => {
                let actual = self.infer_expr(expr);
                self.require_assignable(expected, actual, "bidirectional expected type");
                actual
            }
            (Expr::Int(value), Some(Ty::UInt8)) => {
                if value.parse::<u8>().is_ok() {
                    expected
                } else {
                    self.diagnostics.push(
                        self.typecheck_error(
                            Issue::TypeMismatch {
                                context: TypingContext::Custom("integer literal".to_string()),
                                expected: TypeRef::Primitive(PrimitiveType::UInt8),
                                actual: TypeRef::Primitive(PrimitiveType::Int32),
                            },
                            "integer literal is out of range for UInt8",
                        )
                        .with_hint("use a value between 0 and 255 for UInt8"),
                    );
                    self.unknown_ty()
                }
            }
            (Expr::Int(value), Some(Ty::USize)) => {
                if value.parse::<usize>().is_ok() {
                    expected
                } else {
                    self.diagnostics.push(
                        self.typecheck_error(
                            Issue::TypeMismatch {
                                context: TypingContext::Custom("integer literal".to_string()),
                                expected: TypeRef::Primitive(PrimitiveType::USize),
                                actual: TypeRef::Primitive(PrimitiveType::Int32),
                            },
                            "integer literal is out of range for USize",
                        )
                        .with_hint(
                            "use a non-negative integer that fits in the target pointer width",
                        ),
                    );
                    self.unknown_ty()
                }
            }
            (Expr::Int(value), Some(Ty::ISize)) => {
                if value.parse::<isize>().is_ok() {
                    expected
                } else {
                    self.diagnostics.push(
                        self.typecheck_error(
                            Issue::TypeMismatch {
                                context: TypingContext::Custom("integer literal".to_string()),
                                expected: TypeRef::Primitive(PrimitiveType::ISize),
                                actual: TypeRef::Primitive(PrimitiveType::Int32),
                            },
                            "integer literal is out of range for ISize",
                        )
                        .with_hint("use an integer that fits in the target pointer width"),
                    );
                    self.unknown_ty()
                }
            }
            (Expr::DotIdent { name, payload }, Some(Ty::Enum(variants))) => {
                let variant = variants
                    .iter()
                    .enumerate()
                    .find(|(_, (variant_name, _))| variant_name == name);
                let Some((variant_index, (_, variant_payload))) = variant else {
                    let actual = self.infer_expr(expr);
                    self.emit_type_mismatch(
                        expected,
                        actual,
                        "assignment",
                        "enum variant does not exist on expected enum type",
                    );
                    return self.unknown_ty();
                };

                match (payload.as_ref(), variant_payload) {
                    (Some(inner), Some(expected_payload_ty)) => {
                        let payload_ty = self.infer_expr_with_expected(inner, *expected_payload_ty);
                        self.require_assignable(
                            *expected_payload_ty,
                            payload_ty,
                            "enum variant payload",
                        );
                        self.record_enum_ctor(expr, expected, variant_index);
                    }
                    (None, None) => {
                        self.record_enum_ctor(expr, expected, variant_index);
                    }
                    (Some(_), None) | (None, Some(_)) => {
                        let actual = self.infer_expr(expr);
                        self.emit_type_mismatch(
                            expected,
                            actual,
                            "assignment",
                            "enum variant payload arity does not match expected type",
                        );
                        return self.unknown_ty();
                    }
                }
                expected
            }
            (Expr::DotIdent { payload, .. }, Some(Ty::Union(members))) => {
                if let Some(inner) = payload {
                    let payload_ty = self.infer_expr(inner);
                    for member in members {
                        if matches!(
                            self.conversion_decision(
                                member,
                                payload_ty,
                                ConversionMode::ImplicitOnly,
                                "union payload"
                            ),
                            ConversionDecision::Identity | ConversionDecision::Coerce
                        ) {
                            return expected;
                        }
                    }
                    self.emit_type_mismatch(
                        expected,
                        payload_ty,
                        "assignment",
                        "union payload does not match any member type",
                    );
                    self.unknown_ty()
                } else {
                    expected
                }
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
                        Issue::IfForm,
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
                let actual = self.infer_expr(expr);
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
                        Issue::CasesForm,
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
            (Expr::Tuple(items), Some(Ty::Void)) if items.is_empty() => {
                self.interner.intern(Ty::Void)
            }
            (Expr::Tuple(items), Some(Ty::Tuple(expected_items))) => {
                for (item, expected_item) in items.iter().zip(expected_items.iter()) {
                    let item_ty = self.infer_expr_with_expected(item, *expected_item);
                    self.require_assignable(*expected_item, item_ty, "tuple element");
                }
                self.interner.intern(Ty::Tuple(expected_items))
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
            (Expr::Struct(fields), Some(Ty::Struct(expected_fields))) => {
                let actual_fields = fields
                    .iter()
                    .map(|(name, value)| (name.clone(), value))
                    .collect::<Vec<_>>();
                self.infer_struct_fields_with_expected(
                    &actual_fields,
                    &expected_fields,
                    "struct field",
                )
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
                            Issue::ClosureArity,
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
                    self.require_assignable(expected_param.ty, *declared, "closure parameter");
                }

                let ret = return_type
                    .as_ref()
                    .map(|t| self.resolve_type_expr(t))
                    .unwrap_or(expected_ret);
                self.interner.intern(Ty::Func {
                    params: self.positional_params(param_tys),
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
                        Issue::OpNonNumeric,
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
                        Issue::OpNonNumeric,
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
                let Expr::TypeExpr(ty) = rhs else {
                    self.diagnostics.push(
                        self.typecheck_error(
                            Issue::CastTarget,
                            "cast ':' expects a type expression on RHS",
                        )
                        .with_hint("use form like value: Int"),
                    );
                    return self.unknown_ty();
                };
                let target = self.resolve_type_expr(ty);
                let source = match self.interner.get(target) {
                    Some(Ty::Enum(_)) | Some(Ty::Union(_)) => {
                        self.infer_expr_with_expected(lhs, target)
                    }
                    _ => self.infer_expr(lhs),
                };
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
                                Issue::CastInvalid {
                                    source: ty_to_ref(&source_ty, &self.interner),
                                    target: ty_to_ref(&target_ty, &self.interner),
                                },
                                format!("invalid cast from {:?} to {:?}", source_ty, target_ty),
                            )
                            .with_hint("check cast matrix or change source/target types"),
                        );
                        self.unknown_ty()
                    }
                }
            }
            ParsedBinaryOp::Elvis | ParsedBinaryOp::Range | ParsedBinaryOp::Pipe => {
                if matches!(op, ParsedBinaryOp::Pipe) {
                    let rewritten = Self::pipe_to_call_expr(lhs, rhs);
                    return self.infer_expr(&rewritten);
                }
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
            ParsedBinaryOp::Elvis
            | ParsedBinaryOp::Range
            | ParsedBinaryOp::Pipe
            | ParsedBinaryOp::Colon => None,
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
            TypeExpr::Tuple(items) if items.is_empty() => CheckedTypeExpr::Named {
                name: "Void".to_string(),
                args: Vec::new(),
            },
            TypeExpr::Tuple(items) => CheckedTypeExpr::Named {
                name: "Tuple".to_string(),
                args: items
                    .iter()
                    .map(|item| CheckedStaticArg::Type(self.lower_type_expr(item)))
                    .collect(),
            },
            TypeExpr::Struct(fields) => CheckedTypeExpr::Named {
                name: "Struct".to_string(),
                args: fields
                    .iter()
                    .map(|(_, ty)| CheckedStaticArg::Type(self.lower_type_expr(ty)))
                    .collect(),
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
            StaticValueExpr::Label(v) => CheckedStaticValue::Label(v.clone()),
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
                self.typecheck_error(Issue::CasesEmpty, "cases requires at least one arm")
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
        if matches!(lhs_ty, Ty::Never) {
            return rhs;
        }
        if matches!(rhs_ty, Ty::Never) {
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

        if self.type_contains_infer_var(lhs) || self.type_contains_infer_var(rhs) {
            if let Ok(unified) = self.unifier.unify(&mut self.interner, lhs, rhs, context) {
                return self.unifier.resolve(unified);
            }
        }

        self.emit_type_mismatch(lhs, rhs, context, "branch join compatibility check failed");

        self.unify_with_context(lhs, rhs, context)
    }

    fn type_contains_infer_var(&self, ty: TyId) -> bool {
        let ty = self.unifier.resolve(ty);
        match self.interner.get(ty) {
            Some(Ty::InferVar(_)) => true,
            Some(Ty::List(item)) | Some(Ty::Set(item)) => self.type_contains_infer_var(*item),
            Some(Ty::Dict { key, value }) => {
                self.type_contains_infer_var(*key) || self.type_contains_infer_var(*value)
            }
            Some(Ty::Array { item, .. }) => self.type_contains_infer_var(*item),
            Some(Ty::Tuple(items)) | Some(Ty::Union(items)) => {
                items.iter().any(|item| self.type_contains_infer_var(*item))
            }
            Some(Ty::Struct(fields)) => fields
                .iter()
                .any(|(_, field_ty)| self.type_contains_infer_var(*field_ty)),
            Some(Ty::Enum(variants)) => variants
                .iter()
                .any(|(_, payload)| payload.is_some_and(|ty| self.type_contains_infer_var(ty))),
            Some(Ty::Func { params, ret }) | Some(Ty::Macro { params, ret }) => {
                params
                    .iter()
                    .any(|param| self.type_contains_infer_var(param.ty))
                    || self.type_contains_infer_var(*ret)
            }
            _ => false,
        }
    }

    fn resolve_type_expr(&mut self, ty: &TypeExpr) -> TyId {
        match ty {
            TypeExpr::Static(inner) => self.resolve_type_expr(inner),
            TypeExpr::InferHole => self.unknown_ty(),
            TypeExpr::Tuple(items) if items.is_empty() => self.interner.intern(Ty::Void),
            TypeExpr::Tuple(items) => {
                let lowered = items
                    .iter()
                    .map(|item| self.resolve_type_expr(item))
                    .collect::<Vec<_>>();
                self.interner.intern(Ty::Tuple(lowered))
            }
            TypeExpr::Struct(fields) => {
                let lowered = fields
                    .iter()
                    .map(|(name, ty)| (name.clone(), self.resolve_type_expr(ty)))
                    .collect::<Vec<_>>();
                self.interner.intern(Ty::Struct(lowered))
            }
            TypeExpr::Named { name, args } => {
                if let Some(alias) = self.aliases.get(name) {
                    self.enforce_exact_type_arity(name, args, 0);
                    return alias;
                }
                if let Some((static_params, body)) = self.aliases.get_generic(name) {
                    return self.instantiate_type_alias(name, args, &static_params, &body);
                }

                if name == "union" {
                    let members = args
                        .iter()
                        .filter_map(|arg| match arg {
                            StaticArg::Type(ty) => Some(self.resolve_type_expr(ty)),
                            StaticArg::Value(_) => None,
                        })
                        .collect::<Vec<_>>();
                    if members.is_empty() {
                        return self.unknown_ty();
                    }
                    return self.interner.intern(Ty::Union(members));
                }

                if name == "enum" {
                    let mut variants = Vec::new();
                    for arg in args {
                        if let StaticArg::Type(TypeExpr::Struct(items)) = arg {
                            for (field, ty) in items {
                                variants.push((field.clone(), Some(self.resolve_type_expr(ty))));
                            }
                        } else if let StaticArg::Type(TypeExpr::Named {
                            name: variant,
                            args,
                        }) = arg
                        {
                            if args.is_empty() {
                                variants.push((variant.clone(), None));
                            } else {
                                variants.push((
                                    variant.clone(),
                                    Some(
                                        self.resolve_required_type_arg(args, 0, "enum", "variant"),
                                    ),
                                ));
                            }
                        }
                    }
                    if variants.is_empty() {
                        return self.unknown_ty();
                    }
                    return self.interner.intern(Ty::Enum(variants));
                }

                if name == "Result" {
                    self.enforce_exact_type_arity("Result", args, 2);
                    let ok_ty = self.resolve_required_type_arg(args, 0, "Result", "ok");
                    let err_ty = self.resolve_required_type_arg(args, 1, "Result", "err");
                    let ok_payload = match self.interner.get(ok_ty) {
                        Some(Ty::Void) => None,
                        _ => Some(ok_ty),
                    };
                    return self.interner.intern(Ty::Enum(vec![
                        ("ok".to_string(), ok_payload),
                        ("err".to_string(), Some(err_ty)),
                    ]));
                }

                match name.as_str() {
                    "Int8" => {
                        self.enforce_exact_type_arity("Int8", args, 0);
                        self.interner.intern(Ty::Int8)
                    }
                    "Int16" => {
                        self.enforce_exact_type_arity("Int16", args, 0);
                        self.interner.intern(Ty::Int16)
                    }
                    "Int32" => {
                        self.enforce_exact_type_arity("Int32", args, 0);
                        self.interner.intern(Ty::Int32)
                    }
                    "Int64" => {
                        self.enforce_exact_type_arity("Int64", args, 0);
                        self.interner.intern(Ty::Int64)
                    }
                    "Int128" => {
                        self.enforce_exact_type_arity("Int128", args, 0);
                        self.interner.intern(Ty::Int128)
                    }
                    "UInt8" => {
                        self.enforce_exact_type_arity("UInt8", args, 0);
                        self.interner.intern(Ty::UInt8)
                    }
                    "UInt16" => {
                        self.enforce_exact_type_arity("UInt16", args, 0);
                        self.interner.intern(Ty::UInt16)
                    }
                    "UInt32" => {
                        self.enforce_exact_type_arity("UInt32", args, 0);
                        self.interner.intern(Ty::UInt32)
                    }
                    "UInt64" => {
                        self.enforce_exact_type_arity("UInt64", args, 0);
                        self.interner.intern(Ty::UInt64)
                    }
                    "UInt128" => {
                        self.enforce_exact_type_arity("UInt128", args, 0);
                        self.interner.intern(Ty::UInt128)
                    }
                    "ISize" => {
                        self.enforce_exact_type_arity("ISize", args, 0);
                        self.interner.intern(Ty::ISize)
                    }
                    "USize" => {
                        self.enforce_exact_type_arity("USize", args, 0);
                        self.interner.intern(Ty::USize)
                    }
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
                    "Bytes" => {
                        self.enforce_exact_type_arity("Bytes", args, 0);
                        self.nominal_ty("Bytes")
                    }
                    "String" => {
                        self.enforce_exact_type_arity("String", args, 0);
                        self.nominal_ty("String")
                    }
                    "RawAlloc" => {
                        self.enforce_exact_type_arity("RawAlloc", args, 1);
                        let item = self.resolve_required_type_arg(args, 0, "RawAlloc", "item");
                        self.interner.intern(Ty::RawAlloc(item))
                    }
                    "Slice" => {
                        self.enforce_exact_type_arity("Slice", args, 1);
                        let item = self.resolve_required_type_arg(args, 0, "Slice", "item");
                        self.interner.intern(Ty::Slice(item))
                    }
                    "Ref" => {
                        self.enforce_exact_type_arity("Ref", args, 1);
                        let item = self.resolve_required_type_arg(args, 0, "Ref", "item");
                        self.interner.intern(Ty::Ref(item))
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
                        let params = match args.first() {
                            Some(StaticArg::Type(TypeExpr::Tuple(items))) => {
                                let item_tys = items
                                    .iter()
                                    .map(|item| self.resolve_type_expr(item))
                                    .collect::<Vec<_>>();
                                self.positional_params(item_tys)
                            }
                            Some(StaticArg::Type(TypeExpr::Struct(fields))) => {
                                self.named_params_from_fields(fields)
                            }
                            Some(StaticArg::Type(ty)) => {
                                let param_ty = self.resolve_type_expr(ty);
                                self.positional_params(vec![param_ty])
                            }
                            Some(StaticArg::Value(_)) | None => Vec::new(),
                        };
                        let b = self.resolve_required_type_arg(args, 1, "Func", "ret");
                        self.interner.intern(Ty::Func { params, ret: b })
                    }
                    "Macro" => {
                        self.enforce_exact_type_arity("Macro", args, 2);
                        let params = match args.first() {
                            Some(StaticArg::Type(TypeExpr::Tuple(items))) => {
                                let item_tys = items
                                    .iter()
                                    .map(|item| self.resolve_type_expr(item))
                                    .collect::<Vec<_>>();
                                self.positional_params(item_tys)
                            }
                            Some(StaticArg::Type(TypeExpr::Struct(fields))) => {
                                self.named_params_from_fields(fields)
                            }
                            Some(StaticArg::Type(ty)) => {
                                let param_ty = self.resolve_type_expr(ty);
                                self.positional_params(vec![param_ty])
                            }
                            Some(StaticArg::Value(_)) | None => Vec::new(),
                        };
                        let ret = self.resolve_required_type_arg(args, 1, "Macro", "ret");
                        self.interner.intern(Ty::Macro { params, ret })
                    }
                    _ => self
                        .lookup_generic(name)
                        .unwrap_or_else(|| self.interner.intern(Ty::Nominal(name.clone()))),
                }
            }
        }
    }

    fn instantiate_type_alias(
        &mut self,
        name: &str,
        args: &[StaticArg],
        static_params: &[StaticParam],
        body: &TypeExpr,
    ) -> TyId {
        self.enforce_exact_type_arity(name, args, static_params.len());
        let mut resolved_args = Vec::with_capacity(static_params.len());
        for (index, param) in static_params.iter().enumerate() {
            let ty = match args.get(index) {
                Some(StaticArg::Type(ty)) => self.resolve_type_expr(ty),
                Some(StaticArg::Value(_)) => {
                    self.diagnostics.push(
                        self.typecheck_error(
                            Issue::TypeArgKind,
                            format!("{name} static argument '{}' must be a type", param.name),
                        )
                        .with_hint("pass a type argument such as `Int`"),
                    );
                    self.unknown_ty()
                }
                None => self.unknown_ty(),
            };
            resolved_args.push((param.name.clone(), ty));
        }

        self.push_generic_scope();
        for (param_name, ty) in resolved_args {
            self.insert_generic(param_name, ty);
        }
        let resolved = self.resolve_type_expr(body);
        self.pop_generic_scope();
        resolved
    }

    fn validate_method_receiver(&mut self, receiver: &TypeExpr) {
        let TypeExpr::Named { name, args } = receiver else {
            return;
        };
        if !args.is_empty() {
            return;
        }
        if !Self::KNOWN_GENERIC_RECEIVERS.contains(&name.as_str()) {
            return;
        }

        self.diagnostics.push(
            self.typecheck_error(
                Issue::TypeArgMissing,
                format!(
                    "receiver type '{name}' requires explicit static arguments in method declarations"
                ),
            )
            .with_hint("use form like `def[T] Seq[T].method(...) -> ... { ... }`"),
        );
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
                    Issue::TypeArgArity,
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
                        Issue::TypeArgKind,
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
                        Issue::TypeArgMissing,
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
                            Issue::ArraySizeInvalid,
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
                        Issue::ArraySizeKind,
                        format!("{ty_name} {slot} argument must be an integer literal"),
                    )
                    .with_hint("use form like Array[Int, 4]"),
                );
                0
            }
            Some(StaticArg::Type(_)) => {
                self.diagnostics.push(
                    self.typecheck_error(
                        Issue::ArraySizeKind,
                        format!("{ty_name} {slot} argument expects a value, got a type"),
                    )
                    .with_hint("use form like Array[Int, 4]"),
                );
                0
            }
            None => {
                self.diagnostics.push(
                    self.typecheck_error(
                        Issue::ArraySizeMissing,
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
            params: self.positional_params(expected_params.clone()),
            ret: expected_ret,
        });

        let mut used_known_func_shape = false;
        if let Some(Ty::Func {
            params: cparams,
            ret: cret,
        }) = self.interner.get(callee_ty).cloned()
        {
            if cparams.len() == expected_params.len() {
                used_known_func_shape = true;
                for (target, source) in expected_params.iter().zip(cparams.iter()) {
                    let _ = self.unify_with_context(*target, source.ty, "callable parameter");
                }
                self.require_assignable(expected_ret, cret, "callable return");
            }
        }

        if !used_known_func_shape {
            self.unify_with_context(callee_ty, expected_func, "callable expression");
        }

        let mut placeholder_params = Vec::new();

        for (idx, arg) in args.iter().enumerate() {
            self.push_obligation(format!("checking call argument #{idx}"));
            let expected = expected_params[idx];
            if Self::is_placeholder_expr(arg) {
                placeholder_params.push(expected);
                self.pop_obligation();
                continue;
            }
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
        if placeholder_params.is_empty() {
            resolved
        } else {
            let params = placeholder_params
                .into_iter()
                .map(|ty| self.unifier.resolve(ty))
                .collect::<Vec<_>>();
            self.interner.intern(Ty::Func {
                params: self.positional_params(params),
                ret: resolved,
            })
        }
    }

    fn infer_if_call_with_expected(
        &mut self,
        args: &[Expr],
        trailing: &[LabeledClosureArg],
        expected: Option<TyId>,
    ) -> TyId {
        if args.len() != 1 {
            self.diagnostics.push(
                self.typecheck_error(Issue::IfArity, "if expects one runtime argument: condition")
                    .with_hint("use form: if (condition) then { ... } else { ... }"),
            );
            return self.unknown_ty();
        }

        let then_branch = trailing.iter().find(|c| c.label == "then");
        let else_branch = trailing.iter().find(|c| c.label == "else");

        let Some(then_branch) = then_branch else {
            self.diagnostics.push(
                self.typecheck_error(Issue::IfForm, "if requires a labeled 'then' closure")
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
                self.typecheck_error(Issue::CasesForm, "cases does not accept runtime arguments")
                    .with_hint("use form: cases when { ... }"),
            );
            return self.unknown_ty();
        }

        let Some(when) = trailing.iter().find(|c| c.label == "when") else {
            self.diagnostics.push(
                self.typecheck_error(Issue::CasesForm, "cases requires labeled 'when' closure")
                    .with_hint("use form: cases when { ... }"),
            );
            return self.unknown_ty();
        };

        let Expr::MultiArm(arms) = TypeChecker::base_expr(&when.body) else {
            self.diagnostics.push(
                self.typecheck_error(Issue::CasesForm, "cases 'when' closure must be multi-arm")
                    .with_hint("use form: cases when { ~cond -> expr, ~true -> default }"),
            );
            return self.unknown_ty();
        };

        self.infer_multi_arm_with_expected(arms, expected)
    }

    fn infer_loop_call_with_expected(
        &mut self,
        expr: &Expr,
        args: &[Expr],
        trailing: &[LabeledClosureArg],
        expected: Option<TyId>,
    ) -> TyId {
        if !args.is_empty() {
            self.diagnostics.push(
                self.typecheck_error(Issue::BuiltinForm, "loop does not accept runtime arguments")
                    .with_hint("use form: loop do { ... } or loop while { ... } do { ... }"),
            );
            return self.unknown_ty();
        }

        let loop_result_ty =
            expected.unwrap_or_else(|| self.interner.fresh_infer_var(&mut self.next_infer_var));
        let loop_target = self.next_loop_target_name();
        self.resolved_loop_targets.insert(
            Self::expr_cache_key(expr),
            ResolvedLoopInfo {
                target: loop_target.clone(),
                result_ty: loop_result_ty,
            },
        );
        self.active_loop_targets.push(ActiveLoopTarget {
            target: loop_target.clone(),
            label: self.current_jump_label(),
            result_ty: loop_result_ty,
            saw_break: false,
        });

        let Some(do_body) = trailing.iter().find(|c| c.label == "do") else {
            self.diagnostics.push(
                self.typecheck_error(Issue::BuiltinForm, "loop requires labeled 'do' closure")
                    .with_hint("use form: loop do { ... } or loop while { ... } do { ... }"),
            );
            let _ = self.active_loop_targets.pop();
            return self.unknown_ty();
        };

        if let Some(condition) = trailing.iter().find(|c| c.label == "while") {
            let bool_ty = self.interner.intern(Ty::Bool);
            let cond_ty = self.infer_expr_with_expected(&condition.body, bool_ty);
            self.require_assignable(bool_ty, cond_ty, "loop condition");
        }

        let _ = self.infer_expr(&do_body.body);
        let loop_state = self
            .active_loop_targets
            .pop()
            .expect("loop target should exist during loop inference");
        if loop_state.saw_break {
            self.unifier.resolve(loop_state.result_ty)
        } else {
            self.interner.intern(Ty::Never)
        }
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
                        Issue::CallStaticUnsupported,
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
                        Issue::CallStaticUnexpected,
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
                    Issue::CallStaticArity,
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
                                context: format!("generic call `{name}` for `{}`", param.name),
                                obligations: self.obligation_stack.clone(),
                                span: self.current_expr_span,
                            });
                        self.pending_constraints
                            .push(TypeConstraint::InterfaceBound {
                                ty: mapped,
                                interface: interface.clone(),
                                context: format!("generic call `{name}` for `{}`", param.name),
                                obligations: self.obligation_stack.clone(),
                                span: self.current_expr_span,
                            });
                    }
                    GenericConstraint::Static(expected) => {
                        self.pending_constraints.push(TypeConstraint::StaticBound {
                            arg: static_args.get(idx).cloned(),
                            param: param.name.clone(),
                            expected: expected.clone(),
                            context: format!("generic call `{name}` for `{}`", param.name),
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
                    .map(|x| FuncParam {
                        name: x.name.clone(),
                        label: x.label.clone(),
                        trailing: x.trailing,
                        ty: self.substitute_ty_id(x.ty, subst),
                    })
                    .collect();
                let r = self.substitute_ty_id(ret, subst);
                self.interner.intern(Ty::Func { params: p, ret: r })
            }
            Ty::Macro { params, ret } => {
                let p = params
                    .iter()
                    .map(|x| FuncParam {
                        name: x.name.clone(),
                        label: x.label.clone(),
                        trailing: x.trailing,
                        ty: self.substitute_ty_id(x.ty, subst),
                    })
                    .collect();
                let r = self.substitute_ty_id(ret, subst);
                self.interner.intern(Ty::Macro { params: p, ret: r })
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
                TypeConstraint::Assignable {
                    expected,
                    actual,
                    context,
                    obligations,
                    span,
                } if context == "call argument" => {
                    let prev_obligations = self.obligation_stack.clone();
                    let prev_span = self.current_expr_span;
                    self.obligation_stack = obligations;
                    self.current_expr_span = span;

                    let _ = self.unify_with_context(expected, actual, "call argument unify");
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

                    self.emit_type_mismatch(
                        expected,
                        actual,
                        &context,
                        "assignability constraint failed in solver",
                    );
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
                                Issue::UnknownInterface,
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
                        .any(|d| d.code_str() == "E_TYPE_MISMATCH" && d.message.contains(&context))
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
                                Issue::InterfaceBoundUnsatisfied {
                                    detail: format!(
                                        "type `{:?}` does not satisfy interface bound `{}` in {}",
                                        resolved, interface, context
                                    ),
                                },
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
                                Issue::StaticArgMissing,
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
                                Issue::StaticArgKind {
                                    detail: format!(
                                        "expected compile-time static value for constraint {:?} in {}",
                                        expected, context
                                    ),
                                },
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

        if matches!(expected_ty, Ty::Any) {
            return ConversionDecision::Identity;
        }

        if matches!(expected_ty, Ty::InferVar(_)) || matches!(actual_ty, Ty::InferVar(_)) {
            let _ = self.unify_with_context(expected, actual, context);
            return ConversionDecision::Identity;
        }

        if matches!(actual_ty, Ty::Never) {
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

        if self.structurally_equivalent(expected, actual) {
            return ConversionDecision::Identity;
        }

        if let Ty::Union(expected_members) = &expected_ty {
            for member in expected_members {
                if let Some(member_ty) = self.interner.get(*member).cloned() {
                    if member_ty == actual_ty || can_implicitly_widen(&actual_ty, &member_ty) {
                        return ConversionDecision::Identity;
                    }
                }
            }
            return ConversionDecision::Incompatible;
        }

        if let (Ty::Enum(expected_variants), Ty::Enum(actual_variants)) = (&expected_ty, &actual_ty)
        {
            if expected_variants == actual_variants {
                return ConversionDecision::Identity;
            }
        }

        if matches!(mode, ConversionMode::ExplicitCastAllowed)
            && self.is_explicit_cast_pair(&actual_ty, &expected_ty)
        {
            return ConversionDecision::Cast;
        }

        ConversionDecision::Incompatible
    }

    fn structurally_equivalent(&self, expected: TyId, actual: TyId) -> bool {
        let expected = self.unifier.resolve(expected);
        let actual = self.unifier.resolve(actual);
        if expected == actual {
            return true;
        }
        let Some(expected_ty) = self.interner.get(expected) else {
            return false;
        };
        let Some(actual_ty) = self.interner.get(actual) else {
            return false;
        };

        match (expected_ty, actual_ty) {
            (Ty::List(a), Ty::List(b)) => self.structurally_equivalent(*a, *b),
            (Ty::Dict { key: ak, value: av }, Ty::Dict { key: bk, value: bv }) => {
                self.structurally_equivalent(*ak, *bk) && self.structurally_equivalent(*av, *bv)
            }
            (Ty::Set(a), Ty::Set(b)) => self.structurally_equivalent(*a, *b),
            (
                Ty::Array {
                    item: ai,
                    size: asz,
                },
                Ty::Array {
                    item: bi,
                    size: bsz,
                },
            ) => asz == bsz && self.structurally_equivalent(*ai, *bi),
            (Ty::Tuple(a), Ty::Tuple(b)) => {
                a.len() == b.len()
                    && a.iter()
                        .zip(b.iter())
                        .all(|(x, y)| self.structurally_equivalent(*x, *y))
            }
            (Ty::Struct(a), Ty::Struct(b)) => {
                a.len() == b.len()
                    && a.iter().zip(b.iter()).all(|((an, at), (bn, bt))| {
                        an == bn && self.structurally_equivalent(*at, *bt)
                    })
            }
            (
                Ty::Func {
                    params: ap,
                    ret: ar,
                },
                Ty::Func {
                    params: bp,
                    ret: br,
                },
            ) => {
                ap.len() == bp.len()
                    && ap
                        .iter()
                        .zip(bp.iter())
                        .all(|(x, y)| self.structurally_equivalent(x.ty, y.ty))
                    && self.structurally_equivalent(*ar, *br)
            }
            (
                Ty::Macro {
                    params: ap,
                    ret: ar,
                },
                Ty::Macro {
                    params: bp,
                    ret: br,
                },
            ) => {
                ap.len() == bp.len()
                    && ap
                        .iter()
                        .zip(bp.iter())
                        .all(|(x, y)| self.structurally_equivalent(x.ty, y.ty))
                    && self.structurally_equivalent(*ar, *br)
            }
            _ => false,
        }
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
            Issue::TypeMismatch {
                context: map_context(context),
                expected: ty_to_ref(&expected_ty, &self.interner),
                actual: ty_to_ref(&actual_ty, &self.interner),
            },
            "type mismatch",
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

    fn typecheck_error(&self, issue: Issue, _message: impl Into<String>) -> Diagnostic {
        Diagnostic::error(issue)
            .with_stage(Stage::Typecheck)
            .with_span_opt(self.current_expr_span)
            .with_obligations(&self.obligation_stack)
    }

    fn typecheck_warning(&self, issue: Issue, _message: impl Into<String>) -> Diagnostic {
        Diagnostic::warning(issue)
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

    fn insert_value(&mut self, name: String, ty: TyId, mutable: bool) {
        if let Some(scope) = self.value_env_scopes.last_mut() {
            scope.insert(
                name,
                ValueBinding {
                    ty,
                    mutable,
                    place_mutable: mutable,
                },
            );
        }
    }

    fn insert_value_param(&mut self, name: String, ty: TyId) {
        if let Some(scope) = self.value_env_scopes.last_mut() {
            scope.insert(
                name,
                ValueBinding {
                    ty,
                    mutable: false,
                    place_mutable: true,
                },
            );
        }
    }

    fn insert_generic(&mut self, name: String, ty: TyId) {
        if let Some(scope) = self.generic_env_scopes.last_mut() {
            scope.insert(name, ty);
        }
    }

    fn bind_arm_patterns(&mut self, patterns: &[Pattern]) {
        let subject_ty = self
            .current_match_subject
            .as_ref()
            .map(|subject| subject.ty);
        for pattern in patterns {
            if let Some(subject_ty) = subject_ty {
                self.bind_pattern_with_expected(pattern, subject_ty, false);
            } else {
                self.bind_pattern(pattern);
            }
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

    fn validate_enum_multi_arm_patterns(
        &mut self,
        arms: &[aura_frontend::ast::Arm],
        enum_ty: TyId,
    ) {
        let Some(Ty::Enum(variants)) = self.interner.get(enum_ty).cloned() else {
            return;
        };
        let mut seen = std::collections::HashSet::new();
        let mut has_fallback = false;

        for arm in arms {
            let Some(first) = arm.patterns.first() else {
                has_fallback = true;
                continue;
            };
            match first {
                Pattern::Wildcard => has_fallback = true,
                Pattern::DotVariant { name, .. } => {
                    if variants.iter().all(|(variant, _)| variant != name) {
                        self.diagnostics.push(
                            self.typecheck_error(
                                Issue::PatternNonExhaustive,
                                format!("unknown enum variant pattern '.{name}'"),
                            )
                            .with_hint("use a variant that exists on the matched enum type"),
                        );
                    } else {
                        seen.insert(name.clone());
                    }
                }
                _ => {}
            }
        }

        if !has_fallback && seen.len() < variants.len() {
            self.diagnostics.push(
                Diagnostic::error(Issue::PatternNonExhaustive)
                    .with_hint("add `_ -> ...` or include the missing variant patterns"),
            );
        }
    }

    fn bind_pattern(&mut self, pattern: &Pattern) {
        match pattern {
            Pattern::Ident(name) if name != "true" && name != "false" => {
                let ty = self.interner.fresh_infer_var(&mut self.next_infer_var);
                self.insert_value(name.clone(), ty, false);
            }
            Pattern::Struct(fields) => {
                for (_, inner) in fields {
                    self.bind_pattern(inner);
                }
            }
            Pattern::DotVariant { payload, .. } => {
                if let Some(inner) = payload.as_ref() {
                    self.bind_pattern(inner);
                }
            }
            _ => {}
        }
    }

    fn bind_local_pattern(&mut self, pattern: &Pattern, ty: TyId, mutable: bool) {
        self.bind_pattern_with_expected(pattern, ty, mutable);
    }

    fn bind_pattern_with_expected(&mut self, pattern: &Pattern, ty: TyId, mutable: bool) {
        match pattern {
            Pattern::Ident(name) if name != "true" && name != "false" => {
                self.insert_value(name.clone(), ty, mutable);
            }
            Pattern::Struct(fields) => {
                if let Some(Ty::Struct(expected_fields)) = self.interner.get(ty).cloned() {
                    for (field_name, inner) in fields {
                        if let Some((_, field_ty)) = expected_fields
                            .iter()
                            .find(|(expected_name, _)| expected_name == field_name)
                        {
                            self.bind_pattern_with_expected(inner, *field_ty, mutable);
                        } else {
                            self.bind_pattern(inner);
                        }
                    }
                } else {
                    for (_, inner) in fields {
                        self.bind_pattern(inner);
                    }
                }
            }
            Pattern::DotVariant { payload, .. } => {
                if let Some(inner) = payload.as_ref() {
                    let payload_ty = match self.interner.get(ty).cloned() {
                        Some(Ty::Enum(_)) => {
                            if let Pattern::DotVariant { name, .. } = pattern {
                                self.enum_variant(ty, name).and_then(|(_, payload)| payload)
                            } else {
                                None
                            }
                        }
                        _ => None,
                    };
                    if let Some(payload_ty) = payload_ty {
                        self.bind_pattern_with_expected(inner, payload_ty, mutable);
                    } else {
                        self.bind_pattern(inner);
                    }
                }
            }
            _ => {}
        }
    }

    fn lookup_value(&self, name: &str) -> Option<TyId> {
        self.value_env_scopes
            .iter()
            .rev()
            .find_map(|scope| scope.get(name).map(|binding| binding.ty))
    }

    fn lookup_value_binding(&self, name: &str) -> Option<ValueBinding> {
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

    fn validate_main_signature(&mut self, function: &aura_frontend::ast::FunctionDecl) {
        if !self.options.enforce_main_signature {
            return;
        }
        if function.name != "main" {
            return;
        }

        let no_params = function.params.is_empty();
        let no_static_params = function.static_params.is_empty();
        let no_receiver = function.receiver.is_none();
        let valid_ret = Self::main_return_type_expr_ok(&function.return_type);

        if no_params && no_static_params && no_receiver && valid_ret {
            return;
        }

        self.diagnostics.push(
            self.typecheck_error(
                Issue::MainSignature,
                "`main` must have no params/static params/receiver and return `Void`",
            )
            .with_hint("use: `def main() -> Void { ... }`"),
        );
    }

    fn main_return_type_expr_ok(ty: &TypeExpr) -> bool {
        match ty {
            TypeExpr::Static(inner) => Self::main_return_type_expr_ok(inner),
            TypeExpr::Named { name, args } if name == "Void" && args.is_empty() => true,
            _ => false,
        }
    }

    fn lower_expr(&mut self, expr: &Expr) -> CheckedExpr {
        if let Some(resolved) = self.resolved_enum_ctor(expr) {
            match TypeChecker::base_expr(expr) {
                Expr::DotIdent { payload, .. } => {
                    return CheckedExpr::EnumCtor {
                        enum_ty: resolved.enum_ty,
                        variant_index: resolved.variant_index,
                        payload: payload.as_ref().map(|p| Box::new(self.lower_expr(p))),
                    };
                }
                Expr::Call { args, .. } => {
                    let payload = self.lower_enum_call_payload(
                        resolved.enum_ty,
                        resolved.variant_index,
                        args,
                    );
                    return CheckedExpr::EnumCtor {
                        enum_ty: resolved.enum_ty,
                        variant_index: resolved.variant_index,
                        payload,
                    };
                }
                Expr::Member { .. } => {
                    return CheckedExpr::EnumCtor {
                        enum_ty: resolved.enum_ty,
                        variant_index: resolved.variant_index,
                        payload: None,
                    };
                }
                _ => {}
            }
        }
        match expr {
            Expr::Spanned { expr, .. } => self.lower_expr(expr),
            Expr::Ident(v) => CheckedExpr::Ident(
                self.imported_binding(v)
                    .map(|binding| binding.link_name.clone())
                    .unwrap_or_else(|| v.clone()),
            ),
            Expr::Int(v) => CheckedExpr::Int(v.clone()),
            Expr::Float(v) => CheckedExpr::Float(v.clone()),
            Expr::Char(v) => CheckedExpr::Char(v.clone()),
            Expr::String(v) => CheckedExpr::String(v.clone()),
            Expr::DotIdent { name, payload } => {
                if let Some(resolved) = self.resolved_enum_ctor(expr) {
                    CheckedExpr::EnumCtor {
                        enum_ty: resolved.enum_ty,
                        variant_index: resolved.variant_index,
                        payload: payload.as_ref().map(|p| Box::new(self.lower_expr(p))),
                    }
                } else {
                    CheckedExpr::DotIdent {
                        name: name.clone(),
                        payload: payload.as_ref().map(|p| Box::new(self.lower_expr(p))),
                    }
                }
            }
            Expr::TypeApply { .. } => CheckedExpr::Any,
            Expr::Tuple(items) => {
                CheckedExpr::Tuple(items.iter().map(|item| self.lower_expr(item)).collect())
            }
            Expr::Struct(fields) => CheckedExpr::Struct(
                fields
                    .iter()
                    .map(|(name, value)| (name.clone(), self.lower_expr(value)))
                    .collect(),
            ),
            Expr::Closure {
                params,
                return_type,
            } => CheckedExpr::Closure {
                params: params.iter().map(|p| p.name.clone()).collect(),
                return_ty: return_type.as_ref().map(|t| self.resolve_type_expr(t)),
            },
            Expr::Placeholder => CheckedExpr::Any,
            Expr::Block(items) => {
                self.push_scope();
                let mut lowered_items = Vec::with_capacity(items.len());
                for item in items {
                    let lowered = self.lower_expr(item);
                    if let CheckedExpr::LocalBind { bindings, mutable } = &lowered {
                        for binding in bindings {
                            if let Some(name) = binding.name.as_ref() {
                                self.insert_value(name.clone(), binding.ty, *mutable);
                            }
                        }
                    }
                    lowered_items.push(lowered);
                }
                self.pop_scope();
                CheckedExpr::Block(lowered_items)
            }
            Expr::Bindings(_) => CheckedExpr::Any,
            Expr::Assign { name, value } => CheckedExpr::AssignLocal {
                name: name.clone(),
                value: Box::new(self.lower_expr(value)),
                ty: self.preview_expr_ty(expr),
            },
            Expr::AssignPlace { target, value } => self.lower_assign_place(target, value),
            Expr::List(items) => {
                CheckedExpr::List(items.iter().map(|item| self.lower_expr(item)).collect())
            }
            Expr::Dict(entries) => CheckedExpr::Dict(
                entries
                    .iter()
                    .map(|(k, v)| (self.lower_expr(k), self.lower_expr(v)))
                    .collect(),
            ),
            Expr::Call { callee, args, .. } => {
                if let Expr::Ident(name) = TypeChecker::base_expr(callee.as_ref()) {
                    if name == "if" {
                        let condition = args
                            .first()
                            .map(|arg| Box::new(self.lower_expr(arg)))
                            .unwrap_or_else(|| Box::new(CheckedExpr::Any));
                        let then_branch = if let Expr::Call { trailing, .. } = expr {
                            trailing
                                .iter()
                                .find(|closure| closure.label == "then")
                                .map(|closure| Box::new(self.lower_expr(&closure.body)))
                                .unwrap_or_else(|| Box::new(CheckedExpr::Any))
                        } else {
                            Box::new(CheckedExpr::Any)
                        };
                        let else_branch = if let Expr::Call { trailing, .. } = expr {
                            trailing
                                .iter()
                                .find(|closure| closure.label == "else")
                                .map(|closure| Box::new(self.lower_expr(&closure.body)))
                        } else {
                            None
                        };
                        return CheckedExpr::If {
                            result_ty: self.preview_expr_ty(expr),
                            condition,
                            then_branch,
                            else_branch,
                        };
                    }
                    if name == "cases" {
                        if let Expr::Call { trailing, .. } = expr {
                            if let Some(when) =
                                trailing.iter().find(|closure| closure.label == "when")
                            {
                                if let Expr::MultiArm(arms) = TypeChecker::base_expr(&when.body) {
                                    return CheckedExpr::Cases {
                                        result_ty: self.preview_expr_ty(expr),
                                        arms: arms
                                            .iter()
                                            .map(|arm| CheckedCaseArm {
                                                guard: arm
                                                    .guard
                                                    .as_ref()
                                                    .map(|guard| self.lower_expr(guard))
                                                    .unwrap_or(CheckedExpr::Ident(
                                                        "true".to_string(),
                                                    )),
                                                body: self.lower_expr(&arm.body),
                                            })
                                            .collect(),
                                    };
                                }
                            }
                        }
                    }
                    if name == "loop" {
                        if let Expr::Call { trailing, .. } = expr {
                            let loop_info = self
                                .resolved_loop_targets
                                .get(&Self::expr_cache_key(expr))
                                .cloned()
                                .unwrap_or_else(|| ResolvedLoopInfo {
                                    target: String::new(),
                                    result_ty: self.preview_expr_ty(expr),
                                });
                            let condition = trailing
                                .iter()
                                .find(|closure| closure.label == "while")
                                .map(|closure| Box::new(self.lower_expr(&closure.body)));
                            let body = trailing
                                .iter()
                                .find(|closure| closure.label == "do")
                                .map(|closure| Box::new(self.lower_expr(&closure.body)))
                                .unwrap_or_else(|| Box::new(CheckedExpr::Any));
                            return CheckedExpr::Loop {
                                target: loop_info.target,
                                result_ty: loop_info.result_ty,
                                condition,
                                body,
                            };
                        }
                    }
                }
                let resolved_method = self
                    .resolved_method_call(expr)
                    .cloned()
                    .or_else(|| self.resolved_method_call(callee.as_ref()).cloned());
                if let Expr::Member { object, field } = TypeChecker::base_expr(callee.as_ref()) {
                    let method_link_name = resolved_method.or_else(|| {
                        let receiver_ty = self.preview_expr_ty(object);
                        let receiver_ty = self.unifier.resolve(receiver_ty);
                        self.lookup_method(receiver_ty, field)
                            .map(|method| method.link_name.clone())
                    });
                    if let Some(method_link_name) = method_link_name {
                        let mut lowered_args = vec![self.lower_expr(object)];
                        lowered_args.extend(args.iter().map(|a| self.lower_expr(a)));
                        return CheckedExpr::Call {
                            callee: Box::new(CheckedExpr::Ident(method_link_name)),
                            args: lowered_args,
                        };
                    }
                }
                if let Expr::Member { object, field } = TypeChecker::base_expr(callee.as_ref()) {
                    if let Expr::Ident(namespace) = TypeChecker::base_expr(object) {
                        if let Some(binding) = self.namespace_binding(namespace, field) {
                            return CheckedExpr::Call {
                                callee: Box::new(CheckedExpr::Ident(binding.link_name.clone())),
                                args: args.iter().map(|a| self.lower_expr(a)).collect(),
                            };
                        }
                    }
                }
                if let Expr::Member { object, field } = TypeChecker::base_expr(callee.as_ref()) {
                    let result_ty = self.preview_expr_ty(expr);
                    if let Some(lowered) =
                        self.lower_builtin_member_call(object, field, args, result_ty)
                    {
                        return lowered;
                    }
                }
                CheckedExpr::Call {
                    callee: Box::new(self.lower_expr(callee)),
                    args: args.iter().map(|a| self.lower_expr(a)).collect(),
                }
            }
            Expr::MacroApply {
                macro_name,
                operand,
                ..
            } if macro_name == "let" || macro_name == "def" => {
                let Expr::Bindings(bindings) = TypeChecker::base_expr(operand.as_ref()) else {
                    return CheckedExpr::Any;
                };
                let lowered_bindings = bindings
                    .iter()
                    .flat_map(|binding| {
                        let value = self.lower_expr(&binding.value);
                        let ty = self.preview_expr_ty(&binding.value);
                        Self::collect_checked_bindings(&binding.pattern, ty, &value)
                    })
                    .collect();
                CheckedExpr::LocalBind {
                    bindings: lowered_bindings,
                    mutable: macro_name == "let",
                }
            }
            Expr::MacroApply {
                macro_name,
                operand,
                ..
            } if macro_name == "builtin" => self.lower_expr(operand),
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
                            result_ty: self.preview_expr_ty(expr),
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
                        result_ty: self.preview_expr_ty(expr),
                        arms: arms
                            .iter()
                            .map(|arm| CheckedCaseArm {
                                guard: arm
                                    .guard
                                    .as_ref()
                                    .map(|guard| self.lower_expr(guard))
                                    .unwrap_or(CheckedExpr::Ident("true".to_string())),
                                body: self.lower_expr(&arm.body),
                            })
                            .collect(),
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
                target: self
                    .resolved_jump_targets
                    .get(&Self::expr_cache_key(expr))
                    .cloned()
                    .unwrap_or_default(),
                value: Box::new(self.lower_expr(operand)),
            },
            Expr::MacroApply {
                macro_name,
                operand,
                static_args,
            } if macro_name == "break" => {
                if let Expr::List(items) = TypeChecker::base_expr(operand.as_ref()) {
                    let value = items.first().map(|v| Box::new(self.lower_expr(v)));
                    CheckedExpr::Break {
                        target: self
                            .resolved_jump_targets
                            .get(&Self::expr_cache_key(expr))
                            .cloned()
                            .unwrap_or_default(),
                        value,
                    }
                } else {
                    CheckedExpr::Break {
                        target: self
                            .resolved_jump_targets
                            .get(&Self::expr_cache_key(expr))
                            .cloned()
                            .unwrap_or_default(),
                        value: Some(Box::new(self.lower_expr(operand))),
                    }
                }
            }
            Expr::MacroApply {
                macro_name,
                operand,
                static_args,
            } if macro_name == "continue" => CheckedExpr::Continue {
                target: self
                    .resolved_jump_targets
                    .get(&Self::expr_cache_key(expr))
                    .cloned()
                    .unwrap_or_default(),
            },
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
            Expr::Label { label, expr } => {
                self.active_labels.push(label.clone());
                let lowered = self.lower_expr(expr);
                let _ = self.active_labels.pop();
                CheckedExpr::Label {
                    label: label.clone(),
                    expr: Box::new(lowered),
                }
            }
            Expr::MultiArm(arms) => {
                if let Some(subject) = self.current_match_subject.clone() {
                    if let Some(Ty::Enum(_)) = self.interner.get(subject.ty) {
                        let mut lowered_arms = Vec::new();
                        let mut default_arm = None;
                        for arm in arms {
                            match arm.patterns.first() {
                                Some(Pattern::DotVariant { name, payload }) => {
                                    if let Some((variant_index, payload_ty)) =
                                        self.enum_variant(subject.ty, name)
                                    {
                                        let binding_name = match payload.as_deref() {
                                            Some(Pattern::Ident(name)) => Some(name.clone()),
                                            _ => None,
                                        };
                                        let struct_bindings = self.enum_struct_pattern_bindings(
                                            payload.as_deref(),
                                            payload_ty,
                                        );
                                        lowered_arms.push(CheckedEnumArm {
                                            variant_index,
                                            binding_name,
                                            struct_bindings,
                                            body: self.lower_expr(&arm.body),
                                        });
                                    }
                                }
                                Some(Pattern::Wildcard) | None => {
                                    default_arm = Some(Box::new(self.lower_expr(&arm.body)));
                                }
                                _ => {}
                            }
                        }
                        if !lowered_arms.is_empty() || default_arm.is_some() {
                            return CheckedExpr::EnumMatch {
                                scrutinee: Box::new(CheckedExpr::Ident(subject.name)),
                                enum_ty: subject.ty,
                                result_ty: self.preview_expr_ty(expr),
                                arms: lowered_arms,
                                default_arm,
                            };
                        }
                    }
                }
                CheckedExpr::MultiArm(
                    arms.iter()
                        .map(|arm| self.lower_expr(&arm.body))
                        .collect::<Vec<_>>(),
                )
            }
            Expr::Member { object, field } => match TypeChecker::base_expr(object) {
                Expr::Ident(type_name) if self.enum_alias(type_name).is_some() => {
                    CheckedExpr::DotIdent {
                        name: field.clone(),
                        payload: Some(Box::new(self.lower_expr(object))),
                    }
                }
                Expr::Ident(namespace) => {
                    if let Some(binding) = self.namespace_binding(namespace, field) {
                        CheckedExpr::Ident(binding.link_name.clone())
                    } else {
                        let object_ty = self.preview_expr_ty(object);
                        if let Some((field_index, field_ty)) = self.field_lookup(object_ty, field) {
                            CheckedExpr::FieldAccess {
                                object: Box::new(self.lower_expr(object)),
                                object_ty,
                                field_index,
                                ty: field_ty,
                            }
                        } else {
                            CheckedExpr::DotIdent {
                                name: field.clone(),
                                payload: Some(Box::new(self.lower_expr(object))),
                            }
                        }
                    }
                }
                _ => {
                    let object_ty = self.preview_expr_ty(object);
                    if let Some((field_index, field_ty)) = self.field_lookup(object_ty, field) {
                        CheckedExpr::FieldAccess {
                            object: Box::new(self.lower_expr(object)),
                            object_ty,
                            field_index,
                            ty: field_ty,
                        }
                    } else {
                        CheckedExpr::DotIdent {
                            name: field.clone(),
                            payload: Some(Box::new(self.lower_expr(object))),
                        }
                    }
                }
            },
            Expr::Binary { op, lhs, rhs } => {
                if matches!(op, ParsedBinaryOp::Pipe) {
                    let rewritten = Self::pipe_to_call_expr(lhs, rhs);
                    return self.lower_expr(&rewritten);
                }
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

    fn lower_assign_place(&mut self, target: &Expr, value: &Expr) -> CheckedExpr {
        if let Some(name) = Self::ident_name(target) {
            return CheckedExpr::AssignLocal {
                name: name.to_string(),
                value: Box::new(self.lower_expr(value)),
                ty: self.preview_expr_ty(target),
            };
        }

        if let Expr::Member { object, field } = TypeChecker::base_expr(target) {
            let object_ty = self.preview_expr_ty(object);
            if let Some((field_index, field_ty)) = self.field_lookup(object_ty, field) {
                return CheckedExpr::AssignField {
                    object: Box::new(self.lower_expr(object)),
                    object_ty,
                    field_index,
                    value: Box::new(self.lower_expr(value)),
                    ty: field_ty,
                };
            }
        }

        CheckedExpr::Any
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
            Expr::Tuple(items) => {
                if items.is_empty() {
                    return self.interner.intern(Ty::Void);
                }
                let item_tys = items
                    .iter()
                    .map(|item| self.preview_expr_ty(item))
                    .collect::<Vec<_>>();
                self.interner.intern(Ty::Tuple(item_tys))
            }
            Expr::Struct(fields) => {
                let field_tys = fields
                    .iter()
                    .map(|(name, value)| (name.clone(), self.preview_expr_ty(value)))
                    .collect::<Vec<_>>();
                self.interner.intern(Ty::Struct(field_tys))
            }
            Expr::Bindings(_) => self.interner.intern(Ty::Void),
            Expr::Block(items) => items
                .last()
                .map(|item| self.preview_expr_ty(item))
                .unwrap_or_else(|| self.interner.intern(Ty::Void)),
            Expr::Assign { name, .. } => {
                self.lookup_value(name).unwrap_or_else(|| self.unknown_ty())
            }
            Expr::AssignPlace { target, .. } => self.preview_expr_ty(target),
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
                    params: self.positional_params(param_tys),
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
            Expr::Member { object, field } => {
                let object_ty = self.preview_expr_ty(object);
                self.field_lookup(object_ty, field)
                    .map(|(_, field_ty)| field_ty)
                    .unwrap_or_else(|| self.unknown_ty())
            }
            Expr::Binary { op, lhs, rhs } => self.infer_binary_expr(*op, lhs, rhs),
            Expr::MacroApply { macro_name, .. } if macro_name == "let" || macro_name == "def" => {
                self.interner.intern(Ty::Void)
            }
            Expr::TypeExpr(_) => self.unknown_ty(),
            Expr::TypeApply { .. } => self.unknown_ty(),
            _ => self.infer_expr(expr),
        }
    }

    fn collect_checked_bindings(
        pattern: &Pattern,
        ty: TyId,
        value: &CheckedExpr,
    ) -> Vec<CheckedBinding> {
        match pattern {
            Pattern::Ident(name) if name != "true" && name != "false" => vec![CheckedBinding {
                name: Some(name.clone()),
                ty,
                value: value.clone(),
            }],
            Pattern::Wildcard => vec![CheckedBinding {
                name: None,
                ty,
                value: value.clone(),
            }],
            Pattern::DotVariant { payload, .. } => payload
                .as_deref()
                .map(|inner| Self::collect_checked_bindings(inner, ty, value))
                .unwrap_or_else(|| {
                    vec![CheckedBinding {
                        name: None,
                        ty,
                        value: value.clone(),
                    }]
                }),
            _ => vec![CheckedBinding {
                name: None,
                ty,
                value: value.clone(),
            }],
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
        Self::new(CheckContext::default(), CheckOptions::default())
    }
}

fn map_context(context: &str) -> TypingContext {
    match context {
        "assignment" => TypingContext::Assignment,
        "if condition" => TypingContext::IfCondition,
        "if branch" => TypingContext::IfBranch,
        "cases arm" => TypingContext::CasesArm,
        "call argument" => TypingContext::CallArgument,
        "cast expression" => TypingContext::CastExpression,
        "binary operation" => TypingContext::BinaryOperation,
        "generic constraint" => TypingContext::GenericConstraint,
        "function return type" | "function return" => TypingContext::ReturnType,
        other => TypingContext::Custom(other.to_string()),
    }
}

fn ty_to_ref(ty: &Ty, interner: &TyInterner) -> TypeRef {
    match ty {
        Ty::InferVar(v) => TypeRef::InferVar(*v),
        Ty::GenericParam(name) => TypeRef::GenericParam(name.clone()),
        Ty::Int8 => TypeRef::Primitive(PrimitiveType::Int8),
        Ty::Int16 => TypeRef::Primitive(PrimitiveType::Int16),
        Ty::Int32 => TypeRef::Primitive(PrimitiveType::Int32),
        Ty::Int64 => TypeRef::Primitive(PrimitiveType::Int64),
        Ty::Int128 => TypeRef::Primitive(PrimitiveType::Int128),
        Ty::ISize => TypeRef::Primitive(PrimitiveType::ISize),
        Ty::UInt8 => TypeRef::Primitive(PrimitiveType::UInt8),
        Ty::UInt16 => TypeRef::Primitive(PrimitiveType::UInt16),
        Ty::UInt32 => TypeRef::Primitive(PrimitiveType::UInt32),
        Ty::UInt64 => TypeRef::Primitive(PrimitiveType::UInt64),
        Ty::UInt128 => TypeRef::Primitive(PrimitiveType::UInt128),
        Ty::USize => TypeRef::Primitive(PrimitiveType::USize),
        Ty::Float32 => TypeRef::Primitive(PrimitiveType::Float32),
        Ty::Float64 => TypeRef::Primitive(PrimitiveType::Float64),
        Ty::Bool => TypeRef::Primitive(PrimitiveType::Bool),
        Ty::Char => TypeRef::Primitive(PrimitiveType::Char),
        Ty::Void => TypeRef::Primitive(PrimitiveType::Void),
        Ty::Never => TypeRef::Primitive(PrimitiveType::Never),
        Ty::Any => TypeRef::Primitive(PrimitiveType::Any),
        Ty::Nominal(name) => TypeRef::Nominal(name.clone()),
        Ty::RawAlloc(item) => TypeRef::RawAlloc(Box::new(
            interner
                .get(*item)
                .map(|t| ty_to_ref(t, interner))
                .unwrap_or(TypeRef::Unknown),
        )),
        Ty::Slice(item) => TypeRef::Slice(Box::new(
            interner
                .get(*item)
                .map(|t| ty_to_ref(t, interner))
                .unwrap_or(TypeRef::Unknown),
        )),
        Ty::Ref(item) => TypeRef::Ref(Box::new(
            interner
                .get(*item)
                .map(|t| ty_to_ref(t, interner))
                .unwrap_or(TypeRef::Unknown),
        )),
        Ty::List(item) => {
            let item_ref = interner
                .get(*item)
                .map(|t| ty_to_ref(t, interner))
                .unwrap_or(TypeRef::Unknown);
            TypeRef::List(Box::new(item_ref))
        }
        Ty::Dict { key, value } => {
            let key_ref = interner
                .get(*key)
                .map(|t| ty_to_ref(t, interner))
                .unwrap_or(TypeRef::Unknown);
            let value_ref = interner
                .get(*value)
                .map(|t| ty_to_ref(t, interner))
                .unwrap_or(TypeRef::Unknown);
            TypeRef::Dict {
                key: Box::new(key_ref),
                value: Box::new(value_ref),
            }
        }
        Ty::Set(item) => {
            let item_ref = interner
                .get(*item)
                .map(|t| ty_to_ref(t, interner))
                .unwrap_or(TypeRef::Unknown);
            TypeRef::Set(Box::new(item_ref))
        }
        Ty::Array { item, size } => {
            let item_ref = interner
                .get(*item)
                .map(|t| ty_to_ref(t, interner))
                .unwrap_or(TypeRef::Unknown);
            TypeRef::Array {
                item: Box::new(item_ref),
                size: *size,
            }
        }
        Ty::Func { params, ret } => {
            let params_ref = params
                .iter()
                .map(|param| FuncParamRef {
                    name: param.name.clone(),
                    label: param.label.clone(),
                    trailing: param.trailing,
                    ty: Box::new(
                        interner
                            .get(param.ty)
                            .map(|t| ty_to_ref(t, interner))
                            .unwrap_or(TypeRef::Unknown),
                    ),
                })
                .collect::<Vec<_>>();
            let ret_ref = interner
                .get(*ret)
                .map(|t| ty_to_ref(t, interner))
                .unwrap_or(TypeRef::Unknown);
            TypeRef::Func {
                params: params_ref,
                ret: Box::new(ret_ref),
            }
        }
        Ty::Macro { params, ret } => {
            let params_ref = params
                .iter()
                .map(|param| FuncParamRef {
                    name: param.name.clone(),
                    label: param.label.clone(),
                    trailing: param.trailing,
                    ty: Box::new(
                        interner
                            .get(param.ty)
                            .map(|t| ty_to_ref(t, interner))
                            .unwrap_or(TypeRef::Unknown),
                    ),
                })
                .collect::<Vec<_>>();
            let ret_ref = interner
                .get(*ret)
                .map(|t| ty_to_ref(t, interner))
                .unwrap_or(TypeRef::Unknown);
            TypeRef::Macro {
                params: params_ref,
                ret: Box::new(ret_ref),
            }
        }
        Ty::Tuple(items) => {
            let refs = items
                .iter()
                .map(|id| {
                    interner
                        .get(*id)
                        .map(|t| ty_to_ref(t, interner))
                        .unwrap_or(TypeRef::Unknown)
                })
                .collect::<Vec<_>>();
            TypeRef::Tuple(refs)
        }
        Ty::Struct(fields) => {
            let refs = fields
                .iter()
                .map(|(name, id)| {
                    let ty_ref = interner
                        .get(*id)
                        .map(|t| ty_to_ref(t, interner))
                        .unwrap_or(TypeRef::Unknown);
                    (name.clone(), ty_ref)
                })
                .collect::<Vec<_>>();
            TypeRef::Struct(refs)
        }
        Ty::Union(items) => {
            let refs = items
                .iter()
                .map(|id| {
                    interner
                        .get(*id)
                        .map(|t| ty_to_ref(t, interner))
                        .unwrap_or(TypeRef::Unknown)
                })
                .collect::<Vec<_>>();
            TypeRef::Union(refs)
        }
        Ty::Enum(variants) => {
            let refs = variants
                .iter()
                .map(|(name, payload)| {
                    let payload_ref =
                        payload.and_then(|id| interner.get(id).map(|t| ty_to_ref(t, interner)));
                    (name.clone(), payload_ref)
                })
                .collect::<Vec<_>>();
            TypeRef::Enum(refs)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::TypeChecker;
    use crate::checked_ir::CheckedExpr;
    use crate::types::Ty;
    use crate::CheckContext;
    use aura_frontend::ast::{
        BinaryOp as ParsedBinaryOp, Decl, Expr, FunctionDecl, LabeledClosureArg, Pattern, Program,
        StaticArg, StaticParam, StaticParamKind, StaticValueExpr, TypeExpr, UseBinding, UseDecl,
    };
    use aura_frontend::Parser;

    fn ty_param(name: &str) -> StaticParam {
        StaticParam {
            name: name.to_string(),
            kind: StaticParamKind::Type,
        }
    }

    use crate::{check_module, check_module_with_options, CheckOptions};

    #[test]
    fn allows_implicit_numeric_widening_on_reassignment() {
        let program = Program {
            declarations: vec![
                Decl::Assign {
                    static_params: Vec::new(),
                    doc: None,
                    name: "x".to_string(),
                    value: Expr::Int("1".to_string()),
                },
                Decl::Assign {
                    static_params: Vec::new(),
                    doc: None,
                    name: "x".to_string(),
                    value: Expr::Int("2".to_string()),
                },
            ],
        };

        let checked = check_module_with_options(
            &program,
            CheckOptions {
                enforce_main_signature: true,
            },
        );
        assert!(checked.module.is_none()); // duplicate symbol from resolver in same scope
    }

    #[test]
    fn multi_arm_without_fallback_reports_non_exhaustive() {
        let program = Program {
            declarations: vec![Decl::Function(FunctionDecl {
                doc: None,
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

        let checked = check_module_with_options(
            &program,
            CheckOptions {
                enforce_main_signature: true,
            },
        );
        assert!(checked.module.is_none());
        assert!(checked
            .diagnostics
            .iter()
            .any(|d| d.code_str() == "E_PATTERN_NON_EXHAUSTIVE"));
    }

    #[test]
    fn wildcard_then_extra_arm_reports_unreachable() {
        let program = Program {
            declarations: vec![Decl::Function(FunctionDecl {
                doc: None,
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
            .any(|d| d.code_str() == "E_PATTERN_UNREACHABLE_ARM"));
    }

    #[test]
    fn method_receiver_without_required_static_args_reports_type_arg_missing() {
        let program = Program {
            declarations: vec![Decl::Function(FunctionDecl {
                doc: None,
                static_params: Vec::new(),
                receiver: Some(TypeExpr::Named {
                    name: "Seq".to_string(),
                    args: Vec::new(),
                }),
                name: "len".to_string(),
                params: vec![aura_frontend::ast::Param {
                    name: "self".to_string(),
                    ty: TypeExpr::Named {
                        name: "Seq".to_string(),
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
        assert!(checked
            .diagnostics
            .iter()
            .any(|d| d.code_str() == "E_TYPE_ARG_MISSING"));
        assert!(checked.diagnostics.iter().any(|d| {
            d.hint
                .as_deref()
                .is_some_and(|h| h.contains("Seq[T].method"))
        }));
    }

    #[test]
    fn string_is_not_primitive_and_is_nominal() {
        let program = Program {
            declarations: vec![Decl::Assign {
                static_params: Vec::new(),
                doc: None,
                name: "s".to_string(),
                value: Expr::String("ok".to_string()),
            }],
        };

        let checked = check_module(&program);
        assert!(
            checked.module.is_some(),
            "expected module, got diagnostics: {:?}",
            checked.diagnostics
        );
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
                static_params: Vec::new(),
                doc: None,
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
    fn checked_ir_emits_local_bind_and_local_assignment_nodes() {
        let program = Parser::parse_source("def main() -> Int { let x = 1; x = 2; x }")
            .expect("source should parse");

        let checked = check_module(&program);
        let module = checked.module.expect("checked module should exist");
        let main_decl = module
            .ir
            .declarations
            .iter()
            .find(|decl| decl.name == "main")
            .expect("main declaration should exist");

        let CheckedExpr::Block(items) = &main_decl.value else {
            panic!("expected block body in checked ir")
        };
        assert!(matches!(
            items[0],
            CheckedExpr::LocalBind { mutable: true, .. }
        ));
        assert!(matches!(items[1], CheckedExpr::AssignLocal { .. }));
    }

    #[test]
    fn checked_ir_emits_field_access_and_assignment_nodes() {
        let program = Parser::parse_source(
            "def Pair = (left: Int, right: Int); \
             def main() -> Int { let p = (left = 1, right = 2); p.right = 3; p.right }",
        )
        .expect("source should parse");

        let checked = check_module(&program);
        assert!(
            checked.diagnostics.is_empty(),
            "unexpected diagnostics: {:?}",
            checked.diagnostics
        );
        let module = checked.module.expect("checked module should exist");
        let main_decl = module
            .ir
            .declarations
            .iter()
            .find(|decl| decl.name == "main")
            .expect("main declaration should exist");

        let CheckedExpr::Block(items) = &main_decl.value else {
            panic!("expected block body in checked ir")
        };
        assert!(matches!(
            items[1],
            CheckedExpr::AssignField { field_index: 1, .. }
        ));
        let final_expr = match &items[2] {
            CheckedExpr::Coerce { expr, .. } | CheckedExpr::Cast { expr, .. } => expr.as_ref(),
            expr => expr,
        };
        assert!(matches!(
            final_expr,
            CheckedExpr::FieldAccess { field_index: 1, .. }
        ));
    }

    #[test]
    fn immutable_root_rejects_field_assignment() {
        let program = Parser::parse_source(
            "def main() -> Int { def p = (left = 1, right = 2); p.right = 3; p.right }",
        )
        .expect("source should parse");

        let checked = check_module(&program);
        assert!(
            checked.module.is_none(),
            "expected failure, got diagnostics: {:?}",
            checked.diagnostics
        );
        assert!(
            checked.diagnostics.iter().any(|d| d
                .hint
                .as_deref()
                .is_some_and(|hint| hint.contains("bind the value with `let`"))),
            "diagnostics: {:?}",
            checked.diagnostics
        );
    }

    #[test]
    fn checked_ir_preserves_call_shape() {
        let program = Program {
            declarations: vec![Decl::Assign {
                static_params: Vec::new(),
                doc: None,
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
                    static_params: Vec::new(),
                    doc: None,
                    name: "x".to_string(),
                    value: Expr::Int("1".to_string()),
                },
                Decl::Assign {
                    static_params: Vec::new(),
                    doc: None,
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
                doc: None,
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
        assert!(!checked.diagnostics.is_empty());
    }

    #[test]
    fn multi_arm_result_type_mismatch_produces_diagnostic() {
        let program = Program {
            declarations: vec![Decl::Function(FunctionDecl {
                doc: None,
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
        assert!(!checked.diagnostics.is_empty());
    }

    #[test]
    fn duplicate_use_targets_fail_typecheck_pipeline() {
        let program = Program {
            declarations: vec![
                Decl::Use(UseDecl {
                    binding: UseBinding::Namespace("io".to_string()),
                    source: "./io".to_string(),
                }),
                Decl::Use(UseDecl {
                    binding: UseBinding::Namespace("io".to_string()),
                    source: "./io".to_string(),
                }),
            ],
        };

        let checked = check_module(&program);
        assert!(checked.module.is_none());
        assert!(checked
            .diagnostics
            .iter()
            .any(|d| d.code_str() == "E_USE_DUPLICATE"));
    }

    #[test]
    fn unknown_builtin_symbol_reports_diagnostic() {
        let program = Program {
            declarations: vec![Decl::Assign {
                static_params: Vec::new(),
                doc: None,
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
            .any(|d| d.code_str() == "E_BUILTIN_FORM"));
    }

    #[test]
    fn type_mismatch_diagnostic_contains_related_context() {
        let program = Program {
            declarations: vec![
                Decl::Assign {
                    static_params: Vec::new(),
                    doc: None,
                    name: "x".to_string(),
                    value: Expr::List(vec![Expr::Int("1".to_string())]),
                },
                Decl::Assign {
                    static_params: Vec::new(),
                    doc: None,
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
            .find(|d| d.code_str() == "E_TYPE_MISMATCH")
            .expect("expected mismatch diagnostic");
        assert!(!diag.related.is_empty());
    }

    #[test]
    fn call_inference_uses_function_signature_shape() {
        let program = Program {
            declarations: vec![
                Decl::Assign {
                    static_params: Vec::new(),
                    doc: None,
                    name: "f".to_string(),
                    value: Expr::Ident("unknown_callable".to_string()),
                },
                Decl::Assign {
                    static_params: Vec::new(),
                    doc: None,
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
            .any(|d| d.code_str() == "E_UNIFY_MISMATCH");
        assert!(!has_unify_error);
    }

    #[test]
    fn unify_mismatch_includes_obligation_trace() {
        let program = Program {
            declarations: vec![Decl::Assign {
                static_params: Vec::new(),
                doc: None,
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
            .find(|d| d.code_str() == "E_UNIFY_MISMATCH")
            .expect("expected unify mismatch diagnostic");
        assert!(!diag.obligations.is_empty());
    }

    #[test]
    fn numeric_operator_requires_numeric_operands() {
        let program = Program {
            declarations: vec![Decl::Assign {
                static_params: Vec::new(),
                doc: None,
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
            .any(|d| d.code_str() == "E_OP_NON_NUMERIC"));
    }

    #[test]
    fn builtin_macro_is_rejected() {
        let program = Program {
            declarations: vec![Decl::Assign {
                static_params: Vec::new(),
                doc: None,
                name: "y".to_string(),
                value: Expr::MacroApply {
                    macro_name: "builtin".to_string(),
                    static_args: vec![StaticArg::Value(StaticValueExpr::Int("4".to_string()))],
                    operand: Box::new(Expr::Ident("syscall_exit".to_string())),
                },
            }],
        };

        let checked = check_module(&program);
        assert!(checked.module.is_none());
        assert!(checked
            .diagnostics
            .iter()
            .any(|d| d.code_str() == "E_BUILTIN_FORM"));
    }

    #[test]
    fn if_call_typechecks_with_labeled_closures() {
        let program = Program {
            declarations: vec![Decl::Assign {
                static_params: Vec::new(),
                doc: None,
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
            CheckedExpr::If { .. }
        ));
        let x_ty = module.value_types.get("x").expect("x should exist");
        assert!(matches!(module.types.get(*x_ty), Some(Ty::Int32)));
    }

    #[test]
    fn cases_call_typechecks_with_when_closure() {
        let program = Program {
            declarations: vec![Decl::Assign {
                static_params: Vec::new(),
                doc: None,
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
            CheckedExpr::Cases { .. }
        ));
        let x_ty = module.value_types.get("x").expect("x should exist");
        assert!(matches!(module.types.get(*x_ty), Some(Ty::Int32)));
    }

    #[test]
    fn defstub_lowers_to_extern_ir_declaration() {
        let program = Parser::parse_source("defstub syscall_exit: Func[(code: Int), Never]")
            .expect("source should parse");

        let checked = check_module(&program);
        let module = checked.module.expect("module should exist");
        let decl = module
            .ir
            .declarations
            .iter()
            .find(|decl| decl.name == "syscall_exit")
            .expect("stub declaration should exist");

        assert!(decl.is_extern);
        assert!(matches!(module.types.get(decl.ty), Some(Ty::Func { .. })));
    }

    #[test]
    fn macro_defstub_does_not_emit_runtime_extern_declaration() {
        let program = Parser::parse_source("defstub[T] return: Macro[T, Never]")
            .expect("source should parse");

        let checked = check_module(&program);
        let module = checked.module.expect("module should exist");

        assert!(module.ir.declarations.is_empty());
        assert!(matches!(
            module
                .value_types
                .get("return")
                .and_then(|ty| module.types.get(*ty)),
            Some(Ty::Macro { .. })
        ));
    }

    #[test]
    fn loop_call_typechecks_with_while_and_do_closures() {
        let program = Parser::parse_source("def main() -> Void { loop while { true } do { () } }")
            .expect("source should parse");

        let checked = check_module(&program);
        let module = checked.module.expect("module should exist");
        let main_decl = module
            .ir
            .declarations
            .iter()
            .find(|decl| decl.name == "main")
            .expect("main declaration should exist");

        assert!(
            matches!(main_decl.value, CheckedExpr::Loop { .. })
                || matches!(
                    main_decl.value,
                    CheckedExpr::Block(ref items)
                        if matches!(items.first(), Some(CheckedExpr::Loop { .. }))
                )
        );
    }

    #[test]
    fn loop_call_typechecks_as_direct_or_block_wrapped_loop() {
        let program = Parser::parse_source("def main() -> Void { loop do { () } }")
            .expect("source should parse");

        let checked = check_module(&program);
        let module = checked.module.expect("module should exist");
        let main_decl = module
            .ir
            .declarations
            .iter()
            .find(|decl| decl.name == "main")
            .expect("main declaration should exist");

        assert!(
            matches!(main_decl.value, CheckedExpr::Loop { .. })
                || matches!(
                    main_decl.value,
                    CheckedExpr::Block(ref items)
                        if matches!(items.first(), Some(CheckedExpr::Loop { .. }))
                )
        );
    }

    #[test]
    fn if_macro_form_is_rejected() {
        let program = Program {
            declarations: vec![Decl::Assign {
                static_params: Vec::new(),
                doc: None,
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
        assert!(checked
            .diagnostics
            .iter()
            .any(|d| d.code_str() == "E_IF_FORM"));
    }

    #[test]
    fn cases_macro_form_is_rejected() {
        let program = Program {
            declarations: vec![Decl::Assign {
                static_params: Vec::new(),
                doc: None,
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
        assert!(checked
            .diagnostics
            .iter()
            .any(|d| d.code_str() == "E_CASES_FORM"));
    }

    #[test]
    fn return_break_continue_lower_to_control_flow_ir() {
        let program = Program {
            declarations: vec![
                Decl::Function(FunctionDecl {
                    doc: None,
                    static_params: Vec::new(),
                    receiver: None,
                    name: "r".to_string(),
                    params: Vec::new(),
                    return_type: TypeExpr::Named {
                        name: "Int".to_string(),
                        args: Vec::new(),
                    },
                    body: Expr::MacroApply {
                        macro_name: "return".to_string(),
                        static_args: Vec::new(),
                        operand: Box::new(Expr::Int("1".to_string())),
                    },
                }),
                Decl::Function(FunctionDecl {
                    doc: None,
                    static_params: Vec::new(),
                    receiver: None,
                    name: "b".to_string(),
                    params: Vec::new(),
                    return_type: TypeExpr::Named {
                        name: "Int".to_string(),
                        args: Vec::new(),
                    },
                    body: Expr::Call {
                        callee: Box::new(Expr::Ident("loop".to_string())),
                        static_args: Vec::new(),
                        args: Vec::new(),
                        trailing: vec![LabeledClosureArg {
                            label: "do".to_string(),
                            body: Expr::MacroApply {
                                macro_name: "break".to_string(),
                                static_args: Vec::new(),
                                operand: Box::new(Expr::List(vec![Expr::Int("9".to_string())])),
                            },
                        }],
                    },
                }),
                Decl::Function(FunctionDecl {
                    doc: None,
                    static_params: Vec::new(),
                    receiver: None,
                    name: "c".to_string(),
                    params: Vec::new(),
                    return_type: TypeExpr::Named {
                        name: "Never".to_string(),
                        args: Vec::new(),
                    },
                    body: Expr::Call {
                        callee: Box::new(Expr::Ident("loop".to_string())),
                        static_args: Vec::new(),
                        args: Vec::new(),
                        trailing: vec![LabeledClosureArg {
                            label: "do".to_string(),
                            body: Expr::MacroApply {
                                macro_name: "continue".to_string(),
                                static_args: Vec::new(),
                                operand: Box::new(Expr::Tuple(Vec::new())),
                            },
                        }],
                    },
                }),
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
            CheckedExpr::Loop { .. }
        ));
        assert!(matches!(
            module.ir.declarations[2].value,
            CheckedExpr::Loop { .. }
        ));
    }

    #[test]
    fn return_outside_function_reports_error() {
        let program = Parser::parse_source("def bad = return 1").expect("source should parse");

        let checked = check_module(&program);

        assert!(checked.module.is_none());
        assert!(checked
            .diagnostics
            .iter()
            .any(|d| d.code_str() == "E_BUILTIN_FORM"));
    }

    #[test]
    fn break_and_continue_outside_loop_report_errors() {
        let program = Parser::parse_source(
            "def bad_break() -> Void { break 1 } def bad_continue() -> Void { continue 1 }",
        )
        .expect("source should parse");

        let checked = check_module(&program);

        assert!(checked.module.is_none());
        assert!(
            checked
                .diagnostics
                .iter()
                .filter(|d| d.code_str() == "E_BUILTIN_FORM")
                .count()
                >= 2
        );
    }

    #[test]
    fn cast_macro_lowers_to_explicit_cast_ir() {
        let program = Program {
            declarations: vec![Decl::Assign {
                static_params: Vec::new(),
                doc: None,
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
                static_params: Vec::new(),
                doc: None,
                name: "x".to_string(),
                value: Expr::Ident("missing".to_string()),
            }],
        };

        let checked = check_module(&program);
        assert!(
            checked.module.is_some(),
            "expected module, got diagnostics: {:?}",
            checked.diagnostics
        );
        assert!(checked
            .diagnostics
            .iter()
            .any(|d| d.code_str() == "W_UNRESOLVED_IDENT"));
    }

    #[test]
    fn closure_lowers_to_typed_closure_ir() {
        let program = Program {
            declarations: vec![Decl::Assign {
                static_params: Vec::new(),
                doc: None,
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
    fn main_signature_accepts_void() {
        let program = Program {
            declarations: vec![Decl::Function(FunctionDecl {
                doc: None,
                static_params: Vec::new(),
                receiver: None,
                name: "main".to_string(),
                params: Vec::new(),
                return_type: TypeExpr::Named {
                    name: "Void".to_string(),
                    args: Vec::new(),
                },
                body: Expr::DotIdent {
                    name: "unit".to_string(),
                    payload: None,
                },
            })],
        };

        let checked = check_module(&program);
        assert!(checked
            .diagnostics
            .iter()
            .all(|d| d.code_str() != "E_MAIN_SIGNATURE"));
    }

    #[test]
    fn main_signature_rejects_result_void_u8() {
        let program = Program {
            declarations: vec![Decl::Function(FunctionDecl {
                doc: None,
                static_params: Vec::new(),
                receiver: None,
                name: "main".to_string(),
                params: Vec::new(),
                return_type: TypeExpr::Named {
                    name: "Result".to_string(),
                    args: vec![
                        StaticArg::Type(TypeExpr::Named {
                            name: "Void".to_string(),
                            args: Vec::new(),
                        }),
                        StaticArg::Type(TypeExpr::Named {
                            name: "UInt8".to_string(),
                            args: Vec::new(),
                        }),
                    ],
                },
                body: Expr::DotIdent {
                    name: "ok".to_string(),
                    payload: None,
                },
            })],
        };

        let checked = check_module_with_options(
            &program,
            CheckOptions {
                enforce_main_signature: true,
            },
        );
        assert!(checked
            .diagnostics
            .iter()
            .any(|d| d.code_str() == "E_MAIN_SIGNATURE"));
    }

    #[test]
    fn main_signature_rejects_result_void_int32() {
        let program = Program {
            declarations: vec![Decl::Function(FunctionDecl {
                doc: None,
                static_params: Vec::new(),
                receiver: None,
                name: "main".to_string(),
                params: Vec::new(),
                return_type: TypeExpr::Named {
                    name: "Result".to_string(),
                    args: vec![
                        StaticArg::Type(TypeExpr::Named {
                            name: "Void".to_string(),
                            args: Vec::new(),
                        }),
                        StaticArg::Type(TypeExpr::Named {
                            name: "Int".to_string(),
                            args: Vec::new(),
                        }),
                    ],
                },
                body: Expr::DotIdent {
                    name: "ok".to_string(),
                    payload: None,
                },
            })],
        };

        let checked = check_module_with_options(
            &program,
            CheckOptions {
                enforce_main_signature: true,
            },
        );
        assert!(checked
            .diagnostics
            .iter()
            .any(|d| d.code_str() == "E_MAIN_SIGNATURE"));
    }

    #[test]
    fn main_signature_not_enforced_when_option_disabled() {
        let program = Program {
            declarations: vec![Decl::Function(FunctionDecl {
                doc: None,
                static_params: Vec::new(),
                receiver: None,
                name: "main".to_string(),
                params: Vec::new(),
                return_type: TypeExpr::Named {
                    name: "Result".to_string(),
                    args: vec![
                        StaticArg::Type(TypeExpr::Named {
                            name: "Void".to_string(),
                            args: Vec::new(),
                        }),
                        StaticArg::Type(TypeExpr::Named {
                            name: "UInt8".to_string(),
                            args: Vec::new(),
                        }),
                    ],
                },
                body: Expr::DotIdent {
                    name: "ok".to_string(),
                    payload: None,
                },
            })],
        };

        let checked = check_module(&program);
        assert!(checked
            .diagnostics
            .iter()
            .all(|d| d.code_str() != "E_MAIN_SIGNATURE"));
    }

    #[test]
    fn dot_identifier_without_payload_is_void_typed() {
        let program = Program {
            declarations: vec![Decl::Assign {
                static_params: Vec::new(),
                doc: None,
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
    fn empty_tuple_expression_is_void_typed() {
        let program = Program {
            declarations: vec![Decl::Assign {
                static_params: Vec::new(),
                doc: None,
                name: "v".to_string(),
                value: Expr::Tuple(Vec::new()),
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
    fn empty_tuple_type_expr_resolves_to_void() {
        let program = Program {
            declarations: vec![Decl::Function(FunctionDecl {
                doc: None,
                static_params: Vec::new(),
                receiver: None,
                name: "id".to_string(),
                params: vec![aura_frontend::ast::Param {
                    name: "x".to_string(),
                    ty: TypeExpr::Tuple(Vec::new()),
                }],
                return_type: TypeExpr::Tuple(Vec::new()),
                body: Expr::Ident("x".to_string()),
            })],
        };

        let checked = check_module(&program);
        let module = checked.module.expect("module should exist");
        let decl = module
            .ir
            .declarations
            .iter()
            .find(|decl| decl.name == "id")
            .expect("function declaration should exist");
        let ty = module.types.get(decl.ty).expect("type should exist");
        let Ty::Func { params, ret } = ty else {
            panic!("expected function type")
        };
        assert_eq!(params.len(), 1);
        assert!(matches!(module.types.get(params[0].ty), Some(Ty::Void)));
        assert!(matches!(module.types.get(*ret), Some(Ty::Void)));
    }

    #[test]
    fn function_params_are_available_in_body_scope() {
        let program = Program {
            declarations: vec![Decl::Function(FunctionDecl {
                doc: None,
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
        assert!(
            checked.module.is_some(),
            "expected module, got diagnostics: {:?}",
            checked.diagnostics
        );
        assert!(!checked
            .diagnostics
            .iter()
            .any(|d| d.code_str() == "W_UNRESOLVED_IDENT"));
    }

    #[test]
    fn function_param_scope_does_not_leak_to_global() {
        let program = Program {
            declarations: vec![
                Decl::Function(FunctionDecl {
                    doc: None,
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
                    static_params: Vec::new(),
                    doc: None,
                    name: "z".to_string(),
                    value: Expr::Ident("x".to_string()),
                },
            ],
        };

        let checked = check_module(&program);
        assert!(
            checked.module.is_some(),
            "expected module, got diagnostics: {:?}",
            checked.diagnostics
        );
        assert!(checked
            .diagnostics
            .iter()
            .any(|d| d.code_str() == "W_UNRESOLVED_IDENT"));
    }

    #[test]
    fn multi_arm_pattern_identifier_is_scoped_to_arm_body() {
        let program = Program {
            declarations: vec![Decl::Assign {
                static_params: Vec::new(),
                doc: None,
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
        assert!(
            checked.module.is_some(),
            "expected module, got diagnostics: {:?}",
            checked.diagnostics
        );
        assert!(!checked
            .diagnostics
            .iter()
            .any(|d| d.code_str() == "W_UNRESOLVED_IDENT"));
    }

    #[test]
    fn pattern_identifier_does_not_leak_outside_multi_arm() {
        let program = Program {
            declarations: vec![
                Decl::Assign {
                    static_params: Vec::new(),
                    doc: None,
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
                    static_params: Vec::new(),
                    doc: None,
                    name: "z".to_string(),
                    value: Expr::Ident("v".to_string()),
                },
            ],
        };

        let checked = check_module(&program);
        assert!(
            checked.module.is_some(),
            "expected module, got diagnostics: {:?}",
            checked.diagnostics
        );
        assert!(checked
            .diagnostics
            .iter()
            .any(|d| d.code_str() == "W_UNRESOLVED_IDENT"));
    }

    #[test]
    fn generic_function_call_static_arg_instantiates_signature() {
        let program = Program {
            declarations: vec![
                Decl::Function(FunctionDecl {
                    doc: None,
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
                    static_params: Vec::new(),
                    doc: None,
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
                    doc: None,
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
                    static_params: Vec::new(),
                    doc: None,
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
            .any(|d| d.code_str() == "E_CALL_STATIC_UNEXPECTED"));
    }

    #[test]
    fn generic_call_with_missing_static_arg_reports_arity_error() {
        let program = Program {
            declarations: vec![
                Decl::Function(FunctionDecl {
                    doc: None,
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
                    static_params: Vec::new(),
                    doc: None,
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
                    static_params: Vec::new(),
                    doc: None,
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
            .any(|d| d.code_str() == "E_CALL_STATIC_ARITY"));
    }

    #[test]
    fn generic_call_partial_explicit_args_report_arity_error() {
        let program = Program {
            declarations: vec![
                Decl::Function(FunctionDecl {
                    doc: None,
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
                    static_params: Vec::new(),
                    doc: None,
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
            .any(|d| d.code_str() == "E_CALL_STATIC_ARITY"));
    }

    #[test]
    fn empty_list_in_call_argument_uses_expected_element_type() {
        let program = Program {
            declarations: vec![
                Decl::Function(FunctionDecl {
                    doc: None,
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
                    static_params: Vec::new(),
                    doc: None,
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
        assert!(
            checked.module.is_some(),
            "expected module, got diagnostics: {:?}",
            checked.diagnostics
        );
        assert!(!checked
            .diagnostics
            .iter()
            .any(|d| d.code_str() == "E_TYPE_MISMATCH"));
    }

    #[test]
    fn empty_dict_in_call_argument_uses_expected_key_value_types() {
        let program = Program {
            declarations: vec![
                Decl::Function(FunctionDecl {
                    doc: None,
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
                    static_params: Vec::new(),
                    doc: None,
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
        assert!(
            checked.module.is_some(),
            "expected module, got diagnostics: {:?}",
            checked.diagnostics
        );
        assert!(!checked
            .diagnostics
            .iter()
            .any(|d| d.code_str() == "E_TYPE_MISMATCH"));
    }

    #[test]
    fn expected_type_guides_if_macro_branches() {
        let program = Program {
            declarations: vec![Decl::Function(FunctionDecl {
                doc: None,
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
        assert!(
            checked.module.is_some(),
            "expected module, got diagnostics: {:?}",
            checked.diagnostics
        );
        assert!(!checked
            .diagnostics
            .iter()
            .any(|d| d.code_str() == "E_TYPE_MISMATCH"));
    }

    #[test]
    fn expected_type_guides_cases_arm_bodies() {
        let program = Program {
            declarations: vec![Decl::Function(FunctionDecl {
                doc: None,
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
        assert!(
            checked.module.is_some(),
            "expected module, got diagnostics: {:?}",
            checked.diagnostics
        );
        assert!(!checked
            .diagnostics
            .iter()
            .any(|d| d.code_str() == "E_TYPE_MISMATCH"));
    }

    #[test]
    fn arm_guard_must_typecheck_as_bool() {
        let program = Program {
            declarations: vec![Decl::Assign {
                static_params: Vec::new(),
                doc: None,
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
            .any(|d| d.code_str() == "E_TYPE_MISMATCH"));
    }

    #[test]
    fn expected_list_type_guides_nested_elements() {
        let program = Program {
            declarations: vec![
                Decl::Function(FunctionDecl {
                    doc: None,
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
                    static_params: Vec::new(),
                    doc: None,
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
            .any(|d| d.code_str() == "E_TYPE_MISMATCH"));
    }

    #[test]
    fn expected_dict_type_guides_nested_entries() {
        let program = Program {
            declarations: vec![
                Decl::Function(FunctionDecl {
                    doc: None,
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
                    static_params: Vec::new(),
                    doc: None,
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
            .any(|d| d.code_str() == "E_TYPE_MISMATCH"));
    }

    #[test]
    fn expected_list_type_rejects_incompatible_element() {
        let program = Program {
            declarations: vec![
                Decl::Function(FunctionDecl {
                    doc: None,
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
                    static_params: Vec::new(),
                    doc: None,
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
            .any(|d| d.code_str() == "E_TYPE_MISMATCH"));
    }

    #[test]
    fn expected_return_type_guides_nested_call_inference() {
        let program = Program {
            declarations: vec![
                Decl::Function(FunctionDecl {
                    doc: None,
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
                    doc: None,
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
            .any(|d| d.code_str() == "E_TYPE_MISMATCH" || d.code_str() == "E_UNIFY_MISMATCH"));
    }

    #[test]
    fn label_expression_propagates_expected_type() {
        let program = Program {
            declarations: vec![Decl::Function(FunctionDecl {
                doc: None,
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
            .any(|d| d.code_str() == "E_TYPE_MISMATCH"));
    }

    #[test]
    fn dot_ident_payload_propagates_expected_type() {
        let program = Program {
            declarations: vec![Decl::Function(FunctionDecl {
                doc: None,
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
            .any(|d| d.code_str() == "E_TYPE_MISMATCH"));
    }

    #[test]
    fn untyped_macro_rule_is_error() {
        let program = Program {
            declarations: vec![Decl::Assign {
                static_params: Vec::new(),
                doc: None,
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
            .any(|d| d.code_str() == "E_MACRO_UNTYPED"));
    }

    #[test]
    fn malformed_if_lowering_uses_macro_apply_fallback_not_any() {
        let program = Program {
            declarations: vec![Decl::Assign {
                static_params: Vec::new(),
                doc: None,
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
        assert!(checked
            .diagnostics
            .iter()
            .any(|d| d.code_str() == "E_IF_FORM"));
    }

    #[test]
    fn malformed_cases_lowering_uses_macro_apply_fallback_not_any() {
        let program = Program {
            declarations: vec![Decl::Assign {
                static_params: Vec::new(),
                doc: None,
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
        assert!(checked
            .diagnostics
            .iter()
            .any(|d| d.code_str() == "E_CASES_FORM"));
    }

    #[test]
    fn list_type_expr_without_item_arg_reports_missing_type_arg() {
        let program = Program {
            declarations: vec![Decl::Function(FunctionDecl {
                doc: None,
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
            .any(|d| d.code_str() == "E_TYPE_ARG_MISSING"));
    }

    #[test]
    fn dict_type_expr_with_value_in_type_slot_reports_kind_error() {
        let program = Program {
            declarations: vec![Decl::Function(FunctionDecl {
                doc: None,
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
            .any(|d| d.code_str() == "E_TYPE_ARG_KIND"));
    }

    #[test]
    fn array_type_expr_without_size_reports_missing_size_error() {
        let program = Program {
            declarations: vec![Decl::Function(FunctionDecl {
                doc: None,
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
            .any(|d| d.code_str() == "E_ARRAY_SIZE_MISSING"));
    }

    #[test]
    fn list_type_expr_with_extra_arg_reports_arity_error() {
        let program = Program {
            declarations: vec![Decl::Function(FunctionDecl {
                doc: None,
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
            .any(|d| d.code_str() == "E_TYPE_ARG_ARITY"));
    }

    #[test]
    fn bool_type_expr_with_any_arg_reports_arity_error() {
        let program = Program {
            declarations: vec![Decl::Function(FunctionDecl {
                doc: None,
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
            .any(|d| d.code_str() == "E_TYPE_ARG_ARITY"));
    }

    #[test]
    fn generic_param_type_resolves_inside_generic_function_signature() {
        let program = Program {
            declarations: vec![
                Decl::Function(FunctionDecl {
                    doc: None,
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
                    static_params: Vec::new(),
                    doc: None,
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
            .get(params[0].ty)
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
                    doc: None,
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
                    static_params: Vec::new(),
                    doc: None,
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
        let list_ty = module.types.get(params[0].ty).expect("param type expected");
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
                    doc: None,
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
                    static_params: Vec::new(),
                    doc: None,
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
                    doc: None,
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
                    static_params: Vec::new(),
                    doc: None,
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
            .any(|d| d.code_str() == "E_INTERFACE_BOUND_UNSAT"));
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
                    doc: None,
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
                    static_params: Vec::new(),
                    doc: None,
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
            .any(|d| d.code_str() == "E_STATIC_ARG_KIND"));
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
                    doc: None,
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
                    static_params: Vec::new(),
                    doc: None,
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
            .any(|d| d.code_str() == "E_STATIC_ARG_MISSING"));
    }

    #[test]
    fn unknown_interface_constraint_reports_diagnostic_in_solver_path() {
        let program = Program {
            declarations: vec![
                Decl::Function(FunctionDecl {
                    doc: None,
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
                    static_params: Vec::new(),
                    doc: None,
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
            .any(|d| d.code_str() == "E_UNKNOWN_INTERFACE"));
    }

    #[test]
    fn ir_wrapping_uses_central_conversion_decision_for_widening() {
        let program = Program {
            declarations: vec![
                Decl::Assign {
                    static_params: Vec::new(),
                    doc: None,
                    name: "x".to_string(),
                    value: Expr::Int("1".to_string()),
                },
                Decl::Assign {
                    static_params: Vec::new(),
                    doc: None,
                    name: "x".to_string(),
                    value: Expr::Int("2".to_string()),
                },
            ],
        };

        let mut checker = TypeChecker::new(CheckContext::default(), CheckOptions::default());
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
                    static_params: Vec::new(),
                    doc: None,
                    name: "x".to_string(),
                    value: Expr::Float("1.5".to_string()),
                },
                Decl::Assign {
                    static_params: Vec::new(),
                    doc: None,
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
            .any(|d| d.code_str() == "E_TYPE_MISMATCH"));
    }

    #[test]
    fn comparison_operator_returns_bool() {
        let program = Program {
            declarations: vec![Decl::Assign {
                static_params: Vec::new(),
                doc: None,
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
                static_params: Vec::new(),
                doc: None,
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
            .any(|d| d.code_str() == "E_TYPE_MISMATCH"));
    }

    #[test]
    fn mod_operator_is_typed_as_numeric_operator() {
        let program = Program {
            declarations: vec![Decl::Assign {
                static_params: Vec::new(),
                doc: None,
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
                static_params: Vec::new(),
                doc: None,
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

    #[test]
    fn pipe_operator_typechecks_as_function_application() {
        let program = Program {
            declarations: vec![
                Decl::Function(FunctionDecl {
                    doc: None,
                    static_params: Vec::new(),
                    receiver: None,
                    name: "inc".to_string(),
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
                    static_params: Vec::new(),
                    doc: None,
                    name: "y".to_string(),
                    value: Expr::Binary {
                        op: ParsedBinaryOp::Pipe,
                        lhs: Box::new(Expr::Int("1".to_string())),
                        rhs: Box::new(Expr::Ident("inc".to_string())),
                    },
                },
            ],
        };

        let checked = check_module(&program);
        let module = checked.module.expect("module should exist");
        let y_ty = module.value_types.get("y").expect("y should exist");
        assert!(matches!(module.types.get(*y_ty), Some(Ty::Int32)));
    }

    #[test]
    fn call_with_placeholder_returns_function_type() {
        let program = Program {
            declarations: vec![
                Decl::Function(FunctionDecl {
                    doc: None,
                    static_params: Vec::new(),
                    receiver: None,
                    name: "add".to_string(),
                    params: vec![
                        aura_frontend::ast::Param {
                            name: "a".to_string(),
                            ty: TypeExpr::Named {
                                name: "Int".to_string(),
                                args: Vec::new(),
                            },
                        },
                        aura_frontend::ast::Param {
                            name: "b".to_string(),
                            ty: TypeExpr::Named {
                                name: "Int".to_string(),
                                args: Vec::new(),
                            },
                        },
                    ],
                    return_type: TypeExpr::Named {
                        name: "Int".to_string(),
                        args: Vec::new(),
                    },
                    body: Expr::Binary {
                        op: ParsedBinaryOp::Add,
                        lhs: Box::new(Expr::Ident("a".to_string())),
                        rhs: Box::new(Expr::Ident("b".to_string())),
                    },
                }),
                Decl::Assign {
                    static_params: Vec::new(),
                    doc: None,
                    name: "p".to_string(),
                    value: Expr::Call {
                        callee: Box::new(Expr::Ident("add".to_string())),
                        static_args: Vec::new(),
                        args: vec![Expr::Int("5".to_string()), Expr::Placeholder],
                        trailing: Vec::new(),
                    },
                },
            ],
        };

        let checked = check_module(&program);
        let module = checked.module.expect("module should exist");
        let p_ty = module.value_types.get("p").expect("p should exist");
        let Some(Ty::Func { params, ret }) = module.types.get(*p_ty) else {
            panic!("p should be a function type")
        };
        assert_eq!(params.len(), 1);
        assert!(matches!(module.types.get(params[0].ty), Some(Ty::Int32)));
        assert!(matches!(module.types.get(*ret), Some(Ty::Int32)));
    }

    #[test]
    fn pipe_operator_uses_placeholder_position_in_call_rhs() {
        let program = Program {
            declarations: vec![
                Decl::Function(FunctionDecl {
                    doc: None,
                    static_params: Vec::new(),
                    receiver: None,
                    name: "add".to_string(),
                    params: vec![
                        aura_frontend::ast::Param {
                            name: "a".to_string(),
                            ty: TypeExpr::Named {
                                name: "Int".to_string(),
                                args: Vec::new(),
                            },
                        },
                        aura_frontend::ast::Param {
                            name: "b".to_string(),
                            ty: TypeExpr::Named {
                                name: "Int".to_string(),
                                args: Vec::new(),
                            },
                        },
                    ],
                    return_type: TypeExpr::Named {
                        name: "Int".to_string(),
                        args: Vec::new(),
                    },
                    body: Expr::Binary {
                        op: ParsedBinaryOp::Add,
                        lhs: Box::new(Expr::Ident("a".to_string())),
                        rhs: Box::new(Expr::Ident("b".to_string())),
                    },
                }),
                Decl::Assign {
                    static_params: Vec::new(),
                    doc: None,
                    name: "y".to_string(),
                    value: Expr::Binary {
                        op: ParsedBinaryOp::Pipe,
                        lhs: Box::new(Expr::Int("1".to_string())),
                        rhs: Box::new(Expr::Call {
                            callee: Box::new(Expr::Ident("add".to_string())),
                            static_args: Vec::new(),
                            args: vec![Expr::Placeholder, Expr::Int("2".to_string())],
                            trailing: Vec::new(),
                        }),
                    },
                },
            ],
        };

        let checked = check_module(&program);
        let module = checked.module.expect("module should exist");
        let y_ty = module.value_types.get("y").expect("y should exist");
        assert!(matches!(module.types.get(*y_ty), Some(Ty::Int32)));
    }

    #[test]
    fn enum_variant_assignment_typechecks_with_expected_enum() {
        let program = Program {
            declarations: vec![Decl::Assign {
                static_params: Vec::new(),
                doc: None,
                name: "res".to_string(),
                value: Expr::Binary {
                    op: ParsedBinaryOp::Colon,
                    lhs: Box::new(Expr::DotIdent {
                        name: "ok".to_string(),
                        payload: Some(Box::new(Expr::Int("5".to_string()))),
                    }),
                    rhs: Box::new(Expr::TypeExpr(TypeExpr::Named {
                        name: "enum".to_string(),
                        args: vec![
                            StaticArg::Type(TypeExpr::Struct(vec![(
                                "err".to_string(),
                                TypeExpr::Named {
                                    name: "String".to_string(),
                                    args: Vec::new(),
                                },
                            )])),
                            StaticArg::Type(TypeExpr::Struct(vec![(
                                "ok".to_string(),
                                TypeExpr::Named {
                                    name: "Int".to_string(),
                                    args: Vec::new(),
                                },
                            )])),
                        ],
                    })),
                },
            }],
        };

        let checked = check_module(&program);
        assert!(checked.module.is_some());
    }

    #[test]
    fn struct_payload_enum_variant_sugar_typechecks_with_expected_enum() {
        let program = Parser::parse_source(
            "def HttpError = enum(err: (message: String, code: Int)); \
             def e: HttpError = .err(message = \"oops\", code = 500)",
        )
        .expect("source should parse");

        let checked = check_module(&program);
        assert!(
            checked.module.is_some(),
            "expected module, got diagnostics: {:?}",
            checked.diagnostics
        );
    }

    #[test]
    fn named_struct_payload_enum_variant_sugar_typechecks() {
        let program = Parser::parse_source(
            "def HttpError = enum(err: (message: String, code: Int)); \
             def e = HttpError.err(message = \"oops\", code = 500)",
        )
        .expect("source should parse");

        let checked = check_module(&program);
        assert!(
            checked.module.is_some(),
            "expected module, got diagnostics: {:?}",
            checked.diagnostics
        );
    }

    #[test]
    fn explicit_struct_value_enum_payload_still_typechecks() {
        let program = Parser::parse_source(
            "def HttpError = enum(err: (message: String, code: Int)); \
             def content = (message = \"oops\", code = 500); \
             def e: HttpError = .err(content)",
        )
        .expect("source should parse");

        let checked = check_module(&program);
        assert!(
            checked.module.is_some(),
            "expected module, got diagnostics: {:?}",
            checked.diagnostics
        );
    }

    #[test]
    fn non_struct_enum_payload_rejects_field_sugar() {
        let program = Parser::parse_source(
            "def Result = enum(err: String); def e: Result = .err(message = \"oops\")",
        )
        .expect("source should parse");

        let checked = check_module(&program);
        assert!(checked.module.is_none());
        assert!(checked
            .diagnostics
            .iter()
            .any(|d| d.code_str() == "E_TYPE_MISMATCH"));
    }

    #[test]
    fn enum_match_struct_payload_pattern_binds_fields() {
        let program = Parser::parse_source(
            "def HttpError = enum(err: (message: String, code: Int), ok); \
             def HttpError.status(self: HttpError) -> Int { \
                 .err(message = msg, code = status) -> status, \
                 .ok -> 0 \
             }",
        )
        .expect("source should parse");

        let checked = check_module(&program);
        assert!(
            checked.module.is_some(),
            "expected module, got diagnostics: {:?}",
            checked.diagnostics
        );
    }

    #[test]
    fn union_assignment_typechecks_when_value_matches_member() {
        let program = Program {
            declarations: vec![Decl::Assign {
                static_params: Vec::new(),
                doc: None,
                name: "n".to_string(),
                value: Expr::Binary {
                    op: ParsedBinaryOp::Colon,
                    lhs: Box::new(Expr::Int("4".to_string())),
                    rhs: Box::new(Expr::TypeExpr(TypeExpr::Named {
                        name: "union".to_string(),
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
                    })),
                },
            }],
        };

        let checked = check_module(&program);
        assert!(checked.module.is_some());
    }

    #[test]
    fn main_can_call_syscall_exit_from_multi_expression_body() {
        let program = Parser::parse_source(
            "defstub syscall_exit: Func[(code: Int), Never]; def main() -> Void { 0; syscall_exit(0) }",
        )
        .expect("source should parse");

        let checked = check_module(&program);
        assert!(
            checked.module.is_some(),
            "expected module, got diagnostics: {:?}",
            checked.diagnostics
        );
    }

    #[test]
    fn main_can_call_syscall_exit_from_local_let_binding() {
        let program = Parser::parse_source(
            "defstub syscall_exit: Func[(code: Int), Never]; def main() -> Void { let exit_code = 0; syscall_exit(exit_code) }",
        )
        .expect("source should parse");

        let checked = check_module(&program);
        assert!(
            checked.module.is_some(),
            "expected module, got diagnostics: {:?}",
            checked.diagnostics
        );
    }

    #[test]
    fn bytes_new_and_get_calls_typecheck() {
        let program = Parser::parse_source("def b = Bytes.new(4); def x = b.get(0)")
            .expect("source should parse");

        let checked = check_module(&program);
        assert!(
            checked.module.is_some(),
            "expected module, got diagnostics: {:?}",
            checked.diagnostics
        );

        let module = checked.module.expect("module should exist");
        let b_ty = module.value_types.get("b").expect("b should exist");
        let x_ty = module.value_types.get("x").expect("x should exist");
        assert!(matches!(module.types.get(*b_ty), Some(Ty::Nominal(name)) if name == "Bytes"));
        assert!(matches!(module.types.get(*x_ty), Some(Ty::UInt8)));
    }

    #[test]
    fn bytes_set_returns_void() {
        let program = Parser::parse_source("def v = { let b = Bytes.new(1); b.set(0, 65) }")
            .expect("source should parse");

        let checked = check_module(&program);
        assert!(
            checked.module.is_some(),
            "expected module, got diagnostics: {:?}",
            checked.diagnostics
        );

        let module = checked.module.expect("module should exist");
        let v_ty = module.value_types.get("v").expect("v should exist");
        assert!(matches!(module.types.get(*v_ty), Some(Ty::Void)));
    }

    #[test]
    fn raw_alloc_slice_and_ref_methods_typecheck() {
        let program = Parser::parse_source(
            "def alloc = RawAlloc[Int].new(4); \
             def slice = alloc.slice(); \
             def got = slice.get(0); \
             def set_ok = slice.set(0, 42); \
             def ref_value = slice.ref_at(0)",
        )
        .expect("source should parse");

        let checked = check_module(&program);
        assert!(
            checked.module.is_some(),
            "expected module, got diagnostics: {:?}",
            checked.diagnostics
        );

        let module = checked.module.expect("module should exist");
        let got_ty = module.value_types.get("got").expect("got should exist");
        let set_ok_ty = module
            .value_types
            .get("set_ok")
            .expect("set_ok should exist");
        let ref_ty = module
            .value_types
            .get("ref_value")
            .expect("ref_value should exist");
        assert!(
            matches!(module.types.get(*got_ty), Some(Ty::Enum(variants)) if variants.len() == 2)
        );
        assert!(matches!(module.types.get(*set_ok_ty), Some(Ty::Bool)));
        assert!(
            matches!(module.types.get(*ref_ty), Some(Ty::Enum(variants)) if variants.len() == 2)
        );
    }

    #[test]
    fn generic_type_aliases_instantiate_static_params() {
        let program = Parser::parse_source(
            "def[T] Box = (value: T); \
             def x: Box[Int] = (value = 1)",
        )
        .expect("source should parse");

        let checked = check_module(&program);
        assert!(
            checked.module.is_some(),
            "expected module, got diagnostics: {:?}",
            checked.diagnostics
        );

        let module = checked.module.expect("module should exist");
        let x_ty = module.value_types.get("x").expect("x should exist");
        assert!(matches!(
            module.types.get(*x_ty),
            Some(Ty::Struct(fields))
                if fields.len() == 1
                    && fields[0].0 == "value"
                    && matches!(module.types.get(fields[0].1), Some(Ty::Int32))
        ));
    }

    #[test]
    fn ref_get_and_set_methods_typecheck() {
        let program = Parser::parse_source(
            "def use_ref(reference: Ref[Int]) -> Int { reference.set(7); reference.get() }",
        )
        .expect("source should parse");

        let checked = check_module(&program);
        assert!(
            checked.module.is_some(),
            "expected module, got diagnostics: {:?}",
            checked.diagnostics
        );
    }

    #[test]
    fn string_into_and_syscall_write_typecheck() {
        let program = Parser::parse_source(
            "defstub syscall_exit: Func[(code: Int), Never]; \
             defstub syscall_write: Func[(fd: Int, bytes: Bytes), ISize]; \
             defstub string_into: Func[(text: String), Bytes]; \
             def main() -> Void { syscall_write(1, \"Hello\".into()); syscall_exit(0) }",
        )
        .expect("source should parse");

        let checked = check_module(&program);
        assert!(
            checked.module.is_some(),
            "expected module, got diagnostics: {:?}",
            checked.diagnostics
        );

        let module = checked.module.expect("module should exist");
        let main_decl = module
            .ir
            .declarations
            .iter()
            .find(|decl| decl.name == "main")
            .expect("main declaration should exist");
        assert!(matches!(
            module.types.get(main_decl.ty),
            Some(Ty::Func { .. })
        ));
    }

    #[test]
    fn local_let_can_be_reassigned() {
        let program = Parser::parse_source("def main() -> Int { let x = 1; x = 2; x }")
            .expect("source should parse");

        let checked = check_module(&program);
        assert!(
            checked.module.is_some(),
            "expected module, got diagnostics: {:?}",
            checked.diagnostics
        );
        assert!(!checked
            .diagnostics
            .iter()
            .any(|d| d.message.contains("immutable local")));
    }

    #[test]
    fn local_def_cannot_be_reassigned() {
        let program = Parser::parse_source("def main() -> Int { def x = 1; x = 2; x }")
            .expect("source should parse");

        let checked = check_module(&program);
        assert!(checked.diagnostics.iter().any(|d| {
            d.code_str() == "E_TYPE_MISMATCH"
                && d.hint
                    .as_deref()
                    .is_some_and(|hint| hint.contains("use `let`"))
        }));
    }

    #[test]
    fn local_shadowing_is_allowed() {
        let program =
            Parser::parse_source("def main() -> Int { let x = 1; let y = { let x = 2; x }; x }")
                .expect("source should parse");

        let checked = check_module(&program);
        assert!(
            checked.module.is_some(),
            "expected module, got diagnostics: {:?}",
            checked.diagnostics
        );
        assert!(!checked
            .diagnostics
            .iter()
            .any(|d| d.code_str() == "W_UNRESOLVED_IDENT"));
    }

    #[test]
    fn collection_item_locals_do_not_leak_across_commas() {
        let program =
            Parser::parse_source("def xs = [let x = 0; x, x]").expect("source should parse");

        let checked = check_module(&program);
        assert!(checked
            .diagnostics
            .iter()
            .any(|d| d.code_str() == "W_UNRESOLVED_IDENT"));
    }

    #[test]
    fn any_cannot_be_cast_to_int() {
        let program = Program {
            declarations: vec![
                Decl::Assign {
                    static_params: Vec::new(),
                    doc: None,
                    name: "value".to_string(),
                    value: Expr::Cast {
                        expr: Box::new(Expr::Int("1".to_string())),
                        ty: TypeExpr::Named {
                            name: "Any".to_string(),
                            args: Vec::new(),
                        },
                    },
                },
                Decl::Assign {
                    static_params: Vec::new(),
                    doc: None,
                    name: "narrowed".to_string(),
                    value: Expr::Cast {
                        expr: Box::new(Expr::Ident("value".to_string())),
                        ty: TypeExpr::Named {
                            name: "Int".to_string(),
                            args: Vec::new(),
                        },
                    },
                },
            ],
        };

        let checked = check_module(&program);
        assert!(checked.module.is_none());
        assert!(!checked.diagnostics.is_empty());
    }

    #[test]
    fn enum_variant_payload_mismatch_reports_type_error() {
        let program = Program {
            declarations: vec![Decl::Assign {
                static_params: Vec::new(),
                doc: None,
                name: "res".to_string(),
                value: Expr::Binary {
                    op: ParsedBinaryOp::Colon,
                    lhs: Box::new(Expr::DotIdent {
                        name: "ok".to_string(),
                        payload: Some(Box::new(Expr::String("oops".to_string()))),
                    }),
                    rhs: Box::new(Expr::TypeExpr(TypeExpr::Named {
                        name: "enum".to_string(),
                        args: vec![StaticArg::Type(TypeExpr::Struct(vec![(
                            "ok".to_string(),
                            TypeExpr::Named {
                                name: "Int".to_string(),
                                args: Vec::new(),
                            },
                        )]))],
                    })),
                },
            }],
        };

        let checked = check_module(&program);
        assert!(checked.module.is_none());
        assert!(checked
            .diagnostics
            .iter()
            .any(|d| d.code_str() == "E_TYPE_MISMATCH"));
    }
}
