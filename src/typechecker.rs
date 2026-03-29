//! Static type checker for the Aura language.
//!
//! This module is the Phase 4 type-checking pass. It sits between the parser
//! and the compiler in the pipeline:
//!
//!   lex → parse → **typecheck** → compile → run
//!
//! # Current status
//!
//! Phase 4c — expression/statement checking pass.
//! Builds on 4b (type resolution, registration passes) and adds:
//! - `is_assignable` — full widening-only assignability rules
//! - `infer_expr` — bottom-up type inference for all `Expr` variants
//! - `check_block` / `check_stmt` — statement/block type checking
//! - `check_defn_body` — function body checking against declared return type
//! - Fourth pass in `check_program` that walks all function bodies

use std::collections::HashMap;

use crate::ast::{
    BinOp, Block, ClosureArm, DeclKind, DefBinding, Expr, Item, LabelledBlock, LocalBinding, Param,
    Pattern, Program, Stmt, TypeExpr, UnOp, UseDecl,
};
use crate::stl_registry::{stl_module_exports, stl_module_type};
use crate::token::Span;

mod assignability;
mod export_support;
mod infer;

// ─────────────────────────────────────────────────────────────────────────────
// Type representation
// ─────────────────────────────────────────────────────────────────────────────

/// The internal type representation used by the type checker.
///
/// This is distinct from [`TypeExpr`] (the AST surface syntax) — `Type` is the
/// resolved, canonical form that the checker works with after all aliases have
/// been expanded and names resolved.
#[derive(Debug, Clone, PartialEq)]
pub enum Type {
    // ── Primitives ──────────────────────────────────────────────────────────
    Int,
    Float,
    Bool,
    String,
    /// A Unicode character.
    Char,
    /// The unit value `null`.
    Null,
    /// Return type of functions that never produce a value (e.g. `println`).
    Void,

    // ── Structural types ────────────────────────────────────────────────────
    /// `List` — homogeneous sequence.
    List(Box<Type>),
    /// `Dict` — homogeneous key→value map.
    Dict(Box<Type>, Box<Type>),
    /// `Array[T, N]` — fixed-length homogeneous array (`N == 0` means length not fixed in the type).
    Array {
        elem: Box<Type>,
        len: usize,
    },
    /// `Set[T]` — homogeneous set.
    Set(Box<Type>),
    /// Anonymous or named tuple: `(T, U, ...)`.
    Tuple(Vec<Type>),
    /// Anonymous or named struct: `(field: T, ...)`.
    /// `name` is `Some` for named types defined via `def Foo = (...)`.
    Struct {
        name: Option<std::string::String>,
        fields: Vec<(std::string::String, Type)>,
    },

    // ── Sum types ───────────────────────────────────────────────────────────
    /// `union(T, U, ...)` — open union.
    Union(Vec<Type>),
    /// `enum(variant: T, ...)` — closed tagged union.
    Enum {
        name: Option<std::string::String>,
        variants: Vec<(std::string::String, Option<Type>)>,
    },

    // ── Behavioural types ───────────────────────────────────────────────────
    /// `interface(method: Func[...], ...)` — structural interface / trait.
    /// `name` is `Some` when defined via `def Foo = interface(...)`.
    Interface {
        name: Option<std::string::String>,
        methods: Vec<(std::string::String, Type)>,
    },

    /// Imported module namespace with known exports.
    Module {
        path: std::string::String,
        exports: HashMap<std::string::String, Type>,
    },

    // ── Function types ──────────────────────────────────────────────────────
    /// `Func[(Param, ...), Ret]`
    Func {
        params: Vec<Type>,
        ret: Box<Type>,
    },

    // ── Special types ───────────────────────────────────────────────────────
    /// An unresolved type parameter (e.g. `T` in `defn identity[T](x: T) -> T`).
    TypeVar(std::string::String),
    /// Top type — every value is assignable to `Any`.
    /// Equivalent to `interface()` (empty interface); provided as a convenience
    /// variant so that common code paths don't need to construct an empty
    /// `Interface { name: None, methods: vec![] }`.
    Any,
    /// Bottom type — `Never` is assignable to every other type.
    /// Used as the return type of functions that always diverge / panic.
    Never,
}

impl Type {
    /// Returns `true` if this type is `Any` (or the equivalent empty interface).
    pub fn is_any(&self) -> bool {
        match self {
            Type::Any => true,
            Type::Interface { methods, .. } => methods.is_empty(),
            _ => false,
        }
    }

    /// Returns a human-readable name for use in error messages.
    pub fn display_name(&self) -> std::string::String {
        match self {
            Type::Int => "Int".into(),
            Type::Float => "Float".into(),
            Type::Bool => "Bool".into(),
            Type::String => "String".into(),
            Type::Char => "Char".into(),
            Type::Null => "Null".into(),
            Type::Void => "Void".into(),
            Type::Any => "Any".into(),
            Type::Never => "Never".into(),
            Type::List(inner) => format!("List[{}]", inner.display_name()),
            Type::Dict(k, v) => format!("Dict[{}, {}]", k.display_name(), v.display_name()),
            Type::Array { elem, len } => {
                if *len == 0 {
                    format!("Array[{}]", elem.display_name())
                } else {
                    format!("Array[{}, {}]", elem.display_name(), len)
                }
            }
            Type::Set(inner) => format!("Set[{}]", inner.display_name()),
            Type::Tuple(elems) => {
                let parts: Vec<_> = elems.iter().map(|t| t.display_name()).collect();
                format!("({})", parts.join(", "))
            }
            Type::Struct { name: Some(n), .. } => n.clone(),
            Type::Struct { name: None, fields } => {
                let parts: Vec<_> = fields
                    .iter()
                    .map(|(k, v)| format!("{}: {}", k, v.display_name()))
                    .collect();
                format!("({})", parts.join(", "))
            }
            Type::Union(members) => {
                let parts: Vec<_> = members.iter().map(|t| t.display_name()).collect();
                format!("union({})", parts.join(", "))
            }
            Type::Enum { name: Some(n), .. } => n.clone(),
            Type::Enum {
                name: None,
                variants,
            } => {
                let parts: Vec<_> = variants
                    .iter()
                    .map(|(k, v)| {
                        if let Some(ty) = v {
                            format!("{}: {}", k, ty.display_name())
                        } else {
                            k.clone()
                        }
                    })
                    .collect();
                format!("enum({})", parts.join(", "))
            }
            Type::Interface { name: Some(n), .. } => n.clone(),
            Type::Interface {
                name: None,
                methods,
            } => {
                if methods.is_empty() {
                    "Any".into()
                } else {
                    let parts: Vec<_> = methods
                        .iter()
                        .map(|(k, v)| format!("{}: {}", k, v.display_name()))
                        .collect();
                    format!("interface({})", parts.join(", "))
                }
            }
            Type::Module { path, .. } => format!("Module[{path}]"),
            Type::Func { params, ret } => {
                let ps: Vec<_> = params.iter().map(|t| t.display_name()).collect();
                format!("Func[({}), {}]", ps.join(", "), ret.display_name())
            }
            Type::TypeVar(name) => name.clone(),
        }
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Error type
// ─────────────────────────────────────────────────────────────────────────────

/// A single type error produced by the type checker.
#[derive(Debug, Clone)]
pub struct TypeError {
    /// Human-readable error message.
    pub message: std::string::String,
    /// Source location of the offending expression or declaration.
    pub span: Span,
}

impl std::fmt::Display for TypeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "type error at {}: {}", self.span, self.message)
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Type environment
// ─────────────────────────────────────────────────────────────────────────────

/// A lexically-scoped environment that maps names to their resolved [`Type`]s.
///
/// Each scope layer is a `HashMap`; lookup walks from innermost to outermost.
/// The root scope contains the built-in types and STL bindings.
#[derive(Debug, Default)]
pub struct TypeEnv {
    /// Active type-parameter bindings for the current generic context.
    pub type_params: HashMap<std::string::String, Type>,
    /// Named type aliases defined via `def Name = TypeExpr`.
    pub type_aliases: HashMap<std::string::String, Type>,
    /// Value bindings: variable/constant names → their types.
    pub bindings: HashMap<std::string::String, Type>,
    /// Function signatures: function name → `Type::Func { .. }`.
    pub functions: HashMap<std::string::String, Type>,
    /// Optional reference to the enclosing scope (for nested scopes).
    pub parent: Option<Box<TypeEnv>>,
}

impl TypeEnv {
    /// Create a fresh root environment with no parent.
    pub fn new() -> Self {
        Self::default()
    }

    /// Create a child scope that delegates to `self` for unknown names.
    pub fn child(self) -> Self {
        TypeEnv {
            parent: Some(Box::new(self)),
            ..Default::default()
        }
    }

    /// Look up a value binding by name, walking the scope chain.
    pub fn lookup_binding(&self, name: &str) -> Option<&Type> {
        self.bindings
            .get(name)
            .or_else(|| self.parent.as_ref()?.lookup_binding(name))
    }

    /// Look up a function signature by name, walking the scope chain.
    pub fn lookup_function(&self, name: &str) -> Option<&Type> {
        self.functions
            .get(name)
            .or_else(|| self.parent.as_ref()?.lookup_function(name))
    }

    /// Look up a type alias by name, walking the scope chain.
    pub fn lookup_alias(&self, name: &str) -> Option<&Type> {
        self.type_aliases
            .get(name)
            .or_else(|| self.parent.as_ref()?.lookup_alias(name))
    }

    /// Look up a type parameter by name, walking the scope chain.
    pub fn lookup_type_param(&self, name: &str) -> Option<&Type> {
        self.type_params
            .get(name)
            .or_else(|| self.parent.as_ref()?.lookup_type_param(name))
    }

    /// Create a child scope by cloning the current environment.
    ///
    /// Unlike `child()` (which moves `self` and wraps it in `parent`), this
    /// method clones all maps into the child so that the checker can hold a
    /// shared reference to `self.env` while also building child scopes.
    ///
    /// Both parent and child start with the same bindings; new bindings added
    /// to the child are invisible to the parent and vice-versa.
    pub fn snapshot_child(&self) -> TypeEnv {
        TypeEnv {
            type_params: self.type_params.clone(),
            type_aliases: self.type_aliases.clone(),
            bindings: self.bindings.clone(),
            functions: self.functions.clone(),
            parent: None, // flat clone — no chain needed since we copied everything
        }
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Free helpers (Phase 4c)
// ─────────────────────────────────────────────────────────────────────────────

/// Unify a list of types into a single type.
///
/// - Empty list → `Type::Void`
/// - All identical → that type
/// - Mixed → `Type::Union(deduplicated members)`
fn unify_types(mut types: Vec<Type>) -> Type {
    types.dedup();
    match types.len() {
        0 => Type::Void,
        1 => types.into_iter().next().unwrap(),
        _ => Type::Union(types),
    }
}

/// Walk a [`Pattern`] and insert all bound names into `env` with the given `ty`.
///
/// For simple `Pattern::Bind` patterns this is just a single insert.
/// For destructuring patterns (Tuple, Struct) we recursively bind sub-names.
/// Unknown sub-structure gets `Type::Any`.
fn bind_pattern_names(pat: &Pattern, ty: Type, env: &mut TypeEnv) {
    match pat {
        Pattern::Bind(name, _) => {
            env.bindings.insert(name.clone(), ty);
        }
        Pattern::Wildcard(_) | Pattern::Rest { name: None, .. } => {
            // Nothing to bind
        }
        Pattern::Rest {
            name: Some(name), ..
        } => {
            env.bindings.insert(name.clone(), Type::List(Box::new(ty)));
        }
        Pattern::Tuple(pats, _) => {
            // Destructure tuple elements
            let elems = match &ty {
                Type::Tuple(elems) => elems.clone(),
                _ => vec![Type::Any; pats.len()],
            };
            for (sub_pat, sub_ty) in pats
                .iter()
                .zip(elems.into_iter().chain(std::iter::repeat(Type::Any)))
            {
                bind_pattern_names(sub_pat, sub_ty, env);
            }
        }
        Pattern::Struct { fields, .. } => {
            // Destructure struct fields
            let field_types: Vec<(std::string::String, Type)> = match &ty {
                Type::Struct {
                    fields: src_fields, ..
                } => src_fields.clone(),
                _ => vec![],
            };
            for spf in fields {
                let field_ty = field_types
                    .iter()
                    .find(|(n, _)| n == &spf.name)
                    .map_or(Type::Any, |(_, t)| t.clone());
                let binding_name = spf.binding.as_ref().unwrap_or(&spf.name).clone();
                env.bindings.insert(binding_name, field_ty);
            }
        }
        Pattern::Variant { inner, .. } => {
            if let Some(inner_pat) = inner {
                bind_pattern_names(inner_pat, Type::Any, env);
            }
        }
        Pattern::Constructor { inner, .. } => {
            bind_pattern_names(inner, Type::Any, env);
        }
        Pattern::TypeCheck { name, .. } => {
            // The name is bound to the checked type; we use Any since we'd need
            // to resolve the TypeExpr here — deferred to Phase 4d.
            env.bindings.insert(name.clone(), Type::Any);
        }
        Pattern::Literal(_) => {
            // Literal patterns don't introduce bindings
        }
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Type checker
// ─────────────────────────────────────────────────────────────────────────────

/// The type checker state.
///
/// The checker performs multiple passes over the [`Program`], accumulating all
/// [`TypeError`]s rather than stopping at the first one — consistent with how
/// the parser reports errors.
pub struct TypeChecker {
    env: TypeEnv,
    errors: Vec<TypeError>,
}

impl TypeChecker {
    /// Create a new type checker with prelude globals pre-registered.
    pub fn new() -> Self {
        let mut tc = TypeChecker {
            env: TypeEnv::new(),
            errors: Vec::new(),
        };
        // Register prelude globals: true, false, null.
        // These are plain identifiers (not keywords) that the VM always defines.
        tc.env.bindings.insert("true".into(), Type::Bool);
        tc.env.bindings.insert("false".into(), Type::Bool);
        tc.env.bindings.insert("null".into(), Type::Null);

        // Kernel globals available without imports.
        tc.env.bindings.insert(
            "os_args".into(),
            Type::Func {
                params: vec![],
                ret: Box::new(Type::List(Box::new(Type::String))),
            },
        );
        tc.env.bindings.insert(
            "os_env".into(),
            Type::Func {
                params: vec![Type::String],
                ret: Box::new(Type::Any),
            },
        );
        tc.env.bindings.insert(
            "os_cwd".into(),
            Type::Func {
                params: vec![],
                ret: Box::new(Type::String),
            },
        );
        tc.env.bindings.insert(
            "os_now".into(),
            Type::Func {
                params: vec![],
                ret: Box::new(Type::Int),
            },
        );
        tc.env.bindings.insert(
            "os_exists".into(),
            Type::Func {
                params: vec![Type::String],
                ret: Box::new(Type::Bool),
            },
        );
        tc.env.bindings.insert(
            "os_is_file".into(),
            Type::Func {
                params: vec![Type::String],
                ret: Box::new(Type::Bool),
            },
        );
        tc.env.bindings.insert(
            "os_is_dir".into(),
            Type::Func {
                params: vec![Type::String],
                ret: Box::new(Type::Bool),
            },
        );
        tc.env.bindings.insert(
            "os_ls".into(),
            Type::Func {
                params: vec![Type::String],
                ret: Box::new(Type::List(Box::new(Type::String))),
            },
        );
        tc
    }

    /// Record a type error at the given source location.
    fn error(&mut self, message: impl Into<std::string::String>, span: Span) {
        self.errors.push(TypeError {
            message: message.into(),
            span,
        });
    }

    // ─────────────────────────────────────────────────────────────────────────
    // Type expression resolution (Phase 4b)
    // ─────────────────────────────────────────────────────────────────────────

    /// Resolve a surface [`TypeExpr`] to its canonical [`Type`].
    ///
    /// Built-in type names are handled directly. User-defined names are looked
    /// up in the current environment's type-alias table and type-parameter
    /// bindings. Unknown names produce a `TypeError` and fall back to
    /// `Type::Any` so that checking can continue.
    fn resolve_type_expr(&mut self, ty: &TypeExpr) -> Type {
        match ty {
            TypeExpr::LitInt(n, span) => {
                self.error(
                    format!(
                        "integer literal `{}` is only valid as an array length in `Array[T, n]`",
                        n
                    ),
                    *span,
                );
                Type::Int
            }
            // ── Named types (built-ins + user aliases + type params) ──────────
            TypeExpr::Named { name, args, span } => {
                match name.as_str() {
                    // Primitives
                    "Int" => Type::Int,
                    "Float" => Type::Float,
                    "Bool" => Type::Bool,
                    "String" => Type::String,
                    "Char" => Type::Char,
                    "Null" => Type::Null,
                    "Void" => Type::Void,
                    "Any" => Type::Any,
                    "Never" => Type::Never,
                    // `Value` is the STL name for the top type → treat as Any
                    "Value" => Type::Any,

                    // Generic containers
                    "List" => {
                        if args.len() == 1 {
                            Type::List(Box::new(self.resolve_type_expr(&args[0])))
                        } else {
                            self.error(
                                format!("List expects 1 type argument, got {}", args.len()),
                                *span,
                            );
                            Type::List(Box::new(Type::Any))
                        }
                    }
                    "Dict" => {
                        if args.len() == 2 {
                            let k = self.resolve_type_expr(&args[0]);
                            let v = self.resolve_type_expr(&args[1]);
                            Type::Dict(Box::new(k), Box::new(v))
                        } else {
                            self.error(
                                format!("Dict expects 2 type arguments, got {}", args.len()),
                                *span,
                            );
                            Type::Dict(Box::new(Type::Any), Box::new(Type::Any))
                        }
                    }
                    "Array" => match args.as_slice() {
                        [elem, len_te] => {
                            let len = match len_te {
                                TypeExpr::LitInt(n, sp) => {
                                    if *n < 0 {
                                        self.error("array length must be non-negative", *sp);
                                        0usize
                                    } else {
                                        *n as usize
                                    }
                                }
                                _ => {
                                    self.error(
                                        "second argument to `Array` must be an integer literal (e.g. `Array[Int, 4]`)",
                                        len_te.span(),
                                    );
                                    0usize
                                }
                            };
                            Type::Array {
                                elem: Box::new(self.resolve_type_expr(elem)),
                                len,
                            }
                        }
                        [elem] => Type::Array {
                            elem: Box::new(self.resolve_type_expr(elem)),
                            len: 0,
                        },
                        _ => {
                            self.error(
                                format!(
                                    "`Array` expects 1 or 2 arguments (`Array[T]` or `Array[T, n]`), got {}",
                                    args.len()
                                ),
                                *span,
                            );
                            Type::Array {
                                elem: Box::new(Type::Any),
                                len: 0,
                            }
                        }
                    },
                    "Set" => {
                        if args.len() == 1 {
                            Type::Set(Box::new(self.resolve_type_expr(&args[0])))
                        } else {
                            self.error(
                                format!("Set expects 1 type argument, got {}", args.len()),
                                *span,
                            );
                            Type::Set(Box::new(Type::Any))
                        }
                    }
                    "Func" => {
                        // `Func[(P1, P2, ...), Ret]` — args are a tuple + return type,
                        // or just a return type when the param list is omitted.
                        match args.as_slice() {
                            [params_te, ret_te] => {
                                let params = match params_te {
                                    TypeExpr::Tuple(elems, _) => {
                                        elems.iter().map(|e| self.resolve_type_expr(e)).collect()
                                    }
                                    other => vec![self.resolve_type_expr(other)],
                                };
                                let ret = self.resolve_type_expr(ret_te);
                                Type::Func {
                                    params,
                                    ret: Box::new(ret),
                                }
                            }
                            [ret_te] => {
                                let ret = self.resolve_type_expr(ret_te);
                                Type::Func {
                                    params: vec![],
                                    ret: Box::new(ret),
                                }
                            }
                            _ => {
                                self.error(
                                    "Func expects 1 or 2 type arguments: Func[Params, Ret] or Func[Ret]",
                                    *span,
                                );
                                Type::Func {
                                    params: vec![],
                                    ret: Box::new(Type::Any),
                                }
                            }
                        }
                    }

                    // User-defined alias or type parameter
                    other => {
                        // Check type parameters first (innermost wins)
                        if let Some(t) = self.env.lookup_type_param(other).cloned() {
                            return t;
                        }
                        // Then check type aliases
                        if let Some(t) = self.env.lookup_alias(other).cloned() {
                            // If the alias has type params and the user supplied args,
                            // we just return the base alias type for now (no substitution yet).
                            return t;
                        }
                        self.error(format!("unknown type `{other}`"), *span);
                        Type::Any
                    }
                }
            }

            // ── Structural types ───────────────────────────────────────────────
            TypeExpr::Tuple(elems, _span) => {
                if elems.is_empty() {
                    // `()` in type position is the unit type, same as `Void`.
                    return Type::Void;
                }
                let resolved: Vec<Type> = elems.iter().map(|e| self.resolve_type_expr(e)).collect();
                Type::Tuple(resolved)
            }

            TypeExpr::Struct(fields, _span) => {
                let resolved: Vec<(std::string::String, Type)> = fields
                    .iter()
                    .map(|f| (f.name.clone(), self.resolve_type_expr(&f.ty)))
                    .collect();
                Type::Struct {
                    name: None,
                    fields: resolved,
                }
            }

            TypeExpr::Union(members, _span) => {
                let resolved: Vec<Type> =
                    members.iter().map(|m| self.resolve_type_expr(m)).collect();
                Type::Union(resolved)
            }

            TypeExpr::Enum(variants, _span) => {
                let resolved: Vec<(std::string::String, Option<Type>)> = variants
                    .iter()
                    .map(|v| {
                        let ty = v.ty.as_ref().map(|t| self.resolve_type_expr(t));
                        (v.name.clone(), ty)
                    })
                    .collect();
                Type::Enum {
                    name: None,
                    variants: resolved,
                }
            }

            TypeExpr::Interface(methods, _span) => {
                let resolved: Vec<(std::string::String, Type)> = methods
                    .iter()
                    .map(|m| (m.name.clone(), self.resolve_type_expr(&m.ty)))
                    .collect();
                Type::Interface {
                    name: None,
                    methods: resolved,
                }
            }
        }
    }

    // ─────────────────────────────────────────────────────────────────────────
    // Literal type inference (helpers for the third pass)
    // ─────────────────────────────────────────────────────────────────────────

    /// Infer the type of a simple literal expression.
    ///
    /// Only handles the "obvious" literal forms. All others return `Type::Any`.
    /// Full expression inference is Phase 4c work.
    fn infer_literal(&self, expr: &Expr) -> Type {
        match expr {
            Expr::Int(..) => Type::Int,
            Expr::Float(..) => Type::Float,
            Expr::Str(..) => Type::String,
            Expr::Char(..) => Type::Char,
            // Everything else is deferred to 4c
            _ => Type::Any,
        }
    }

    // ─────────────────────────────────────────────────────────────────────────
    // Registration passes (Phase 4b)
    // ─────────────────────────────────────────────────────────────────────────

    /// **First pass**: walk all top-level items and register type aliases from
    /// `def Name = TypeExpr` (`DefBinding::TypeAlias`) into `env.type_aliases`.
    ///
    /// This pass runs before function-signature registration so that type aliases
    /// defined in user code are available when resolving parameter/return types.
    fn register_type_aliases(&mut self, program: &Program) {
        for item in &program.items {
            match item {
                Item::Use(_) => {
                    // use declarations don't introduce type aliases — skip.
                }
                Item::Decl(decl) => {
                    let DeclKind::Def(def_decl) = &decl.kind else {
                        continue;
                    };

                    for binding in &def_decl.bindings {
                        let DefBinding::TypeAlias {
                            name,
                            type_params,
                            ty,
                            span,
                        } = binding
                        else {
                            continue;
                        };

                        // Install type parameters as TypeVar bindings for the duration
                        // of resolving this alias's RHS.
                        for tp in type_params {
                            self.env
                                .type_params
                                .insert(tp.name.clone(), Type::TypeVar(tp.name.clone()));
                        }

                        let resolved = self.resolve_type_expr(ty);

                        // Attach the alias name to the resolved type for named structs/enums.
                        let named = match resolved {
                            Type::Struct { fields, .. } => Type::Struct {
                                name: Some(name.clone()),
                                fields,
                            },
                            Type::Enum { variants, .. } => Type::Enum {
                                name: Some(name.clone()),
                                variants,
                            },
                            Type::Interface { methods, .. } => Type::Interface {
                                name: Some(name.clone()),
                                methods,
                            },
                            other => other,
                        };

                        // Remove the temporary type-param bindings.
                        for tp in type_params {
                            self.env.type_params.remove(&tp.name);
                        }

                        if self.env.type_aliases.contains_key(name) {
                            self.error(format!("type `{name}` is already defined"), *span);
                        } else {
                            self.env.type_aliases.insert(name.clone(), named);
                        }
                    }
                }
            }
        }
    }

    /// **Second pass**: walk all `defn` declarations, resolve their parameter
    /// and return-type annotations, and register them as `Type::Func` entries in
    /// `env.functions`.
    ///
    /// Hard error if any parameter of a `defn` lacks a type annotation, or if
    /// the return type is missing. (Closures are exempt — they are checked in 4c
    /// when context provides an expected type.)
    fn register_functions(&mut self, program: &Program) {
        for item in &program.items {
            match item {
                Item::Use(use_decl) => {
                    // Register imported names as Any so body-checking passes don't
                    // produce "unknown identifier" errors for imported bindings.
                    self.register_use_names(use_decl);
                }
                Item::Decl(decl) => {
                    let DeclKind::Def(def_decl) = &decl.kind else {
                        continue;
                    };

                    for binding in &def_decl.bindings {
                        let DefBinding::FuncDef {
                            receiver,
                            name,
                            type_params,
                            params,
                            return_type,
                            span,
                            ..
                        } = binding
                        else {
                            continue;
                        };

                        // Install generic type parameters for this function.
                        for tp in type_params {
                            self.env
                                .type_params
                                .insert(tp.name.clone(), Type::TypeVar(tp.name.clone()));
                        }

                        let param_types = self.resolve_params(params, *span);

                        let ret_type = match return_type {
                            Some(te) => self.resolve_type_expr(te),
                            None => {
                                self.error(
                                    format!(
                                        "function `{}` is missing a return type annotation",
                                        name
                                    ),
                                    *span,
                                );
                                Type::Any
                            }
                        };

                        // Remove generic type-param bindings.
                        for tp in type_params {
                            self.env.type_params.remove(&tp.name);
                        }

                        let func_type = Type::Func {
                            params: param_types,
                            ret: Box::new(ret_type),
                        };

                        // Use qualified name for methods (e.g. "Point.distanceTo").
                        let full_name = match receiver {
                            Some(recv) => format!("{}.{}", recv, name),
                            None => name.clone(),
                        };

                        self.env.functions.insert(full_name, func_type);
                    }
                }
            }
        }
    }

    /// Resolve a parameter list to a `Vec<Type>`, emitting errors for any
    /// unannotated parameters.
    fn resolve_params(&mut self, params: &[Param], fn_span: Span) -> Vec<Type> {
        params
            .iter()
            .map(|p| match &p.ty {
                Some(te) => self.resolve_type_expr(te),
                None => {
                    self.error(
                        format!("parameter `{}` is missing a type annotation", p.internal),
                        if p.span.start == 0 && p.span.end == 0 {
                            fn_span
                        } else {
                            p.span
                        },
                    );
                    Type::Any
                }
            })
            .collect()
    }

    /// Register imported names from a `use` declaration into the environment.
    fn register_use_names(&mut self, use_decl: &UseDecl) {
        let exports = match stl_module_exports(&use_decl.path) {
            Ok(Some(exports)) => exports,
            Ok(None) => {
                self.error(
                    format!(
                        "unknown module path `{}` in typechecker import pass",
                        use_decl.path
                    ),
                    use_decl.span,
                );
                return;
            }
            Err(err) => {
                self.error(
                    format!("failed to build STL type registry: {err}"),
                    use_decl.span,
                );
                return;
            }
        };

        match &use_decl.pattern {
            Pattern::Bind(local_name, _) => match stl_module_type(&use_decl.path) {
                Ok(Some(module_ty)) => {
                    self.env.bindings.insert(local_name.clone(), module_ty);
                }
                Ok(None) => {}
                Err(err) => {
                    self.error(
                        format!("failed to build STL module type `{}`: {err}", use_decl.path),
                        use_decl.span,
                    );
                }
            },
            Pattern::Struct { fields, .. } => {
                // Destructuring import: validate exports and bind local aliases.
                for field in fields {
                    let Some(ty) = exports.get(&field.name).cloned() else {
                        self.error(
                            format!("module `{}` has no export `{}`", use_decl.path, field.name),
                            field.span,
                        );
                        continue;
                    };
                    let local_name = field.binding.as_ref().unwrap_or(&field.name);
                    self.env.bindings.insert(local_name.clone(), ty);
                }
            }
            _ => {
                // Other patterns: not a supported use form, ignore.
            }
        }
    }

    /// **Third pass**: walk all `def` value bindings, infer their type from the
    /// initialiser expression (literal inference only at this stage), and
    /// register them in `env.bindings`.
    fn register_def_values(&mut self, program: &Program) {
        for item in &program.items {
            let Item::Decl(decl) = item else { continue };
            let DeclKind::Def(def_decl) = &decl.kind else {
                continue;
            };

            for binding in &def_decl.bindings {
                let DefBinding::Value { pattern, init, .. } = binding else {
                    continue;
                };

                let ty = self.infer_literal(init);

                // For simple `def name = expr` bindings, register the name.
                // Complex patterns are deferred to 4c.
                if let crate::ast::Pattern::Bind(name, _) = pattern {
                    self.env.bindings.insert(name.clone(), ty);
                }
            }
        }
    }

    // ─────────────────────────────────────────────────────────────────────────
    // Top-level entry
    // ─────────────────────────────────────────────────────────────────────────

    /// Type-check an entire [`Program`].
    ///
    /// Runs four passes:
    /// 1. Register type aliases.
    /// 2. Register function signatures (with annotation enforcement).
    /// 3. Register `def` value bindings (literal inference).
    /// 4. Check all function bodies (Phase 4c).
    fn check_program(&mut self, program: &Program) {
        self.register_type_aliases(program);
        self.register_functions(program);
        self.register_def_values(program);
        self.check_all_bodies(program);
    }
}

impl Default for TypeChecker {
    fn default() -> Self {
        Self::new()
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Assignability (Phase 4c)
// ─────────────────────────────────────────────────────────────────────────────

impl TypeChecker {}

// expression inference moved to `infer` module

// ─────────────────────────────────────────────────────────────────────────────
// Pattern type checking (Phase 4d)
// ─────────────────────────────────────────────────────────────────────────────

impl TypeChecker {
    /// Check `pat` against `subject_ty`, populate `env` with typed bindings,
    /// and emit errors for type mismatches.
    ///
    /// Returns the *narrowed* type that the pattern matches (useful for binding
    /// names to more-specific types in the arm body).
    fn check_pattern(&mut self, pat: &Pattern, subject_ty: &Type, env: &mut TypeEnv) -> Type {
        match pat {
            // ── Wildcard: no binding, no check ───────────────────────────────
            Pattern::Wildcard(_) => subject_ty.clone(),

            // ── Bind: bind name to subject type ──────────────────────────────
            Pattern::Bind(name, _) => {
                env.bindings.insert(name.clone(), subject_ty.clone());
                subject_ty.clone()
            }

            // ── Literal: verify literal type is compatible ────────────────────
            Pattern::Literal(lit_expr) => {
                let lit_ty = self.infer_expr(lit_expr, env);
                if !self.is_assignable(&lit_ty, subject_ty) && !subject_ty.is_any() {
                    self.error(
                        format!(
                            "literal pattern type {} is not compatible with subject type {}",
                            lit_ty.display_name(),
                            subject_ty.display_name()
                        ),
                        lit_expr.span(),
                    );
                }
                lit_ty
            }

            // ── TypeCheck: bind name to the checked (narrowed) type ───────────
            Pattern::TypeCheck { name, ty, span } => {
                let checked_ty = self.resolve_type_expr(ty);
                // The narrowing is always valid (it's a runtime check); no static
                // error here.  Just bind the name to the narrower type.
                env.bindings.insert(name.clone(), checked_ty.clone());
                let _ = span;
                checked_ty
            }

            // ── Tuple: check arity and recurse into elements ──────────────────
            Pattern::Tuple(pats, span) => {
                let elems: Vec<Type> = match subject_ty {
                    Type::Tuple(elems) => {
                        if elems.len() != pats.len() {
                            self.error(
                                format!(
                                    "tuple pattern has {} elements but subject has {}",
                                    pats.len(),
                                    elems.len()
                                ),
                                *span,
                            );
                        }
                        elems.clone()
                    }
                    // Any or unknown: let sub-patterns bind as Any
                    _ if subject_ty.is_any() => vec![Type::Any; pats.len()],
                    other => {
                        self.error(
                            format!(
                                "tuple pattern cannot match subject of type {}",
                                other.display_name()
                            ),
                            *span,
                        );
                        vec![Type::Any; pats.len()]
                    }
                };
                let resolved_elems: Vec<Type> = pats
                    .iter()
                    .zip(elems.into_iter().chain(std::iter::repeat(Type::Any)))
                    .map(|(sub_pat, elem_ty)| self.check_pattern(sub_pat, &elem_ty, env))
                    .collect();
                Type::Tuple(resolved_elems)
            }

            // ── Struct: check field names exist and recurse ───────────────────
            Pattern::Struct { fields, span } => {
                let field_types: Vec<(String, Type)> = match subject_ty {
                    Type::Struct {
                        fields: src_fields, ..
                    } => src_fields.clone(),
                    _ if subject_ty.is_any() => vec![],
                    other => {
                        self.error(
                            format!(
                                "struct pattern cannot match subject of type {}",
                                other.display_name()
                            ),
                            *span,
                        );
                        vec![]
                    }
                };
                for spf in fields {
                    let field_ty = field_types
                        .iter()
                        .find(|(n, _)| n == &spf.name)
                        .map_or_else(
                            || {
                                if !subject_ty.is_any() {
                                    self.error(
                                        format!(
                                            "struct pattern references unknown field `{}`",
                                            spf.name
                                        ),
                                        spf.span,
                                    );
                                }
                                Type::Any
                            },
                            |(_, t)| t.clone(),
                        );
                    let binding_name = spf.binding.as_ref().unwrap_or(&spf.name).clone();
                    env.bindings.insert(binding_name, field_ty);
                }
                subject_ty.clone()
            }

            // ── Variant: check against Enum type, bind inner ──────────────────
            Pattern::Variant { name, inner, span } => {
                let inner_ty = match subject_ty {
                    Type::Enum { variants, .. } => variants
                        .iter()
                        .find(|(vname, _)| vname == name)
                        .map_or_else(
                            || {
                                self.error(
                                    format!(
                                        "variant `.{}` does not exist in enum type {}",
                                        name,
                                        subject_ty.display_name()
                                    ),
                                    *span,
                                );
                                Type::Any
                            },
                            |(_, payload)| payload.clone().unwrap_or(Type::Void),
                        ),
                    _ if subject_ty.is_any() => Type::Any,
                    other => {
                        self.error(
                            format!(
                                "variant pattern `.{}` cannot match subject of type {}",
                                name,
                                other.display_name()
                            ),
                            *span,
                        );
                        Type::Any
                    }
                };
                if let Some(inner_pat) = inner {
                    self.check_pattern(inner_pat, &inner_ty, env);
                }
                inner_ty
            }

            // ── Constructor: look up named type, bind inner ───────────────────
            Pattern::Constructor {
                type_name,
                inner,
                span,
            } => {
                // Look up the registered type alias for `type_name`
                let alias_ty = self.env.lookup_alias(type_name).cloned();
                match alias_ty {
                    Some(Type::Struct { fields, .. }) => {
                        // Named struct — inner pattern matches the struct itself
                        let reconstructed = Type::Struct {
                            name: Some(type_name.clone()),
                            fields,
                        };
                        self.check_pattern(inner, &reconstructed, env);
                        reconstructed
                    }
                    Some(Type::Tuple(elems)) => {
                        let reconstructed = Type::Tuple(elems);
                        self.check_pattern(inner, &reconstructed, env);
                        reconstructed
                    }
                    Some(other) => {
                        self.check_pattern(inner, &other, env);
                        other
                    }
                    None => {
                        // Unknown constructor type — bind inner as Any
                        let _ = span;
                        self.check_pattern(inner, &Type::Any, env);
                        Type::Any
                    }
                }
            }

            // ── Rest: bind name to List<subject> ─────────────────────────────
            Pattern::Rest { name, .. } => {
                let list_ty = Type::List(Box::new(subject_ty.clone()));
                if let Some(n) = name {
                    env.bindings.insert(n.clone(), list_ty.clone());
                }
                list_ty
            }
        }
    }

    /// Check the arms of a closure for basic exhaustiveness when the subject
    /// type is known.
    ///
    /// For `Bool` subjects: both `true` and `false` must be covered (by literal
    /// or wildcard/bind).
    /// For `Enum` subjects: every variant must be covered (by a `.variant`
    /// pattern, wildcard, or bind).
    /// All other types: exhaustiveness is not checked (deferred / too complex).
    fn check_exhaustiveness(&mut self, arms: &[ClosureArm], subject_ty: &Type, span: Span) {
        // A wildcard or bind in any arm position 0 covers everything.
        let has_catch_all = arms.iter().any(|arm| {
            arm.guard.is_none()
                && arm
                    .patterns
                    .first()
                    .is_some_and(|p| matches!(p, Pattern::Wildcard(_) | Pattern::Bind(_, _)))
        });
        if has_catch_all {
            return;
        }

        match subject_ty {
            Type::Bool => {
                let has_true = arms.iter().any(|arm| {
                    arm.patterns.first().is_some_and(
                        |p| matches!(p, Pattern::Literal(Expr::Ident(s, _)) if s == "true"),
                    )
                });
                let has_false = arms.iter().any(|arm| {
                    arm.patterns.first().is_some_and(
                        |p| matches!(p, Pattern::Literal(Expr::Ident(s, _)) if s == "false"),
                    )
                });
                if !has_true {
                    self.error(
                        "non-exhaustive pattern match: missing `true` case for Bool",
                        span,
                    );
                }
                if !has_false {
                    self.error(
                        "non-exhaustive pattern match: missing `false` case for Bool",
                        span,
                    );
                }
            }
            Type::Enum { variants, .. } => {
                for (vname, _) in variants {
                    let covered = arms.iter().any(|arm| {
                        arm.patterns.first().is_some_and(|p| match p {
                            Pattern::Variant { name, .. } => name == vname,
                            _ => false,
                        })
                    });
                    if !covered {
                        self.error(
                            format!(
                                "non-exhaustive pattern match: variant `.{}` is not covered",
                                vname
                            ),
                            span,
                        );
                    }
                }
            }
            // Union: check each member type
            Type::Union(members) => {
                for member in members {
                    self.check_exhaustiveness(arms, member, span);
                }
            }
            // All other types: skip exhaustiveness check
            _ => {}
        }
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Block and statement checking (Phase 4c)
// ─────────────────────────────────────────────────────────────────────────────

impl TypeChecker {
    /// Check all statements in `block` and return the type of the final
    /// (tail) expression, or `Type::Void` if there is none.
    ///
    /// `ret_ty` is the expected return type of the enclosing function, forwarded
    /// to `check_stmt` for `return` statement validation.
    fn check_block(&mut self, block: &Block, mut env: TypeEnv, ret_ty: Option<&Type>) -> Type {
        for stmt in &block.stmts {
            self.check_stmt(stmt, &mut env, ret_ty);
        }
        match &block.tail {
            Some(tail) => self.infer_expr(tail, &env),
            None => Type::Void,
        }
    }

    /// Check a labelled block (used by loops and trailing closure args).
    fn check_labelled_block(
        &mut self,
        lb: &LabelledBlock,
        env: &TypeEnv,
        ret_ty: Option<&Type>,
    ) -> Type {
        let child = env.snapshot_child();
        self.check_block(&lb.block, child, ret_ty)
    }

    /// Check a single statement, mutating `env` with any new bindings.
    ///
    /// `ret_ty` is forwarded for `return` validation.
    fn check_stmt(&mut self, stmt: &Stmt, env: &mut TypeEnv, ret_ty: Option<&Type>) {
        match stmt {
            Stmt::Let(let_stmt) => {
                for binding in &let_stmt.bindings {
                    self.check_local_binding(binding, env, ret_ty);
                }
            }

            Stmt::Const(const_stmt) => {
                for binding in &const_stmt.bindings {
                    self.check_local_binding(binding, env, ret_ty);
                }
            }

            Stmt::Def(def_stmt) => {
                // Local `def` — handle each binding.
                for binding in &def_stmt.bindings {
                    match binding {
                        DefBinding::Value { pattern, init, .. } => {
                            let init_ty = self.infer_expr(init, env);
                            bind_pattern_names(pattern, init_ty, env);
                        }
                        DefBinding::FuncDef {
                            name,
                            params,
                            body,
                            return_type,
                            ..
                        } => {
                            // Register the local function name as Func type.
                            let param_types: Vec<Type> = params
                                .iter()
                                .map(|p| {
                                    p.ty.as_ref()
                                        .map(|te| self.resolve_type_expr(te))
                                        .unwrap_or(Type::Any)
                                })
                                .collect();
                            let ret_type = return_type
                                .as_ref()
                                .map(|te| self.resolve_type_expr(te))
                                .unwrap_or(Type::Any);
                            let func_type = Type::Func {
                                params: param_types,
                                ret: Box::new(ret_type),
                            };
                            env.bindings.insert(name.clone(), func_type);
                            // Also check the body (best-effort).
                            let child = env.snapshot_child();
                            let _ = self.check_block(body, child, None);
                        }
                        DefBinding::TypeAlias { name, .. } => {
                            // Local type aliases are not registered in the binding env.
                            let _ = name;
                        }
                    }
                }
            }

            Stmt::Return(ret_stmt) => {
                let value_ty = match &ret_stmt.value {
                    Some(v) => self.infer_expr(v, env),
                    None => Type::Void,
                };
                if let Some(expected) = ret_ty {
                    if !self.is_assignable(&value_ty, expected) {
                        self.error(
                            format!(
                                "return type mismatch: expected {}, got {}",
                                expected.display_name(),
                                value_ty.display_name()
                            ),
                            ret_stmt.span,
                        );
                    }
                }
            }

            Stmt::Break(brk) => {
                if let Some(v) = &brk.value {
                    self.infer_expr(v, env);
                }
            }

            Stmt::Continue(_) => {}

            Stmt::Expr(expr_stmt) => {
                self.infer_expr(&expr_stmt.expr, env);
            }
        }
    }

    /// Check a single `let`/`const` binding, register the bound name(s) in `env`.
    fn check_local_binding(
        &mut self,
        binding: &LocalBinding,
        env: &mut TypeEnv,
        ret_ty: Option<&Type>,
    ) {
        let init_ty = self.infer_expr(&binding.init, env);

        // Check annotation if present
        let declared_ty = binding.ty.as_ref().map(|te| self.resolve_type_expr(te));

        let effective_ty = if let Some(ref decl) = declared_ty {
            if !self.is_assignable(&init_ty, decl) {
                self.error(
                    format!(
                        "type annotation mismatch: expected {}, got {}",
                        decl.display_name(),
                        init_ty.display_name()
                    ),
                    binding.span,
                );
            }
            decl.clone()
        } else {
            init_ty
        };

        // Register name(s) into env
        bind_pattern_names(&binding.pattern, effective_ty, env);

        // Check any nested stmts referenced via the init (already handled in
        // infer_expr; nothing extra needed here).
        let _ = ret_ty; // forwarded but not used at this level
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Function body checking (Phase 4c)
// ─────────────────────────────────────────────────────────────────────────────

impl TypeChecker {
    /// Check all function bodies in the program (fourth pass).
    fn check_all_bodies(&mut self, program: &Program) {
        // Collect FuncDef bindings to avoid borrow conflicts — we need &mut self inside
        // the loop but program is already borrowed.
        let func_defs: Vec<_> = program
            .items
            .iter()
            .filter_map(|item| {
                if let Item::Decl(decl) = item {
                    if let DeclKind::Def(def_decl) = &decl.kind {
                        let funcs: Vec<_> = def_decl
                            .bindings
                            .iter()
                            .filter_map(|b| {
                                if let DefBinding::FuncDef {
                                    receiver,
                                    name,
                                    type_params,
                                    params,
                                    return_type,
                                    body,
                                    span,
                                } = b
                                {
                                    // Convert to legacy DefnDecl for reuse of check_defn_body.
                                    Some(crate::ast::DefnDecl {
                                        receiver: receiver.clone(),
                                        name: name.clone(),
                                        type_params: type_params.clone(),
                                        params: params.clone(),
                                        return_type: return_type.clone(),
                                        body: body.clone(),
                                        span: *span,
                                    })
                                } else {
                                    None
                                }
                            })
                            .collect();
                        return Some(funcs);
                    }
                }
                None
            })
            .flatten()
            .collect();

        for defn in func_defs {
            self.check_defn_body(&defn);
        }
    }

    /// Type-check the body of a single `defn` declaration.
    ///
    /// Creates a child environment with:
    /// - type parameters bound as `TypeVar`
    /// - parameters bound to their resolved types
    ///
    /// Then checks the body block and validates the tail type against the
    /// declared return type.
    fn check_defn_body(&mut self, defn: &crate::ast::DefnDecl) {
        // Build a child env with type params and params
        let mut child = self.env.snapshot_child();

        // Bind type parameters
        for tp in &defn.type_params {
            child
                .type_params
                .insert(tp.name.clone(), Type::TypeVar(tp.name.clone()));
        }

        // Bind parameters with their resolved types
        for param in &defn.params {
            let ty = match &param.ty {
                Some(te) => self.resolve_type_expr(te),
                None => Type::Any, // already errored in register_functions
            };
            child.bindings.insert(param.internal.clone(), ty);
        }

        // Resolve declared return type
        let ret_ty = defn
            .return_type
            .as_ref()
            .map(|te| self.resolve_type_expr(te));

        let actual_ty = self.check_block(&defn.body, child, ret_ty.as_ref());

        // If the body has a tail expression, check it against the return type
        if defn.body.tail.is_some() {
            if let Some(ref expected) = ret_ty {
                if !self.is_assignable(&actual_ty, expected) {
                    self.error(
                        format!(
                            "function `{}` returns {}, but declared return type is {}",
                            defn.name,
                            actual_ty.display_name(),
                            expected.display_name()
                        ),
                        defn.body.span,
                    );
                }
            }
        }
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Public API
// ─────────────────────────────────────────────────────────────────────────────

/// Run the type checker over a parsed [`Program`].
///
/// Returns `Ok(())` if no type errors are found, or `Err(errors)` with all
/// collected errors if any were detected.
///
/// # Phase 4b status
///
/// Runs type-alias registration, function-signature registration (with hard
/// errors for missing annotations), and `def` value-binding registration.
/// Expression / statement checking is deferred to Phase 4c.
pub fn check(program: &Program) -> Result<(), Vec<TypeError>> {
    let mut checker = TypeChecker::new();
    checker.check_program(program);
    if checker.errors.is_empty() {
        Ok(())
    } else {
        Err(checker.errors)
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Tests
// ─────────────────────────────────────────────────────────────────────────────

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::Program;
    use crate::lexer::lex;
    use crate::parser::parse_tokens;
    use crate::stl_registry::stl_registry;

    fn program_from_source(src: &str) -> Program {
        let (tokens, lex_errs) = lex(src);
        assert!(lex_errs.is_empty(), "lex errors: {lex_errs:?}");
        let (program, parse_errs) = parse_tokens(tokens);
        assert!(parse_errs.is_empty(), "parse errors: {parse_errs:?}");
        program
    }

    fn check_src(src: &str) -> Result<(), Vec<TypeError>> {
        let program = program_from_source(src);
        check(&program)
    }

    /// Run the checker and return the `TypeChecker` so tests can inspect `env`.
    fn check_src_env(src: &str) -> TypeChecker {
        let program = program_from_source(src);
        let mut checker = TypeChecker::new();
        checker.check_program(&program);
        checker
    }

    // ── Basic sanity ──────────────────────────────────────────────────────────

    #[test]
    fn test_typecheck_empty_program() {
        assert!(check_src("").is_ok());
    }

    #[test]
    fn test_typecheck_simple_def() {
        assert!(check_src("def x = 42;").is_ok());
    }

    #[test]
    fn test_typecheck_defn_with_annotations() {
        assert!(check_src("def add(a: Int, b: Int) -> Int { a + b }").is_ok());
    }

    /// Phase 4b: unannotated `defn` params are now hard errors.
    #[test]
    fn test_typecheck_defn_missing_param_annotation() {
        let result = check_src("def foo(x) -> Int { x }");
        assert!(result.is_err(), "expected error for unannotated param");
        let errs = result.unwrap_err();
        assert!(
            errs.iter().any(|e| e.message.contains("parameter `x`")),
            "expected param annotation error, got: {errs:?}"
        );
    }

    /// Phase 4b: missing return type annotation is a hard error.
    #[test]
    fn test_typecheck_defn_missing_return_type() {
        let result = check_src("def foo(x: Int) { x }");
        assert!(result.is_err(), "expected error for missing return type");
        let errs = result.unwrap_err();
        assert!(
            errs.iter()
                .any(|e| e.message.contains("return type annotation")),
            "expected return type error, got: {errs:?}"
        );
    }

    // ── resolve_type_expr ─────────────────────────────────────────────────────

    #[test]
    fn test_resolve_builtin_types() {
        let mut tc = TypeChecker::new();
        let make_named = |name: &str| TypeExpr::Named {
            name: name.into(),
            args: vec![],
            span: Span::dummy(),
        };
        assert_eq!(tc.resolve_type_expr(&make_named("Int")), Type::Int);
        assert_eq!(tc.resolve_type_expr(&make_named("Float")), Type::Float);
        assert_eq!(tc.resolve_type_expr(&make_named("Bool")), Type::Bool);
        assert_eq!(tc.resolve_type_expr(&make_named("String")), Type::String);
        assert_eq!(tc.resolve_type_expr(&make_named("Null")), Type::Null);
        assert_eq!(tc.resolve_type_expr(&make_named("Void")), Type::Void);
        assert_eq!(tc.resolve_type_expr(&make_named("Any")), Type::Any);
        assert_eq!(tc.resolve_type_expr(&make_named("Never")), Type::Never);
        assert_eq!(tc.resolve_type_expr(&make_named("Value")), Type::Any);
    }

    #[test]
    fn test_resolve_list_type() {
        let mut tc = TypeChecker::new();
        let te = TypeExpr::Named {
            name: "List".into(),
            args: vec![TypeExpr::Named {
                name: "Int".into(),
                args: vec![],
                span: Span::dummy(),
            }],
            span: Span::dummy(),
        };
        assert_eq!(tc.resolve_type_expr(&te), Type::List(Box::new(Type::Int)));
    }

    #[test]
    fn test_resolve_dict_type() {
        let mut tc = TypeChecker::new();
        let te = TypeExpr::Named {
            name: "Dict".into(),
            args: vec![
                TypeExpr::Named {
                    name: "String".into(),
                    args: vec![],
                    span: Span::dummy(),
                },
                TypeExpr::Named {
                    name: "Int".into(),
                    args: vec![],
                    span: Span::dummy(),
                },
            ],
            span: Span::dummy(),
        };
        assert_eq!(
            tc.resolve_type_expr(&te),
            Type::Dict(Box::new(Type::String), Box::new(Type::Int))
        );
    }

    #[test]
    fn test_resolve_func_type() {
        let mut tc = TypeChecker::new();
        // Func[(Int, Bool), String]
        let te = TypeExpr::Named {
            name: "Func".into(),
            args: vec![
                TypeExpr::Tuple(
                    vec![
                        TypeExpr::Named {
                            name: "Int".into(),
                            args: vec![],
                            span: Span::dummy(),
                        },
                        TypeExpr::Named {
                            name: "Bool".into(),
                            args: vec![],
                            span: Span::dummy(),
                        },
                    ],
                    Span::dummy(),
                ),
                TypeExpr::Named {
                    name: "String".into(),
                    args: vec![],
                    span: Span::dummy(),
                },
            ],
            span: Span::dummy(),
        };
        assert_eq!(
            tc.resolve_type_expr(&te),
            Type::Func {
                params: vec![Type::Int, Type::Bool],
                ret: Box::new(Type::String),
            }
        );
    }

    #[test]
    fn test_resolve_unknown_type_emits_error() {
        let mut tc = TypeChecker::new();
        let te = TypeExpr::Named {
            name: "Bogus".into(),
            args: vec![],
            span: Span::dummy(),
        };
        let result = tc.resolve_type_expr(&te);
        assert_eq!(result, Type::Any, "unknown type should fall back to Any");
        assert!(!tc.errors.is_empty(), "should have recorded an error");
        assert!(tc.errors[0].message.contains("unknown type"));
    }

    // ── Type-alias registration ───────────────────────────────────────────────

    #[test]
    fn test_register_struct_type_alias() {
        // `def Point = (x: Int, y: Int)` — a named-field struct; the parser
        // recognises it as DefBinding::TypeAlias via the `( ident :` lookahead rule.
        let tc = check_src_env("def Point = (x: Int, y: Int);");
        let alias = tc.env.lookup_alias("Point");
        assert!(alias.is_some(), "Point should be registered");
        assert!(
            matches!(alias.unwrap(), Type::Struct { name: Some(n), .. } if n == "Point"),
            "alias should be a named struct, got: {alias:?}"
        );
    }

    #[test]
    fn test_register_enum_type_alias() {
        // `def Color = enum(red, green, blue)` — parsed as DefBinding::TypeAlias
        // because the RHS starts with the keyword-like ident `enum`.
        let tc = check_src_env("def Color = enum(red, green, blue);");
        let alias = tc.env.lookup_alias("Color");
        assert!(alias.is_some(), "Color should be registered");
        assert!(
            matches!(alias.unwrap(), Type::Enum { name: Some(n), .. } if n == "Color"),
            "alias should be a named enum, got: {alias:?}"
        );
    }

    #[test]
    fn test_register_generic_type_alias() {
        // `def[T] Box = (value: T)` — type params present → parsed as TypeAlias.
        let tc = check_src_env("def[T] Box = (value: T);");
        let alias = tc.env.lookup_alias("Box");
        assert!(
            alias.is_some(),
            "Box should be registered after type alias pass"
        );
    }

    #[test]
    fn test_duplicate_struct_type_alias_error() {
        // Both definitions are struct type aliases (parsed via the `( ident :` rule)
        // so the duplicate check fires on the second one.
        let result = check_src("def Foo = (x: Int); def Foo = (y: Bool);");
        assert!(result.is_err(), "duplicate type alias should be an error");
    }

    // ── Function registration ─────────────────────────────────────────────────

    #[test]
    fn test_register_function_signature() {
        let tc = check_src_env("def add(a: Int, b: Int) -> Int { a + b }");
        let sig = tc.env.lookup_function("add");
        assert_eq!(
            sig,
            Some(&Type::Func {
                params: vec![Type::Int, Type::Int],
                ret: Box::new(Type::Int),
            })
        );
    }

    #[test]
    fn test_register_method_signature() {
        let tc = check_src_env("def String.len(self: String) -> Int { builtin str_len }");
        assert!(
            tc.env.lookup_function("String.len").is_some(),
            "method should be registered as 'String.len'"
        );
    }

    #[test]
    fn test_use_destructure_unknown_export_errors() {
        let result = check_src("use (missing) = \"@stl/io\";");
        assert!(result.is_err(), "missing export should be a type error");
    }

    #[test]
    fn test_use_unknown_module_path_errors() {
        let result = check_src("use io = \"@stl/not-real\";");
        assert!(
            result.is_err(),
            "unknown module path should be a type error"
        );
    }

    #[test]
    fn test_use_namespace_binds_module_type() {
        let tc = check_src_env("use io = \"@stl/io\";");
        let Some(ty) = tc.env.lookup_binding("io") else {
            panic!("expected `io` binding");
        };
        assert!(matches!(ty, Type::Module { path, .. } if path == "@stl/io"));
    }

    // ── Def value registration ────────────────────────────────────────────────

    #[test]
    fn test_register_int_def() {
        let tc = check_src_env("def answer = 42;");
        assert_eq!(tc.env.lookup_binding("answer"), Some(&Type::Int));
    }

    #[test]
    fn test_register_string_def() {
        let tc = check_src_env("def greeting = \"hello\";");
        assert_eq!(tc.env.lookup_binding("greeting"), Some(&Type::String));
    }

    #[test]
    fn test_register_bool_def() {
        // `true` is a prelude ident (not a keyword), so `infer_literal` returns Any
        // for it (same as any other non-literal expression).  The binding is still
        // registered; its type resolves fully during Phase 4c with the prelude loaded.
        let tc = check_src_env("def flag = true;");
        assert_eq!(tc.env.lookup_binding("flag"), Some(&Type::Any));
    }

    // ── Type::display_name and TypeEnv (carried over from 4a) ────────────────

    #[test]
    fn test_type_display_names() {
        assert_eq!(Type::Int.display_name(), "Int");
        assert_eq!(Type::Float.display_name(), "Float");
        assert_eq!(Type::Bool.display_name(), "Bool");
        assert_eq!(Type::String.display_name(), "String");
        assert_eq!(Type::Any.display_name(), "Any");
        assert_eq!(Type::Never.display_name(), "Never");
        assert_eq!(Type::List(Box::new(Type::Int)).display_name(), "List[Int]");
        assert_eq!(
            Type::Func {
                params: vec![Type::Int, Type::Int],
                ret: Box::new(Type::Bool)
            }
            .display_name(),
            "Func[(Int, Int), Bool]"
        );
    }

    #[test]
    fn test_type_env_lookup() {
        let mut env = TypeEnv::new();
        env.bindings.insert("x".into(), Type::Int);
        assert_eq!(env.lookup_binding("x"), Some(&Type::Int));
        assert_eq!(env.lookup_binding("y"), None);

        // Child scope can see parent bindings
        let child = env.child();
        assert_eq!(child.lookup_binding("x"), Some(&Type::Int));
    }

    #[test]
    fn test_type_env_shadowing() {
        let mut env = TypeEnv::new();
        env.bindings.insert("x".into(), Type::Int);
        let mut child = env.child();
        child.bindings.insert("x".into(), Type::Bool);
        // Inner binding shadows outer
        assert_eq!(child.lookup_binding("x"), Some(&Type::Bool));
    }

    // ── is_assignable ─────────────────────────────────────────────────────────

    #[test]
    fn test_is_assignable_identity() {
        let tc = TypeChecker::new();
        assert!(tc.is_assignable(&Type::Int, &Type::Int));
        assert!(tc.is_assignable(&Type::String, &Type::String));
        assert!(tc.is_assignable(&Type::Bool, &Type::Bool));
    }

    #[test]
    fn test_is_assignable_never_to_anything() {
        let tc = TypeChecker::new();
        assert!(tc.is_assignable(&Type::Never, &Type::Int));
        assert!(tc.is_assignable(&Type::Never, &Type::String));
        assert!(tc.is_assignable(&Type::Never, &Type::Any));
    }

    #[test]
    fn test_is_assignable_anything_to_any() {
        let tc = TypeChecker::new();
        assert!(tc.is_assignable(&Type::Int, &Type::Any));
        assert!(tc.is_assignable(&Type::String, &Type::Any));
        assert!(tc.is_assignable(&Type::Bool, &Type::Any));
        assert!(tc.is_assignable(
            &Type::Struct {
                name: None,
                fields: vec![]
            },
            &Type::Any
        ));
    }

    #[test]
    fn test_is_assignable_type_to_union_widening() {
        let tc = TypeChecker::new();
        let union_ty = Type::Union(vec![Type::Int, Type::String]);
        assert!(tc.is_assignable(&Type::Int, &union_ty));
        assert!(tc.is_assignable(&Type::String, &union_ty));
        assert!(!tc.is_assignable(&Type::Bool, &union_ty));
    }

    #[test]
    fn test_is_assignable_union_to_union() {
        let tc = TypeChecker::new();
        // {Int} → {Int, String}: every member of from is in to
        let from = Type::Union(vec![Type::Int]);
        let to = Type::Union(vec![Type::Int, Type::String]);
        assert!(tc.is_assignable(&from, &to));

        // {Int, Bool} → {Int, String}: Bool not in to
        let from2 = Type::Union(vec![Type::Int, Type::Bool]);
        assert!(!tc.is_assignable(&from2, &to));
    }

    #[test]
    fn test_is_assignable_struct_same_name() {
        let tc = TypeChecker::new();
        let s = Type::Struct {
            name: Some("Point".into()),
            fields: vec![("x".into(), Type::Int), ("y".into(), Type::Int)],
        };
        assert!(tc.is_assignable(&s, &s));
    }

    #[test]
    fn test_is_assignable_struct_different_names() {
        let tc = TypeChecker::new();
        let a = Type::Struct {
            name: Some("A".into()),
            fields: vec![("x".into(), Type::Int)],
        };
        let b = Type::Struct {
            name: Some("B".into()),
            fields: vec![("x".into(), Type::Int)],
        };
        assert!(!tc.is_assignable(&a, &b));
    }

    #[test]
    fn test_is_assignable_anonymous_structs() {
        let tc = TypeChecker::new();
        // Anonymous structs with same fields are compatible
        let a = Type::Struct {
            name: None,
            fields: vec![("x".into(), Type::Int), ("y".into(), Type::Int)],
        };
        let b = Type::Struct {
            name: None,
            fields: vec![("x".into(), Type::Int), ("y".into(), Type::Int)],
        };
        assert!(tc.is_assignable(&a, &b));
    }

    #[test]
    fn test_is_assignable_tuple_element_wise() {
        let tc = TypeChecker::new();
        let t1 = Type::Tuple(vec![Type::Int, Type::String]);
        let t2 = Type::Tuple(vec![Type::Int, Type::String]);
        assert!(tc.is_assignable(&t1, &t2));

        let t3 = Type::Tuple(vec![Type::Int, Type::Bool]);
        assert!(!tc.is_assignable(&t1, &t3));
    }

    #[test]
    fn test_is_assignable_tuple_struct_incompatible() {
        let tc = TypeChecker::new();
        let tuple = Type::Tuple(vec![Type::Int]);
        let strct = Type::Struct {
            name: None,
            fields: vec![("x".into(), Type::Int)],
        };
        assert!(!tc.is_assignable(&tuple, &strct));
        assert!(!tc.is_assignable(&strct, &tuple));
    }

    #[test]
    fn test_is_assignable_interface_structural() {
        let tc = TypeChecker::new();
        // A struct that has a `len` method-like field satisfies the interface
        let iface = Type::Interface {
            name: None,
            methods: vec![(
                "len".into(),
                Type::Func {
                    params: vec![],
                    ret: Box::new(Type::Int),
                },
            )],
        };
        // Interface itself satisfies an interface with the same methods
        let impl_ty = Type::Interface {
            name: None,
            methods: vec![(
                "len".into(),
                Type::Func {
                    params: vec![],
                    ret: Box::new(Type::Int),
                },
            )],
        };
        assert!(tc.is_assignable(&impl_ty, &iface));
    }

    // ── infer_expr ────────────────────────────────────────────────────────────

    #[test]
    fn test_infer_literals() {
        let mut tc = TypeChecker::new();
        let env = TypeEnv::new();
        assert_eq!(tc.infer_expr(&Expr::Int(1, Span::dummy()), &env), Type::Int);
        assert_eq!(
            tc.infer_expr(&Expr::Float(1.0, Span::dummy()), &env),
            Type::Float
        );
        // `true`, `false`, `null` are now plain idents (prelude globals), not literal keywords.
        // An unbound ident resolves to Type::Any and emits an unknown-identifier error.
        let mut tc2 = TypeChecker::new();
        assert_eq!(
            tc2.infer_expr(&Expr::Ident("true".into(), Span::dummy()), &env),
            Type::Any
        );
        assert!(!tc2.errors.is_empty());
        assert_eq!(
            tc.infer_expr(&Expr::Str(vec![], Span::dummy()), &env),
            Type::String
        );
    }

    #[test]
    fn test_infer_ident_known() {
        let mut tc = TypeChecker::new();
        tc.env.bindings.insert("x".into(), Type::Int);
        let env = tc.env.snapshot_child();
        let result = tc.infer_expr(&Expr::Ident("x".into(), Span::dummy()), &env);
        assert_eq!(result, Type::Int);
        assert!(tc.errors.is_empty());
    }

    #[test]
    fn test_infer_ident_unknown_emits_error() {
        let mut tc = TypeChecker::new();
        let env = TypeEnv::new();
        let result = tc.infer_expr(&Expr::Ident("bogus".into(), Span::dummy()), &env);
        assert_eq!(result, Type::Any);
        assert!(!tc.errors.is_empty());
        assert!(tc.errors[0].message.contains("unknown identifier `bogus`"));
    }

    #[test]
    fn test_infer_binary_arithmetic() {
        use crate::ast::BinOp;
        let mut tc = TypeChecker::new();
        let env = TypeEnv::new();
        let expr = Expr::Binary {
            op: BinOp::Add,
            lhs: Box::new(Expr::Int(1, Span::dummy())),
            rhs: Box::new(Expr::Int(2, Span::dummy())),
            span: Span::dummy(),
        };
        let ty = tc.infer_expr(&expr, &env);
        assert_eq!(ty, Type::Int);
        assert!(tc.errors.is_empty());
    }

    #[test]
    fn test_infer_binary_float_wins() {
        use crate::ast::BinOp;
        let mut tc = TypeChecker::new();
        let env = TypeEnv::new();
        let expr = Expr::Binary {
            op: BinOp::Add,
            lhs: Box::new(Expr::Int(1, Span::dummy())),
            rhs: Box::new(Expr::Float(2.0, Span::dummy())),
            span: Span::dummy(),
        };
        assert_eq!(tc.infer_expr(&expr, &env), Type::Float);
        assert!(tc.errors.is_empty());
    }

    #[test]
    fn test_infer_binary_comparison_returns_bool() {
        use crate::ast::BinOp;
        let mut tc = TypeChecker::new();
        let env = TypeEnv::new();
        let expr = Expr::Binary {
            op: BinOp::Lt,
            lhs: Box::new(Expr::Int(1, Span::dummy())),
            rhs: Box::new(Expr::Int(2, Span::dummy())),
            span: Span::dummy(),
        };
        assert_eq!(tc.infer_expr(&expr, &env), Type::Bool);
    }

    #[test]
    fn test_infer_binary_type_error() {
        use crate::ast::BinOp;
        let mut tc = TypeChecker::new();
        let env = TypeEnv::new();
        // Subtracting String - String should emit an error (String is not numeric for `-`)
        let expr = Expr::Binary {
            op: BinOp::Sub,
            lhs: Box::new(Expr::Str(vec![], Span::dummy())),
            rhs: Box::new(Expr::Str(vec![], Span::dummy())),
            span: Span::dummy(),
        };
        tc.infer_expr(&expr, &env);
        assert!(
            !tc.errors.is_empty(),
            "expected type error for String - String"
        );
    }

    #[test]
    fn test_infer_unary_neg_int() {
        use crate::ast::UnOp;
        let mut tc = TypeChecker::new();
        let env = TypeEnv::new();
        let expr = Expr::Unary {
            op: UnOp::Neg,
            expr: Box::new(Expr::Int(1, Span::dummy())),
            span: Span::dummy(),
        };
        assert_eq!(tc.infer_expr(&expr, &env), Type::Int);
        assert!(tc.errors.is_empty());
    }

    #[test]
    fn test_infer_unary_not_bool() {
        use crate::ast::UnOp;
        let mut tc = TypeChecker::new();
        // Bind `true` as Bool in the env (as the prelude would)
        tc.env.bindings.insert("true".into(), Type::Bool);
        let env = tc.env.snapshot_child();
        let expr = Expr::Unary {
            op: UnOp::Not,
            expr: Box::new(Expr::Ident("true".into(), Span::dummy())),
            span: Span::dummy(),
        };
        assert_eq!(tc.infer_expr(&expr, &env), Type::Bool);
        assert!(tc.errors.is_empty());
    }

    #[test]
    fn test_infer_unary_not_on_int_emits_error() {
        use crate::ast::UnOp;
        let mut tc = TypeChecker::new();
        let env = TypeEnv::new();
        let expr = Expr::Unary {
            op: UnOp::Not,
            expr: Box::new(Expr::Int(1, Span::dummy())),
            span: Span::dummy(),
        };
        tc.infer_expr(&expr, &env);
        assert!(!tc.errors.is_empty(), "expected error for !Int");
    }

    // ── check_stmt ────────────────────────────────────────────────────────────

    #[test]
    fn test_check_let_binding_infers_type() {
        let tc = check_src_env("def foo() -> Void { let x = 42; }");
        // The binding is local to the function; no top-level env entry.
        // But the check should pass without errors.
        assert!(tc.errors.is_empty());
    }

    #[test]
    fn test_check_let_annotation_mismatch() {
        // `let x: Bool = 42` — Int is not assignable to Bool
        let result = check_src("def foo() -> Void { let x: Bool = 42; }");
        assert!(result.is_err(), "expected type mismatch error");
        let errs = result.unwrap_err();
        assert!(
            errs.iter()
                .any(|e| e.message.contains("annotation mismatch")),
            "expected annotation mismatch error, got: {errs:?}"
        );
    }

    #[test]
    fn test_check_let_annotation_ok() {
        // `let x: Int = 42` — should be fine
        assert!(check_src("def foo() -> Void { let x: Int = 42; }").is_ok());
    }

    // ── return type checking ──────────────────────────────────────────────────

    #[test]
    fn test_return_type_mismatch_via_tail() {
        // Body tail returns Bool but declared return type is Int
        let result = check_src("def foo() -> Int { true }");
        assert!(result.is_err(), "expected return type mismatch");
        let errs = result.unwrap_err();
        assert!(
            errs.iter()
                .any(|e| e.message.contains("returns Bool") || e.message.contains("return")),
            "expected return type error, got: {errs:?}"
        );
    }

    #[test]
    fn test_return_type_ok() {
        assert!(check_src("def foo() -> Int { 42 }").is_ok());
    }

    #[test]
    fn test_return_type_ok_any() {
        // A function returning Any accepts any value
        assert!(check_src("def foo() -> Any { 42 }").is_ok());
    }

    #[test]
    fn test_return_stmt_mismatch() {
        // Explicit `return false` inside an Int function
        let result = check_src("def foo() -> Int { return false; 0 }");
        assert!(result.is_err(), "expected return type mismatch");
    }

    #[test]
    fn test_explicit_return_ok() {
        assert!(check_src("def foo() -> Int { return 42; 0 }").is_ok());
    }

    // ── function call checking ────────────────────────────────────────────────

    #[test]
    fn test_call_known_function_ok() {
        let result = check_src(
            "def add(a: Int, b: Int) -> Int { a + b }\ndef main() -> Void { add(1, 2); }",
        );
        assert!(result.is_ok(), "expected no errors, got: {result:?}");
    }

    #[test]
    fn test_call_wrong_arity() {
        let result =
            check_src("def add(a: Int, b: Int) -> Int { a + b }\ndef main() -> Void { add(1); }");
        assert!(result.is_err(), "expected arity error");
        let errs = result.unwrap_err();
        assert!(
            errs.iter()
                .any(|e| e.message.contains("expected 2 argument")),
            "expected arity mismatch, got: {errs:?}"
        );
    }

    #[test]
    fn test_call_wrong_arg_type() {
        let result = check_src(
            "def add(a: Int, b: Int) -> Int { a + b }\ndef main() -> Void { add(true, 1); }",
        );
        assert!(result.is_err(), "expected argument type error");
        let errs = result.unwrap_err();
        assert!(
            errs.iter().any(|e| e.message.contains("argument 1")),
            "expected arg type error, got: {errs:?}"
        );
    }

    #[test]
    fn test_namespace_call_known_export_ok() {
        let result = check_src("use io = \"@stl/io\"; def main() -> Void { io.println(123); }");
        assert!(result.is_ok(), "expected no errors, got: {result:?}");
    }

    #[test]
    fn test_namespace_call_missing_export_errors() {
        let result = check_src("use io = \"@stl/io\"; def main() -> Void { io.nope(123); }");
        assert!(result.is_err(), "expected missing export error");
        let errs = result.unwrap_err();
        assert!(
            errs.iter()
                .any(|e| e.message.contains("has no export `nope`")),
            "expected missing export diagnostic, got: {errs:?}"
        );
    }

    #[test]
    fn test_use_destructure_missing_export_not_bound() {
        let tc = check_src_env("use (missing) = \"@stl/io\";");
        assert!(
            tc.env.lookup_binding("missing").is_none(),
            "unknown import export should not create binding"
        );
    }

    #[test]
    fn test_stl_registry_strict_build() {
        let reg = stl_registry();
        assert!(reg.is_ok(), "stl registry must build: {reg:?}");
        let reg = reg.as_ref().unwrap();
        for path in [
            "@stl/core",
            "@stl/io",
            "@stl/string",
            "@stl/list",
            "@stl/collections",
            "@stl/bool",
            "@stl/option",
            "@stl/result",
        ] {
            assert!(reg.contains_key(path), "registry must include {path}");
        }
    }

    #[test]
    fn test_kernel_os_introspection_builtins_are_typed() {
        let result = check_src(
            "def main() -> Void { let args = os_args(); let cwd = os_cwd(); let now = os_now(); let ex = os_exists(cwd); }",
        );
        assert!(
            result.is_ok(),
            "kernel os introspection builtins should type-check: {result:?}"
        );
    }

    // ── if expression type checking ───────────────────────────────────────────

    #[test]
    fn test_if_non_bool_condition() {
        let result = check_src("def foo() -> Void { if (42) { } }");
        assert!(result.is_err(), "expected Bool condition error");
        let errs = result.unwrap_err();
        assert!(
            errs.iter()
                .any(|e| e.message.contains("if condition must be Bool")),
            "expected condition error, got: {errs:?}"
        );
    }

    #[test]
    fn test_if_bool_condition_ok() {
        // Use a comparison expression so the condition is Bool without needing the prelude.
        assert!(check_src("def foo() -> Void { if (1 < 2) { } }").is_ok());
    }

    // ── end-to-end programs ───────────────────────────────────────────────────

    #[test]
    fn test_full_program_ok() {
        let src = r#"
def add(a: Int, b: Int) -> Int { a + b }
def greet(name: String) -> String { name }
def main() -> Void {
    let x: Int = add(1, 2);
    let s: String = greet("world");
}
"#;
        assert!(check_src(src).is_ok());
    }

    #[test]
    fn test_full_program_multiple_errors() {
        // Two errors: Bool+Bool and Bool returned for Int function
        let src = "def foo(a: Bool, b: Bool) -> Int { a + b }";
        let result = check_src(src);
        assert!(result.is_err());
        let errs = result.unwrap_err();
        // Should have at least the arithmetic error + return type mismatch
        assert!(errs.len() >= 2, "expected multiple errors, got: {errs:?}");
    }

    // ── Phase 4d: pattern type checking ──────────────────────────────────────

    // ── check_pattern direct unit tests ──────────────────────────────────────

    /// Helper: run `check_pattern` against a given pattern and subject type,
    /// return the errors and the bound env.
    fn check_pattern_direct(pat: &Pattern, subject_ty: Type) -> (Vec<TypeError>, TypeEnv) {
        let mut checker = TypeChecker::new();
        let mut env = TypeEnv::new();
        checker.check_pattern(pat, &subject_ty, &mut env);
        (checker.errors, env)
    }

    #[test]
    fn test_pattern_bind_records_type() {
        use crate::token::Span;
        let pat = Pattern::Bind("x".to_string(), Span::default());
        let (errs, env) = check_pattern_direct(&pat, Type::Int);
        assert!(errs.is_empty(), "unexpected errors: {errs:?}");
        assert_eq!(env.bindings.get("x"), Some(&Type::Int));
    }

    #[test]
    fn test_pattern_wildcard_no_binding() {
        use crate::token::Span;
        let pat = Pattern::Wildcard(Span::default());
        let (errs, env) = check_pattern_direct(&pat, Type::String);
        assert!(errs.is_empty(), "unexpected errors: {errs:?}");
        assert!(env.bindings.is_empty());
    }

    #[test]
    fn test_pattern_literal_ok() {
        use crate::token::Span;
        let pat = Pattern::Literal(Expr::Int(42, Span::default()));
        let (errs, _) = check_pattern_direct(&pat, Type::Int);
        assert!(errs.is_empty(), "unexpected errors: {errs:?}");
    }

    #[test]
    fn test_pattern_literal_type_mismatch() {
        use crate::token::Span;
        // Literal 42 (Int) matched against a String subject — should error
        let pat = Pattern::Literal(Expr::Int(42, Span::default()));
        let (errs, _) = check_pattern_direct(&pat, Type::String);
        assert!(
            !errs.is_empty(),
            "expected error for Int literal vs String subject"
        );
        assert!(
            errs.iter().any(|e| e.message.contains("not compatible")),
            "expected compatibility error, got: {errs:?}"
        );
    }

    #[test]
    fn test_pattern_literal_against_any_ok() {
        use crate::token::Span;
        // Literal against Any subject — always ok
        let pat = Pattern::Literal(Expr::Int(1, Span::default()));
        let (errs, _) = check_pattern_direct(&pat, Type::Any);
        assert!(errs.is_empty(), "unexpected errors: {errs:?}");
    }

    #[test]
    fn test_pattern_typecheck_binds_narrowed_type() {
        use crate::token::Span;
        // `x: Int` pattern — should bind `x` to Int regardless of subject
        let pat = Pattern::TypeCheck {
            name: "x".to_string(),
            ty: TypeExpr::Named {
                name: "Int".to_string(),
                args: vec![],
                span: Span::default(),
            },
            span: Span::default(),
        };
        let (errs, env) = check_pattern_direct(&pat, Type::Any);
        assert!(errs.is_empty(), "unexpected errors: {errs:?}");
        assert_eq!(env.bindings.get("x"), Some(&Type::Int));
    }

    #[test]
    fn test_pattern_tuple_ok() {
        use crate::token::Span;
        let subject = Type::Tuple(vec![Type::Int, Type::Bool]);
        let pat = Pattern::Tuple(
            vec![
                Pattern::Bind("a".to_string(), Span::default()),
                Pattern::Bind("b".to_string(), Span::default()),
            ],
            Span::default(),
        );
        let (errs, env) = check_pattern_direct(&pat, subject);
        assert!(errs.is_empty(), "unexpected errors: {errs:?}");
        assert_eq!(env.bindings.get("a"), Some(&Type::Int));
        assert_eq!(env.bindings.get("b"), Some(&Type::Bool));
    }

    #[test]
    fn test_pattern_tuple_arity_mismatch() {
        use crate::token::Span;
        let subject = Type::Tuple(vec![Type::Int, Type::Bool, Type::String]);
        let pat = Pattern::Tuple(
            vec![
                Pattern::Bind("a".to_string(), Span::default()),
                Pattern::Bind("b".to_string(), Span::default()),
            ],
            Span::default(),
        );
        let (errs, _) = check_pattern_direct(&pat, subject);
        assert!(!errs.is_empty(), "expected arity mismatch error");
        assert!(
            errs.iter().any(|e| e.message.contains("elements")),
            "expected arity error, got: {errs:?}"
        );
    }

    #[test]
    fn test_pattern_tuple_against_non_tuple() {
        use crate::token::Span;
        let pat = Pattern::Tuple(
            vec![Pattern::Bind("a".to_string(), Span::default())],
            Span::default(),
        );
        let (errs, _) = check_pattern_direct(&pat, Type::Int);
        assert!(!errs.is_empty(), "expected error for tuple pattern vs Int");
        assert!(
            errs.iter()
                .any(|e| e.message.contains("tuple pattern cannot match")),
            "got: {errs:?}"
        );
    }

    #[test]
    fn test_pattern_struct_ok() {
        use crate::ast::StructPatternField;
        use crate::token::Span;
        let subject = Type::Struct {
            name: Some("Point".to_string()),
            fields: vec![("x".to_string(), Type::Int), ("y".to_string(), Type::Int)],
        };
        let pat = Pattern::Struct {
            fields: vec![
                StructPatternField {
                    name: "x".to_string(),
                    binding: None,
                    span: Span::default(),
                },
                StructPatternField {
                    name: "y".to_string(),
                    binding: Some("my_y".to_string()),
                    span: Span::default(),
                },
            ],
            span: Span::default(),
        };
        let (errs, env) = check_pattern_direct(&pat, subject);
        assert!(errs.is_empty(), "unexpected errors: {errs:?}");
        assert_eq!(env.bindings.get("x"), Some(&Type::Int));
        assert_eq!(env.bindings.get("my_y"), Some(&Type::Int));
    }

    #[test]
    fn test_pattern_struct_unknown_field() {
        use crate::ast::StructPatternField;
        use crate::token::Span;
        let subject = Type::Struct {
            name: Some("Point".to_string()),
            fields: vec![("x".to_string(), Type::Int)],
        };
        let pat = Pattern::Struct {
            fields: vec![StructPatternField {
                name: "z".to_string(), // does not exist
                binding: None,
                span: Span::default(),
            }],
            span: Span::default(),
        };
        let (errs, _) = check_pattern_direct(&pat, subject);
        assert!(!errs.is_empty(), "expected unknown field error");
        assert!(
            errs.iter().any(|e| e.message.contains("unknown field")),
            "got: {errs:?}"
        );
    }

    #[test]
    fn test_pattern_variant_ok() {
        use crate::token::Span;
        let subject = Type::Enum {
            name: Some("Result".to_string()),
            variants: vec![
                ("ok".to_string(), Some(Type::Int)),
                ("err".to_string(), Some(Type::String)),
            ],
        };
        let pat = Pattern::Variant {
            name: "ok".to_string(),
            inner: Some(Box::new(Pattern::Bind("v".to_string(), Span::default()))),
            span: Span::default(),
        };
        let (errs, env) = check_pattern_direct(&pat, subject);
        assert!(errs.is_empty(), "unexpected errors: {errs:?}");
        assert_eq!(env.bindings.get("v"), Some(&Type::Int));
    }

    #[test]
    fn test_pattern_variant_unknown() {
        use crate::token::Span;
        let subject = Type::Enum {
            name: Some("Result".to_string()),
            variants: vec![("ok".to_string(), Some(Type::Int))],
        };
        let pat = Pattern::Variant {
            name: "missing".to_string(),
            inner: None,
            span: Span::default(),
        };
        let (errs, _) = check_pattern_direct(&pat, subject);
        assert!(!errs.is_empty(), "expected unknown variant error");
        assert!(
            errs.iter().any(|e| e.message.contains("does not exist")),
            "got: {errs:?}"
        );
    }

    #[test]
    fn test_pattern_variant_against_non_enum() {
        use crate::token::Span;
        let pat = Pattern::Variant {
            name: "ok".to_string(),
            inner: None,
            span: Span::default(),
        };
        let (errs, _) = check_pattern_direct(&pat, Type::Int);
        assert!(!errs.is_empty(), "expected error for variant vs Int");
        assert!(
            errs.iter().any(|e| e.message.contains("cannot match")),
            "got: {errs:?}"
        );
    }

    #[test]
    fn test_pattern_rest_binds_list() {
        use crate::token::Span;
        let pat = Pattern::Rest {
            name: Some("tail".to_string()),
            span: Span::default(),
        };
        let (errs, env) = check_pattern_direct(&pat, Type::Int);
        assert!(errs.is_empty(), "unexpected errors: {errs:?}");
        assert_eq!(
            env.bindings.get("tail"),
            Some(&Type::List(Box::new(Type::Int)))
        );
    }

    // ── Exhaustiveness checking ───────────────────────────────────────────────

    fn check_exhaustiveness_direct(arms: &[ClosureArm], subject_ty: Type) -> Vec<TypeError> {
        use crate::token::Span;
        let mut checker = TypeChecker::new();
        checker.check_exhaustiveness(arms, &subject_ty, Span::default());
        checker.errors
    }

    #[test]
    fn test_exhaustiveness_bool_complete() {
        use crate::token::Span;
        let arms = vec![
            ClosureArm {
                patterns: vec![Pattern::Literal(Expr::Ident(
                    "true".into(),
                    Span::default(),
                ))],
                guard: None,
                body: Expr::Int(1, Span::default()),
                span: Span::default(),
            },
            ClosureArm {
                patterns: vec![Pattern::Literal(Expr::Ident(
                    "false".into(),
                    Span::default(),
                ))],
                guard: None,
                body: Expr::Int(0, Span::default()),
                span: Span::default(),
            },
        ];
        let errs = check_exhaustiveness_direct(&arms, Type::Bool);
        assert!(errs.is_empty(), "expected no errors: {errs:?}");
    }

    #[test]
    fn test_exhaustiveness_bool_missing_false() {
        use crate::token::Span;
        let arms = vec![ClosureArm {
            patterns: vec![Pattern::Literal(Expr::Ident(
                "true".into(),
                Span::default(),
            ))],
            guard: None,
            body: Expr::Int(1, Span::default()),
            span: Span::default(),
        }];
        let errs = check_exhaustiveness_direct(&arms, Type::Bool);
        assert!(!errs.is_empty(), "expected missing false error");
        assert!(
            errs.iter().any(|e| e.message.contains("missing `false`")),
            "got: {errs:?}"
        );
    }

    #[test]
    fn test_exhaustiveness_bool_missing_true() {
        use crate::token::Span;
        let arms = vec![ClosureArm {
            patterns: vec![Pattern::Literal(Expr::Ident(
                "false".into(),
                Span::default(),
            ))],
            guard: None,
            body: Expr::Int(0, Span::default()),
            span: Span::default(),
        }];
        let errs = check_exhaustiveness_direct(&arms, Type::Bool);
        assert!(!errs.is_empty(), "expected missing true error");
        assert!(
            errs.iter().any(|e| e.message.contains("missing `true`")),
            "got: {errs:?}"
        );
    }

    #[test]
    fn test_exhaustiveness_bool_wildcard_covers_all() {
        use crate::token::Span;
        let arms = vec![ClosureArm {
            patterns: vec![Pattern::Wildcard(Span::default())],
            guard: None,
            body: Expr::Int(0, Span::default()),
            span: Span::default(),
        }];
        let errs = check_exhaustiveness_direct(&arms, Type::Bool);
        assert!(
            errs.is_empty(),
            "wildcard should cover everything: {errs:?}"
        );
    }

    #[test]
    fn test_exhaustiveness_bool_bind_covers_all() {
        use crate::token::Span;
        let arms = vec![ClosureArm {
            patterns: vec![Pattern::Bind("x".to_string(), Span::default())],
            guard: None,
            body: Expr::Ident("x".to_string(), Span::default()),
            span: Span::default(),
        }];
        let errs = check_exhaustiveness_direct(&arms, Type::Bool);
        assert!(errs.is_empty(), "bind catch-all should cover all: {errs:?}");
    }

    #[test]
    fn test_exhaustiveness_enum_complete() {
        use crate::token::Span;
        let subject = Type::Enum {
            name: Some("Color".to_string()),
            variants: vec![
                ("red".to_string(), None),
                ("green".to_string(), None),
                ("blue".to_string(), None),
            ],
        };
        let arms = vec![
            ClosureArm {
                patterns: vec![Pattern::Variant {
                    name: "red".to_string(),
                    inner: None,
                    span: Span::default(),
                }],
                guard: None,
                body: Expr::Int(1, Span::default()),
                span: Span::default(),
            },
            ClosureArm {
                patterns: vec![Pattern::Variant {
                    name: "green".to_string(),
                    inner: None,
                    span: Span::default(),
                }],
                guard: None,
                body: Expr::Int(2, Span::default()),
                span: Span::default(),
            },
            ClosureArm {
                patterns: vec![Pattern::Variant {
                    name: "blue".to_string(),
                    inner: None,
                    span: Span::default(),
                }],
                guard: None,
                body: Expr::Int(3, Span::default()),
                span: Span::default(),
            },
        ];
        let errs = check_exhaustiveness_direct(&arms, subject);
        assert!(errs.is_empty(), "expected no errors: {errs:?}");
    }

    #[test]
    fn test_exhaustiveness_enum_missing_variant() {
        use crate::token::Span;
        let subject = Type::Enum {
            name: Some("Color".to_string()),
            variants: vec![
                ("red".to_string(), None),
                ("green".to_string(), None),
                ("blue".to_string(), None),
            ],
        };
        let arms = vec![
            ClosureArm {
                patterns: vec![Pattern::Variant {
                    name: "red".to_string(),
                    inner: None,
                    span: Span::default(),
                }],
                guard: None,
                body: Expr::Int(1, Span::default()),
                span: Span::default(),
            },
            ClosureArm {
                patterns: vec![Pattern::Variant {
                    name: "green".to_string(),
                    inner: None,
                    span: Span::default(),
                }],
                guard: None,
                body: Expr::Int(2, Span::default()),
                span: Span::default(),
            },
            // missing: blue
        ];
        let errs = check_exhaustiveness_direct(&arms, subject);
        assert!(!errs.is_empty(), "expected missing variant error");
        assert!(
            errs.iter()
                .any(|e| e.message.contains(".blue") || e.message.contains("`blue`")),
            "got: {errs:?}"
        );
    }

    #[test]
    fn test_exhaustiveness_non_exhaustive_type_skipped() {
        // Int subject: exhaustiveness is not checked
        use crate::token::Span;
        let arms = vec![ClosureArm {
            patterns: vec![Pattern::Literal(Expr::Int(1, Span::default()))],
            guard: None,
            body: Expr::Int(1, Span::default()),
            span: Span::default(),
        }];
        let errs = check_exhaustiveness_direct(&arms, Type::Int);
        assert!(errs.is_empty(), "Int exhaustiveness should not be checked");
    }

    // ── let destructuring (end-to-end) ────────────────────────────────────────

    #[test]
    fn test_let_tuple_destructure_ok() {
        // `let (a, b) = (1, 2);` — valid tuple destructuring (avoids prelude dependency)
        assert!(check_src("def foo() -> Void { let (a, b) = (1, 2); }").is_ok());
    }

    #[test]
    fn test_let_bind_typed_ok() {
        // `let x: Int = 42;` — annotation matches
        assert!(check_src("def foo() -> Void { let x: Int = 42; }").is_ok());
    }

    #[test]
    fn test_let_bind_typed_mismatch() {
        // `let x: Bool = 42;` — annotation mismatch
        let result = check_src("def foo() -> Void { let x: Bool = 42; }");
        assert!(result.is_err(), "expected annotation mismatch");
        let errs = result.unwrap_err();
        assert!(
            errs.iter()
                .any(|e| e.message.contains("annotation mismatch")),
            "got: {errs:?}"
        );
    }

    // ── closure arm body uses pattern-bound names with correct type ───────────

    #[test]
    fn test_closure_bind_pattern_propagates_type() {
        // A closure arm that binds a param and uses it arithmetically.
        // The closure is passed to a registered typed function so the
        // typechecker knows the subject type.
        // Since we can't register STL in tests easily, we use a def that
        // takes a Func[Int, Int] and verify it type-checks correctly.
        let src = r#"
def apply(f: Func[(Int), Int], x: Int) -> Int { x }
def main() -> Void {
    let result: Int = apply({ n -> n }, 42);
}
"#;
        assert!(check_src(src).is_ok());
    }

    // ── Phase 4e: cast validation ─────────────────────────────────────────────

    #[test]
    fn test_cast_int_to_float_ok() {
        // Numeric coercion: Int → Float is allowed at cast site
        assert!(check_src("def foo() -> Void { let x: Float = (1 : Float); }").is_ok());
    }

    #[test]
    fn test_cast_float_to_int_ok() {
        // Numeric coercion: Float → Int is allowed at cast site
        assert!(check_src("def foo() -> Void { let x: Int = (3.14 : Int); }").is_ok());
    }

    #[test]
    fn test_cast_any_to_concrete_ok() {
        // Any → Int is runtime narrowing — allowed at cast site
        let src = r#"
def give_any(x: Any) -> Void {
    let n: Int = (x : Int);
}
"#;
        assert!(check_src(src).is_ok());
    }

    #[test]
    fn test_cast_concrete_to_any_ok() {
        // T → Any is widening — always ok
        assert!(check_src("def foo() -> Void { let a: Any = (42 : Any); }").is_ok());
    }

    #[test]
    fn test_cast_union_narrowing_ok() {
        // Union → concrete type at cast site: allowed
        let src = r#"
def give_union(x: union(Int, String)) -> Void {
    let n: Int = (x : Int);
}
"#;
        assert!(check_src(src).is_ok());
    }

    #[test]
    fn test_cast_widening_to_union_ok() {
        // T → Union(T, U) widening: allowed
        let src = r#"
def foo() -> Void {
    let x: Int = 5;
    let y: union(Int, String) = (x : union(Int, String));
}
"#;
        assert!(check_src(src).is_ok());
    }

    #[test]
    fn test_cast_same_type_ok() {
        // Casting a value to the same type is trivially ok
        assert!(check_src("def foo() -> Void { let x: Int = (42 : Int); }").is_ok());
    }

    #[test]
    fn test_cast_to_interface_ok() {
        // T → interface (widening) is always allowed
        // Use `def Printable = interface(...)` syntax
        let src = r#"
def Printable = interface(print: Func[(), Void]);
def foo() -> Void {
    let x: Int = 1;
    let p: Printable = (x : Printable);
}
"#;
        assert!(check_src(src).is_ok());
    }

    #[test]
    fn test_cast_interface_narrowing_ok() {
        // Interface → concrete: runtime narrowing, allowed at cast site
        let src = r#"
def Printable = interface(print: Func[(), Void]);
def foo(p: Printable) -> Void {
    let n: Int = (p : Int);
}
"#;
        assert!(check_src(src).is_ok());
    }

    #[test]
    fn test_cast_named_struct_to_different_named_struct_error() {
        // Named → Named (different names) is forbidden
        // Use `def Name = (fields...)` syntax
        let src = r#"
def Point = (x: Int, y: Int);
def Vector = (x: Int, y: Int);
def foo(p: Point) -> Void {
    let v: Vector = (p : Vector);
}
"#;
        let result = check_src(src);
        assert!(result.is_err(), "expected cast error");
        let errs = result.unwrap_err();
        assert!(
            errs.iter()
                .any(|e| e.message.contains("Point") || e.message.contains("Vector")),
            "got: {errs:?}"
        );
    }

    #[test]
    fn test_cast_tuple_to_struct_error() {
        // Tuple ↔ Struct is forbidden
        let src = r#"
def Point = (x: Int, y: Int);
def foo() -> Void {
    let t = (1, 2);
    let p: Point = (t : Point);
}
"#;
        let result = check_src(src);
        assert!(result.is_err(), "expected tuple-to-struct cast error");
        let errs = result.unwrap_err();
        assert!(
            errs.iter()
                .any(|e| e.message.contains("tuple") || e.message.contains("struct")),
            "got: {errs:?}"
        );
    }

    #[test]
    fn test_cast_struct_to_tuple_error() {
        // Struct ↔ Tuple is forbidden
        let src = r#"
def Point = (x: Int, y: Int);
def foo(p: Point) -> Void {
    let t: (Int, Int) = (p : (Int, Int));
}
"#;
        let result = check_src(src);
        assert!(result.is_err(), "expected struct-to-tuple cast error");
        let errs = result.unwrap_err();
        assert!(
            errs.iter()
                .any(|e| e.message.contains("tuple") || e.message.contains("struct")),
            "got: {errs:?}"
        );
    }

    #[test]
    fn test_cast_unrelated_types_error() {
        // Bool → Int is not a valid cast (neither numeric coercion nor assignable).
        // Use a parameter annotation to get a properly-typed Bool variable.
        let src = r#"
def foo(b: Bool) -> Void {
    let n: Int = (b : Int);
}
"#;
        let result = check_src(src);
        assert!(result.is_err(), "expected invalid cast error");
        let errs = result.unwrap_err();
        assert!(
            errs.iter()
                .any(|e| e.message.contains("invalid cast") || e.message.contains("Bool")),
            "got: {errs:?}"
        );
    }

    #[test]
    fn test_cast_string_to_int_error() {
        // String → Int is not a valid cast
        let src = r#"
def foo() -> Void {
    let s: String = "hello";
    let n: Int = (s : Int);
}
"#;
        let result = check_src(src);
        assert!(result.is_err(), "expected invalid cast error");
        let errs = result.unwrap_err();
        assert!(
            errs.iter()
                .any(|e| e.message.contains("invalid cast") || e.message.contains("String")),
            "got: {errs:?}"
        );
    }

    #[test]
    fn test_struct_type_void_field_assignable() {
        let s = r#"
def main() -> Void {
    let r: (age: Int, name: String, author: Void) = (age = 1, name = "a", author = ());
    let _: (age: Int, name: String, author) = r;
}
"#;
        assert!(check_src(s).is_ok());
    }

    #[test]
    fn test_array_literal_and_cast() {
        let s = r#"
def main() -> Void {
    let a = array[1, 2, 3] : Array[Int, 3];
    let _x: Int = a[0];
}
"#;
        assert!(check_src(s).is_ok());
    }

    #[test]
    fn test_set_literal() {
        let s = r#"
def main() -> Void {
    let s = set[1, 2, 3] : Set[Int];
    let _b: Set[Int] = s;
}
"#;
        assert!(check_src(s).is_ok());
    }
}
