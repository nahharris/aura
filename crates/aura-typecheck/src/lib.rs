pub mod aliases;
pub mod builtins;
pub mod checked_ir;
pub mod checker;
pub mod generics;
pub mod interfaces;
pub mod modules;
pub mod numeric;
pub mod patterns;
pub mod resolver;
pub mod symbols;
pub mod types;
pub mod unify;

use aura_diagnostics::TypeRef;
use aura_diagnostics::{Diagnostic, Severity};
use aura_frontend::ast::{Program, StaticParam, TypeExpr};
use std::collections::HashMap;

use checker::TypeChecker;
pub use resolver::Resolver;
pub use symbols::{ScopeId, SymbolId, SymbolKind};
pub use types::{Ty, TyId, TyInterner};

#[derive(Debug, Clone, Copy, Default)]
pub struct CheckOptions {
    pub enforce_main_signature: bool,
}

#[derive(Debug, Clone)]
pub struct CheckedModule {
    pub symbols: resolver::ResolvedSymbols,
    pub value_types: HashMap<String, TyId>,
    pub type_aliases: HashMap<String, TyId>,
    pub generic_type_aliases: HashMap<String, GenericTypeAlias>,
    pub methods: Vec<MethodImportBinding>,
    pub types: TyInterner,
    pub ir: checked_ir::CheckedIr,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct GenericTypeAlias {
    pub static_params: Vec<StaticParam>,
    pub body: TypeExpr,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ImportBinding {
    pub source_name: String,
    pub local_name: String,
    pub link_name: String,
    pub ty: TypeRef,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct TypeImportBinding {
    pub source_name: String,
    pub local_name: String,
    pub ty: TypeRef,
    pub generic: Option<GenericTypeAlias>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MethodImportBinding {
    pub source_name: String,
    pub local_name: String,
    pub link_name: String,
    pub receiver_ty: TypeRef,
    pub ty: TypeRef,
    pub static_params: Vec<StaticParam>,
}

#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct CheckContext {
    pub imported_values: Vec<ImportBinding>,
    pub imported_types: Vec<TypeImportBinding>,
    pub imported_methods: Vec<MethodImportBinding>,
    pub namespaces: HashMap<String, Vec<ImportBinding>>,
}

#[derive(Debug, Clone)]
pub struct CheckResult {
    pub module: Option<CheckedModule>,
    pub diagnostics: Vec<Diagnostic>,
}

pub fn check_module(ast: &Program) -> CheckResult {
    check_module_with_context(ast, CheckContext::default(), CheckOptions::default())
}

pub fn check_module_with_options(ast: &Program, options: CheckOptions) -> CheckResult {
    check_module_with_context(ast, CheckContext::default(), options)
}

pub fn check_module_with_context(
    ast: &Program,
    context: CheckContext,
    options: CheckOptions,
) -> CheckResult {
    let mut resolver = Resolver::new();
    let symbols = resolver.resolve_program(ast);
    let mut diagnostics = resolver.into_diagnostics();

    let mut checker = TypeChecker::new(context, options);
    let (value_types, type_aliases, generic_type_aliases) = checker.check_program(ast);
    let (types, checker_diagnostics, ir, methods) = checker.into_parts();
    diagnostics.extend(checker_diagnostics);

    if diagnostics.iter().any(|d| d.severity == Severity::Error) {
        return CheckResult {
            module: None,
            diagnostics,
        };
    }
    CheckResult {
        module: Some(CheckedModule {
            symbols,
            value_types,
            type_aliases,
            generic_type_aliases,
            methods,
            types,
            ir,
        }),
        diagnostics,
    }
}
