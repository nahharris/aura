use std::collections::{HashMap, HashSet};
use std::fmt;
use std::fs;
use std::path::{Path, PathBuf};

use aura_diagnostics::type_ref::FuncParamRef;
use aura_diagnostics::{Diagnostic, PrimitiveType, TypeRef};
use aura_frontend::Parser;
use aura_frontend::ast::{Decl, Program, UseBinding};
use aura_typecheck::checked_ir::{CheckedDecl, CheckedExpr};
use aura_typecheck::types::{FuncParam, Ty, TyInterner};
use aura_typecheck::{
    CheckContext, CheckOptions, CheckedModule, ImportBinding, MethodImportBinding,
    TypeImportBinding,
    check_module_with_context,
};

use super::discover::find_project_root;
use super::manifest::{DependencySource, Manifest, ManifestError, ProjectType, load_manifest};

#[derive(Debug, Clone, Copy, Default)]
pub struct ProjectCompileOptions {
    pub enforce_entry_main_signature: bool,
}

#[derive(Debug, Clone)]
pub struct ProjectBuild {
    pub manifest: Manifest,
    pub root: PathBuf,
    pub entry_path: PathBuf,
    pub modules: Vec<CompiledProjectModule>,
}

#[derive(Debug, Clone)]
pub struct CompiledProjectModule {
    pub path: PathBuf,
    pub module_name: String,
    pub checked: CheckedModule,
}

#[derive(Debug, Clone)]
pub enum ProjectCompileError {
    Manifest {
        path: PathBuf,
        error: ManifestError,
    },
    ReadSource {
        path: PathBuf,
        error: String,
    },
    ParseSource {
        path: PathBuf,
        source: String,
        diagnostic: Box<Diagnostic>,
    },
    Typecheck {
        path: PathBuf,
        source: String,
        diagnostics: Vec<Diagnostic>,
    },
    Resolve {
        path: Option<PathBuf>,
        message: String,
    },
}

impl fmt::Display for ProjectCompileError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Manifest { path, error } => {
                write!(f, "manifest error in '{}': {error}", path.display())
            }
            Self::ReadSource { path, error } => {
                write!(f, "failed reading '{}': {error}", path.display())
            }
            Self::ParseSource {
                path, diagnostic, ..
            } => {
                write!(
                    f,
                    "failed parsing '{}': {}",
                    path.display(),
                    diagnostic.message
                )
            }
            Self::Typecheck {
                path, diagnostics, ..
            } => {
                write!(
                    f,
                    "typecheck failed for '{}' with {} diagnostic(s)",
                    path.display(),
                    diagnostics.len()
                )
            }
            Self::Resolve { path, message } => match path {
                Some(path) => write!(
                    f,
                    "module resolution failed at '{}': {message}",
                    path.display()
                ),
                None => write!(f, "module resolution failed: {message}"),
            },
        }
    }
}

impl std::error::Error for ProjectCompileError {}

#[derive(Debug, Clone)]
struct PackageRecord {
    manifest: Manifest,
    root: PathBuf,
    dependencies: HashMap<String, PathBuf>,
}

#[derive(Debug, Clone)]
struct ExportBinding {
    owner_path: PathBuf,
    binding: ImportBinding,
}

#[derive(Debug, Clone)]
struct TypeExportBinding {
    owner_path: PathBuf,
    binding: TypeImportBinding,
}

#[derive(Debug, Clone)]
struct ModuleRecord {
    path: PathBuf,
    package_root: PathBuf,
    logical_name: String,
    checked: CheckedModule,
    value_exports: Vec<ExportBinding>,
    type_exports: Vec<TypeExportBinding>,
    macro_exports: Vec<ExportBinding>,
    method_exports: Vec<MethodImportBinding>,
}

type BuildContextResult = (
    CheckContext,
    Vec<ExportBinding>,
    Vec<TypeExportBinding>,
    Vec<ImportBinding>,
);

#[derive(Debug, Default)]
struct ProjectCompiler {
    packages: HashMap<PathBuf, PackageRecord>,
    modules: HashMap<PathBuf, ModuleRecord>,
    loading_modules: HashSet<PathBuf>,
    module_order: Vec<PathBuf>,
}

pub fn compile_project(
    manifest_file: &Path,
    options: ProjectCompileOptions,
) -> Result<ProjectBuild, ProjectCompileError> {
    let mut compiler = ProjectCompiler::default();
    let root = canonicalize_existing(manifest_file.parent().ok_or_else(|| {
        ProjectCompileError::Resolve {
            path: Some(manifest_file.to_path_buf()),
            message: "project.auon should have a parent directory".to_string(),
        }
    })?)?;
    compiler.ensure_package(&root)?;
    let manifest = compiler
        .packages
        .get(&root)
        .expect("package should be loaded")
        .manifest
        .clone();

    let entry_path = match manifest.kind {
        ProjectType::Binary => root.join("src").join("main.aura"),
        ProjectType::Library => root.join("src").join("lib.aura"),
    };
    let entry_path = canonicalize_existing(&entry_path)?;
    compiler.ensure_module(&entry_path, &entry_path, options)?;

    let required_paths = compiler.required_modules(&entry_path);
    let modules = compiler
        .module_order
        .iter()
        .filter(|path| required_paths.contains(*path))
        .filter_map(|path| compiler.modules.get(path))
        .map(|record| {
            let manifest = &compiler
                .packages
                .get(&record.package_root)
                .expect("package should exist")
                .manifest;
            CompiledProjectModule {
                path: record.path.clone(),
                module_name: stable_module_name(&manifest.name, &record.logical_name),
                checked: record.checked.clone(),
            }
        })
        .collect::<Vec<_>>();

    Ok(ProjectBuild {
        manifest,
        root,
        entry_path,
        modules,
    })
}

impl ProjectCompiler {
    fn ensure_package(&mut self, root: &Path) -> Result<(), ProjectCompileError> {
        let root = canonicalize_existing(root)?;
        if self.packages.contains_key(&root) {
            return Ok(());
        }

        let manifest_file = root.join("project.auon");
        let manifest =
            load_manifest(&manifest_file).map_err(|error| ProjectCompileError::Manifest {
                path: manifest_file.clone(),
                error,
            })?;

        let mut dependencies = HashMap::new();
        for dependency in &manifest.dependencies {
            let dependency_root = match &dependency.source {
                DependencySource::Path { path } => {
                    let dependency_path = PathBuf::from(path);
                    let resolved = if dependency_path.is_absolute() {
                        dependency_path
                    } else {
                        root.join(dependency_path)
                    };
                    canonicalize_existing(&resolved)?
                }
                DependencySource::Git { .. } => {
                    canonicalize_existing(&root.join("vendor").join(&dependency.alias))?
                }
            };
            self.ensure_package(&dependency_root)?;
            dependencies.insert(dependency.alias.clone(), dependency_root);
        }

        self.packages.insert(
            root.clone(),
            PackageRecord {
                manifest,
                root,
                dependencies,
            },
        );
        Ok(())
    }

    fn ensure_module(
        &mut self,
        path: &Path,
        entry_path: &Path,
        options: ProjectCompileOptions,
    ) -> Result<(), ProjectCompileError> {
        let path = canonicalize_existing(path)?;
        if self.modules.contains_key(&path) {
            return Ok(());
        }
        if !self.loading_modules.insert(path.clone()) {
            return Err(ProjectCompileError::Resolve {
                path: Some(path),
                message: "cyclic module loading is not supported yet".to_string(),
            });
        }

        let package_root = canonicalize_existing(&find_project_root(&path).ok_or_else(|| {
            ProjectCompileError::Resolve {
                path: Some(path.clone()),
                message: "could not determine owning package root".to_string(),
            }
        })?)?;
        self.ensure_package(&package_root)?;

        let source =
            fs::read_to_string(&path).map_err(|error| ProjectCompileError::ReadSource {
                path: path.clone(),
                error: error.to_string(),
            })?;
        let program = Parser::parse_source(&source).map_err(|diagnostic| {
            ProjectCompileError::ParseSource {
                path: path.clone(),
                source: source.clone(),
                diagnostic: Box::new(diagnostic),
            }
        })?;

        let (context, explicit_value_reexports, explicit_type_reexports, namespace_bindings) =
            self.build_check_context(&package_root, &path, &program, entry_path, options)?;
        let enforce_main_signature =
            options.enforce_entry_main_signature && path.as_path() == entry_path;
        let checked = check_module_with_context(
            &program,
            context,
            CheckOptions {
                enforce_main_signature,
            },
        );
        if checked
            .diagnostics
            .iter()
            .any(|diagnostic| diagnostic.severity == aura_diagnostics::Severity::Error)
        {
            return Err(ProjectCompileError::Typecheck {
                path: path.clone(),
                source,
                diagnostics: checked.diagnostics,
            });
        }
        let mut checked = checked.module.expect("error-free module should exist");
        let manifest = &self
            .packages
            .get(&package_root)
            .expect("package should be loaded")
            .manifest;
        let logical_name = module_logical_name(&package_root, &path)?;
        for decl in &mut checked.ir.declarations {
            if !decl.is_extern {
                decl.link_name = stable_link_name(&manifest.name, &logical_name, &decl.name);
            }
        }
        for method in &mut checked.methods {
            if let Some(decl) = checked
                .ir
                .declarations
                .iter()
                .find(|decl| decl.name == method.source_name && !decl.is_extern)
            {
                method.link_name = decl.link_name.clone();
            }
        }
        for binding in namespace_bindings {
            if checked
                .ir
                .declarations
                .iter()
                .any(|decl| decl.link_name == binding.link_name)
            {
                continue;
            }
            checked.ir.declarations.push(CheckedDecl {
                name: binding.link_name.clone(),
                link_name: binding.link_name,
                params: Vec::new(),
                ty: checked
                    .ir
                    .declarations
                    .iter()
                    .find(|decl| decl.is_extern && decl.name == binding.local_name)
                    .map(|decl| decl.ty)
                    .unwrap_or_else(|| ty_ref_to_ty_id(&mut checked.types, &binding.ty)),
                is_extern: true,
                value: CheckedExpr::Any,
            });
        }

        let mut value_exports: Vec<ExportBinding> = Vec::new();
        let mut macro_exports: Vec<ExportBinding> = Vec::new();
        for decl in &checked.ir.declarations {
            let ty = ty_to_type_ref(&checked.types, decl.ty);
            let binding = ExportBinding {
                owner_path: path.clone(),
                binding: ImportBinding {
                    source_name: decl.name.clone(),
                    local_name: decl.name.clone(),
                    link_name: decl.link_name.clone(),
                    ty: ty.clone(),
                },
            };
            if matches!(ty, TypeRef::Macro { .. }) {
                macro_exports.push(binding);
            } else if matches!(ty, TypeRef::Func { .. }) && decl.is_extern {
                macro_exports.push(binding);
            } else {
                value_exports.push(binding);
            }
        }
        for export in explicit_value_reexports {
            if !value_exports.iter().any(|existing| {
                existing.binding.source_name == export.binding.source_name
                    && existing.binding.link_name == export.binding.link_name
            }) {
                value_exports.push(export);
            }
        }
        let mut type_exports = checked
            .type_aliases
            .iter()
            .map(|(name, ty)| TypeExportBinding {
                owner_path: path.clone(),
                binding: TypeImportBinding {
                    source_name: name.clone(),
                    local_name: name.clone(),
                    ty: ty_to_type_ref(&checked.types, *ty),
                    generic: None,
                },
            })
            .collect::<Vec<_>>();
        type_exports.extend(checked.generic_type_aliases.iter().map(|(name, generic)| {
            TypeExportBinding {
                owner_path: path.clone(),
                binding: TypeImportBinding {
                    source_name: name.clone(),
                    local_name: name.clone(),
                    ty: TypeRef::Unknown,
                    generic: Some(generic.clone()),
                },
            }
        }));
        type_exports.extend(explicit_type_reexports);

        let method_exports = checked.methods.clone();
        self.loading_modules.remove(&path);
        self.module_order.push(path.clone());
        self.modules.insert(
            path.clone(),
            ModuleRecord {
                path,
                package_root,
                logical_name,
                checked,
                value_exports,
                type_exports,
                macro_exports,
                method_exports,
            },
        );
        Ok(())
    }

    #[allow(clippy::type_complexity)]
    fn build_check_context(
        &mut self,
        package_root: &Path,
        importer_path: &Path,
        program: &Program,
        entry_path: &Path,
        options: ProjectCompileOptions,
    ) -> Result<BuildContextResult, ProjectCompileError> {
        let package = self
            .packages
            .get(package_root)
            .expect("package should be loaded")
            .clone();
        let mut context = CheckContext::default();
        let mut explicit_value_reexports = Vec::new();
        let mut explicit_type_reexports = Vec::new();
        let mut imported_origins = HashMap::<String, String>::new();
        let mut imported_type_origins = HashMap::<String, String>::new();
        let mut namespace_origins = HashMap::<String, String>::new();
        let logical_name = module_logical_name(package_root, importer_path)?;

        if logical_name != "lib" && package.manifest.kind == ProjectType::Binary {
            let lib_path = package.root.join("src").join("lib.aura");
            if lib_path.is_file() {
                let lib_path = canonicalize_existing(&lib_path)?;
                self.ensure_module(&lib_path, entry_path, options)?;
                self.import_library_exports(
                    &mut context,
                    &mut imported_origins,
                    &mut imported_type_origins,
                    &mut namespace_origins,
                    importer_path,
                    &lib_path,
                    "current package lib",
                )?;
            }
        }

        for dependency_root in package.dependencies.values() {
            let lib_path = dependency_root.join("src").join("lib.aura");
            if !lib_path.is_file() {
                continue;
            }
            let lib_path = canonicalize_existing(&lib_path)?;
            self.ensure_module(&lib_path, entry_path, options)?;
            self.import_library_exports(
                &mut context,
                &mut imported_origins,
                &mut imported_type_origins,
                &mut namespace_origins,
                importer_path,
                &lib_path,
                "direct dependency lib",
            )?;
        }

        for decl in &program.declarations {
            let Decl::Use(use_decl) = decl else {
                continue;
            };
            let import_path =
                self.resolve_import_path(&package, importer_path, &use_decl.source)?;
            self.ensure_module(&import_path, entry_path, options)?;
            let value_exports = self.module_value_exports(&import_path)?;
            let type_exports = self.module_type_exports(&import_path)?;
            let macro_exports = self.module_macro_exports(&import_path)?;
            let method_exports = self.module_method_exports(&import_path)?;
            match &use_decl.binding {
                UseBinding::Namespace(alias) => {
                    let all_exports: Vec<ImportBinding> = value_exports
                        .iter()
                        .chain(macro_exports.iter())
                        .map(|binding| binding.binding.clone())
                        .collect();
                    self.insert_namespace(
                        &mut context,
                        &mut imported_origins,
                        &mut namespace_origins,
                        importer_path,
                        alias,
                        all_exports,
                        format!("namespace import from {}", use_decl.source),
                    )?;
                }
                UseBinding::Fields(fields) => {
                    for field in fields {
                        let mut found = false;
                        let field_name = &field.source_name;
                        if let Some(export) = value_exports
                            .iter()
                            .find(|binding| binding.binding.source_name == *field_name)
                        {
                            if matches!(export.binding.ty, TypeRef::Macro { .. }) {
                                if !imported_origins.contains_key(&field.local_name) {
                                    imported_origins.insert(
                                        field.local_name.clone(),
                                        format!("macro stub from {}", use_decl.source),
                                    );
                                }
                                found = true;
                            } else {
                                if imported_origins.contains_key(&field.local_name) {
                                    found = true;
                                } else {
                                    let binding = ImportBinding {
                                        source_name: field.source_name.clone(),
                                        local_name: field.local_name.clone(),
                                        link_name: export.binding.link_name.clone(),
                                        ty: export.binding.ty.clone(),
                                    };
                                    self.insert_imported_value(
                                        &mut context,
                                        &mut imported_origins,
                                        &namespace_origins,
                                        importer_path,
                                        binding.clone(),
                                        format!("field import from {}", use_decl.source),
                                    )?;
                                    explicit_value_reexports.push(ExportBinding {
                                        owner_path: export.owner_path.clone(),
                                        binding,
                                    });
                                    found = true;
                                }
                            }
                        }
                        if macro_exports
                            .iter()
                            .find(|binding| binding.binding.source_name == *field_name)
                            .is_some()
                        {
                            if !imported_origins.contains_key(&field.local_name) {
                                imported_origins.insert(
                                    field.local_name.clone(),
                                    format!("macro stub from {}", use_decl.source),
                                );
                            }
                            found = true;
                        }
                        if let Some(export) = type_exports
                            .iter()
                            .find(|binding| binding.binding.source_name == *field_name)
                        {
                            let binding = TypeImportBinding {
                                source_name: field.source_name.clone(),
                                local_name: field.local_name.clone(),
                                ty: export.binding.ty.clone(),
                                generic: export.binding.generic.clone(),
                            };
                            self.insert_imported_type(
                                &mut context,
                                &mut imported_type_origins,
                                importer_path,
                                binding.clone(),
                                format!("field import from {}", use_decl.source),
                            )?;
                            explicit_type_reexports.push(TypeExportBinding {
                                owner_path: export.owner_path.clone(),
                                binding,
                            });
                            found = true;
                        }
                        context.imported_methods.extend(method_exports.iter().cloned());
                        if !found {
                            return Err(ProjectCompileError::Resolve {
                                path: Some(importer_path.to_path_buf()),
                                message: format!(
                                    "module '{}' does not export '{}'",
                                    use_decl.source, field_name
                                ),
                            });
                        }
                    }
                }
            }
        }

        let namespace_bindings = context
            .namespaces
            .values()
            .flat_map(|bindings| bindings.iter().cloned())
            .collect::<Vec<_>>();

        Ok((
            context,
            explicit_value_reexports,
            explicit_type_reexports,
            namespace_bindings,
        ))
    }

    #[allow(clippy::too_many_arguments)]
    fn import_library_exports(
        &self,
        context: &mut CheckContext,
        imported_origins: &mut HashMap<String, String>,
        imported_type_origins: &mut HashMap<String, String>,
        namespace_origins: &mut HashMap<String, String>,
        importer_path: &Path,
        lib_path: &Path,
        origin_label: &str,
    ) -> Result<(), ProjectCompileError> {
        for export in self.module_value_exports(lib_path)? {
            if matches!(export.binding.ty, TypeRef::Macro { .. }) {
                continue;
            }
            self.insert_imported_value(
                context,
                imported_origins,
                namespace_origins,
                importer_path,
                export.binding.clone(),
                format!("{origin_label} ({})", lib_path.display()),
            )?;
        }
        for export in self.module_type_exports(lib_path)? {
            self.insert_imported_type(
                context,
                imported_type_origins,
                importer_path,
                export.binding.clone(),
                format!("{origin_label} ({})", lib_path.display()),
            )?;
        }
        context
            .imported_methods
            .extend(self.module_method_exports(lib_path)?);
        Ok(())
    }

    fn insert_imported_value(
        &self,
        context: &mut CheckContext,
        imported_origins: &mut HashMap<String, String>,
        namespace_origins: &HashMap<String, String>,
        importer_path: &Path,
        binding: ImportBinding,
        origin: String,
    ) -> Result<(), ProjectCompileError> {
        if let Some(existing) = namespace_origins.get(&binding.local_name) {
            return Err(ProjectCompileError::Resolve {
                path: Some(importer_path.to_path_buf()),
                message: format!(
                    "import '{}' conflicts with namespace alias from {existing}",
                    binding.local_name
                ),
            });
        }
        if let Some(existing) = imported_origins.get(&binding.local_name) {
            return Err(ProjectCompileError::Resolve {
                path: Some(importer_path.to_path_buf()),
                message: format!(
                    "import '{}' is provided by both {existing} and {origin}",
                    binding.local_name
                ),
            });
        }
        imported_origins.insert(binding.local_name.clone(), origin);
        context.imported_values.push(binding);
        Ok(())
    }

    fn insert_imported_type(
        &self,
        context: &mut CheckContext,
        imported_type_origins: &mut HashMap<String, String>,
        importer_path: &Path,
        binding: TypeImportBinding,
        origin: String,
    ) -> Result<(), ProjectCompileError> {
        if let Some(existing) = imported_type_origins.get(&binding.local_name) {
            return Err(ProjectCompileError::Resolve {
                path: Some(importer_path.to_path_buf()),
                message: format!(
                    "type import '{}' is provided by both {existing} and {origin}",
                    binding.local_name
                ),
            });
        }
        imported_type_origins.insert(binding.local_name.clone(), origin);
        context.imported_types.push(binding);
        Ok(())
    }

    #[allow(clippy::too_many_arguments)]
    fn insert_namespace(
        &self,
        context: &mut CheckContext,
        imported_origins: &mut HashMap<String, String>,
        namespace_origins: &mut HashMap<String, String>,
        importer_path: &Path,
        alias: &str,
        bindings: Vec<ImportBinding>,
        origin: String,
    ) -> Result<(), ProjectCompileError> {
        if imported_origins.contains_key(alias) {
            return Err(ProjectCompileError::Resolve {
                path: Some(importer_path.to_path_buf()),
                message: format!("namespace alias '{alias}' conflicts with an imported value"),
            });
        }
        if let Some(existing) = namespace_origins.get(alias) {
            return Err(ProjectCompileError::Resolve {
                path: Some(importer_path.to_path_buf()),
                message: format!(
                    "namespace alias '{alias}' is provided by both {existing} and {origin}"
                ),
            });
        }
        namespace_origins.insert(alias.to_string(), origin);
        context.namespaces.insert(alias.to_string(), bindings);
        Ok(())
    }

    fn resolve_import_path(
        &self,
        package: &PackageRecord,
        importer_path: &Path,
        source: &str,
    ) -> Result<PathBuf, ProjectCompileError> {
        let target = if let Some(alias_source) = source.strip_prefix('@') {
            let (alias_tail, module_tail) = alias_source
                .split_once('/')
                .map(|(alias, rest)| (format!("@{alias}"), Some(rest)))
                .unwrap_or_else(|| (format!("@{alias_source}"), None));
            let dependency_root = package.dependencies.get(&alias_tail).ok_or_else(|| {
                ProjectCompileError::Resolve {
                    path: Some(importer_path.to_path_buf()),
                    message: format!("unknown dependency alias '{alias_tail}'"),
                }
            })?;
            module_source_to_file(&dependency_root.join("src"), module_tail.unwrap_or("lib"))
        } else if source.starts_with("./") || source.starts_with("../") {
            let importer_dir =
                importer_path
                    .parent()
                    .ok_or_else(|| ProjectCompileError::Resolve {
                        path: Some(importer_path.to_path_buf()),
                        message: "importing module has no parent directory".to_string(),
                    })?;
            module_source_to_file(importer_dir, source)
        } else {
            module_source_to_file(&package.root.join("src"), source)
        };
        canonicalize_existing(&target)
    }

    fn module_value_exports(&self, path: &Path) -> Result<Vec<ExportBinding>, ProjectCompileError> {
        self.modules
            .get(path)
            .map(|module| module.value_exports.clone())
            .ok_or_else(|| ProjectCompileError::Resolve {
                path: Some(path.to_path_buf()),
                message: "module was not loaded before export lookup".to_string(),
            })
    }

    fn module_type_exports(
        &self,
        path: &Path,
    ) -> Result<Vec<TypeExportBinding>, ProjectCompileError> {
        self.modules
            .get(path)
            .map(|module| module.type_exports.clone())
            .ok_or_else(|| ProjectCompileError::Resolve {
                path: Some(path.to_path_buf()),
                message: "module was not loaded before export lookup".to_string(),
            })
    }

    fn module_macro_exports(&self, path: &Path) -> Result<Vec<ExportBinding>, ProjectCompileError> {
        self.modules
            .get(path)
            .map(|module| module.macro_exports.clone())
            .ok_or_else(|| ProjectCompileError::Resolve {
                path: Some(path.to_path_buf()),
                message: "module was not loaded before export lookup".to_string(),
            })
    }

    fn module_method_exports(
        &self,
        path: &Path,
    ) -> Result<Vec<MethodImportBinding>, ProjectCompileError> {
        self.modules
            .get(path)
            .map(|module| module.method_exports.clone())
            .ok_or_else(|| ProjectCompileError::Resolve {
                path: Some(path.to_path_buf()),
                message: "module was not loaded before export lookup".to_string(),
            })
    }

    fn required_modules(&self, entry_path: &Path) -> HashSet<PathBuf> {
        let entry_path = entry_path.to_path_buf();
        let link_owners = self
            .modules
            .values()
            .flat_map(|module| module.value_exports.iter())
            .map(|binding| {
                (
                    binding.binding.link_name.clone(),
                    binding.owner_path.clone(),
                )
            })
            .collect::<HashMap<_, _>>();

        let mut required = HashSet::from([entry_path.clone()]);
        let mut queue = vec![entry_path];

        while let Some(path) = queue.pop() {
            let Some(module) = self.modules.get(&path) else {
                continue;
            };
            for link_name in collect_external_link_names(&module.checked) {
                let Some(owner_path) = link_owners.get(&link_name) else {
                    continue;
                };
                if owner_path == &path {
                    continue;
                }
                if required.insert(owner_path.clone()) {
                    queue.push(owner_path.clone());
                }
            }
        }

        required
    }
}

fn canonicalize_existing(path: &Path) -> Result<PathBuf, ProjectCompileError> {
    fs::canonicalize(path).map_err(|error| ProjectCompileError::Resolve {
        path: Some(path.to_path_buf()),
        message: error.to_string(),
    })
}

fn module_source_to_file(root: &Path, source: &str) -> PathBuf {
    let trimmed = source.trim_matches('"');
    let relative = if trimmed.ends_with(".aura") {
        PathBuf::from(trimmed)
    } else {
        PathBuf::from(format!("{trimmed}.aura"))
    };
    root.join(relative)
}

fn module_logical_name(
    package_root: &Path,
    module_path: &Path,
) -> Result<String, ProjectCompileError> {
    let src_root = package_root.join("src");
    let relative =
        module_path
            .strip_prefix(&src_root)
            .map_err(|_| ProjectCompileError::Resolve {
                path: Some(module_path.to_path_buf()),
                message: "module path is not inside package src/".to_string(),
            })?;
    let mut logical = relative.to_path_buf();
    logical.set_extension("");
    Ok(logical
        .components()
        .map(|component| component.as_os_str().to_string_lossy().to_string())
        .collect::<Vec<_>>()
        .join("/"))
}

fn stable_module_name(package_name: &str, logical_name: &str) -> String {
    format!(
        "{}__{}",
        sanitize_symbol_fragment(package_name),
        sanitize_symbol_fragment(logical_name)
    )
}

fn stable_link_name(package_name: &str, logical_name: &str, symbol_name: &str) -> String {
    format!(
        "{}__{}__{}",
        sanitize_symbol_fragment(package_name),
        sanitize_symbol_fragment(logical_name),
        sanitize_symbol_fragment(symbol_name)
    )
}

fn sanitize_symbol_fragment(value: &str) -> String {
    let mut out = String::with_capacity(value.len());
    for ch in value.chars() {
        if ch.is_ascii_alphanumeric() {
            out.push(ch.to_ascii_lowercase());
        } else {
            out.push('_');
        }
    }
    out
}

fn ty_to_type_ref(types: &TyInterner, ty_id: aura_typecheck::TyId) -> TypeRef {
    match types.get(ty_id) {
        Some(Ty::InferVar(v)) => TypeRef::InferVar(*v),
        Some(Ty::GenericParam(name)) => TypeRef::GenericParam(name.clone()),
        Some(Ty::Int8) => TypeRef::Primitive(PrimitiveType::Int8),
        Some(Ty::Int16) => TypeRef::Primitive(PrimitiveType::Int16),
        Some(Ty::Int32) => TypeRef::Primitive(PrimitiveType::Int32),
        Some(Ty::Int64) => TypeRef::Primitive(PrimitiveType::Int64),
        Some(Ty::Int128) => TypeRef::Primitive(PrimitiveType::Int128),
        Some(Ty::ISize) => TypeRef::Primitive(PrimitiveType::ISize),
        Some(Ty::UInt8) => TypeRef::Primitive(PrimitiveType::UInt8),
        Some(Ty::UInt16) => TypeRef::Primitive(PrimitiveType::UInt16),
        Some(Ty::UInt32) => TypeRef::Primitive(PrimitiveType::UInt32),
        Some(Ty::UInt64) => TypeRef::Primitive(PrimitiveType::UInt64),
        Some(Ty::UInt128) => TypeRef::Primitive(PrimitiveType::UInt128),
        Some(Ty::USize) => TypeRef::Primitive(PrimitiveType::USize),
        Some(Ty::Float32) => TypeRef::Primitive(PrimitiveType::Float32),
        Some(Ty::Float64) => TypeRef::Primitive(PrimitiveType::Float64),
        Some(Ty::Bool) => TypeRef::Primitive(PrimitiveType::Bool),
        Some(Ty::Char) => TypeRef::Primitive(PrimitiveType::Char),
        Some(Ty::Void) => TypeRef::Primitive(PrimitiveType::Void),
        Some(Ty::Never) => TypeRef::Primitive(PrimitiveType::Never),
        Some(Ty::Any) => TypeRef::Primitive(PrimitiveType::Any),
        Some(Ty::Nominal(name)) => TypeRef::Nominal(name.clone()),
        Some(Ty::RawAlloc(item)) => TypeRef::RawAlloc(Box::new(ty_to_type_ref(types, *item))),
        Some(Ty::Slice(item)) => TypeRef::Slice(Box::new(ty_to_type_ref(types, *item))),
        Some(Ty::Ref(item)) => TypeRef::Ref(Box::new(ty_to_type_ref(types, *item))),
        Some(Ty::List(item)) => TypeRef::List(Box::new(ty_to_type_ref(types, *item))),
        Some(Ty::Dict { key, value }) => TypeRef::Dict {
            key: Box::new(ty_to_type_ref(types, *key)),
            value: Box::new(ty_to_type_ref(types, *value)),
        },
        Some(Ty::Set(item)) => TypeRef::Set(Box::new(ty_to_type_ref(types, *item))),
        Some(Ty::Array { item, size }) => TypeRef::Array {
            item: Box::new(ty_to_type_ref(types, *item)),
            size: *size,
        },
        Some(Ty::Func { params, ret }) => TypeRef::Func {
            params: params
                .iter()
                .map(|param| FuncParamRef {
                    name: param.name.clone(),
                    label: param.label.clone(),
                    trailing: param.trailing,
                    ty: Box::new(ty_to_type_ref(types, param.ty)),
                })
                .collect(),
            ret: Box::new(ty_to_type_ref(types, *ret)),
        },
        Some(Ty::Macro { params, ret }) => TypeRef::Macro {
            params: params
                .iter()
                .map(|param| FuncParamRef {
                    name: param.name.clone(),
                    label: param.label.clone(),
                    trailing: param.trailing,
                    ty: Box::new(ty_to_type_ref(types, param.ty)),
                })
                .collect(),
            ret: Box::new(ty_to_type_ref(types, *ret)),
        },
        Some(Ty::Tuple(items)) => {
            TypeRef::Tuple(items.iter().map(|ty| ty_to_type_ref(types, *ty)).collect())
        }
        Some(Ty::Struct(fields)) => TypeRef::Struct(
            fields
                .iter()
                .map(|(name, ty)| (name.clone(), ty_to_type_ref(types, *ty)))
                .collect(),
        ),
        Some(Ty::Union(items)) => {
            TypeRef::Union(items.iter().map(|ty| ty_to_type_ref(types, *ty)).collect())
        }
        Some(Ty::Enum(variants)) => TypeRef::Enum(
            variants
                .iter()
                .map(|(name, ty)| {
                    (
                        name.clone(),
                        ty.as_ref().map(|ty| ty_to_type_ref(types, *ty)),
                    )
                })
                .collect(),
        ),
        None => TypeRef::Unknown,
    }
}

fn ty_ref_to_ty_id(types: &mut TyInterner, ty: &TypeRef) -> aura_typecheck::TyId {
    match ty {
        TypeRef::Primitive(primitive) => match primitive {
            PrimitiveType::Int8 => types.intern(Ty::Int8),
            PrimitiveType::Int16 => types.intern(Ty::Int16),
            PrimitiveType::Int32 => types.intern(Ty::Int32),
            PrimitiveType::Int64 => types.intern(Ty::Int64),
            PrimitiveType::Int128 => types.intern(Ty::Int128),
            PrimitiveType::ISize => types.intern(Ty::ISize),
            PrimitiveType::UInt8 => types.intern(Ty::UInt8),
            PrimitiveType::UInt16 => types.intern(Ty::UInt16),
            PrimitiveType::UInt32 => types.intern(Ty::UInt32),
            PrimitiveType::UInt64 => types.intern(Ty::UInt64),
            PrimitiveType::UInt128 => types.intern(Ty::UInt128),
            PrimitiveType::USize => types.intern(Ty::USize),
            PrimitiveType::Float32 => types.intern(Ty::Float32),
            PrimitiveType::Float64 => types.intern(Ty::Float64),
            PrimitiveType::Bool => types.intern(Ty::Bool),
            PrimitiveType::Char => types.intern(Ty::Char),
            PrimitiveType::Void => types.intern(Ty::Void),
            PrimitiveType::Never => types.intern(Ty::Never),
            PrimitiveType::Any => types.intern(Ty::Any),
        },
        TypeRef::InferVar(v) => types.intern(Ty::InferVar(*v)),
        TypeRef::GenericParam(name) => types.intern(Ty::GenericParam(name.clone())),
        TypeRef::Nominal(name) => types.intern(Ty::Nominal(name.clone())),
        TypeRef::RawAlloc(item) => {
            let item = ty_ref_to_ty_id(types, item);
            types.intern(Ty::RawAlloc(item))
        }
        TypeRef::Slice(item) => {
            let item = ty_ref_to_ty_id(types, item);
            types.intern(Ty::Slice(item))
        }
        TypeRef::Ref(item) => {
            let item = ty_ref_to_ty_id(types, item);
            types.intern(Ty::Ref(item))
        }
        TypeRef::List(item) => {
            let item = ty_ref_to_ty_id(types, item);
            types.intern(Ty::List(item))
        }
        TypeRef::Dict { key, value } => {
            let key = ty_ref_to_ty_id(types, key);
            let value = ty_ref_to_ty_id(types, value);
            types.intern(Ty::Dict { key, value })
        }
        TypeRef::Set(item) => {
            let item = ty_ref_to_ty_id(types, item);
            types.intern(Ty::Set(item))
        }
        TypeRef::Array { item, size } => {
            let item = ty_ref_to_ty_id(types, item);
            types.intern(Ty::Array { item, size: *size })
        }
        TypeRef::Func { params, ret } => {
            let params = params
                .iter()
                .map(|param| FuncParam {
                    name: param.name.clone(),
                    label: param.label.clone(),
                    trailing: param.trailing,
                    ty: ty_ref_to_ty_id(types, &param.ty),
                })
                .collect::<Vec<_>>();
            let ret = ty_ref_to_ty_id(types, ret);
            types.intern(Ty::Func { params, ret })
        }
        TypeRef::Macro { params, ret } => {
            let params = params
                .iter()
                .map(|param| FuncParam {
                    name: param.name.clone(),
                    label: param.label.clone(),
                    trailing: param.trailing,
                    ty: ty_ref_to_ty_id(types, &param.ty),
                })
                .collect::<Vec<_>>();
            let ret = ty_ref_to_ty_id(types, ret);
            types.intern(Ty::Macro { params, ret })
        }
        TypeRef::Tuple(items) => {
            let items = items
                .iter()
                .map(|item| ty_ref_to_ty_id(types, item))
                .collect::<Vec<_>>();
            types.intern(Ty::Tuple(items))
        }
        TypeRef::Struct(fields) => {
            let fields = fields
                .iter()
                .map(|(name, ty)| (name.clone(), ty_ref_to_ty_id(types, ty)))
                .collect::<Vec<_>>();
            types.intern(Ty::Struct(fields))
        }
        TypeRef::Union(items) => {
            let items = items
                .iter()
                .map(|item| ty_ref_to_ty_id(types, item))
                .collect::<Vec<_>>();
            types.intern(Ty::Union(items))
        }
        TypeRef::Enum(variants) => {
            let variants = variants
                .iter()
                .map(|(name, ty)| {
                    (
                        name.clone(),
                        ty.as_ref().map(|ty| ty_ref_to_ty_id(types, ty)),
                    )
                })
                .collect::<Vec<_>>();
            types.intern(Ty::Enum(variants))
        }
        TypeRef::Unknown => types.intern(Ty::Any),
    }
}

fn collect_external_link_names(module: &CheckedModule) -> HashSet<String> {
    let extern_links = module
        .ir
        .declarations
        .iter()
        .filter(|decl| decl.is_extern)
        .map(|decl| decl.link_name.clone())
        .collect::<HashSet<_>>();
    let mut out = HashSet::new();
    for decl in &module.ir.declarations {
        collect_expr_external_link_names(&decl.value, &extern_links, &mut out);
    }
    out
}

fn collect_expr_external_link_names(
    expr: &CheckedExpr,
    extern_links: &HashSet<String>,
    out: &mut HashSet<String>,
) {
    match expr {
        CheckedExpr::Ident(name) => {
            if extern_links.contains(name) {
                out.insert(name.clone());
            }
        }
        CheckedExpr::EnumCtor { payload, .. } => {
            if let Some(payload) = payload.as_deref() {
                collect_expr_external_link_names(payload, extern_links, out);
            }
        }
        CheckedExpr::DotIdent { payload, .. } => {
            if let Some(payload) = payload.as_deref() {
                collect_expr_external_link_names(payload, extern_links, out);
            }
        }
        CheckedExpr::Tuple(items) => {
            for item in items {
                collect_expr_external_link_names(item, extern_links, out);
            }
        }
        CheckedExpr::Block(items) | CheckedExpr::List(items) | CheckedExpr::MultiArm(items) => {
            for item in items {
                collect_expr_external_link_names(item, extern_links, out);
            }
        }
        CheckedExpr::Struct(fields) => {
            for (_, value) in fields {
                collect_expr_external_link_names(value, extern_links, out);
            }
        }
        CheckedExpr::LocalBind { bindings, .. } => {
            for binding in bindings {
                collect_expr_external_link_names(&binding.value, extern_links, out);
            }
        }
        CheckedExpr::AssignLocal { value, .. } => {
            collect_expr_external_link_names(value, extern_links, out);
        }
        CheckedExpr::FieldAccess { object, .. } => {
            collect_expr_external_link_names(object, extern_links, out);
        }
        CheckedExpr::ForceUnwrap { expr, .. } => {
            collect_expr_external_link_names(expr, extern_links, out);
        }
        CheckedExpr::AssignField { object, value, .. } => {
            collect_expr_external_link_names(object, extern_links, out);
            collect_expr_external_link_names(value, extern_links, out);
        }
        CheckedExpr::Call { callee, args } => {
            collect_expr_external_link_names(callee, extern_links, out);
            for arg in args {
                collect_expr_external_link_names(arg, extern_links, out);
            }
        }
        CheckedExpr::MemoryOp { args, .. } => {
            for arg in args {
                collect_expr_external_link_names(arg, extern_links, out);
            }
        }
        CheckedExpr::BinaryOp { lhs, rhs, .. } => {
            collect_expr_external_link_names(lhs, extern_links, out);
            collect_expr_external_link_names(rhs, extern_links, out);
        }
        CheckedExpr::MacroApply { operand, .. } => {
            collect_expr_external_link_names(operand, extern_links, out);
        }
        CheckedExpr::Label { expr, .. } => {
            collect_expr_external_link_names(expr, extern_links, out);
        }
        CheckedExpr::EnumMatch {
            scrutinee,
            arms,
            default_arm,
            ..
        } => {
            collect_expr_external_link_names(scrutinee, extern_links, out);
            for arm in arms {
                collect_expr_external_link_names(&arm.body, extern_links, out);
            }
            if let Some(default_arm) = default_arm.as_deref() {
                collect_expr_external_link_names(default_arm, extern_links, out);
            }
        }
        CheckedExpr::If {
            condition,
            then_branch,
            else_branch,
            ..
        } => {
            collect_expr_external_link_names(condition, extern_links, out);
            collect_expr_external_link_names(then_branch, extern_links, out);
            if let Some(else_branch) = else_branch.as_deref() {
                collect_expr_external_link_names(else_branch, extern_links, out);
            }
        }
        CheckedExpr::Cases { arms, .. } => {
            for arm in arms {
                collect_expr_external_link_names(&arm.guard, extern_links, out);
                collect_expr_external_link_names(&arm.body, extern_links, out);
            }
        }
        CheckedExpr::Loop {
            condition, body, ..
        } => {
            if let Some(condition) = condition.as_deref() {
                collect_expr_external_link_names(condition, extern_links, out);
            }
            collect_expr_external_link_names(body, extern_links, out);
        }
        CheckedExpr::Return { value, .. } => {
            collect_expr_external_link_names(value, extern_links, out);
        }
        CheckedExpr::Break { value, .. } => {
            if let Some(value) = value.as_deref() {
                collect_expr_external_link_names(value, extern_links, out);
            }
        }
        CheckedExpr::Coerce { expr, .. } | CheckedExpr::Cast { expr, .. } => {
            collect_expr_external_link_names(expr, extern_links, out);
        }
        CheckedExpr::Int(_)
        | CheckedExpr::Float(_)
        | CheckedExpr::Char(_)
        | CheckedExpr::String(_)
        | CheckedExpr::Closure { .. }
        | CheckedExpr::Any
        | CheckedExpr::Dict(_)
        | CheckedExpr::Continue { .. } => {}
    }
}

#[cfg(test)]
mod tests {
    use super::{ProjectCompileOptions, compile_project};
    use aura_typecheck::Ty;
    use std::fs;
    use std::path::Path;
    use std::time::{SystemTime, UNIX_EPOCH};

    fn temp_test_dir(prefix: &str) -> std::path::PathBuf {
        let mut dir = std::env::temp_dir();
        let nanos = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("clock must be after unix epoch")
            .as_nanos();
        dir.push(format!("aura_project_compile_{prefix}_{nanos}"));
        dir
    }

    fn create_file(path: &Path, content: &str) {
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent).expect("should create parent dirs");
        }
        fs::write(path, content).expect("should write file");
    }

    #[test]
    fn path_dependencies_and_direct_lib_auto_imports_compile() {
        let root = temp_test_dir("path_dep_auto_import");
        let dependency_root = root.join("vendor").join("dep");

        create_file(
            &dependency_root.join("project.auon"),
            r#"
                name = "dep",
                version = "0.1.0",
                kind = .library,
                dependencies = [],
            "#,
        );
        create_file(
            &dependency_root.join("src").join("helper.aura"),
            "def greet() -> Int { 7 }",
        );
        create_file(
            &dependency_root.join("src").join("lib.aura"),
            r#"use (greet) = "helper";"#,
        );

        create_file(
            &root.join("project.auon"),
            r#"
                name = "app",
                version = "0.1.0",
                kind = .binary,
                dependencies = [
                    "dep" = .path("vendor/dep"),
                ],
            "#,
        );
        create_file(
            &root.join("src").join("main.aura"),
            "def main() -> Int { greet() }",
        );

        let build = compile_project(
            &root.join("project.auon"),
            ProjectCompileOptions {
                enforce_entry_main_signature: false,
            },
        )
        .expect("project should compile");

        assert_eq!(build.modules.len(), 2);
        assert!(
            build
                .modules
                .iter()
                .any(|module| module.path.ends_with(Path::new("src").join("main.aura")))
        );
        assert!(
            build
                .modules
                .iter()
                .any(|module| module.path.ends_with(Path::new("src").join("helper.aura")))
        );

        fs::remove_dir_all(root).expect("cleanup should succeed");
    }

    #[test]
    fn only_lib_exports_are_auto_imported() {
        let root = temp_test_dir("lib_auto_import_scope");
        let dependency_root = root.join("vendor").join("dep");

        create_file(
            &dependency_root.join("project.auon"),
            r#"
                name = "dep",
                version = "0.1.0",
                kind = .library,
                dependencies = [],
            "#,
        );
        create_file(
            &dependency_root.join("src").join("hidden.aura"),
            "def hidden() -> Int { 7 }",
        );
        create_file(
            &dependency_root.join("src").join("lib.aura"),
            "def exported = 1;",
        );

        create_file(
            &root.join("project.auon"),
            r#"
                name = "app",
                version = "0.1.0",
                kind = .binary,
                dependencies = [
                    "dep" = .path("vendor/dep"),
                ],
            "#,
        );
        create_file(
            &root.join("src").join("main.aura"),
            "def main() -> Int { exported }",
        );

        let build = compile_project(
            &root.join("project.auon"),
            ProjectCompileOptions {
                enforce_entry_main_signature: false,
            },
        )
        .expect("project should compile");

        let main_module = build
            .modules
            .iter()
            .find(|module| module.path.ends_with(Path::new("src").join("main.aura")))
            .expect("main module should be present");
        assert!(
            main_module
                .checked
                .ir
                .declarations
                .iter()
                .any(|decl| decl.is_extern && decl.name == "exported")
        );
        assert!(
            !main_module
                .checked
                .ir
                .declarations
                .iter()
                .any(|decl| decl.name == "hidden")
        );

        fs::remove_dir_all(root).expect("cleanup should succeed");
    }

    #[test]
    fn exported_type_aliases_from_lib_are_visible_to_consumers() {
        let root = temp_test_dir("lib_type_alias_auto_import");
        let dependency_root = root.join("vendor").join("stl");

        create_file(
            &dependency_root.join("project.auon"),
            r#"
                name = "stl",
                version = "0.1.0",
                kind = .library,
                dependencies = [],
            "#,
        );
        create_file(
            &dependency_root.join("src").join("lib.aura"),
            r#"
                def ExitCode = enum(success, custom: Int);
                def exit(code: ExitCode) -> Void { () }
            "#,
        );

        create_file(
            &root.join("project.auon"),
            r#"
                name = "app",
                version = "0.1.0",
                kind = .binary,
                dependencies = [
                    "stl" = .path("vendor/stl"),
                ],
            "#,
        );
        create_file(
            &root.join("src").join("main.aura"),
            r#"
                def main() -> Void {
                    exit(.custom(100))
                }
            "#,
        );

        let build = compile_project(
            &root.join("project.auon"),
            ProjectCompileOptions {
                enforce_entry_main_signature: false,
            },
        )
        .expect("project should compile");

        let main_module = build
            .modules
            .iter()
            .find(|module| module.path.ends_with(Path::new("src").join("main.aura")))
            .expect("main module should be present");
        assert!(
            main_module
                .checked
                .ir
                .declarations
                .iter()
                .any(|decl| decl.is_extern && decl.name == "exit")
        );
        assert!(
            !main_module
                .checked
                .ir
                .declarations
                .iter()
                .any(|decl| decl.is_extern && decl.name == "ExitCode")
        );

        fs::remove_dir_all(root).expect("cleanup should succeed");
    }

    #[test]
    fn exported_generic_type_aliases_instantiate_in_consumers() {
        let root = temp_test_dir("lib_generic_type_alias_auto_import");
        let dependency_root = root.join("vendor").join("stl");

        create_file(
            &dependency_root.join("project.auon"),
            r#"
                name = "stl",
                version = "0.1.0",
                kind = .library,
                dependencies = [],
            "#,
        );
        create_file(
            &dependency_root.join("src").join("lib.aura"),
            r#"
                def[T] Box = (value: T);
            "#,
        );

        create_file(
            &root.join("project.auon"),
            r#"
                name = "app",
                version = "0.1.0",
                kind = .binary,
                dependencies = [
                    "stl" = .path("vendor/stl"),
                ],
            "#,
        );
        create_file(
            &root.join("src").join("main.aura"),
            r#"
                def x: Box[Int] = (value = 1);
                def main() -> Void { () }
            "#,
        );

        let build = compile_project(
            &root.join("project.auon"),
            ProjectCompileOptions {
                enforce_entry_main_signature: false,
            },
        )
        .expect("project should compile");

        let main_module = build
            .modules
            .iter()
            .find(|module| module.path.ends_with(Path::new("src").join("main.aura")))
            .expect("main module should be present");
        let x_ty = main_module
            .checked
            .value_types
            .get("x")
            .expect("x should be typed");
        assert!(matches!(
            main_module.checked.types.get(*x_ty),
            Some(Ty::Struct(fields)) if fields.len() == 1 && fields[0].0 == "value"
        ));

        fs::remove_dir_all(root).expect("cleanup should succeed");
    }
}
