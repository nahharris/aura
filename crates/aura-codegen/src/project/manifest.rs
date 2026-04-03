use std::collections::HashSet;
use std::fmt;
use std::fs;
use std::path::Path;

use aura_frontend::ast::{Decl, Expr};
use aura_frontend::Parser;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Manifest {
    pub name: String,
    pub version: String,
    pub dependencies: Vec<Dependency>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Dependency {
    pub alias: String,
    pub source: DependencySource,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DependencySource {
    Git { url: String, tag: String },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ManifestError {
    ReadFailed(String),
    ParseFailed(String),
    MissingProjectDecl,
    ProjectMustBeStructType,
    MissingField(&'static str),
    DuplicateField(&'static str),
    InvalidFieldType {
        field: &'static str,
        expected: &'static str,
    },
    UnknownField(String),
    InvalidDependencyAlias(String),
    DuplicateDependencyAlias(String),
    InvalidDependencySource(String),
}

impl fmt::Display for ManifestError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ManifestError::ReadFailed(message) => write!(f, "failed reading build.aura: {message}"),
            ManifestError::ParseFailed(message) => {
                write!(f, "failed parsing build.aura: {message}")
            }
            ManifestError::MissingProjectDecl => {
                write!(f, "build.aura must contain `def project = (...)`")
            }
            ManifestError::ProjectMustBeStructType => {
                write!(f, "project declaration must be a struct literal")
            }
            ManifestError::MissingField(field) => {
                write!(f, "manifest field `{field}` is required")
            }
            ManifestError::DuplicateField(field) => {
                write!(f, "manifest field `{field}` appears more than once")
            }
            ManifestError::InvalidFieldType { field, expected } => {
                write!(f, "manifest field `{field}` must be {expected}")
            }
            ManifestError::UnknownField(field) => {
                write!(f, "unknown manifest field `{field}`")
            }
            ManifestError::InvalidDependencyAlias(alias) => {
                write!(f, "dependency alias `{alias}` must start with '@'")
            }
            ManifestError::DuplicateDependencyAlias(alias) => {
                write!(f, "dependency alias `{alias}` is duplicated")
            }
            ManifestError::InvalidDependencySource(source) => {
                write!(
                    f,
                    "dependency source `{source}` must have `<git-url>@<tag>`"
                )
            }
        }
    }
}

impl std::error::Error for ManifestError {}

pub fn load_manifest(path: &Path) -> Result<Manifest, ManifestError> {
    let source = fs::read_to_string(path)
        .map_err(|e| ManifestError::ReadFailed(format!("{} ({})", path.display(), e)))?;
    parse_manifest_source(&source)
}

pub fn parse_manifest_source(source: &str) -> Result<Manifest, ManifestError> {
    let parsed =
        Parser::parse_source(source).map_err(|d| ManifestError::ParseFailed(format!("{d:?}")))?;

    let project_expr = parsed
        .declarations
        .iter()
        .find_map(|decl| match decl {
            Decl::Assign { name, value, .. } if name == "project" => Some(value),
            _ => None,
        })
        .ok_or(ManifestError::MissingProjectDecl)?;

    let Expr::Struct(fields) = unspan_expr(project_expr) else {
        return Err(ManifestError::ProjectMustBeStructType);
    };

    let mut name: Option<String> = None;
    let mut version: Option<String> = None;
    let mut dependencies: Option<Vec<Dependency>> = None;

    for (field_name, field_value) in fields {
        match field_name.as_str() {
            "name" => {
                if name.is_some() {
                    return Err(ManifestError::DuplicateField("name"));
                }
                name = Some(expect_string(field_value, "name")?);
            }
            "version" => {
                if version.is_some() {
                    return Err(ManifestError::DuplicateField("version"));
                }
                version = Some(expect_string(field_value, "version")?);
            }
            "dependencies" => {
                if dependencies.is_some() {
                    return Err(ManifestError::DuplicateField("dependencies"));
                }
                dependencies = Some(parse_dependencies(field_value)?);
            }
            other => return Err(ManifestError::UnknownField(other.to_string())),
        }
    }

    Ok(Manifest {
        name: name.ok_or(ManifestError::MissingField("name"))?,
        version: version.ok_or(ManifestError::MissingField("version"))?,
        dependencies: dependencies.ok_or(ManifestError::MissingField("dependencies"))?,
    })
}

fn parse_dependencies(value: &Expr) -> Result<Vec<Dependency>, ManifestError> {
    let entries = match unspan_expr(value) {
        Expr::Dict(entries) => entries,
        Expr::List(items) if items.is_empty() => return Ok(Vec::new()),
        _ => {
            return Err(ManifestError::InvalidFieldType {
                field: "dependencies",
                expected: "a dictionary literal like [\"@a\" = \"url@tag\"]",
            })
        }
    };

    let mut out = Vec::with_capacity(entries.len());
    let mut aliases = HashSet::new();

    for (alias_expr, source_expr) in entries {
        let alias = expect_string(alias_expr, "dependencies")?;
        if !alias.starts_with('@') || alias.len() < 2 {
            return Err(ManifestError::InvalidDependencyAlias(alias));
        }
        if !aliases.insert(alias.clone()) {
            return Err(ManifestError::DuplicateDependencyAlias(alias));
        }

        let source_raw = expect_string(source_expr, "dependencies")?;
        let source = parse_dependency_source(&source_raw)?;
        out.push(Dependency { alias, source });
    }

    Ok(out)
}

fn parse_dependency_source(value: &str) -> Result<DependencySource, ManifestError> {
    let Some((url, tag)) = value.rsplit_once('@') else {
        return Err(ManifestError::InvalidDependencySource(value.to_string()));
    };
    if url.is_empty() || tag.is_empty() {
        return Err(ManifestError::InvalidDependencySource(value.to_string()));
    }
    Ok(DependencySource::Git {
        url: url.to_string(),
        tag: tag.to_string(),
    })
}

fn expect_string(expr: &Expr, field: &'static str) -> Result<String, ManifestError> {
    match unspan_expr(expr) {
        Expr::String(s) => Ok(s.clone()),
        _ => Err(ManifestError::InvalidFieldType {
            field,
            expected: "a string literal",
        }),
    }
}

fn unspan_expr(expr: &Expr) -> &Expr {
    let mut current = expr;
    while let Expr::Spanned { expr, .. } = current {
        current = expr.as_ref();
    }
    current
}

#[cfg(test)]
mod tests {
    use super::{parse_manifest_source, DependencySource, ManifestError};

    #[test]
    fn parses_struct_manifest_shape() {
        let src = r#"
            def project = (
                name = "hello",
                version = "0.1.0",
                dependencies = [
                    "@json" = "https://github.com/acme/aura-json@v1.2.3",
                ],
            );
        "#;
        let manifest = parse_manifest_source(src).expect("must parse");
        assert_eq!(manifest.name, "hello");
        assert_eq!(manifest.version, "0.1.0");
        assert_eq!(manifest.dependencies.len(), 1);
        assert_eq!(manifest.dependencies[0].alias, "@json");
        assert!(matches!(
            manifest.dependencies[0].source,
            DependencySource::Git { ref url, ref tag } if url == "https://github.com/acme/aura-json" && tag == "v1.2.3"
        ));
    }

    #[test]
    fn rejects_non_struct_project_value() {
        let src = "def project = [\"name\" = \"x\"];";
        let err = parse_manifest_source(src).expect_err("must fail");
        assert!(matches!(err, ManifestError::ProjectMustBeStructType));
    }

    #[test]
    fn rejects_missing_project_decl() {
        let src = "def x = 1;";
        let err = parse_manifest_source(src).expect_err("must fail");
        assert!(matches!(err, ManifestError::MissingProjectDecl));
    }

    #[test]
    fn rejects_dependencies_as_non_dict() {
        let src = r#"
            def project = (
                name = "hello",
                version = "0.1.0",
                dependencies = "bad",
            );
        "#;
        let err = parse_manifest_source(src).expect_err("must fail");
        assert!(matches!(
            err,
            ManifestError::InvalidFieldType {
                field: "dependencies",
                ..
            }
        ));
    }

    #[test]
    fn rejects_alias_without_at() {
        let src = r#"
            def project = (
                name = "hello",
                version = "0.1.0",
                dependencies = [
                    "json" = "https://github.com/acme/aura-json@v1.2.3",
                ],
            );
        "#;
        let err = parse_manifest_source(src).expect_err("must fail");
        assert!(matches!(err, ManifestError::InvalidDependencyAlias(alias) if alias == "json"));
    }

    #[test]
    fn rejects_git_source_without_tag() {
        let src = r#"
            def project = (
                name = "hello",
                version = "0.1.0",
                dependencies = [
                    "@json" = "https://github.com/acme/aura-json",
                ],
            );
        "#;
        let err = parse_manifest_source(src).expect_err("must fail");
        assert!(
            matches!(err, ManifestError::InvalidDependencySource(v) if v == "https://github.com/acme/aura-json")
        );
    }
}
