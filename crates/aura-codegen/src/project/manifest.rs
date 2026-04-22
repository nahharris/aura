use std::collections::HashSet;
use std::fmt;
use std::fs;
use std::path::Path;

use auon::{Value, parse_value};

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Manifest {
    pub name: String,
    pub version: String,
    pub kind: ProjectType,
    pub dependencies: Vec<Dependency>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ProjectType {
    Binary,
    Library,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Dependency {
    pub alias: String,
    pub source: DependencySource,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DependencySource {
    Path { path: String },
    Git { url: String, reference: String },
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ManifestError {
    ReadFailed(String),
    ParseFailed(String),
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
            ManifestError::ReadFailed(message) => {
                write!(f, "failed reading project.auon: {message}")
            }
            ManifestError::ParseFailed(message) => {
                write!(f, "failed parsing project.auon: {message}")
            }
            ManifestError::ProjectMustBeStructType => {
                write!(f, "project.auon must contain a root struct document")
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
                write!(
                    f,
                    "dependency alias `{alias}` must be non-empty and must not include `@`"
                )
            }
            ManifestError::DuplicateDependencyAlias(alias) => {
                write!(f, "dependency alias `{alias}` is duplicated")
            }
            ManifestError::InvalidDependencySource(source) => {
                write!(f, "invalid dependency source: {source}")
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
    let parsed = parse_value(source).map_err(|err| ManifestError::ParseFailed(err.to_string()))?;

    let Value::Struct(fields) = parsed else {
        return Err(ManifestError::ProjectMustBeStructType);
    };

    let mut name: Option<String> = None;
    let mut version: Option<String> = None;
    let mut kind: Option<ProjectType> = None;
    let mut dependencies: Option<Vec<Dependency>> = None;

    for (field_name, field_value) in &fields {
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
            "kind" => {
                if kind.is_some() {
                    return Err(ManifestError::DuplicateField("kind"));
                }
                kind = Some(parse_project_type(field_value)?);
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
        kind: kind.ok_or(ManifestError::MissingField("kind"))?,
        dependencies: dependencies.ok_or(ManifestError::MissingField("dependencies"))?,
    })
}

fn parse_project_type(value: &Value) -> Result<ProjectType, ManifestError> {
    let Value::Variant { name, payload } = value else {
        return Err(ManifestError::InvalidFieldType {
            field: "kind",
            expected: "a dot variant: .binary or .library",
        });
    };
    if payload.is_some() {
        return Err(ManifestError::InvalidFieldType {
            field: "kind",
            expected: "a unit dot variant: .binary or .library",
        });
    }
    match name.as_str() {
        "binary" => Ok(ProjectType::Binary),
        "library" => Ok(ProjectType::Library),
        _ => Err(ManifestError::InvalidFieldType {
            field: "kind",
            expected: "one of: .binary, .library",
        }),
    }
}

fn parse_dependencies(value: &Value) -> Result<Vec<Dependency>, ManifestError> {
    let entries = match value {
        Value::Dict(entries) => entries,
        Value::List(items) if items.is_empty() => return Ok(Vec::new()),
        _ => {
            return Err(ManifestError::InvalidFieldType {
                field: "dependencies",
                expected: "a dictionary literal like [\"a\" = .path(\"vendor/a\")]",
            });
        }
    };

    let mut out = Vec::with_capacity(entries.len());
    let mut aliases = HashSet::new();

    for (alias_expr, source_expr) in entries {
        let alias = expect_string(alias_expr, "dependencies")?;
        if alias.is_empty() || alias.contains('@') {
            return Err(ManifestError::InvalidDependencyAlias(alias));
        }
        if !aliases.insert(alias.clone()) {
            return Err(ManifestError::DuplicateDependencyAlias(alias));
        }

        let source = parse_dependency_source(source_expr)?;
        out.push(Dependency { alias, source });
    }

    Ok(out)
}

fn parse_dependency_source(value: &Value) -> Result<DependencySource, ManifestError> {
    let Value::Variant { name, payload } = value else {
        return Err(ManifestError::InvalidDependencySource(
            "dependency sources must be .path(...) or .git((url = ..., ref = ...))".to_string(),
        ));
    };

    match name.as_str() {
        "path" => {
            let Some(payload) = payload.as_deref() else {
                return Err(ManifestError::InvalidDependencySource(
                    ".path must carry a string payload".to_string(),
                ));
            };
            let path = expect_string(payload, "dependencies")?;
            if path.is_empty() {
                return Err(ManifestError::InvalidDependencySource(
                    ".path payload must be a non-empty string".to_string(),
                ));
            }
            Ok(DependencySource::Path { path })
        }
        "git" => parse_git_source(payload.as_deref()),
        other => Err(ManifestError::InvalidDependencySource(format!(
            ".{other} is not a supported dependency source"
        ))),
    }
}

fn parse_git_source(payload: Option<&Value>) -> Result<DependencySource, ManifestError> {
    let Some(payload) = payload else {
        return Err(ManifestError::InvalidDependencySource(
            ".git must carry a struct payload".to_string(),
        ));
    };
    let Value::Struct(fields) = payload else {
        return Err(ManifestError::InvalidDependencySource(
            ".git must carry a struct payload".to_string(),
        ));
    };

    let mut url: Option<String> = None;
    let mut reference: Option<String> = None;

    for (field_name, field_value) in fields {
        match field_name.as_str() {
            "url" => {
                if url.is_some() {
                    return Err(ManifestError::InvalidDependencySource(
                        ".git field `url` appears more than once".to_string(),
                    ));
                }
                url = Some(expect_string(field_value, "dependencies")?);
            }
            "ref" => {
                if reference.is_some() {
                    return Err(ManifestError::InvalidDependencySource(
                        ".git field `ref` appears more than once".to_string(),
                    ));
                }
                reference = Some(expect_string(field_value, "dependencies")?);
            }
            other => {
                return Err(ManifestError::InvalidDependencySource(format!(
                    ".git does not support field `{other}`"
                )));
            }
        }
    }

    let url = url.ok_or_else(|| {
        ManifestError::InvalidDependencySource(".git requires `url`".to_string())
    })?;
    let reference = reference.ok_or_else(|| {
        ManifestError::InvalidDependencySource(".git requires `ref`".to_string())
    })?;

    if url.is_empty() || reference.is_empty() {
        return Err(ManifestError::InvalidDependencySource(
            ".git `url` and `ref` must be non-empty strings".to_string(),
        ));
    }

    Ok(DependencySource::Git { url, reference })
}

fn expect_string(value: &Value, field: &'static str) -> Result<String, ManifestError> {
    match value {
        Value::String(s) => Ok(s.clone()),
        _ => Err(ManifestError::InvalidFieldType {
            field,
            expected: "a string literal",
        }),
    }
}

#[cfg(test)]
mod tests {
    use super::{DependencySource, ManifestError, ProjectType, parse_manifest_source};
    use std::fs;
    use std::time::{SystemTime, UNIX_EPOCH};

    fn temp_manifest_path(prefix: &str) -> std::path::PathBuf {
        let mut path = std::env::temp_dir();
        let nanos = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("clock must be after unix epoch")
            .as_nanos();
        path.push(format!("aura_manifest_{prefix}_{nanos}.auon"));
        path
    }

    #[test]
    fn parses_auon_manifest_shape() {
        let src = r#"
            name = "hello",
            version = "0.1.0",
            kind = .binary,
            dependencies = [
                "json" = .git((url = "https://github.com/acme/aura-json", ref = "v1.2.3")),
            ],
        "#;
        let manifest = parse_manifest_source(src).expect("must parse");
        assert_eq!(manifest.name, "hello");
        assert_eq!(manifest.version, "0.1.0");
        assert_eq!(manifest.kind, ProjectType::Binary);
        assert_eq!(manifest.dependencies.len(), 1);
        assert_eq!(manifest.dependencies[0].alias, "json");
        assert!(matches!(
            &manifest.dependencies[0].source,
            DependencySource::Git { url, reference } if url == "https://github.com/acme/aura-json" && reference == "v1.2.3"
        ));
    }

    #[test]
    fn parses_path_dependency_sources() {
        let src = r#"
            name = "hello",
            version = "0.1.0",
            kind = .binary,
            dependencies = [
                "stl" = .path("../../aura-stl"),
            ],
        "#;
        let manifest = parse_manifest_source(src).expect("must parse");
        assert_eq!(manifest.dependencies.len(), 1);
        assert_eq!(manifest.dependencies[0].alias, "stl");
        assert!(matches!(
            &manifest.dependencies[0].source,
            DependencySource::Path { path } if path == "../../aura-stl"
        ));
    }

    #[test]
    fn rejects_non_struct_project_value() {
        let src = "[\"name\" = \"x\"]";
        let err = parse_manifest_source(src).expect_err("must fail");
        assert!(matches!(err, ManifestError::ProjectMustBeStructType));
    }

    #[test]
    fn rejects_missing_name_field() {
        let src = r#"
            version = "0.1.0",
            kind = .binary,
            dependencies = [],
        "#;
        let err = parse_manifest_source(src).expect_err("must fail");
        assert!(matches!(err, ManifestError::MissingField("name")));
    }

    #[test]
    fn rejects_dependencies_as_non_dict() {
        let src = r#"
            name = "hello",
            version = "0.1.0",
            kind = .binary,
            dependencies = "bad",
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
    fn rejects_empty_alias() {
        let src = r#"
            name = "hello",
            version = "0.1.0",
            kind = .binary,
            dependencies = [
                "" = .git((url = "https://github.com/acme/aura-json", ref = "v1.2.3")),
            ],
        "#;
        let err = parse_manifest_source(src).expect_err("must fail");
        assert!(matches!(err, ManifestError::InvalidDependencyAlias(alias) if alias.is_empty()));
    }

    #[test]
    fn rejects_git_source_without_ref() {
        let src = r#"
            name = "hello",
            version = "0.1.0",
            kind = .binary,
            dependencies = [
                "json" = .git((url = "https://github.com/acme/aura-json")),
            ],
        "#;
        let err = parse_manifest_source(src).expect_err("must fail");
        assert!(matches!(err, ManifestError::InvalidDependencySource(source) if source.contains("git")));
    }

    #[test]
    fn rejects_empty_path_dependency_source() {
        let src = r#"
            name = "hello",
            version = "0.1.0",
            kind = .binary,
            dependencies = [
                "stl" = .path(""),
            ],
        "#;
        let err = parse_manifest_source(src).expect_err("must fail");
        assert!(matches!(
            err,
            ManifestError::InvalidDependencySource(v) if v.contains("path")
        ));
    }

    #[test]
    fn rejects_missing_kind_field() {
        let src = r#"
            name = "hello",
            version = "0.1.0",
            dependencies = [],
        "#;
        let err = parse_manifest_source(src).expect_err("must fail");
        assert!(matches!(err, ManifestError::MissingField("kind")));
    }

    #[test]
    fn rejects_invalid_kind_variant() {
        let src = r#"
            name = "hello",
            version = "0.1.0",
            kind = .plugin,
            dependencies = [],
        "#;
        let err = parse_manifest_source(src).expect_err("must fail");
        assert!(matches!(
            err,
            ManifestError::InvalidFieldType { field: "kind", .. }
        ));
    }

    #[test]
    fn load_manifest_reports_project_auon_for_parse_errors() {
        let path = temp_manifest_path("parse_error");
        fs::write(&path, "name = \"hello\", kind = .binary, dependencies = [").expect("write");

        let err = super::load_manifest(&path).expect_err("must fail");
        assert!(err.to_string().contains("project.auon"));

        fs::remove_file(path).expect("cleanup");
    }
}
