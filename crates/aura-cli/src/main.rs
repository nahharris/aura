use std::collections::BTreeMap;
use std::env;
use std::fs;
use std::io::IsTerminal;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::process::ExitCode;

use anstyle::{AnsiColor, Color, Effects, Style};
use anyhow::{Context, Result};
use aura_codegen::project::discover::discover_layout;
use aura_codegen::project::manifest::{ProjectType, load_manifest};
use aura_codegen::{emit_llvm_ir, emit_object_file};
use aura_diagnostics::{Diagnostic, Severity, Span};
use aura_frontend::ast::{Decl, Program};
use aura_frontend::{FormatOptions, Parser, format_source, unified_diff};
use aura_typecheck::{CheckOptions, CheckedModule, check_module_with_options};
use clap::{Parser as ClapParser, Subcommand, ValueEnum};
use serde::Serialize;

#[derive(ClapParser, Debug)]
#[command(name = "aura")]
#[command(about = "Aura frontend CLI", long_about = None)]
struct Cli {
    #[command(subcommand)]
    command: Commands,
}

#[derive(Subcommand, Debug)]
enum Commands {
    Init {
        name: String,
    },
    Build {
        input: Option<PathBuf>,
        #[arg(short = 'o', long = "out")]
        out: Option<PathBuf>,
        #[arg(long, value_enum, default_value_t = OutputFormat::Native)]
        format: OutputFormat,
        #[arg(long, value_enum, default_value_t = DiagnosticsFormat::Pretty)]
        diagnostics: DiagnosticsFormat,
    },
    Fmt {
        input: PathBuf,
        #[arg(long)]
        write: bool,
        #[arg(long)]
        check: bool,
        #[arg(long, default_value_t = 4)]
        indent_width: usize,
        #[arg(long, default_value_t = 100)]
        max_width: usize,
    },
    Doc {
        input: PathBuf,
        symbol: Option<String>,
        #[arg(long, value_enum, default_value_t = DocOutputFormat::Pretty)]
        format: DocOutputFormat,
    },
}

#[derive(Debug, Clone, Copy, ValueEnum, PartialEq, Eq)]
enum OutputFormat {
    Auir,
    Ll,
    Obj,
    Native,
}

#[derive(Debug, Clone, Copy, ValueEnum, PartialEq, Eq)]
enum DocOutputFormat {
    Pretty,
    Json,
}

#[derive(Debug, Clone, Copy, ValueEnum, PartialEq, Eq)]
enum DiagnosticsFormat {
    Pretty,
    Json,
}

fn main() -> ExitCode {
    match run() {
        Ok(code) => code,
        Err(err) => {
            eprintln!("error: {err:#}");
            ExitCode::from(2)
        }
    }
}

fn run() -> Result<ExitCode> {
    let cli = Cli::parse();
    match cli.command {
        Commands::Init { name } => init_cmd(&name),
        Commands::Build {
            input,
            out,
            format,
            diagnostics,
        } => build_cmd(input.as_deref(), out.as_deref(), format, diagnostics),
        Commands::Fmt {
            input,
            write,
            check,
            indent_width,
            max_width,
        } => fmt_cmd(&input, write, check, indent_width, max_width),
        Commands::Doc {
            input,
            symbol,
            format,
        } => doc_cmd(&input, symbol.as_deref(), format),
    }
}

#[derive(Debug, Serialize)]
struct DocRecord {
    symbol: String,
    doc: String,
}

fn doc_cmd(input: &Path, symbol: Option<&str>, format: DocOutputFormat) -> Result<ExitCode> {
    let source = fs::read_to_string(input)
        .with_context(|| format!("failed to read source file '{}'", input.display()))?;
    let program = match Parser::parse_source(&source) {
        Ok(program) => program,
        Err(diag) => {
            print_diagnostics(&[diag], DiagnosticsFormat::Pretty, input, &source)?;
            return Ok(ExitCode::from(1));
        }
    };
    let docs = collect_docs(&program);

    if let Some(symbol) = symbol {
        if let Some(doc) = docs.get(symbol) {
            match format {
                DocOutputFormat::Pretty => {
                    println!("# {symbol}\n\n{doc}");
                }
                DocOutputFormat::Json => {
                    println!(
                        "{}",
                        serde_json::to_string_pretty(&DocRecord {
                            symbol: symbol.to_string(),
                            doc: doc.clone(),
                        })?
                    );
                }
            }
            return Ok(ExitCode::SUCCESS);
        }
        eprintln!("No documentation found for symbol `{symbol}`");
        return Ok(ExitCode::from(1));
    }

    let mut records = docs
        .into_iter()
        .map(|(symbol, doc)| DocRecord { symbol, doc })
        .collect::<Vec<_>>();
    records.sort_by(|a, b| a.symbol.cmp(&b.symbol));

    match format {
        DocOutputFormat::Pretty => {
            for (i, record) in records.iter().enumerate() {
                if i > 0 {
                    println!();
                }
                println!("# {}\n\n{}", record.symbol, record.doc);
            }
        }
        DocOutputFormat::Json => {
            println!("{}", serde_json::to_string_pretty(&records)?);
        }
    }

    Ok(ExitCode::SUCCESS)
}

fn collect_docs(program: &Program) -> BTreeMap<String, String> {
    let mut out = BTreeMap::new();
    for decl in &program.declarations {
        match decl {
            Decl::Assign { name, doc, .. } => {
                if let Some(doc) = doc {
                    out.insert(name.clone(), doc.markdown.clone());
                    for symbol_doc in &doc.symbol_docs {
                        if symbol_doc.name != *name {
                            out.insert(symbol_doc.name.clone(), symbol_doc.doc.clone());
                        }
                    }
                }
            }
            Decl::Function(function) => {
                if let Some(doc) = &function.doc {
                    out.insert(function.name.clone(), doc.markdown.clone());
                    for symbol_doc in &doc.symbol_docs {
                        if symbol_doc.name == "return" {
                            out.insert(format!("{}.return", function.name), symbol_doc.doc.clone());
                        } else if function.params.iter().any(|p| p.name == symbol_doc.name) {
                            out.insert(
                                format!("{}.{}", function.name, symbol_doc.name),
                                symbol_doc.doc.clone(),
                            );
                        } else if symbol_doc.name != function.name {
                            out.insert(symbol_doc.name.clone(), symbol_doc.doc.clone());
                        }
                    }
                }
            }
            Decl::Macro(_) => {}
            Decl::Use(_) => {}
        }
    }
    out
}

fn init_cmd(name: &str) -> Result<ExitCode> {
    let target = std::env::current_dir()
        .context("failed to read current directory")?
        .join(name);
    if target.exists() {
        anyhow::bail!("target directory '{}' already exists", target.display());
    }

    create_project_scaffold(&target, name)?;
    println!("initialized Aura project at {}", target.display());
    Ok(ExitCode::SUCCESS)
}

fn create_project_scaffold(project_root: &Path, project_name: &str) -> Result<()> {
    let src_dir = project_root.join("src");
    let target_dir = project_root.join("target");
    let gitignore_file = project_root.join(".gitignore");

    fs::create_dir_all(&src_dir)
        .with_context(|| format!("failed to create '{}'", src_dir.display()))?;
    fs::create_dir_all(&target_dir)
        .with_context(|| format!("failed to create '{}'", target_dir.display()))?;

    let manifest =
        include_str!("../templates/build.aura.tpl").replace("{{project_name}}", project_name);
    let build_file = project_root.join("build.aura");
    fs::write(&build_file, manifest)
        .with_context(|| format!("failed to write '{}'", build_file.display()))?;

    let main_file = src_dir.join("main.aura");
    let main_template = include_str!("../templates/main.aura.tpl");
    fs::write(&main_file, main_template)
        .with_context(|| format!("failed to write '{}'", main_file.display()))?;

    let gitignore_template = include_str!("../templates/gitignore.tpl");
    fs::write(&gitignore_file, gitignore_template)
        .with_context(|| format!("failed to write '{}'", gitignore_file.display()))?;

    Ok(())
}

fn fmt_cmd(
    input: &Path,
    write: bool,
    check: bool,
    indent_width: usize,
    max_width: usize,
) -> Result<ExitCode> {
    let source = fs::read_to_string(input)
        .with_context(|| format!("failed to read source file '{}'", input.display()))?;

    let options = FormatOptions {
        indent_width,
        max_width,
    };
    let formatted = format_source(&source, &options);

    if source == formatted {
        return Ok(ExitCode::SUCCESS);
    }

    if write {
        fs::write(input, formatted)
            .with_context(|| format!("failed to write formatted source '{}'", input.display()))?;
        return Ok(ExitCode::SUCCESS);
    }

    let diff = unified_diff(&source, &formatted, &input.display().to_string());
    print!("{diff}");

    if check {
        Ok(ExitCode::from(1))
    } else {
        Ok(ExitCode::SUCCESS)
    }
}

fn build_cmd(
    input: Option<&Path>,
    out: Option<&Path>,
    format: OutputFormat,
    diagnostics_format: DiagnosticsFormat,
) -> Result<ExitCode> {
    let start = input
        .map(PathBuf::from)
        .unwrap_or(std::env::current_dir().context("failed to read current directory")?);

    if let Some(layout) = discover_layout(&start) {
        return build_project_cmd(&layout.build_file, out, format, diagnostics_format);
    }

    build_single_file_cmd(&start, out, format, diagnostics_format, false)
}

fn build_single_file_cmd(
    input: &Path,
    out: Option<&Path>,
    format: OutputFormat,
    diagnostics_format: DiagnosticsFormat,
    enforce_main_signature: bool,
) -> Result<ExitCode> {
    let source = fs::read_to_string(input)
        .with_context(|| format!("failed to read source file '{}'", input.display()))?;

    let program = match Parser::parse_source(&source) {
        Ok(program) => program,
        Err(diag) => {
            print_diagnostics(&[diag], diagnostics_format, input, &source)?;
            return Ok(ExitCode::from(1));
        }
    };

    let checked = check_module_with_options(
        &program,
        CheckOptions {
            enforce_main_signature,
        },
    );
    let has_errors = checked
        .diagnostics
        .iter()
        .any(|d| d.severity == Severity::Error);

    if has_errors {
        print_diagnostics(&checked.diagnostics, diagnostics_format, input, &source)?;
        return Ok(ExitCode::from(1));
    }

    if !checked.diagnostics.is_empty() {
        print_diagnostics(&checked.diagnostics, diagnostics_format, input, &source)?;
    }

    let module = checked
        .module
        .as_ref()
        .expect("module should exist when diagnostics are error-free");

    match format {
        OutputFormat::Auir => {
            let output_path = out
                .map(PathBuf::from)
                .unwrap_or_else(|| default_output_path(input, format));
            ensure_parent_dir(&output_path)?;
            let rendered = render_ir_pretty(module);
            fs::write(&output_path, rendered).with_context(|| {
                format!(
                    "failed to write checked IR output '{}'",
                    output_path.display()
                )
            })?;
            println!("checked IR emitted to {}", output_path.display());
        }
        OutputFormat::Ll => {
            let output_path = out
                .map(PathBuf::from)
                .unwrap_or_else(|| default_output_path(input, format));
            ensure_parent_dir(&output_path)?;
            let module_name = module_name_from_path(input);
            let llvm_ir = emit_llvm_ir(&module_name, module)
                .map_err(|e| anyhow::anyhow!("LLVM IR emission failed: {e}"))?;
            fs::write(&output_path, llvm_ir)
                .with_context(|| format!("failed to write LLVM IR '{}'", output_path.display()))?;
            println!("LLVM IR emitted to {}", output_path.display());
        }
        OutputFormat::Obj => {
            let output_path = out
                .map(PathBuf::from)
                .unwrap_or_else(|| default_output_path(input, format));
            ensure_parent_dir(&output_path)?;
            let module_name = module_name_from_path(input);
            emit_object_file(&module_name, module, &output_path)
                .map_err(|e| anyhow::anyhow!("object emission failed: {e}"))?;
            println!("object emitted to {}", output_path.display());
        }
        OutputFormat::Native => {
            let executable_path = out
                .map(PathBuf::from)
                .unwrap_or_else(|| default_output_path(input, format));
            ensure_parent_dir(&executable_path)?;
            ensure_runtime_host_built()?;
            let module_name = module_name_from_path(input);
            let stem = executable_path
                .file_stem()
                .and_then(|s| s.to_str())
                .unwrap_or("aura_main");
            let intermediates_dir = executable_path
                .parent()
                .map(PathBuf::from)
                .unwrap_or_else(|| PathBuf::from("."));
            let ll_path = intermediates_dir.join(format!("{stem}.ll"));
            let obj_path = intermediates_dir.join(format!("{stem}.obj"));

            let llvm_ir = emit_llvm_ir(&module_name, module)
                .map_err(|e| anyhow::anyhow!("LLVM IR emission failed: {e}"))?;
            fs::write(&ll_path, llvm_ir)
                .with_context(|| format!("failed to write LLVM IR '{}'", ll_path.display()))?;

            emit_object_file(&module_name, module, &obj_path)
                .map_err(|e| anyhow::anyhow!("object emission failed: {e}"))?;

            link_native_binary(&obj_path, &executable_path)?;
            println!("native executable emitted to {}", executable_path.display());
            println!("kept intermediate LLVM IR at {}", ll_path.display());
            println!("kept intermediate object file at {}", obj_path.display());
        }
    }

    Ok(ExitCode::SUCCESS)
}

fn build_project_cmd(
    build_file: &Path,
    out: Option<&Path>,
    format: OutputFormat,
    diagnostics_format: DiagnosticsFormat,
) -> Result<ExitCode> {
    let manifest = match load_manifest(build_file) {
        Ok(m) => m,
        Err(e) => {
            eprintln!("manifest error: {e}");
            return Ok(ExitCode::from(1));
        }
    };

    let project_root = build_file
        .parent()
        .context("build.aura should have a parent directory")?;
    let src_main = project_root.join("src").join("main.aura");
    if manifest.kind == ProjectType::Binary && !src_main.is_file() {
        eprintln!(
            "binary project '{}' does not have entry file '{}'",
            manifest.name,
            src_main.display()
        );
        return Ok(ExitCode::from(1));
    }

    println!(
        "building project '{}' ({}) from {}",
        manifest.name,
        manifest.version,
        build_file.display()
    );

    match manifest.kind {
        ProjectType::Binary => {
            let project_out = if out.is_none() {
                Some(project_default_output_path(
                    project_root,
                    &manifest.name,
                    format,
                ))
            } else {
                None
            };
            build_single_file_cmd(
                &src_main,
                out.or(project_out.as_deref()),
                format,
                diagnostics_format,
                true,
            )
        }
        ProjectType::Library => {
            println!(
                "project '{}' is a library; skipping entrypoint build",
                manifest.name
            );
            Ok(ExitCode::SUCCESS)
        }
    }
}

fn project_default_output_path(
    project_root: &Path,
    project_name: &str,
    format: OutputFormat,
) -> PathBuf {
    let target_dir = project_root.join("target");
    let file_name = match format {
        OutputFormat::Auir => format!("{project_name}.auir"),
        OutputFormat::Ll => format!("{project_name}.ll"),
        OutputFormat::Obj => format!("{project_name}.obj"),
        OutputFormat::Native => {
            if cfg!(windows) {
                format!("{project_name}.exe")
            } else {
                project_name.to_string()
            }
        }
    };
    target_dir.join(file_name)
}

fn default_output_path(input: &Path, format: OutputFormat) -> PathBuf {
    let stem = input
        .file_stem()
        .and_then(|s| s.to_str())
        .unwrap_or("output");
    let file_name = match format {
        OutputFormat::Auir => format!("{stem}.auir"),
        OutputFormat::Ll => format!("{stem}.ll"),
        OutputFormat::Obj => format!("{stem}.obj"),
        OutputFormat::Native => {
            if cfg!(windows) {
                format!("{stem}.exe")
            } else {
                stem.to_string()
            }
        }
    };
    match input.parent() {
        Some(parent) => parent.join(file_name),
        None => PathBuf::from(file_name),
    }
}

fn module_name_from_path(path: &Path) -> String {
    path.file_stem()
        .and_then(|s| s.to_str())
        .unwrap_or("module")
        .to_string()
}

fn ensure_parent_dir(path: &Path) -> Result<()> {
    if let Some(parent) = path.parent()
        && !parent.as_os_str().is_empty()
    {
        fs::create_dir_all(parent)
            .with_context(|| format!("failed to create output directory '{}'", parent.display()))?;
    }
    Ok(())
}

fn llvm_prefix_from_env() -> Result<PathBuf> {
    let prefix = env::var("LLVM_SYS_180_PREFIX").context(
        "LLVM_SYS_180_PREFIX is not set. Use `cargo xtask llvm run -- ...` for LLVM-native builds",
    )?;
    Ok(PathBuf::from(prefix))
}

fn clang_path_from_prefix(prefix: &Path) -> PathBuf {
    if cfg!(windows) {
        prefix.join("bin").join("clang.exe")
    } else {
        prefix.join("bin").join("clang")
    }
}

fn runtime_host_staticlib_path() -> Result<PathBuf> {
    let profile_dir = if cfg!(debug_assertions) {
        "debug"
    } else {
        "release"
    };
    let file_name = if cfg!(windows) {
        "aura_runtime_host.lib"
    } else {
        "libaura_runtime_host.a"
    };
    let path = PathBuf::from("target").join(profile_dir).join(file_name);
    if !path.is_file() {
        anyhow::bail!(
            "runtime host staticlib not found at '{}'; build `aura-runtime-host` first",
            path.display()
        );
    }
    Ok(path)
}

fn link_native_binary(obj_path: &Path, output_path: &Path) -> Result<()> {
    let llvm_prefix = llvm_prefix_from_env()?;
    let clang = clang_path_from_prefix(&llvm_prefix);
    if !clang.is_file() {
        anyhow::bail!("failed to locate clang at '{}'", clang.display());
    }

    let runtime_staticlib = runtime_host_staticlib_path()?;
    let status = Command::new(&clang)
        .arg(obj_path)
        .arg(runtime_staticlib)
        // Let the Rust staticlib supply its own CRT defaults; forcing MSVCRT here
        // conflicts with the staticlib's runtime model and triggers LNK4098.
        .arg("-lkernel32")
        .arg("-luserenv")
        .arg("-lws2_32")
        .arg("-lntdll")
        .arg("-ladvapi32")
        .arg("-lbcrypt")
        .arg("-o")
        .arg(output_path)
        .status()
        .with_context(|| format!("failed to invoke '{}'", clang.display()))?;
    if !status.success() {
        anyhow::bail!(
            "native link failed (clang exit status {status}); object: '{}', output: '{}'",
            obj_path.display(),
            output_path.display()
        );
    }
    Ok(())
}

fn ensure_runtime_host_built() -> Result<()> {
    let status = Command::new("cargo")
        .arg("build")
        .arg("-p")
        .arg("aura-runtime-host")
        .status()
        .context("failed to invoke cargo for aura-runtime-host build")?;
    if !status.success() {
        anyhow::bail!("failed to build aura-runtime-host (cargo status {status})");
    }
    Ok(())
}

fn render_ir_pretty(module: &CheckedModule) -> String {
    let mut out = String::new();
    out.push_str("# Aura Checked IR\n\n");
    out.push_str("## Declarations\n");
    for decl in &module.ir.declarations {
        out.push_str(&format!(
            "- {}: ty#{}\n{:#?}\n\n",
            decl.name, decl.ty.0, decl.value
        ));
    }

    out.push_str("## Value Types\n");
    let mut values: Vec<_> = module.value_types.iter().collect();
    values.sort_by(|(a, _), (b, _)| a.cmp(b));
    for (name, ty) in values {
        out.push_str(&format!("- {name}: ty#{}\n", ty.0));
    }
    out.push('\n');

    out.push_str("## Type Table\n");
    let mut i = 0usize;
    while let Some(ty) = module.types.get(aura_typecheck::TyId(i)) {
        out.push_str(&format!("- ty#{i}: {ty:?}\n"));
        i += 1;
    }
    out
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum SpanOrigin {
    Reported,
    Inferred,
}

#[derive(Debug, Clone)]
struct PreparedDiagnostic {
    code: &'static str,
    stage: String,
    severity: Severity,
    message: String,
    span: Option<Span>,
    span_origin: Option<SpanOrigin>,
    hint: Option<String>,
    related: Vec<aura_diagnostics::RelatedLabel>,
    obligations: Vec<String>,
}

fn print_diagnostics(
    diags: &[Diagnostic],
    fmt: DiagnosticsFormat,
    input: &Path,
    source: &str,
) -> Result<()> {
    let prepared = prepare_diagnostics(diags, source);
    match fmt {
        DiagnosticsFormat::Pretty => {
            let colors = std::io::stderr().is_terminal();
            for (idx, d) in prepared.iter().enumerate() {
                if idx > 0 {
                    eprintln!();
                }
                render_pretty_diagnostic(d, input, source, colors);
            }
            Ok(())
        }
        DiagnosticsFormat::Json => {
            let payload: Vec<_> = prepared
                .iter()
                .map(|d| {
                    serde_json::json!({
                        "code": d.code,
                        "file": input.display().to_string(),
                        "stage": d.stage,
                        "severity": match d.severity { Severity::Error => "error", Severity::Warning => "warning" },
                        "message": d.message,
                        "span": d.span.map(|s| serde_json::json!({"line": s.line, "column": s.column, "start": s.start, "end": s.end})),
                        "span_origin": d.span_origin.map(|o| match o { SpanOrigin::Reported => "reported", SpanOrigin::Inferred => "inferred" }),
                        "hint": d.hint,
                        "related": d.related.iter().map(|r| serde_json::json!({"label": r.label, "span": r.span.map(|s| serde_json::json!({"line": s.line, "column": s.column, "start": s.start, "end": s.end}))})).collect::<Vec<_>>(),
                        "obligations": d.obligations,
                    })
                })
                .collect();
            eprintln!("{}", serde_json::to_string_pretty(&payload)?);
            Ok(())
        }
    }
}

fn prepare_diagnostics(diags: &[Diagnostic], source: &str) -> Vec<PreparedDiagnostic> {
    let mut prepared = Vec::new();
    let mut seen = std::collections::HashSet::new();
    for d in diags {
        let stage = format!("{:?}", d.stage);
        let (span, span_origin) = match d.span {
            Some(span) => (Some(span), Some(SpanOrigin::Reported)),
            None if stage == "Typecheck" => infer_span_from_obligations(source, &d.obligations)
                .map(|s| (Some(s), Some(SpanOrigin::Inferred)))
                .unwrap_or((None, None)),
            None => (None, None),
        };
        let related = d
            .related
            .iter()
            .filter(|r| !is_internal_related_label(&r.label))
            .cloned()
            .collect::<Vec<_>>();
        let fingerprint = format!(
            "{:?}|{:?}|{}|{}|{:?}|{:?}",
            d.severity,
            d.stage,
            d.code_str(),
            d.message,
            span,
            d.hint
        );
        if !seen.insert(fingerprint) {
            continue;
        }
        prepared.push(PreparedDiagnostic {
            code: d.code_str(),
            stage,
            severity: d.severity,
            message: normalize_for_llm(&d.message),
            span,
            span_origin,
            hint: d.hint.as_ref().map(|h| normalize_for_llm(h)),
            related: related
                .into_iter()
                .map(|mut r| {
                    r.label = normalize_for_llm(&r.label);
                    r
                })
                .collect(),
            obligations: d.obligations.iter().map(|o| normalize_for_llm(o)).collect(),
        });
    }
    prepared
}

fn normalize_for_llm(text: &str) -> String {
    let chars: Vec<char> = text.chars().collect();
    let mut out = String::new();
    let mut i = 0usize;
    while i < chars.len() {
        if chars[i] == '\'' {
            let mut j = i + 1;
            while j < chars.len() && chars[j] != '\'' {
                j += 1;
            }
            if j < chars.len() {
                let inner: String = chars[i + 1..j].iter().collect();
                if !inner.is_empty() {
                    out.push('`');
                    out.push_str(&inner);
                    out.push('`');
                    i = j + 1;
                    continue;
                }
            }
        }
        out.push(chars[i]);
        i += 1;
    }
    out
}

fn is_internal_related_label(label: &str) -> bool {
    label == "source span unavailable in current typed AST"
        || label.ends_with("compatibility check failed")
        || label.ends_with("decision failed")
}

fn infer_span_from_obligations(source: &str, obligations: &[String]) -> Option<Span> {
    for obligation in obligations.iter().rev() {
        if let Some(name) = extract_obligation_name(obligation, "checking function '")
            && let Some(span) = find_function_name_span(source, &name)
        {
            return Some(span);
        }
        if let Some(name) = extract_obligation_name(obligation, "checking declaration '")
            && let Some(span) = find_static_decl_name_span(source, &name)
        {
            return Some(span);
        }
    }
    None
}

fn extract_obligation_name(obligation: &str, prefix: &str) -> Option<String> {
    let start = obligation.find(prefix)? + prefix.len();
    let end_rel = obligation[start..].find('\'')?;
    Some(obligation[start..start + end_rel].to_string())
}

fn find_function_name_span(source: &str, name: &str) -> Option<Span> {
    for (line_idx, line) in source.lines().enumerate() {
        let marker = format!("def {name}");
        if let Some(start_idx) = line.find(&marker) {
            let name_start = start_idx + 4;
            return Some(span_from_line(
                source,
                line_idx + 1,
                name_start + 1,
                name.len(),
            ));
        }
        let method_marker = format!(".{name}(");
        if let Some(start_idx) = line.find(&method_marker) {
            let name_start = start_idx + 1;
            return Some(span_from_line(
                source,
                line_idx + 1,
                name_start + 1,
                name.len(),
            ));
        }
    }
    None
}

fn find_static_decl_name_span(source: &str, name: &str) -> Option<Span> {
    for (line_idx, line) in source.lines().enumerate() {
        let marker = format!("def {name}");
        if let Some(start_idx) = line.find(&marker) {
            let name_start = start_idx + 4;
            return Some(span_from_line(
                source,
                line_idx + 1,
                name_start + 1,
                name.len(),
            ));
        }
    }
    None
}

fn span_from_line(source: &str, line_number: usize, column: usize, len: usize) -> Span {
    let mut start = 0usize;
    let mut line = 1usize;
    for part in source.split_inclusive('\n') {
        if line == line_number {
            break;
        }
        start += part.len();
        line += 1;
    }
    let start = start + column.saturating_sub(1);
    Span {
        start,
        end: start + len.max(1),
        line: line_number,
        column,
    }
}

fn render_pretty_diagnostic(d: &PreparedDiagnostic, input: &Path, source: &str, colors: bool) {
    let palette = Palette::new(colors);
    let symbol_tokens = collect_symbol_tokens(d);
    let sev_label = match d.severity {
        Severity::Error => palette.error("error"),
        Severity::Warning => palette.warning("warning"),
    };
    let stage = palette.dim(&format!(" [{}]", d.stage.to_lowercase()));
    eprintln!(
        "{}{}{}{}{}: {}",
        sev_label,
        palette.dim("["),
        palette.dim(d.code),
        palette.dim("]"),
        stage,
        style_inline_symbols(&d.message, &palette)
    );

    if let Some(span) = d.span {
        eprintln!(
            "  {} {}:{}:{}",
            palette.dim("-->"),
            input.display(),
            span.line,
            span.column
        );
        if let Some((line_no, line_text, pointer)) = render_span_snippet(
            source,
            span,
            &style_inline_symbols(&d.message, &palette),
            colors,
            &symbol_tokens,
        ) {
            eprintln!("  {}", palette.dim("|"));
            eprintln!(
                "{} {} {}",
                palette.dim(&format!("{:>3}", line_no)),
                palette.dim("|"),
                line_text
            );
            eprintln!("{} {} {}", palette.dim("   "), palette.dim("|"), pointer);
        }
        if d.span_origin == Some(SpanOrigin::Inferred) {
            eprintln!(
                "  {} location inferred from typechecking context",
                palette.dim("= note:")
            );
        }
    }

    if !d.obligations.is_empty() {
        eprintln!(
            "  {} {}",
            palette.dim("= context:"),
            style_inline_symbols(&d.obligations.join(" > "), &palette)
        );
    }

    for related in &d.related {
        if let Some(span) = related.span {
            eprintln!(
                "  {} {} ({}:{})",
                palette.dim("= related:"),
                style_inline_symbols(&related.label, &palette),
                span.line,
                span.column
            );
        } else {
            eprintln!(
                "  {} {}",
                palette.dim("= related:"),
                style_inline_symbols(&related.label, &palette)
            );
        }
    }

    if let Some(hint) = &d.hint {
        eprintln!(
            "  {} {}",
            palette.help("= help:"),
            style_inline_symbols(hint, &palette)
        );
    }
}

fn style_inline_symbols(text: &str, palette: &Palette) -> String {
    let chars: Vec<char> = text.chars().collect();
    let mut out = String::new();
    let mut i = 0usize;
    while i < chars.len() {
        if chars[i] == '`' {
            let mut j = i + 1;
            while j < chars.len() && chars[j] != '`' {
                j += 1;
            }
            if j < chars.len() {
                let inner: String = chars[i + 1..j].iter().collect();
                out.push_str(&palette.symbol(&inner));
                i = j + 1;
                continue;
            }
        }
        out.push(chars[i]);
        i += 1;
    }
    out
}

fn collect_symbol_tokens(d: &PreparedDiagnostic) -> std::collections::HashSet<String> {
    let mut set = std::collections::HashSet::new();
    extract_backtick_tokens(&d.message, &mut set);
    if let Some(hint) = &d.hint {
        extract_backtick_tokens(hint, &mut set);
    }
    for related in &d.related {
        extract_backtick_tokens(&related.label, &mut set);
    }
    for obligation in &d.obligations {
        extract_backtick_tokens(obligation, &mut set);
    }
    set
}

fn extract_backtick_tokens(text: &str, out: &mut std::collections::HashSet<String>) {
    let chars: Vec<char> = text.chars().collect();
    let mut i = 0usize;
    while i < chars.len() {
        if chars[i] == '`' {
            let mut j = i + 1;
            while j < chars.len() && chars[j] != '`' {
                j += 1;
            }
            if j < chars.len() {
                let inner: String = chars[i + 1..j].iter().collect();
                if !inner.is_empty() {
                    out.insert(inner);
                }
                i = j + 1;
                continue;
            }
        }
        i += 1;
    }
}

fn render_span_snippet(
    source: &str,
    span: Span,
    message: &str,
    colors: bool,
    symbol_tokens: &std::collections::HashSet<String>,
) -> Option<(usize, String, String)> {
    let lines = source.lines().collect::<Vec<_>>();
    if lines.is_empty() {
        return None;
    }
    let line_idx = span
        .line
        .saturating_sub(1)
        .min(lines.len().saturating_sub(1));
    let line_text = lines[line_idx];
    let highlighted = highlight_source_line(line_text, colors, symbol_tokens);
    let default_col = if line_text.is_empty() {
        1
    } else {
        line_text.chars().count() + 1
    };
    let caret_column = if span.line.saturating_sub(1) >= lines.len() {
        default_col
    } else {
        span.column.max(1)
    };
    let caret_start = caret_column.saturating_sub(1);
    let span_len = span.end.saturating_sub(span.start).max(1);
    let pointer = format!(
        "{}{} {}",
        " ".repeat(caret_start),
        Palette::new(colors).pointer(&"^".repeat(span_len.min(80))),
        message
    );
    Some((line_idx + 1, highlighted, pointer))
}

fn highlight_source_line(
    line: &str,
    colors: bool,
    symbol_tokens: &std::collections::HashSet<String>,
) -> String {
    if !colors {
        return line.to_string();
    }
    const RESET: &str = "\x1b[0m";
    const KW: &str = "\x1b[35;1m";
    const STR: &str = "\x1b[36m";
    const NUM: &str = "\x1b[33m";
    const SYM: &str = "\x1b[36;1m";
    let keywords = ["def", "defmacro", "use", "if", "cases", "when", "static"];

    let chars: Vec<char> = line.chars().collect();
    let mut i = 0usize;
    let mut out = String::new();
    while i < chars.len() {
        let ch = chars[i];
        if ch == '"' {
            let start = i;
            i += 1;
            while i < chars.len() {
                if chars[i] == '"' && chars.get(i.saturating_sub(1)) != Some(&'\\') {
                    i += 1;
                    break;
                }
                i += 1;
            }
            out.push_str(STR);
            out.push_str(&chars[start..i].iter().collect::<String>());
            out.push_str(RESET);
            continue;
        }
        if ch.is_ascii_digit() {
            let start = i;
            i += 1;
            while i < chars.len() && (chars[i].is_ascii_digit() || chars[i] == '.') {
                i += 1;
            }
            out.push_str(NUM);
            out.push_str(&chars[start..i].iter().collect::<String>());
            out.push_str(RESET);
            continue;
        }
        if ch.is_ascii_alphabetic() || ch == '_' {
            let start = i;
            i += 1;
            while i < chars.len() && (chars[i].is_ascii_alphanumeric() || chars[i] == '_') {
                i += 1;
            }
            let ident = chars[start..i].iter().collect::<String>();
            if keywords.iter().any(|kw| *kw == ident) {
                out.push_str(KW);
                out.push_str(&ident);
                out.push_str(RESET);
            } else if symbol_tokens.contains(&ident) {
                out.push_str(SYM);
                out.push_str(&ident);
                out.push_str(RESET);
            } else {
                out.push_str(&ident);
            }
            continue;
        }
        out.push(ch);
        i += 1;
    }
    out
}

struct Palette {
    enabled: bool,
}

impl Palette {
    fn new(enabled: bool) -> Self {
        Self { enabled }
    }

    fn error(&self, text: &str) -> String {
        self.style(
            text,
            Style::new()
                .fg_color(Some(Color::Ansi(AnsiColor::Red)))
                .effects(Effects::BOLD),
        )
    }

    fn warning(&self, text: &str) -> String {
        self.style(
            text,
            Style::new()
                .fg_color(Some(Color::Ansi(AnsiColor::Yellow)))
                .effects(Effects::BOLD),
        )
    }

    fn help(&self, text: &str) -> String {
        self.style(
            text,
            Style::new()
                .fg_color(Some(Color::Ansi(AnsiColor::Cyan)))
                .effects(Effects::BOLD),
        )
    }

    fn pointer(&self, text: &str) -> String {
        self.style(
            text,
            Style::new()
                .fg_color(Some(Color::Ansi(AnsiColor::Magenta)))
                .effects(Effects::BOLD),
        )
    }

    fn dim(&self, text: &str) -> String {
        self.style(
            text,
            Style::new().fg_color(Some(Color::Ansi(AnsiColor::BrightBlack))),
        )
    }

    fn symbol(&self, text: &str) -> String {
        self.style(
            text,
            Style::new()
                .fg_color(Some(Color::Ansi(AnsiColor::Cyan)))
                .effects(Effects::BOLD),
        )
    }

    fn style(&self, text: &str, style: Style) -> String {
        if self.enabled {
            format!("{style}{text}{style:#}")
        } else {
            text.to_string()
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use aura_diagnostics::{Issue, RelatedLabel, Stage};
    use std::time::{SystemTime, UNIX_EPOCH};

    #[test]
    fn prepare_diagnostics_filters_internal_related_labels() {
        let diag = Diagnostic::error(Issue::ParseUnexpectedToken {
            detail: "mismatch".to_string(),
        })
        .with_stage(Stage::Typecheck)
        .with_related("source span unavailable in current typed AST", None)
        .with_related("assignment compatibility check failed", None)
        .with_related("useful context", None);
        let prepared = prepare_diagnostics(&[diag], "def f(x: Int) -> Int { x }");
        assert_eq!(prepared.len(), 1);
        assert_eq!(prepared[0].related.len(), 1);
        assert_eq!(prepared[0].related[0].label, "useful context");
    }

    #[test]
    fn prepare_diagnostics_deduplicates_same_payload() {
        let diag1 = Diagnostic::error(Issue::ParseUnexpectedToken {
            detail: "same".to_string(),
        })
        .with_stage(Stage::Parser);
        let diag2 = Diagnostic::error(Issue::ParseUnexpectedToken {
            detail: "same".to_string(),
        })
        .with_stage(Stage::Parser);
        let prepared = prepare_diagnostics(&[diag1, diag2], "def x = 1");
        assert_eq!(prepared.len(), 1);
    }

    #[test]
    fn infer_span_from_function_obligation_finds_name() {
        let source = "def bad(x: Int) -> Int { \"oops\" }\n";
        let obligations = vec!["checking function 'bad'".to_string()];
        let span = infer_span_from_obligations(source, &obligations).expect("inferred span");
        assert_eq!(span.line, 1);
        assert_eq!(span.column, 5);
    }

    #[test]
    fn render_span_snippet_handles_out_of_bounds_line() {
        let span = Span {
            start: 22,
            end: 23,
            line: 2,
            column: 1,
        };
        let symbols = std::collections::HashSet::new();
        let rendered =
            render_span_snippet("def x = macro_name[T]", span, "problem", false, &symbols)
                .expect("snippet fallback");
        assert_eq!(rendered.0, 1);
        assert!(rendered.2.contains('^'));
    }

    #[test]
    fn is_internal_related_label_covers_known_patterns() {
        assert!(is_internal_related_label(
            "source span unavailable in current typed AST"
        ));
        assert!(is_internal_related_label(
            "assignment compatibility check failed"
        ));
        assert!(is_internal_related_label(
            "IR coercion/cast decision failed"
        ));
        assert!(!is_internal_related_label("real related note"));
    }

    #[test]
    fn json_prepared_keeps_user_related_labels() {
        let diag = Diagnostic {
            issue: Issue::ParseUnexpectedToken {
                detail: "problem".to_string(),
            },
            stage: Stage::Typecheck,
            severity: Severity::Error,
            message: "problem".to_string(),
            span: None,
            hint: None,
            related: vec![RelatedLabel {
                label: "actual related".to_string(),
                span: None,
            }],
            obligations: vec![],
        };
        let prepared = prepare_diagnostics(&[diag], "def x = 1");
        assert_eq!(prepared[0].related.len(), 1);
        assert_eq!(prepared[0].related[0].label, "actual related");
    }

    #[test]
    fn init_scaffold_creates_manifest_main_and_target_dir() {
        let mut root = std::env::temp_dir();
        let nanos = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .expect("clock must be after unix epoch")
            .as_nanos();
        root.push(format!("aura_cli_init_test_{nanos}"));

        create_project_scaffold(&root, "demo").expect("scaffold should succeed");

        assert!(root.join("build.aura").is_file());
        let manifest = fs::read_to_string(root.join("build.aura")).expect("manifest should exist");
        assert!(manifest.contains("type = .binary"));
        assert!(root.join("src").join("main.aura").is_file());
        let main = fs::read_to_string(root.join("src").join("main.aura"))
            .expect("main source should exist");
        assert!(main.contains("syscall_exit"));
        assert!(main.contains("let exit_code = 0;"));
        assert!(main.contains("syscall_exit(exit_code)"));
        assert!(root.join("target").is_dir());
        assert!(root.join(".gitignore").is_file());
        let gitignore =
            fs::read_to_string(root.join(".gitignore")).expect("gitignore should exist");
        assert!(gitignore.contains("/target/"));

        fs::remove_dir_all(root).expect("cleanup should succeed");
    }
}
