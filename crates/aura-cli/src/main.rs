use std::collections::BTreeMap;
use std::fs;
use std::io::IsTerminal;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use anyhow::{Context, Result};
use anstyle::{AnsiColor, Color, Effects, Style};
use aura_diagnostics::{Diagnostic, Severity, Span};
use aura_frontend::Parser;
use aura_typecheck::checked_ir::{
    BinaryOpKind, CheckedExpr, CheckedStaticArg, CheckedStaticValue, CheckedTypeExpr,
};
use aura_typecheck::{CheckedModule, check_module};
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
    Build {
        input: PathBuf,
        #[arg(short = 'o', long = "out")]
        out: Option<PathBuf>,
        #[arg(long, value_enum, default_value_t = OutputFormat::Pretty)]
        format: OutputFormat,
        #[arg(long, value_enum, default_value_t = DiagnosticsFormat::Pretty)]
        diagnostics: DiagnosticsFormat,
    },
}

#[derive(Debug, Clone, Copy, ValueEnum, PartialEq, Eq)]
enum OutputFormat {
    Pretty,
    Json,
}

#[derive(Debug, Clone, Copy, ValueEnum, PartialEq, Eq)]
enum DiagnosticsFormat {
    Pretty,
    Json,
}

#[derive(Debug, Serialize)]
struct IrDump {
    contract_version: &'static str,
    declarations: Vec<IrDeclDump>,
    value_types: BTreeMap<String, usize>,
    types: Vec<String>,
}

#[derive(Debug, Serialize)]
struct IrDeclDump {
    name: String,
    ty: usize,
    value: IrExprDump,
}

#[derive(Debug, Serialize)]
#[serde(tag = "kind")]
enum IrExprDump {
    Ident {
        value: String,
    },
    Int {
        value: String,
    },
    Float {
        value: String,
    },
    Char {
        value: String,
    },
    String {
        value: String,
    },
    DotIdent {
        name: String,
        payload: Option<Box<IrExprDump>>,
    },
    Closure {
        params: Vec<String>,
        return_ty: Option<usize>,
    },
    Any,
    List {
        items: Vec<IrExprDump>,
    },
    Dict {
        entries: Vec<(IrExprDump, IrExprDump)>,
    },
    Call {
        callee: Box<IrExprDump>,
        args: Vec<IrExprDump>,
    },
    BinaryOp {
        op: String,
        lhs: Box<IrExprDump>,
        rhs: Box<IrExprDump>,
        ty: usize,
    },
    MacroApply {
        macro_name: String,
        static_args: Vec<IrStaticArgDump>,
        operand: Box<IrExprDump>,
    },
    Label {
        label: String,
        expr: Box<IrExprDump>,
    },
    MultiArm {
        arms: Vec<IrExprDump>,
    },
    If {
        condition: Box<IrExprDump>,
        then_branch: Box<IrExprDump>,
        else_branch: Option<Box<IrExprDump>>,
    },
    Cases {
        arms: Vec<IrExprDump>,
    },
    Return {
        value: Box<IrExprDump>,
    },
    Break {
        value: Option<Box<IrExprDump>>,
    },
    Continue,
    Coerce {
        from: usize,
        to: usize,
        expr: Box<IrExprDump>,
    },
    Cast {
        from: usize,
        to: usize,
        expr: Box<IrExprDump>,
    },
}

#[derive(Debug, Serialize)]
#[serde(tag = "kind")]
enum IrStaticArgDump {
    Type { ty: IrTypeExprDump },
    Value { value: IrStaticValueDump },
}

#[derive(Debug, Serialize)]
#[serde(tag = "kind")]
enum IrTypeExprDump {
    Named {
        name: String,
        args: Vec<IrStaticArgDump>,
    },
    Static {
        inner: Box<IrTypeExprDump>,
    },
    InferHole,
}

#[derive(Debug, Serialize)]
#[serde(tag = "kind")]
enum IrStaticValueDump {
    Int { value: String },
    Float { value: String },
    Ident { value: String },
    String { value: String },
    Char { value: String },
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
        Commands::Build {
            input,
            out,
            format,
            diagnostics,
        } => build_cmd(&input, out.as_deref(), format, diagnostics),
    }
}

fn build_cmd(
    input: &Path,
    out: Option<&Path>,
    format: OutputFormat,
    diagnostics_format: DiagnosticsFormat,
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

    let checked = check_module(&program);
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
    let output_path = out
        .map(PathBuf::from)
        .unwrap_or_else(|| default_output_path(input, format));

    let rendered = match format {
        OutputFormat::Pretty => render_ir_pretty(module),
        OutputFormat::Json => render_ir_json(module)?,
    };

    if let Some(parent) = output_path.parent()
        && !parent.as_os_str().is_empty()
    {
        fs::create_dir_all(parent)
            .with_context(|| format!("failed to create output directory '{}'", parent.display()))?;
    }

    fs::write(&output_path, rendered)
        .with_context(|| format!("failed to write IR output '{}'", output_path.display()))?;
    println!("IR emitted to {}", output_path.display());
    Ok(ExitCode::SUCCESS)
}

fn default_output_path(input: &Path, format: OutputFormat) -> PathBuf {
    let stem = input
        .file_stem()
        .and_then(|s| s.to_str())
        .unwrap_or("output");
    let ext = match format {
        OutputFormat::Pretty => "ir.aura",
        OutputFormat::Json => "ir.json",
    };
    let file_name = format!("{stem}.{ext}");
    match input.parent() {
        Some(parent) => parent.join(file_name),
        None => PathBuf::from(file_name),
    }
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

fn render_ir_json(module: &CheckedModule) -> Result<String> {
    let mut value_types = BTreeMap::new();
    for (name, ty) in &module.value_types {
        value_types.insert(name.clone(), ty.0);
    }

    let mut types = Vec::new();
    let mut i = 0usize;
    while let Some(ty) = module.types.get(aura_typecheck::TyId(i)) {
        types.push(format!("{ty:?}"));
        i += 1;
    }

    let declarations = module
        .ir
        .declarations
        .iter()
        .map(|d| IrDeclDump {
            name: d.name.clone(),
            ty: d.ty.0,
            value: to_ir_expr(&d.value),
        })
        .collect();

    let dump = IrDump {
        contract_version: "v1",
        declarations,
        value_types,
        types,
    };

    Ok(serde_json::to_string_pretty(&dump)?)
}

fn to_ir_expr(expr: &CheckedExpr) -> IrExprDump {
    match expr {
        CheckedExpr::Ident(v) => IrExprDump::Ident { value: v.clone() },
        CheckedExpr::Int(v) => IrExprDump::Int { value: v.clone() },
        CheckedExpr::Float(v) => IrExprDump::Float { value: v.clone() },
        CheckedExpr::Char(v) => IrExprDump::Char { value: v.clone() },
        CheckedExpr::String(v) => IrExprDump::String { value: v.clone() },
        CheckedExpr::DotIdent { name, payload } => IrExprDump::DotIdent {
            name: name.clone(),
            payload: payload.as_ref().map(|p| Box::new(to_ir_expr(p))),
        },
        CheckedExpr::Closure { params, return_ty } => IrExprDump::Closure {
            params: params.clone(),
            return_ty: return_ty.map(|t| t.0),
        },
        CheckedExpr::Any => IrExprDump::Any,
        CheckedExpr::List(items) => IrExprDump::List {
            items: items.iter().map(to_ir_expr).collect(),
        },
        CheckedExpr::Dict(entries) => IrExprDump::Dict {
            entries: entries
                .iter()
                .map(|(k, v)| (to_ir_expr(k), to_ir_expr(v)))
                .collect(),
        },
        CheckedExpr::Call { callee, args } => IrExprDump::Call {
            callee: Box::new(to_ir_expr(callee)),
            args: args.iter().map(to_ir_expr).collect(),
        },
        CheckedExpr::BinaryOp { op, lhs, rhs, ty } => IrExprDump::BinaryOp {
            op: binary_op_name(*op).to_string(),
            lhs: Box::new(to_ir_expr(lhs)),
            rhs: Box::new(to_ir_expr(rhs)),
            ty: ty.0,
        },
        CheckedExpr::MacroApply {
            macro_name,
            static_args,
            operand,
        } => IrExprDump::MacroApply {
            macro_name: macro_name.clone(),
            static_args: static_args.iter().map(to_ir_static_arg).collect(),
            operand: Box::new(to_ir_expr(operand)),
        },
        CheckedExpr::Label { label, expr } => IrExprDump::Label {
            label: label.clone(),
            expr: Box::new(to_ir_expr(expr)),
        },
        CheckedExpr::MultiArm(arms) => IrExprDump::MultiArm {
            arms: arms.iter().map(to_ir_expr).collect(),
        },
        CheckedExpr::If {
            condition,
            then_branch,
            else_branch,
        } => IrExprDump::If {
            condition: Box::new(to_ir_expr(condition)),
            then_branch: Box::new(to_ir_expr(then_branch)),
            else_branch: else_branch.as_ref().map(|e| Box::new(to_ir_expr(e))),
        },
        CheckedExpr::Cases { arms } => IrExprDump::Cases {
            arms: arms.iter().map(to_ir_expr).collect(),
        },
        CheckedExpr::Return { value } => IrExprDump::Return {
            value: Box::new(to_ir_expr(value)),
        },
        CheckedExpr::Break { value } => IrExprDump::Break {
            value: value.as_ref().map(|v| Box::new(to_ir_expr(v))),
        },
        CheckedExpr::Continue => IrExprDump::Continue,
        CheckedExpr::Coerce { from, to, expr } => IrExprDump::Coerce {
            from: from.0,
            to: to.0,
            expr: Box::new(to_ir_expr(expr)),
        },
        CheckedExpr::Cast { from, to, expr } => IrExprDump::Cast {
            from: from.0,
            to: to.0,
            expr: Box::new(to_ir_expr(expr)),
        },
    }
}

fn to_ir_static_arg(arg: &CheckedStaticArg) -> IrStaticArgDump {
    match arg {
        CheckedStaticArg::Type(ty) => IrStaticArgDump::Type {
            ty: to_ir_type_expr(ty),
        },
        CheckedStaticArg::Value(v) => IrStaticArgDump::Value {
            value: to_ir_static_value(v),
        },
    }
}

fn to_ir_type_expr(ty: &CheckedTypeExpr) -> IrTypeExprDump {
    match ty {
        CheckedTypeExpr::Named { name, args } => IrTypeExprDump::Named {
            name: name.clone(),
            args: args.iter().map(to_ir_static_arg).collect(),
        },
        CheckedTypeExpr::Static(inner) => IrTypeExprDump::Static {
            inner: Box::new(to_ir_type_expr(inner)),
        },
        CheckedTypeExpr::InferHole => IrTypeExprDump::InferHole,
    }
}

fn to_ir_static_value(v: &CheckedStaticValue) -> IrStaticValueDump {
    match v {
        CheckedStaticValue::Int(s) => IrStaticValueDump::Int { value: s.clone() },
        CheckedStaticValue::Float(s) => IrStaticValueDump::Float { value: s.clone() },
        CheckedStaticValue::Ident(s) => IrStaticValueDump::Ident { value: s.clone() },
        CheckedStaticValue::String(s) => IrStaticValueDump::String { value: s.clone() },
        CheckedStaticValue::Char(s) => IrStaticValueDump::Char { value: s.clone() },
    }
}

fn binary_op_name(op: BinaryOpKind) -> &'static str {
    match op {
        BinaryOpKind::Add => "add",
        BinaryOpKind::Sub => "sub",
        BinaryOpKind::Mul => "mul",
        BinaryOpKind::Div => "div",
        BinaryOpKind::Mod => "mod",
        BinaryOpKind::Lt => "lt",
        BinaryOpKind::Gt => "gt",
        BinaryOpKind::Le => "le",
        BinaryOpKind::Ge => "ge",
        BinaryOpKind::Eq => "eq",
        BinaryOpKind::Neq => "neq",
        BinaryOpKind::And => "and",
        BinaryOpKind::Or => "or",
    }
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
            d.severity, d.stage, d.code, d.message, span, d.hint
        );
        if !seen.insert(fingerprint) {
            continue;
        }
        prepared.push(PreparedDiagnostic {
            code: d.code,
            stage,
            severity: d.severity,
            message: d.message.clone(),
            span,
            span_origin,
            hint: d.hint.clone(),
            related,
            obligations: d.obligations.clone(),
        });
    }
    prepared
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
            return Some(span_from_line(source, line_idx + 1, name_start + 1, name.len()));
        }
        let method_marker = format!(".{name}(");
        if let Some(start_idx) = line.find(&method_marker) {
            let name_start = start_idx + 1;
            return Some(span_from_line(source, line_idx + 1, name_start + 1, name.len()));
        }
    }
    None
}

fn find_static_decl_name_span(source: &str, name: &str) -> Option<Span> {
    for (line_idx, line) in source.lines().enumerate() {
        let marker = format!("def {name}");
        if let Some(start_idx) = line.find(&marker) {
            let name_start = start_idx + 4;
            return Some(span_from_line(source, line_idx + 1, name_start + 1, name.len()));
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
        d.message
    );

    if let Some(span) = d.span {
        eprintln!(
            "  {} {}:{}:{}",
            palette.dim("-->"),
            input.display(),
            span.line,
            span.column
        );
        if let Some((line_no, line_text, pointer)) = render_span_snippet(source, span, &d.message, colors)
        {
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
                "  {} {}",
                palette.dim("= note:"),
                "location inferred from typechecking context"
            );
        }
    }

    if !d.obligations.is_empty() {
        eprintln!(
            "  {} {}",
            palette.dim("= context:"),
            d.obligations.join(" > ")
        );
    }

    for related in &d.related {
        if let Some(span) = related.span {
            eprintln!(
                "  {} {} ({}:{})",
                palette.dim("= related:"),
                related.label,
                span.line,
                span.column
            );
        } else {
            eprintln!("  {} {}", palette.dim("= related:"), related.label);
        }
    }

    if let Some(hint) = &d.hint {
        eprintln!("  {} {}", palette.help("= help:"), hint);
    }
}

fn render_span_snippet(
    source: &str,
    span: Span,
    message: &str,
    colors: bool,
) -> Option<(usize, String, String)> {
    let lines = source.lines().collect::<Vec<_>>();
    if lines.is_empty() {
        return None;
    }
    let line_idx = span.line.saturating_sub(1).min(lines.len().saturating_sub(1));
    let line_text = lines[line_idx];
    let highlighted = highlight_source_line(line_text, colors);
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

fn highlight_source_line(line: &str, colors: bool) -> String {
    if !colors {
        return line.to_string();
    }
    const RESET: &str = "\x1b[0m";
    const KW: &str = "\x1b[35;1m";
    const STR: &str = "\x1b[36m";
    const NUM: &str = "\x1b[33m";
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
        self.style(text, Style::new().fg_color(Some(Color::Ansi(AnsiColor::Red))).effects(Effects::BOLD))
    }

    fn warning(&self, text: &str) -> String {
        self.style(text, Style::new().fg_color(Some(Color::Ansi(AnsiColor::Yellow))).effects(Effects::BOLD))
    }

    fn help(&self, text: &str) -> String {
        self.style(text, Style::new().fg_color(Some(Color::Ansi(AnsiColor::Cyan))).effects(Effects::BOLD))
    }

    fn pointer(&self, text: &str) -> String {
        self.style(text, Style::new().fg_color(Some(Color::Ansi(AnsiColor::Magenta))).effects(Effects::BOLD))
    }

    fn dim(&self, text: &str) -> String {
        self.style(text, Style::new().fg_color(Some(Color::Ansi(AnsiColor::BrightBlack))))
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
    use aura_diagnostics::{RelatedLabel, Stage};

    #[test]
    fn prepare_diagnostics_filters_internal_related_labels() {
        let diag = Diagnostic::error("E_TYPE_MISMATCH", "mismatch")
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
        let diag1 = Diagnostic::error("E_X", "same").with_stage(Stage::Parser);
        let diag2 = Diagnostic::error("E_X", "same").with_stage(Stage::Parser);
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
        let rendered = render_span_snippet("def x = macro_name[T]", span, "problem", false)
            .expect("snippet fallback");
        assert_eq!(rendered.0, 1);
        assert!(rendered.2.contains('^'));
    }

    #[test]
    fn is_internal_related_label_covers_known_patterns() {
        assert!(is_internal_related_label(
            "source span unavailable in current typed AST"
        ));
        assert!(is_internal_related_label("assignment compatibility check failed"));
        assert!(is_internal_related_label("IR coercion/cast decision failed"));
        assert!(!is_internal_related_label("real related note"));
    }

    #[test]
    fn json_prepared_keeps_user_related_labels() {
        let diag = Diagnostic {
            code: "E_CUSTOM",
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
}
