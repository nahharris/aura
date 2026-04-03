use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::ExitCode;

use anyhow::{Context, Result};
use aura_diagnostics::{Diagnostic, Severity};
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
            print_diagnostics(&[diag], diagnostics_format)?;
            return Ok(ExitCode::from(1));
        }
    };

    let checked = check_module(&program);
    let has_errors = checked
        .diagnostics
        .iter()
        .any(|d| d.severity == Severity::Error);

    if has_errors {
        print_diagnostics(&checked.diagnostics, diagnostics_format)?;
        return Ok(ExitCode::from(1));
    }

    if !checked.diagnostics.is_empty() {
        print_diagnostics(&checked.diagnostics, diagnostics_format)?;
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

fn print_diagnostics(diags: &[Diagnostic], fmt: DiagnosticsFormat) -> Result<()> {
    match fmt {
        DiagnosticsFormat::Pretty => {
            for d in diags {
                let sev = match d.severity {
                    Severity::Error => "error",
                    Severity::Warning => "warning",
                };
                eprintln!("[{sev}][{:?}][{}] {}", d.stage, d.code, d.message);
                if let Some(span) = d.span {
                    eprintln!("  at {}:{}", span.line, span.column);
                }
                if !d.obligations.is_empty() {
                    eprintln!("  obligations: {}", d.obligations.join(" > "));
                }
                for related in &d.related {
                    if let Some(span) = related.span {
                        eprintln!(
                            "  related: {} ({}:{})",
                            related.label, span.line, span.column
                        );
                    } else {
                        eprintln!("  related: {}", related.label);
                    }
                }
                if let Some(hint) = &d.hint {
                    eprintln!("  hint: {hint}");
                }
            }
            Ok(())
        }
        DiagnosticsFormat::Json => {
            let payload: Vec<_> = diags
                .iter()
                .map(|d| {
                    serde_json::json!({
                        "code": d.code,
                        "stage": format!("{:?}", d.stage),
                        "severity": match d.severity { Severity::Error => "error", Severity::Warning => "warning" },
                        "message": d.message,
                        "span": d.span.map(|s| serde_json::json!({"line": s.line, "column": s.column, "start": s.start, "end": s.end})),
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
