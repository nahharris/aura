//! Aura language command-line interface.
//!
//! # Usage
//!
//! ```text
//! aura <file.aura>          # Execute a source file
//! aura --check <file.aura>  # Lex + parse + compile only (no execution)
//! aura --dump-bytecode <file.aura>  # Compile and dump disassembly
//! aura --version            # Print version
//! aura --help               # Print usage
//! ```

use std::path::Path;
use std::process;

fn main() {
    let args: Vec<String> = std::env::args().collect();

    // No arguments: show help.
    if args.len() < 2 {
        print_usage();
        process::exit(1);
    }

    match args[1].as_str() {
        "--help" | "-h" => {
            print_usage();
        }
        "--version" | "-V" => {
            println!("aura {}", env!("CARGO_PKG_VERSION"));
        }
        "--check" => {
            let path = require_path(&args, "--check");
            check_file(&path);
        }
        "--dump-bytecode" => {
            let path = require_path(&args, "--dump-bytecode");
            dump_bytecode(&path);
        }
        flag if flag.starts_with('-') => {
            eprintln!("aura: unknown flag `{flag}`");
            eprintln!("Run `aura --help` for usage.");
            process::exit(1);
        }
        file_path => {
            run_file(file_path);
        }
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Helpers
// ─────────────────────────────────────────────────────────────────────────────

fn print_usage() {
    println!(
        "\
Usage: aura [OPTIONS] <file.aura>

Options:
  --check <file>          Lex, parse, and compile without executing
  --dump-bytecode <file>  Compile and print bytecode disassembly
  --version, -V           Print version information
  --help, -h              Print this help message

Examples:
  aura hello.aura
  aura --check program.aura
  aura --dump-bytecode program.aura"
    );
}

/// Require that a second argument (file path) is present after a flag.
fn require_path(args: &[String], flag: &str) -> String {
    if args.len() < 3 {
        eprintln!("aura: `{flag}` requires a file path");
        process::exit(1);
    }
    args[2].clone()
}

/// Read a source file, reporting errors and exiting on failure.
fn read_source(path: &str) -> String {
    if !Path::new(path).exists() {
        eprintln!("aura: file not found: {path}");
        process::exit(1);
    }
    match std::fs::read_to_string(path) {
        Ok(src) => src,
        Err(e) => {
            eprintln!("aura: cannot read `{path}`: {e}");
            process::exit(1);
        }
    }
}

// ─────────────────────────────────────────────────────────────────────────────
// Modes
// ─────────────────────────────────────────────────────────────────────────────

/// Execute a source file.
fn run_file(path: &str) {
    let src = read_source(path);
    match aura::run_source(&src, path) {
        Ok(()) => {}
        Err(e) => {
            eprintln!("{}", format_error(path, &src, &e));
            process::exit(1);
        }
    }
}

/// Lex + parse + compile only (no execution).
fn check_file(path: &str) {
    let src = read_source(path);
    match aura::parse_source(&src) {
        Err(e) => {
            eprintln!("{}", format_error(path, &src, &e));
            process::exit(1);
        }
        Ok(program) => match aura::compile_program(program) {
            Err(e) => {
                eprintln!("{}", format_error(path, &src, &e));
                process::exit(1);
            }
            Ok(_) => {
                println!("{path}: OK");
            }
        },
    }
}

/// Compile and dump bytecode disassembly.
fn dump_bytecode(path: &str) {
    let src = read_source(path);
    let program = match aura::parse_source(&src) {
        Ok(p) => p,
        Err(e) => {
            eprintln!("{}", format_error(path, &src, &e));
            process::exit(1);
        }
    };
    let chunk = match aura::compile_program(program) {
        Ok(c) => c,
        Err(e) => {
            eprintln!("{}", format_error(path, &src, &e));
            process::exit(1);
        }
    };
    print!("{}", aura::bytecode::disassemble(&chunk, path));
}

// ─────────────────────────────────────────────────────────────────────────────
// Error formatting
// ─────────────────────────────────────────────────────────────────────────────

/// Format an [`aura::AuraError`] with optional source-context caret.
fn format_error(path: &str, src: &str, err: &aura::AuraError) -> String {
    use aura::AuraError;
    match err {
        AuraError::Lex(errors) => {
            let mut out = String::new();
            for e in errors {
                out.push_str(&format_span_error(path, src, e.span.start, &e.message));
            }
            out
        }
        AuraError::Parse(errors) => {
            let mut out = String::new();
            for e in errors {
                out.push_str(&format_span_error(path, src, e.span.start, &e.message));
            }
            out
        }
        AuraError::Compile(msg) => {
            format!("error[compile]: {path}: {msg}\n")
        }
        AuraError::Runtime(msg) => {
            format!("error[runtime]: {path}: {msg}\n")
        }
        AuraError::Io(e) => {
            format!("error[io]: {path}: {e}\n")
        }
    }
}

/// Format a single error with a source-context caret pointing at the error
/// position.
///
/// ```text
/// error: path/to/file.aura:3:12: unexpected token `}`
///    |
///  3 | defn foo() { }
///    |            ^
/// ```
fn format_span_error(path: &str, src: &str, byte_offset: usize, message: &str) -> String {
    // Find line number and column from byte offset.
    let byte_offset = byte_offset.min(src.len());
    let before = &src[..byte_offset];
    let line = before.chars().filter(|&c| c == '\n').count() + 1;
    let col = before
        .rfind('\n')
        .map(|n| byte_offset - n - 1)
        .unwrap_or(byte_offset)
        + 1;

    // Extract the source line.
    let source_line = src
        .lines()
        .nth(line - 1)
        .unwrap_or("")
        .replace('\t', "    ");

    let line_num_str = line.to_string();
    let gutter = " ".repeat(line_num_str.len());
    let caret_col = col.saturating_sub(1);
    let caret = format!("{}^", " ".repeat(caret_col));

    format!(
        "error: {path}:{line}:{col}: {message}\n {gutter} |\n {line_num_str} | {source_line}\n {gutter} | {caret}\n"
    )
}
