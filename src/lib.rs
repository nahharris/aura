//! The Aura language compiler and runtime library.
//!
//! This crate provides the complete Aura language pipeline:
//!
//! 1. **Lexer** (`lexer`) — tokenises source text into a flat `Vec<Token>`.
//! 2. **Parser** (`parser`) — builds a typed [`ast::Program`] from the token stream.
//! 3. **Type checker** (`typechecker`) — static type analysis pass (Phase 4).
//! 4. **Bytecode** (`bytecode`) — `OpCode` definitions and `Chunk` (bytecode + constants).
//! 5. **Values** (`value`) — runtime `Value` enum, heap `Object` variants.
//! 6. **GC** (`gc`) — mark-and-sweep garbage collector with `GcHeap` / `GcPtr<T>`.
//! 7. **Compiler** (`compiler`) — lowers AST to bytecode `Chunk`s.
//! 8. **Builtins** (`builtins`) — native Rust functions exposed to Aura programs.
//! 9. **VM** (`vm`) — stack-based interpreter that executes `Chunk`s.
//!
//! # Entry point
//!
//! The simplest way to run an Aura program from Rust is:
//!
//! ```rust,ignore
//! use aura::run_source;
//! run_source(source_code, file_path).unwrap();
//! ```

// ─────────────────────────────────────────────────────────────────────────────
// Modules
// ─────────────────────────────────────────────────────────────────────────────

pub mod ast;
pub mod builtins;
pub mod bytecode;
pub mod compiler;
pub mod gc;
pub mod lexer;
pub mod parser;
pub mod token;
pub mod typechecker;
pub mod value;
pub mod vm;

// ─────────────────────────────────────────────────────────────────────────────
// Unified error type
// ─────────────────────────────────────────────────────────────────────────────

use crate::lexer::LexError;
use crate::parser::ParseError;
use crate::typechecker::TypeError;

/// The unified error type for all Aura pipeline stages.
///
/// Each variant wraps errors from the corresponding compiler stage so that
/// callers can handle them uniformly or match on the specific stage.
#[derive(Debug, thiserror::Error)]
pub enum AuraError {
    /// One or more lexical errors.
    #[error("Lex error at {}: {}", .0.first().map(|e| e.span.to_string()).unwrap_or_default(), .0.iter().map(|e| e.message.clone()).collect::<Vec<_>>().join("; "))]
    Lex(Vec<LexError>),

    /// One or more parse errors.
    #[error("Parse error at {}: {}", .0.first().map(|e| e.span.to_string()).unwrap_or_default(), .0.iter().map(|e| e.message.clone()).collect::<Vec<_>>().join("; "))]
    Parse(Vec<ParseError>),

    /// One or more static type errors.
    #[error("Type error: {}", .0.iter().map(|e| e.to_string()).collect::<Vec<_>>().join("; "))]
    Type(Vec<TypeError>),

    /// A compile-time error (name resolution, scope, etc.).
    #[error("Compile error: {0}")]
    Compile(String),

    /// A runtime error raised by the VM.
    #[error("Runtime error: {0}")]
    Runtime(String),

    /// An I/O error (file reading, module loading, etc.).
    #[error("I/O error: {0}")]
    Io(#[from] std::io::Error),
}

/// Shorthand result type for all Aura operations.
pub type AuraResult<T> = Result<T, AuraError>;

// ─────────────────────────────────────────────────────────────────────────────
// Pipeline helpers
// ─────────────────────────────────────────────────────────────────────────────

/// Lex and parse an Aura source string, returning a typed [`ast::Program`].
///
/// Both lex errors and parse errors are promoted to [`AuraError`] if non-empty.
/// The function returns the *last* error list that was non-empty, preferring
/// lex errors over parse errors if both appear.
pub fn parse_source(src: &str) -> AuraResult<ast::Program> {
    let (tokens, lex_errors) = lexer::lex(src);
    if !lex_errors.is_empty() {
        return Err(AuraError::Lex(lex_errors));
    }
    let (program, parse_errors) = parser::parse_tokens(tokens);
    if !parse_errors.is_empty() {
        return Err(AuraError::Parse(parse_errors));
    }
    Ok(program)
}

/// Compile an [`ast::Program`] to a bytecode [`bytecode::Chunk`].
pub fn compile_program(program: ast::Program) -> AuraResult<bytecode::Chunk> {
    compiler::compile(program).map_err(|e| AuraError::Compile(e.to_string()))
}

/// Run the static type checker over a parsed [`ast::Program`].
///
/// Returns `Ok(())` if no type errors were found, or `Err(AuraError::Type(...))`
/// with all collected errors otherwise.
pub fn typecheck_program(program: &ast::Program) -> AuraResult<()> {
    typechecker::check(program).map_err(AuraError::Type)
}

/// Full pipeline: lex → parse → typecheck → compile → run.
///
/// `file_path` is used only for error messages and module resolution.
pub fn run_source(src: &str, file_path: &str) -> AuraResult<()> {
    let program = parse_source(src)?;
    typecheck_program(&program)?;
    let chunk = compile_program(program)?;
    let mut heap = gc::GcHeap::new();
    let mut machine = vm::Vm::new(&mut heap, file_path);

    // Load STL modules before user code
    load_stl(&mut machine)?;

    machine
        .run(chunk)
        .map_err(|e| AuraError::Runtime(e.to_string()))
}

/// Load the standard library into the VM.
///
/// This runs the STL files to register their globals before user code executes.
/// Only the minimal set of modules needed by the type checker is loaded:
/// string, list, and io.
fn load_stl(vm: &mut vm::Vm) -> AuraResult<()> {
    let modules: [(&str, &str); 3] = [
        ("stl/string", include_str!("../stl/string.aura")),
        ("stl/list", include_str!("../stl/list.aura")),
        ("stl/io", include_str!("../stl/io.aura")),
    ];

    for (name, source) in modules {
        let program = parse_source(source)?;
        // STL files are trusted internal code; skip the typechecker so that
        // intentionally loose signatures (bare `List`, `Any` params) do not
        // produce false-positive type errors.
        let chunk = compile_program(program)?;
        vm.run_module(chunk, name)
            .map_err(|e| AuraError::Runtime(e.to_string()))?;
    }

    Ok(())
}
