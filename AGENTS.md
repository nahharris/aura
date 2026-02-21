# Aura — Agent Guidelines

This file provides guidance for agentic coding agents working in this repository.

## Project Overview

**Aura** is a Rust implementation of a parser and compiler front-end for a new functional programming language (also named Aura). The language targets application development with functional primitives, macro-based control flow, and trailing-lambda call syntax.

Key source files:
- `src/grammar.pest` — PEG grammar definition (pest)
- `src/ast.rs` — AST node types
- `src/parser.rs` — Recursive-descent parser + Pratt operator precedence
- `src/lib.rs` — Crate root; exports modules and defines `AuraError`/`AuraResult`
- `src/main.rs` — Binary entry point; runs parse verification examples
- `DESIGN.md` — Authoritative language design specification

---

## Build, Lint, and Test Commands

```bash
# Check for compile errors without producing an artifact (fastest feedback loop)
cargo check

# Build (debug)
cargo build

# Build (release)
cargo build --release

# Run the binary (grammar verification examples)
cargo run

# Run all tests
cargo test

# Run a single test by name (substring match against test function names)
cargo test <test_name>

# Run all tests in a module
cargo test parser::

# Run tests with stdout visible (useful for debugging)
cargo test -- --nocapture

# Lint (run before every commit)
cargo clippy

# Lint and treat warnings as errors (CI-equivalent strictness)
cargo clippy -- -D warnings

# Format code
cargo fmt

# Check formatting without modifying files
cargo fmt -- --check
```

There are no custom scripts; Cargo's built-in subcommands serve all roles.  
There is no CI configuration yet, but `cargo clippy -- -D warnings` and `cargo fmt -- --check` define the expected quality gate.

---

## Dependencies

| Crate | Version | Role |
|---|---|---|
| `pest` | 2.7 | PEG parser runtime |
| `pest_derive` | 2.7 | `#[derive(Parser)]` proc-macro; reads `grammar.pest` at compile time |
| `thiserror` | 1.0 | `#[derive(Error)]` for ergonomic error types |
| `lazy_static` | 1.4 | Lazy-initialized statics (used for `PRATT_PARSER`) |

When adding dependencies, prefer crates already in this list before introducing new ones.

---

## Code Style

### Naming Conventions

| Kind | Convention | Example |
|---|---|---|
| Types, structs, enums | `PascalCase` | `AuraParser`, `FnDecl`, `BinaryOp` |
| Enum variants | `PascalCase` | `Expr::BinaryOp`, `Literal::Int` |
| Functions and methods | `snake_case` | `parse_stmt`, `combine_call` |
| Variables and fields | `snake_case` | `final_expr`, `return_type`, `then_block` |
| Lazy statics / constants | `SCREAMING_SNAKE_CASE` | `PRATT_PARSER` |
| Grammar rules (`.pest`) | `snake_case` | `fn_decl`, `list_items`, `trailing_lambda` |

### Imports

Group `use` statements at the top of each file in this order, separated by blank lines:

1. Standard library (`std::`)
2. External crates (`pest::`, `lazy_static::`, etc.)
3. Internal crate modules (`crate::`, `super::`)

Prefer grouped imports on one line when items come from the same module path:

```rust
use pest::{iterators::Pair, iterators::Pairs, Parser};
use pest::pratt_parser::{Assoc, Op, PrattParser};
use crate::ast::*;
use crate::{AuraError, AuraResult};
```

Glob imports (`use crate::ast::*`) are acceptable for AST types since they are universally needed throughout the parser.

### Formatting

Follow the defaults of `rustfmt` (Rust 2021 edition). Run `cargo fmt` before every commit. Notable defaults:
- 4-space indentation
- Maximum line width of 100 characters
- Trailing commas in multi-line structures

### Types and Generics

- Use `Box<T>` for recursive AST nodes (e.g., `Box<Expr>`, `Box<Block>`).
- Prefer `Vec<T>` for lists of children.
- Use `Option<T>` rather than sentinel values or nullable raw pointers.
- Type aliases (`AuraResult<T>`) are preferred over spelling out `Result<T, AuraError>` everywhere.
- Simplified/placeholder types (e.g., `return_type: Option<String>`) are acceptable during prototyping; mark them with `// TODO:` comments.

### Error Handling

- All fallible public functions return `AuraResult<T>` (`Result<T, AuraError>`).
- Propagate errors with the `?` operator; do not `unwrap()` in library code.
- `unwrap()` is acceptable inside `parse_*` private functions when a branch is structurally guaranteed by the grammar (i.e., pest has already validated the shape). Add a comment explaining why the unwrap is safe if it is non-obvious.
- Use `unreachable!()` (with an optional message) for match arms that are impossible given the grammar rules:
  ```rust
  _ => unreachable!("Unexpected primary: {:?}", inner.as_rule()),
  ```
- Extend `AuraError` via `thiserror` for any new error category; use `#[from]` for automatic conversions:
  ```rust
  #[derive(thiserror::Error, Debug)]
  pub enum AuraError {
      #[error("Parse error: {0}")]
      ParseError(#[from] pest::error::Error<parser::Rule>),
  }
  ```

### AST and Data Structures

- Enums model sum types; structs model product types — do not mix them unnecessarily.
- Prefer inline struct variants (`BinaryOp { lhs, op, rhs }`) over separate structs when the type is only used as that variant.
- Use separate named structs (`FnDecl`, `Param`, `Block`) when the type is shared across multiple contexts or is complex enough to benefit from named methods.
- Derive `Debug`, `Clone`, `PartialEq` on all AST nodes unless there is a specific reason not to.

### Parser Functions

- One `parse_*` function per grammar rule; keep them small and single-purpose.
- All `parse_*` functions return `AuraResult<T>`.
- Walk pest parse trees using `.into_inner()` / `.next()` / `.as_rule()` / `.as_str()`.
- Operator precedence is handled centrally by `PRATT_PARSER` (`lazy_static`). Do not implement precedence ad-hoc elsewhere.
- Post-parse AST optimizations (e.g., rewriting `Call { func: "if", ... }` to `Expr::If`) belong in `Expr::optimize()`, not in the parser itself.

### Grammar (`grammar.pest`)

- Rule names use `snake_case`.
- Prefer composing rules from smaller named rules rather than writing large monolithic rules.
- Whitespace/comment handling is done via `WHITESPACE` and `COMMENT` silent rules.
- When modifying the grammar, re-run `cargo run` to verify that all examples in `main.rs` still parse correctly.

### Display Implementations

Implement `fmt::Display` for operator and literal enums via exhaustive `match` with `write!(f, ...)`:

```rust
impl fmt::Display for BinaryOp {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            BinaryOp::Add => write!(f, "+"),
            // ...
        }
    }
}
```

---

## Testing

Tests do not yet exist as a formal suite. When adding tests:

- Place unit tests in `#[cfg(test)]` modules at the bottom of the relevant source file.
- Place integration tests in a `tests/` directory at the crate root.
- Name test functions descriptively: `test_parse_let_binding`, `test_binary_op_precedence`.
- Use `cargo test <test_name>` to run a single test.
- Prefer `assert_eq!` over `assert!` so failures print the actual vs. expected values.

---

## Language Design Reference

`DESIGN.md` is the authoritative specification for the Aura language syntax and semantics. Before modifying the grammar or AST, consult `DESIGN.md` to ensure consistency. Key design decisions:

- Semicolons are required to terminate statements.
- Control flow (`if`, `while`, `for`, `loop`) is macro-based, not built-in syntax.
- Functions are first-class values; closures use `{ params -> body }` syntax.
- Trailing-lambda syntax allows the last function argument(s) to be written outside the parentheses.
- After a `}`, a newline has the same effect as a `;` — no implicit line continuation.
- Type annotations use `:`, casts also use `:`, and the safe-navigation operator is `?.`.
