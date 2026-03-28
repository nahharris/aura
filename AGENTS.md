# Aura — Agent Guidelines

This file provides guidance for agentic coding agents working in this repository.

## Project Overview

**Aura** is a Rust implementation of a lexer, parser, static type checker, bytecode compiler, and garbage-collected VM for the Aura programming language. The surface emphasizes functional primitives, macro-oriented control flow (minimal reserved keywords), closures with trailing-lambda call syntax, and pattern matching via **multi-arm closure application** `{ ... }(value)` — not a separate `match` keyword.

Key source files:

- `src/lexer.rs` — tokenizes source into `Vec<Token>`
- `src/token.rs` — `Token`, `TokenKind`, spans
- `src/parser.rs` — recursive-descent parser + binding-power (Pratt-style) expression parsing
- `src/ast.rs` — AST node types
- `src/typechecker.rs` — static analysis
- `src/compiler.rs` — AST → bytecode
- `src/vm.rs` — bytecode interpreter
- `src/lib.rs` — crate root; `AuraError` / `AuraResult` and pipeline helpers (`parse_source`, `run_source`, …)
- `src/main.rs` — CLI (`aura`, `--check`, `--dump-bytecode`)
- `DESIGN.md` — authoritative language design specification

---

## Build, Lint, and Test Commands

```bash
cargo check
cargo build
cargo build --release
cargo run              # CLI help if no file; use aura <file.aura> for execution
cargo test
cargo test <test_name>
cargo test parser::
cargo test -- --nocapture
cargo clippy
cargo clippy -- -D warnings
cargo fmt
cargo fmt -- --check
```

There is no CI configuration yet; `cargo clippy -- -D warnings` and `cargo fmt -- --check` define the expected quality gate.

---

## Dependencies

| Crate       | Version | Role                                      |
|-------------|---------|-------------------------------------------|
| `thiserror` | 1.0     | `#[derive(Error)]` for `AuraError` stages |

When adding dependencies, prefer crates already in this list before introducing new ones.

---

## Code Style

### Naming Conventions

| Kind                       | Convention              | Example                  |
|----------------------------|-------------------------|--------------------------|
| Types, structs, enums      | `PascalCase`            | `Parser`, `BinaryOp`    |
| Enum variants              | `PascalCase`            | `Expr::Binary`           |
| Functions and methods      | `snake_case`            | `parse_stmt`, `parse_expr` |
| Variables and fields       | `snake_case`            | `then_block`             |
| Constants / statics        | `SCREAMING_SNAKE_CASE`  | (when used)              |

### Imports

Group `use` at the top: std, external crates, then `crate::` / `super::`, separated by blank lines.  
Glob imports (`use crate::ast::*`) are acceptable in parser/compiler code that is AST-heavy.

### Formatting

`rustfmt` defaults, Rust 2021, 100-column width where applicable. Run `cargo fmt` before commit.

### Types and Generics

- Use `Box<T>` for recursive AST nodes.
- Prefer `Vec<T>` and `Option<T>` over sentinels.
- Use `AuraResult<T>` from `lib.rs` for public pipeline APIs.

### Error Handling

- Library pipeline functions return `AuraResult<T>` with `AuraError` variants (`Lex`, `Parse`, `Type`, `Compile`, `Runtime`, `Io`).
- Inside the parser, fallible private methods return `Result<..., ParseError>`; `parse(src)` aggregates lex + parse errors.
- `unwrap()` is acceptable only when grammar guarantees the case; comment non-obvious safety.
- Use `unreachable!` for arms impossible given the tokenizer/grammar.

### Parser Functions

- One `parse_*` per syntactic construct where practical; keep helpers focused.
- Operator precedence is centralized (binding powers in `parser.rs`); do not duplicate precedence tables ad hoc.
- Post-parse rewrites belong in dedicated passes (e.g. `Expr::optimize()`), not scattered in `parse_*`.

### Display implementations

Implement `fmt::Display` for operator enums with exhaustive `match` and `write!`.

---

## Testing

- Unit tests: `#[cfg(test)]` at the bottom of the relevant module (`parser.rs`, `typechecker.rs`, etc.).
- Integration tests: optional `tests/` at crate root.
- Name tests descriptively: `test_parse_let_binding`, `test_binary_op_precedence`.
- Prefer `assert_eq!` when comparing values.

---

## Language design reference

Consult `DESIGN.md` before changing grammar or AST. Important points:

- Semicolons terminate statements (with the newline-after-`}` rule as in the spec).
- Prefer **minimal reserved keywords**; control surfaces trend toward macros (builtin or user).
- Pattern matching on a scrutinee: **multi-arm closure + call** `{ pattern -> expr, ... }(value)` — no `match` / `=>`.
- Closures: `{ params -> body }`; `cases` uses guard arms with `~` and `->`.
- Trailing-lambda call syntax for the last argument(s).
- Type annotations and casts use `:`; safe navigation `?.`.

### Design alignment

- **`DESIGN.md` is authoritative.** If you change lexer, parser, AST, typechecker, or runtime behavior that users can observe, update `DESIGN.md` in the same change when the spec is affected.
- **Strict type, null, and memory safety** is the product stance: disciplined typing (Rust/Haskell-flavored surface), explicit optional/enum designs for null — no “loose” omission of types. Where syntax allows a **bare field name** in a **struct type** `(field)`, it is **sugar for `(field: Void)`** — `Void` is the real, explicit type after desugaring.
- **Maps** are spelled **`Dict[K, V]`** only — not `Map`.
- **Regression tests:** new syntax or typing rules should include `parser::` / `typechecker::` tests (or `tests/`) so the spec does not drift silently.
