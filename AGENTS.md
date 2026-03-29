# Aura — Agent Guidelines

This file provides guidance for coding agents working in this repository.

## Project Overview

Aura is currently frontend-only in active workspace scope.

- Authoritative spec: `DESIGN.md`
- Active crate: `crates/aura-frontend`

Key frontend files:

- `crates/aura-frontend/src/token.rs` — token model
- `crates/aura-frontend/src/lexer.rs` — source to tokens
- `crates/aura-frontend/src/ast.rs` — AST nodes
- `crates/aura-frontend/src/parser.rs` — parser + parser contract tests
- `crates/aura-frontend/src/static_eval.rs` — compile-time-known/static interface hook
- `crates/aura-frontend/src/lib.rs` — crate module surface

## Build, Lint, and Test Commands

From workspace root:

```bash
cargo check
cargo build
cargo test
cargo clippy -- -D warnings
cargo fmt --check
```

Frontend crate only:

```bash
cargo test -p aura-frontend
```

## Design Alignment Rules

- `DESIGN.md` is authoritative for observable syntax and semantics.
- Macro declaration canonical form:
  - `defmacro[static_args] macro_name(ast_node) -> T { ... }`
- Macro application canonical form:
  - `macro_name[args] node`
- Macro application operand is single-node and chaining is right-associative.
- `static` is a reusable compile-time interface concept shared across features.
- Function-like declaration syntax is assignment sugar and should normalize to assignment semantics.

## Testing Expectations

- New syntax work must include parser tests in `crates/aura-frontend/src/parser.rs` (or dedicated frontend tests).
- Prefer descriptive test names and `assert_eq!` where direct value comparison is suitable.
