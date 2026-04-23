---
title: "Frontend"
kind: subsystem
status: active
owner: repo
source_paths:
  - "crates/aura-frontend/src/token.rs"
  - "crates/aura-frontend/src/lexer.rs"
  - "crates/aura-frontend/src/ast.rs"
  - "crates/aura-frontend/src/parser.rs"
  - "crates/aura-frontend/src/static_eval.rs"
  - "crates/aura-frontend/src/fmt.rs"
depends_on:
  - "Language/Design Overview"
related_contracts:
  []
related_notes:
  - "Contracts/Typecheck IR"
  - "Language/Syntax And Semantics"
last_reviewed: 2026-04-23
---

# Frontend

## Purpose

Own the syntax-facing compiler surface: tokens, lexing, AST construction, parsing, static-evaluable constraints, and source formatting.

## Enum Payload Sugar

- Dot-variant constructors parse `.variant(field = value, ...)` as a single `Expr::Struct` payload, preserving the enum invariant that variants carry one optional payload.
- Dot-variant patterns parse `.variant(field = binding, ...)` as a single `Pattern::Struct` payload so typecheck can bind struct fields by payload type.
- Explicit wrapped forms such as `.variant((field = value))` remain accepted and format to the canonical sugar form.

## Entry Points

- `Parser` is re-exported from `crates/aura-frontend/src/lib.rs`
- `format_source` and `unified_diff` expose formatter functionality

## Testing

Primary parser contract tests live in `crates/aura-frontend/src/parser.rs`. Snapshot diagnostics live in `crates/aura-frontend/tests/diagnostics_snapshot.rs`.
