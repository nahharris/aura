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
last_reviewed: 2026-04-18
---

# Frontend

## Purpose

Own the syntax-facing compiler surface: tokens, lexing, AST construction, parsing, static-evaluable constraints, and source formatting.

## Entry Points

- `Parser` is re-exported from `crates/aura-frontend/src/lib.rs`
- `format_source` and `unified_diff` expose formatter functionality

## Testing

Primary parser contract tests live in `crates/aura-frontend/src/parser.rs`. Snapshot diagnostics live in `crates/aura-frontend/tests/diagnostics_snapshot.rs`.

