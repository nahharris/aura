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
- Destructuring imports use the same field-first convention: `use (exported = local_alias) = "module"` stores `exported` as `source_name` and `local_alias` as `local_name`.

## Generic Type Receivers

- Assignment-form `def` preserves static parameters for type aliases, so `def[T] Alias = ...` reaches typecheck with its alias scheme intact.
- Member-call parsing accepts generic type receivers such as `RawAlloc[Int].new(4)` by representing `RawAlloc[Int]` as a type-application receiver before the `.new` call.
- Macro application detection leaves uppercase generic receivers followed by `.` to the member-call parser instead of treating them as macro calls.

## Assignable Places

- Local assignment remains `Expr::Assign`; non-local places such as `obj.field = value` and `coord.0 = value` parse as `Expr::AssignPlace`.
- Compound assignments and postfix `++`/`--` desugar during parsing to normal assignment with a binary RHS, preserving right-associative assignment precedence.
- Numeric member syntax after a postfix-capable expression, such as `coord.0`, is tokenized as member access rather than as a malformed float literal.

## Panic/Catch Surface

- `panic "message"` parses as macro application (`Expr::MacroApply` with `macro_name = "panic"`).
- `catch (expr) else { fallback }` parses as a dedicated `Expr::Catch` node, matching inline call-style control-flow syntax.

## Entry Points

- `Parser` is re-exported from `crates/aura-frontend/src/lib.rs`
- `format_source` and `unified_diff` expose formatter functionality

## Testing

Primary parser contract tests live in `crates/aura-frontend/src/parser.rs`. Snapshot diagnostics live in `crates/aura-frontend/tests/diagnostics_snapshot.rs`.
