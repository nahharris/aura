---
title: "Typecheck"
kind: subsystem
status: active
owner: repo
source_paths:
  - "crates/aura-typecheck/src/checker.rs"
  - "crates/aura-typecheck/src/checked_ir.rs"
  - "crates/aura-typecheck/src/resolver.rs"
  - "crates/aura-typecheck/src/types.rs"
  - "crates/aura-typecheck/src/unify.rs"
depends_on:
  - "Subsystems/Frontend"
  - "Subsystems/Diagnostics"
related_contracts:
  - "Contracts/Typecheck IR"
related_notes:
  - "Language/Syntax And Semantics"
last_reviewed: 2026-04-21
---

# Typecheck

## Purpose

Resolve symbols, enforce type rules, and emit checked IR for downstream codegen.

## Entry Points

- `check_module`
- `check_module_with_options`
- `check_module_with_context`
- `Resolver`

## Import Context

- Typechecking no longer relies on a hardcoded STL prelude injected at the compiler boundary.
- Project/module resolution constructs a `CheckContext` before typechecking and supplies:
  - direct imported values with stable link names
  - namespace imports keyed by alias
- Imported values are emitted into checked IR as extern declarations so downstream codegen can declare or link them without re-typechecking provider modules.

## Runtime Surface

- Runtime callable signatures come from [[Subsystems/Runtime Host]] metadata via `BuiltinRegistry::with_prelude()`.
- This removes duplicated runtime signature tables from the middle of `aura-typecheck`.
- Legacy builtin-member lowering for `Bytes`/`String` still exists, but the callable ABI table is now shared.

## Checked IR Notes

- Checked declarations now preserve both the source name and a separately assigned `link_name`.
- Function declarations also carry parameter names so LLVM lowering can bind function arguments in emitted library objects.

## Testing

Contract snapshots and diagnostics snapshots live under `crates/aura-typecheck/tests/`.
