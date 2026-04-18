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
last_reviewed: 2026-04-18
---

# Typecheck

## Purpose

Resolve symbols, enforce type rules, and emit checked IR for downstream codegen.

## Entry Points

- `check_module`
- `check_module_with_options`
- `Resolver`

## Testing

Contract snapshots and diagnostics snapshots live under `crates/aura-typecheck/tests/`.

