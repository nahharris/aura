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
  - direct imported type aliases from dependency `src/lib.aura` entrypoints
  - namespace imports keyed by alias
- Imported values are emitted into checked IR as extern declarations so downstream codegen can declare or link them without re-typechecking provider modules.
- Imported type aliases stay in the type namespace only; they do not create extern runtime declarations.

## Runtime Surface

- Runtime callable signatures come from Aura source stubs in `aura-stl/src/core.aura`, re-exported through `aura-stl/src/lib.aura`.
- The checker no longer injects `BuiltinRegistry::with_prelude()` as the typing authority; runtime-host metadata remains for host ABI/link validation.
- Non-macro `defstub` declarations are available as typed globals and lower to extern checked-IR declarations.
- `Macro[...]` stubs are declaration-only and provide typing contracts for compiler-lowered builtin forms.
- Legacy builtin-member lowering for `Bytes`/`String` still exists, but direct runtime callables are now typed through stubs.

## Checked IR Notes

- Checked declarations now preserve both the source name and a separately assigned `link_name`.
- Function declarations also carry parameter names so LLVM lowering can bind function arguments in emitted library objects.
- `CheckedModule` now carries exported/local type aliases separately from runtime value exports.
- Enum constructor forms lower to explicit `CheckedExpr::EnumCtor` nodes instead of ad hoc dot-expression placeholders.
- Enum-driven multi-arm methods lower to `CheckedExpr::EnumMatch`, using the resolved enum variant table from the type alias definition.
- Named constructor forms (`Type.variant`, `Type.variant(payload)`) resolve against the type namespace first.
- Shorthand constructor forms (`.variant`, `.variant(payload)`) remain expected-type-driven and work for both local and imported enum aliases.
- `If`, `Cases`, and `Loop` are dedicated checked-IR control-flow nodes.
- `Return`, `Break`, and `Continue` carry resolved target names so LLVM lowering can emit direct control transfer.

## Testing

Contract snapshots and diagnostics snapshots live under `crates/aura-typecheck/tests/`.
