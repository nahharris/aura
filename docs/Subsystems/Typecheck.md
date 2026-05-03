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
last_reviewed: 2026-05-03
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
  - imported method metadata keyed by receiver type shape
  - namespace imports keyed by alias
- Imported values are emitted into checked IR as extern declarations so downstream codegen can declare or link them without re-typechecking provider modules.
- Imported type aliases stay in the type namespace only; they do not create extern runtime declarations.
- Imported generic methods match structurally against instantiated receiver types, so methods declared on `List[T]` are available through an imported `List[String]`.
- Member call dispatch resolves imported methods before builtin-member fallback; this ordering is required so generic `List[T]` methods (`new`, `push`, `get`) do not degrade into unrelated builtin memory/bytes operations.

## Runtime Surface

- Runtime callable signatures come from Aura source stubs in `aura-stl/src/core.aura`, re-exported through `aura-stl/src/lib.aura`.
- The checker no longer injects `BuiltinRegistry::with_prelude()` as the typing authority; runtime-host metadata remains for host ABI/link validation.
- Non-macro `defstub` declarations are available as typed globals and lower to extern checked-IR declarations.
- `Macro[...]` stubs are declaration-only and provide typing contracts for compiler-lowered builtin forms.
- Legacy builtin-member lowering for `Bytes`/`String` still exists, but direct runtime callables are now typed through stubs.
- `RawAlloc[T]`, `Slice[T]`, and `Ref[T]` are compiler-recognized opaque generic types. The checker types their public methods as safe managed-memory operations instead of Aura-callable runtime stubs.

## Type Aliases

- Assignment-form type aliases preserve static parameters: `def[T] Box = (value: T)` records an alias scheme.
- Alias schemes instantiate during type resolution, so `Box[Int]` resolves under a temporary generic scope where `T = Int`.
- Monomorphic aliases export as concrete `TypeRef`s. Generic aliases export their source-level alias scheme through `CheckContext` so consumers can instantiate imported aliases such as `Box[Int]`.
- Interface types are represented as first-class type nodes in checker/type IR (`interface(...)` is not lowered as a nominal fallback name).
- Empty interface `interface()` resolves equivalently to `Any`.

## Checked IR Notes

- Checked declarations now preserve both the source name and a separately assigned `link_name`.
- Function declarations also carry parameter names so LLVM lowering can bind function arguments in emitted library objects.
- `CheckedModule` now carries exported/local type aliases separately from runtime value exports.
- Enum constructor forms lower to explicit `CheckedExpr::EnumCtor` nodes instead of ad hoc dot-expression placeholders.
- Enum-driven multi-arm methods lower to `CheckedExpr::EnumMatch`, using the resolved enum variant table from the type alias definition.
- Named constructor forms (`Type.variant`, `Type.variant(payload)`) resolve against the type namespace first.
- Shorthand constructor forms (`.variant`, `.variant(payload)`) remain expected-type-driven and work for both local and imported enum aliases.
- Struct-payload enum sugar is typechecked as one struct payload. Field sugar is accepted only when the resolved variant payload is a struct; explicit payload values remain valid.
- Enum-match lowering records struct payload field bindings so backend lowering can bind `.variant(field = name)` arms without changing the single-payload enum representation.
- Struct and tuple field reads lower to `CheckedExpr::FieldAccess`; field/index assignments lower to `CheckedExpr::AssignField` after resolving the object type, field index, and field type.
- Field assignment requires an assignable root place. `let` locals are assignable, immutable locals are rejected, and function parameters can be mutated through fields while remaining non-reassignable as bindings.
- `If`, `Cases`, and `Loop` are dedicated checked-IR control-flow nodes.
- Panic/catch lowering now introduces dedicated `CheckedExpr::Panic` and `CheckedExpr::Catch` nodes.
- `Return`, `Break`, and `Continue` carry resolved target names so LLVM lowering can emit direct control transfer.
- Managed-memory calls lower to `CheckedExpr::MemoryOp` nodes so backend codegen receives the operation kind, element type, result type, and already-lowered arguments without exposing raw pointers to Aura source.
- Postfix `!!` lowers to `CheckedExpr::ForceUnwrap` by inspecting enum shape, not by hardcoding `Option`: the source type must be an enum with `null` and exactly one payload variant.
- Blocks with a trailing unit after a diverging expression remain `Never`, allowing `return value;` to typecheck in non-`Void` functions.

## Testing

Contract snapshots and diagnostics snapshots live under `crates/aura-typecheck/tests/`.

## Related

- [[Subsystems/Frontend]]
- [[Subsystems/Codegen]]
- [[Subsystems/Diagnostics]]
- [[Contracts/Typecheck IR]]
- [[Home]]
