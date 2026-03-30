# Aura Typecheck IR Contract (Draft)

This document defines the current checked-IR contract emitted by `crates/aura-typecheck` and consumed by future backend lowering (LLVM target).

Status: draft, iterating toward freeze.

## Goals

- Provide a typed, normalized representation with minimal semantic ambiguity.
- Make coercions and casts explicit for backend lowering.
- Preserve control-flow intent in dedicated IR nodes.

## Root Structure

- `CheckedIr`
  - `declarations: Vec<CheckedDecl>`

- `CheckedDecl`
  - `name: String`
  - `ty: TyId` (resolved type of declaration binding)
  - `value: CheckedExpr`

## Expression Nodes

- Literals/atoms:
  - `Ident(String)`
  - `Int(String)`
  - `Float(String)`
  - `Char(String)`
  - `String(String)`
  - `DotIdent { name, payload }`
  - `Any` (temporary fallback node; target is to eliminate from core paths)

- Collections:
  - `List(Vec<CheckedExpr>)`
  - `Dict(Vec<(CheckedExpr, CheckedExpr)>)`

- Invocation/macro surfaces:
  - `Call { callee, args }`
  - `MacroApply { macro_name, static_args, operand }`

- Structured control flow:
  - `If { condition, then_branch, else_branch }`
  - `Cases { arms }`
  - `Return { value }`
  - `Break { value }`
  - `Continue`

- Structural wrappers:
  - `Label { label, expr }`
  - `MultiArm(Vec<CheckedExpr>)`

- Conversion/typing wrappers:
  - `Coerce { from: TyId, to: TyId, expr }` (implicit safe widening)
  - `Cast { from: TyId, to: TyId, expr }` (explicit conversion)

## Static Arguments

- `CheckedStaticArg`
  - `Type(String)`
  - `Value(String)`

Currently represented as strings from AST debug formatting for preservation fidelity. Planned improvement is structural typed static-arg IR.

## Invariants (Current)

1. Every `CheckedDecl` carries a resolved `TyId`.
2. Assignment compatibility may inject `Coerce`/`Cast` wrappers.
3. `if`/`cases` macro surfaces lower to dedicated control-flow nodes.
4. `return`/`break`/`continue` macro surfaces lower to dedicated jump nodes.

## Invariants (Target before freeze)

1. No `CheckedExpr::Any` on semantically checked core paths.
2. Full operator coverage lowered to typed operator nodes.
3. All cast/coerce decisions represented explicitly and consistently.
4. Stable schema tests ensure backward-compatible backend contract.

## Validation Plan

- Add contract tests that assert:
  - control-flow macro lowering shape
  - cast/coerce wrappers emitted when expected
  - macro static args preserved
- Add negative tests to ensure disallowed forms do not silently lower to `Any`.
