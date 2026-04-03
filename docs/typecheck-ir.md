# Aura Typecheck IR Contract (Frozen v1)

This document defines the current checked-IR contract emitted by `crates/aura-typecheck` and consumed by future backend lowering (LLVM target).

Status: frozen v1.

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
  - `BinaryOp { op, lhs, rhs, ty }`
  - `MacroApply { macro_name, static_args, operand }`

- Typed operator kinds (`BinaryOpKind`):
  - Arithmetic: `Add`, `Sub`, `Mul`, `Div`, `Mod`
  - Comparison: `Lt`, `Gt`, `Le`, `Ge`
  - Equality: `Eq`, `Neq`
  - Logical: `And`, `Or`

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
  - `Type(CheckedTypeExpr)`
  - `Value(CheckedStaticValue)`

- `CheckedTypeExpr`
  - `Named { name, args }`
  - `Static(inner)`
  - `InferHole`

- `CheckedStaticValue`
  - `Int(String)`
  - `Float(String)`
  - `Ident(String)`
  - `String(String)`
  - `Char(String)`

Static arguments are now structural in the checked IR contract (no debug-string payloads).

## Invariants (Frozen v1)

1. Every `CheckedDecl` carries a resolved `TyId`.
2. Assignment compatibility may inject `Coerce`/`Cast` wrappers.
3. `if`/`cases` macro surfaces lower to dedicated control-flow nodes.
4. `return`/`break`/`continue` macro surfaces lower to dedicated jump nodes.
5. Core assignability, branch-join compatibility, and IR conversion wrappers are driven by one centralized conversion decision path in the checker.

1. No `CheckedExpr::Any` on semantically checked core paths.
2. Full operator macro family lowers to typed `BinaryOp` nodes.
3. All cast/coerce decisions represented explicitly and consistently.
4. Stable schema tests enforce frozen contract expectations.

## Compatibility Policy (v1)

- Any new `CheckedExpr` variant is a breaking change unless version is bumped.
- Any new `BinaryOpKind` variant is a breaking change and requires version bump.
- Semantic reinterpretation of existing node fields/variants is breaking.
- Additive metadata fields are breaking in v1 unless explicitly optional and backend-ignored by contract.

## Validation Plan

- Add contract tests that assert:
  - control-flow macro lowering shape
  - typed operator node lowering shape
  - cast/coerce wrappers emitted when expected
  - macro static args preserved
- Add negative tests to ensure disallowed forms do not silently lower to `Any`.
