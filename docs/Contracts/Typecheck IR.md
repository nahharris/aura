---
title: "Typecheck IR"
kind: contract
tags:
  - aura
  - contract
  - typecheck
---

# Aura Typecheck IR Contract (Frozen v1)

This document defines the current checked-IR contract emitted by `crates/aura-typecheck` and consumed by backend lowering.

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
  - `ty: TyId`
  - `value: CheckedExpr`

## Expression Nodes

- Literals and atoms: `Ident`, `Int`, `Float`, `Char`, `String`, `DotIdent`, `Any`
- Collections: `List`, `Dict`
- Product places: `FieldAccess` and `AssignField` for typed struct/tuple field reads and writes
- Invocation and macro surfaces: `Call`, `BinaryOp`, `MacroApply`
- Managed memory: `MemoryOp` with operation kind, element type, result type, and arguments
- Enum constructors: `EnumCtor` with one optional payload expression
- Structured control flow: `If`, `Cases`, `Loop`, `Return`, `Break`, `Continue`
- Structural wrappers: `Label`, `MultiArm`
- Conversion wrappers: `Coerce`, `Cast`

## Static Arguments

- `CheckedStaticArg`
- `CheckedTypeExpr`
- `CheckedStaticValue`

## Invariants (Frozen v1)

1. Every `CheckedDecl` carries a resolved `TyId`.
2. Assignment compatibility may inject `Coerce` and `Cast` wrappers.
3. `if`, `cases`, and `loop` lower to dedicated control-flow nodes.
4. `return`, `break`, and `continue` lower to dedicated jump nodes with resolved target metadata.
5. Core conversion decisions are centralized in the checker.
6. Struct-payload enum constructor sugar lowers to `EnumCtor` with one `Struct` payload, not multiple payloads.
7. `EnumMatch` arms may carry struct field binding metadata for backend locals, but payload storage remains the single enum payload.
8. Safe managed-memory calls lower to `MemoryOp`; raw host pointers are not represented in Aura source-level checked calls.
9. Field reads and field assignments carry the resolved object type, field index, and field type so backends do not re-resolve source member syntax.

## Stub Declarations

- Non-macro `defstub` declarations lower to extern `CheckedDecl` entries with `CheckedExpr::Any` placeholders.
- `Macro[...]` stubs are declaration-only typing contracts and do not emit runtime extern declarations.
- Runtime imports and stubbed externs keep `link_name` separate from source `name` for backend declaration/link validation.

## Compatibility Policy

- New `CheckedExpr` variants are breaking in v1.
- New `BinaryOpKind` variants are breaking in v1.
- Semantic reinterpretation of existing fields is breaking.

## Related Notes

- [[Subsystems/Typecheck]]
- [[Subsystems/Codegen]]
