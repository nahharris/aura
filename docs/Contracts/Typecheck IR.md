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
- Invocation and macro surfaces: `Call`, `BinaryOp`, `MacroApply`
- Structured control flow: `If`, `Cases`, `Return`, `Break`, `Continue`
- Structural wrappers: `Label`, `MultiArm`
- Conversion wrappers: `Coerce`, `Cast`

## Static Arguments

- `CheckedStaticArg`
- `CheckedTypeExpr`
- `CheckedStaticValue`

## Invariants (Frozen v1)

1. Every `CheckedDecl` carries a resolved `TyId`.
2. Assignment compatibility may inject `Coerce` and `Cast` wrappers.
3. `if` and `cases` lower to dedicated control-flow nodes.
4. `return`, `break`, and `continue` lower to dedicated jump nodes.
5. Core conversion decisions are centralized in the checker.

## Compatibility Policy

- New `CheckedExpr` variants are breaking in v1.
- New `BinaryOpKind` variants are breaking in v1.
- Semantic reinterpretation of existing fields is breaking.

## Related Notes

- [[Subsystems/Typecheck]]
- [[Subsystems/Codegen]]
