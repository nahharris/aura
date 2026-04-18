---
title: "Testing Strategy"
kind: architecture
tags:
  - aura
  - testing
---

# Testing Strategy

## Test Layers

- Frontend parser and formatter tests live under `crates/aura-frontend`.
- Typecheck contract and diagnostic coverage lives under `crates/aura-typecheck`.
- Codegen tests live under `crates/aura-codegen`.
- CLI behavior tests live in `crates/aura-cli`.
- Aura standard library tests live beside source modules in `aura-stl/src/*.test.aura`.

## Expectations

- Syntax changes should carry frontend parser coverage.
- IR contract changes should update both code and [[Contracts/Typecheck IR]].
- Use workspace-level checks for broad validation and subsystem-local commands for tight loops.

## Generated Support

![[Generated/Test Inventory]]
