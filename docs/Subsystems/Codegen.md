---
title: "Codegen"
kind: subsystem
status: active
owner: repo
source_paths:
  - "crates/aura-codegen/src/lib.rs"
  - "crates/aura-codegen/src/llvm/mod.rs"
  - "crates/aura-codegen/src/project/discover.rs"
  - "crates/aura-codegen/src/project/manifest.rs"
depends_on:
  - "Subsystems/Typecheck"
  - "Subsystems/Runtime Host"
related_contracts:
  - "Contracts/Typecheck IR"
related_notes:
  - "Architecture/Build And Dev Workflow"
last_reviewed: 2026-04-18
---

# Codegen

## Purpose

Turn checked Aura modules into backend artifacts, currently centered on the LLVM path and project layout discovery.

## Entry Points

- `emit_llvm_ir`
- `emit_object_file`
- project discovery under `project/`

## Testing

LLVM-specific validation runs through `cargo xtask llvm ...`.

