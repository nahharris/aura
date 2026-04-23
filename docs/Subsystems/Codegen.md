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
last_reviewed: 2026-04-21
---

# Codegen

## Purpose

Turn checked Aura modules into backend artifacts, currently centered on the LLVM path and project layout discovery.

## Entry Points

- `emit_llvm_ir`
- `emit_object_file`
- project discovery under `project/`

## Runtime Lowering Notes

LLVM lowering currently treats runtime-backed nominal values such as `Bytes` as pointer-shaped values at the ABI boundary.

Checked-IR control-flow nodes lower directly to LLVM block/branch structures:

- `If` and `Cases` produce conditional branches plus merge blocks/result slots when needed.
- `Loop` produces condition/body/break blocks and records loop targets for nested jumps.
- `Return`, `Break`, and `Continue` emit direct control transfer using resolved checked-IR targets.

For the first byte-buffer path, checked member calls are lowered to runtime symbols:

- `Bytes.new(size)` -> `bytes_new(size)`
- `bytes.get(index)` -> `bytes_get(bytes, index)`
- `bytes.set(index, value)` -> `bytes_set(bytes, index, value)`
- `string.into()` -> `string_into(string_ptr)`
- `syscall_write(fd, bytes)` -> direct external runtime call

String literals still lower to global NUL-terminated byte storage on the LLVM side. `String.into()` is what materializes owned mutable `Bytes` by copying from that literal/runtime string storage in the runtime host.

## Testing

LLVM-specific validation runs through `cargo xtask llvm ...`.
