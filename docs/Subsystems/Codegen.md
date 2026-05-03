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
last_reviewed: 2026-05-03
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
- `Catch` uses runtime panic-state guards (`aura_catch_begin`/`aura_catch_end`) and merge-block result selection.
- `Return`, `Break`, and `Continue` emit direct control transfer using resolved checked-IR targets.
- `ForceUnwrap` checks the enum tag against the payload variant and lowers the payload load on the success path; the null path is currently an LLVM unreachable trap path.
- `Loop` result slots are allocated before the entry branch so generated LLVM blocks remain valid.

For the first byte-buffer path, checked member calls are lowered to runtime symbols:

- `Bytes.new(size)` -> `bytes_new(size)`
- `bytes.get(index)` -> `bytes_get(bytes, index)`
- `bytes.set(index, value)` -> `bytes_set(bytes, index, value)`
- `string.into()` -> `string_into(string_ptr)`
- `panic "message"` -> `aura_panic(message)`
- `syscall_write(fd, bytes)` -> direct external runtime call

String literals still lower to global NUL-terminated byte storage on the LLVM side. `String.into()` is what materializes owned mutable `Bytes` by copying from that literal/runtime string storage in the runtime host.

Managed memory operations lower from `CheckedExpr::MemoryOp` nodes rather than public stubs:

- `RawAlloc[T].new(count)` declares/calls `raw_alloc_new(count, elem_size, elem_align, layout_id, trace_kind)`
- `alloc.slice()` declares/calls `raw_alloc_slice(alloc)`
- `slice.get(index)` declares/calls `slice_get(slice, index, out)` and builds `Option[T]`
- `slice.set(index, value)` declares/calls `slice_set(slice, index, value)` and returns `Bool`
- `slice.ref_at(index)` declares/calls `slice_ref_at(slice, index)` and builds `Option[Ref[T]]`
- `ref.get()` and `ref.set(value)` copy through compiler-created stack slots via `ref_get` and `ref_set`
- checker/codegen can also emit GC-prep `MemoryOp` nodes (`GcRegisterRoot`, `GcUnregisterRoot`, `GcSafepoint`) that lower to internal runtime helpers.

The element size/alignment plus GC-prep metadata (`layout_id`, `trace_kind`) come from LLVM-side type classification in codegen; Aura source cannot call the raw helper symbols directly.

Struct and tuple literals lower to aggregate storage pointers in LLVM. Aggregate literal storage is now heap-backed (`malloc`) rather than function-local `alloca` storage so returned aggregates (for example `List[T].new()`) do not escape dangling stack pointers across call boundaries. `FieldAccess` loads from a resolved field GEP, and `AssignField` stores through the same indexed field pointer before returning the assigned value.

`!!` force unwrap now follows the shared panic path on failure instead of lowering directly to an unconditional trap.

Interface runtime lowering uses a two-pointer object ABI in LLVM codegen:
- data pointer (points to stored concrete receiver value)
- vtable/witness pointer (method function-pointer slots)

`CheckedExpr::MakeInterfaceObj` allocates and initializes that object shape, and `CheckedExpr::InterfaceCall` performs indirect-call lowering through the vtable slot for the selected interface method.

## Testing

LLVM-specific validation runs through `cargo xtask llvm ...`.

## Related

- [[Subsystems/Typecheck]]
- [[Subsystems/Runtime Host]]
- [[Contracts/Typecheck IR]]
- [[Architecture/Build And Dev Workflow]]
- [[Home]]
