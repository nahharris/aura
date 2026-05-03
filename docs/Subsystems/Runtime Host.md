---
title: "Runtime Host"
kind: subsystem
status: active
owner: repo
source_paths:
  - "crates/aura-runtime-host/src/lib.rs"
depends_on:
  []
related_contracts:
  []
related_notes:
  - "Subsystems/Codegen"
last_reviewed: 2026-04-21
---

# Runtime Host

## Purpose

Provide the native runtime boundary required by generated code and act as the single source of truth for host-callable ABI metadata consumed by the compiler.

## Current Export

- `syscall_exit`
- `syscall_write`
- `bytes_new`
- `bytes_get`
- `bytes_set`
- `string_into`
- `aura_panic`
- `aura_catch_begin`
- `aura_catch_end`
- `aura_panic_set_hook`

The host also implements compiler-internal managed-memory helpers:

- `raw_alloc_new`
- `raw_alloc_len`
- `raw_alloc_slice`
- `slice_get`
- `slice_set`
- `slice_ref_at`
- `ref_get`
- `ref_set`

These helpers are not part of the Aura-callable STL stub surface.

## ABI Ownership

- `crates/aura-runtime-host/src/lib.rs` now owns both the Rust implementations and the shared ABI description for host exports.
- `aura-typecheck` builds its runtime builtin signature registry from this shared metadata instead of maintaining an independent match table.
- `aura-codegen` uses the same metadata when it needs to declare runtime functions for LLVM lowering.
- The compiler core still knows about the native executable entry wrapper, but runtime callable names and signatures now live at this host edge.
- Enum layout is not part of this host ABI. Aura enums are lowered by the compiler as tagged storage, and STL enums such as `ExitCode` reach the runtime host only after library code converts them to primitive host-callable values.

## `Bytes` ABI

Generated code treats `Bytes` as an opaque pointer-like runtime value. The host owns the concrete representation and currently stores:

- `len: usize`
- contiguous owned `Vec<u8>` storage

The exported helpers use this object model:

- `bytes_new(size)` allocates zeroed storage and returns an owned `Bytes`
- `bytes_get(bytes, index)` reads one byte
- `bytes_set(bytes, index, value)` writes one byte
- `string_into(string)` copies a NUL-terminated Aura string literal/runtime string into fresh owned `Bytes`

`bytes_get`/`bytes_set` now perform runtime bounds checks and route out-of-bounds access through the panic runtime path.

## Panic Runtime Surface

- `aura_panic(message)` marks panic state and reports the message to stderr.
- `aura_catch_begin()` clears per-thread panic state before evaluating a guarded expression.
- `aura_catch_end()` returns `1` when panic was observed in the guarded region and clears state.
- `aura_panic_set_hook(message)` enables a host-side panic-hook marker (current hook behavior is intentionally minimal).

## Managed Memory ABI

Generated code treats `RawAlloc[T]`, `Slice[T]`, and `Ref[T]` as opaque pointer-shaped handles. The runtime host owns the concrete structs and stores managed allocation bytes in zero-initialized leak-only storage.

- `raw_alloc_new(count, elem_size, elem_align)` allocates process-lifetime storage for `count` elements.
- `raw_alloc_slice(alloc)` creates an opaque full-allocation slice handle.
- `slice_get(slice, index, out)` copies one element into compiler-provided stack storage and returns `false` when out of bounds.
- `slice_set(slice, index, value)` copies one element from compiler-provided stack storage and returns `false` when out of bounds.
- `slice_ref_at(slice, index)` returns a non-null `Ref` handle for in-bounds indices and a null host pointer for out-of-bounds.
- `ref_get(ref, out)` and `ref_set(ref, value)` copy values through non-null `Ref` handles.

Aura source only sees the safe methods documented in [[Syntax And Semantics]]. The raw helper names stay compiler-internal so Aura code cannot obtain or manipulate host pointers directly.

## Native Write Path

- `syscall_write(fd, bytes)` accepts Aura's public ABI shape: `Int32` file descriptor plus `Bytes`
- the host currently maps `fd = 1` to stdout and `fd = 2` to stderr
- successful writes return the buffer length as `ISize`
- unsupported descriptors or host I/O failures return `-1`

## Native Linking Notes

- `crates/aura-runtime-host` is produced as a Rust `staticlib` and linked into native Aura executables by `crates/aura-cli`.
- Multi-module native project builds now link the entry module object plus any required library module objects together with this runtime-host staticlib.
- On Windows, the CLI link step should not force CRT import libraries such as `msvcrt`, `ucrt`, or `vcruntime`.
- The Rust staticlib already carries the correct CRT defaults for its own build, and overriding them from the CLI causes MSVC linker conflicts such as `LNK4098` (`libcmt` vs `msvcrt`).
- The native link step still adds the non-CRT Windows system libraries that Rust `std` needs in this embedding path:
  - `kernel32`
  - `userenv`
  - `ws2_32`
  - `ntdll`
  - `advapi32`
  - `bcrypt`
