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

Provide the native runtime boundary required by generated code. The current exported surface includes process exit plus the first owned byte-buffer ABI used by Aura native code.

## Current Export

- `syscall_exit`
- `syscall_write`
- `bytes_new`
- `bytes_get`
- `bytes_set`
- `string_into`

## `Bytes` ABI

Generated code treats `Bytes` as an opaque pointer-like runtime value. The host owns the concrete representation and currently stores:

- `len: usize`
- contiguous owned `Vec<u8>` storage

The exported helpers use this object model:

- `bytes_new(size)` allocates zeroed storage and returns an owned `Bytes`
- `bytes_get(bytes, index)` reads one byte
- `bytes_set(bytes, index, value)` writes one byte
- `string_into(string)` copies a NUL-terminated Aura string literal/runtime string into fresh owned `Bytes`

Bounds checks are intentionally absent right now; out-of-bounds `get`/`set` is UB until panic handling exists.

## Native Write Path

- `syscall_write(fd, bytes)` accepts Aura's public ABI shape: `Int32` file descriptor plus `Bytes`
- the host currently maps `fd = 1` to stdout and `fd = 2` to stderr
- successful writes return the buffer length as `ISize`
- unsupported descriptors or host I/O failures return `-1`

## Native Linking Notes

- `crates/aura-runtime-host` is produced as a Rust `staticlib` and linked into native Aura executables by `crates/aura-cli`.
- On Windows, the CLI link step should not force CRT import libraries such as `msvcrt`, `ucrt`, or `vcruntime`.
- The Rust staticlib already carries the correct CRT defaults for its own build, and overriding them from the CLI causes MSVC linker conflicts such as `LNK4098` (`libcmt` vs `msvcrt`).
- The native link step still adds the non-CRT Windows system libraries that Rust `std` needs in this embedding path:
  - `kernel32`
  - `userenv`
  - `ws2_32`
  - `ntdll`
  - `advapi32`
  - `bcrypt`
