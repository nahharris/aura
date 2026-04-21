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

Provide the native runtime boundary required by generated code. The current exported surface is intentionally minimal.

## Current Export

- `syscall_exit`

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
