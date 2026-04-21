---
title: "Stdlib"
kind: subsystem
status: active
owner: repo
source_paths:
  - "aura-stl/build.aura"
  - "aura-stl/src/"
depends_on:
  []
related_contracts:
  []
related_notes:
  - "Language/Examples Index"
last_reviewed: 2026-04-21
---

# Stdlib

## Purpose

Hold the Aura standard library package as Aura source rather than Rust implementation detail.

## Package Entry

- `aura-stl/build.aura` is a real Aura library manifest.
- `aura-stl/src/lib.aura` is the entrypoint surface for the package.
- Only names exported from `src/lib.aura` participate in direct-library auto-import for consuming projects.

## Current Scope

- I/O helpers such as `print`, `println`, `printerr`, and `printerrln`
- process-exit helpers exported through `os.aura`
- prelude exports such as `Option`, `Result`, `ExitCode`, `print`, and `exit`
- real library-defined enums and methods used by consumers through normal import/type resolution

## Internal Structure

- `src/runtime.aura` is the only Aura source file in the STL that names host ABI symbols directly.
- `src/io.aura` and `src/os.aura` call through `runtime.aura` instead of binding `syscall_*` or `string_into` themselves.
- `src/lib.aura` re-exports the prelude-like surface consumed by programs.
- `src/os.aura` now defines the real `ExitCode = enum(success, failure, custom: Int)` surface and `ExitCode.into(self)` as ordinary Aura declarations.

## Import Behavior

- Direct dependencies contribute auto-imports from their own `src/lib.aura` only.
- Submodules such as `@stl/io` stay explicit imports unless `lib.aura` re-exports their names.
- Current package internal modules do not automatically import a library package's own `lib.aura`; the auto-import surface is applied at the consuming program boundary to avoid `lib.aura`/submodule cycles with the current loader.

## Enum Surface

- Consumers can rely on `ExitCode.success`, `.success`, `ExitCode.custom(100)`, and `.custom(100)` because enum constructor lowering now comes from the imported type alias definition, not compiler name checks.
- `exit(code: ExitCode)` is a normal STL function that converts the enum to an `Int` through `ExitCode.into(self)` and then calls `runtime.exit_process`.
