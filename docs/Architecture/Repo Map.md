---
title: "Repo Map"
kind: architecture
tags:
  - aura
  - architecture
---

# Repo Map

## Top-Level Layout

- `crates/` contains the Rust workspace crates that implement the compiler pipeline and CLI surfaces.
- `aura-stl/` contains the Aura standard library package written in Aura, including `src/lib.aura` as the package entrypoint and `src/runtime.aura` as the thin host-ABI binding layer.
- `e2e/` contains project-shaped end-to-end fixtures, including `hello-world-stl` for the current direct-library auto-import flow and `exit-stl` for enum-driven process exit.
- `examples/` contains positive and negative sample programs used to exercise frontend and pipeline behavior.
- `tool/` contains editor integrations and the Tree-sitter grammar.
- `xtask/` contains project automation and LLVM toolchain management.
- `docs/` is the Obsidian second brain for the repo.

## Project Build Edges

- `crates/aura-codegen/src/project/manifest.rs` parses `build.aura`, including `path:` dependencies alongside vendored Git dependencies.
- `crates/aura-codegen/src/project/compile.rs` resolves module imports, loads dependency `src/lib.aura` entrypoints, assigns stable link names, and builds the typed project module graph ahead of codegen.
- The same project compile layer also carries exported type alias metadata so consumers can resolve imported library enums and aliases without turning them into fake runtime symbols.
- `crates/aura-cli/src/main.rs` now emits and links multiple object files for native project builds instead of treating dependencies as a single-file special case.

## Main Navigation Paths

- Language rules: [[Language/Design Overview]] and [[Language/Syntax And Semantics]]
- Compiler subsystems: [[Subsystems/Frontend]], [[Subsystems/Typecheck]], [[Subsystems/Codegen]]
- Developer workflows: [[Architecture/Build And Dev Workflow]] and [[Architecture/Testing Strategy]]
- Current IR contract: [[Contracts/Typecheck IR]]

## Generated Support

Use ![[Generated/Directory Inventory]] and ![[Generated/Workspace Inventory]] when you need a quick filesystem map before diving into a specific subsystem note.
