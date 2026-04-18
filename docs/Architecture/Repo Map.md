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
- `aura-stl/` contains the Aura standard library package written in Aura.
- `examples/` contains positive and negative sample programs used to exercise frontend and pipeline behavior.
- `tool/` contains editor integrations and the Tree-sitter grammar.
- `xtask/` contains project automation and LLVM toolchain management.
- `docs/` is the Obsidian second brain for the repo.

## Main Navigation Paths

- Language rules: [[Language/Design Overview]] and [[Language/Syntax And Semantics]]
- Compiler subsystems: [[Subsystems/Frontend]], [[Subsystems/Typecheck]], [[Subsystems/Codegen]]
- Developer workflows: [[Architecture/Build And Dev Workflow]] and [[Architecture/Testing Strategy]]
- Current IR contract: [[Contracts/Typecheck IR]]

## Generated Support

Use ![[Generated/Directory Inventory]] and ![[Generated/Workspace Inventory]] when you need a quick filesystem map before diving into a specific subsystem note.
