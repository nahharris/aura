---
title: "Editor Tooling"
kind: subsystem
status: active
owner: repo
source_paths:
  - "tool/aura-vscode/"
  - "tool/aura-zed/"
  - "tool/aura-nvim/"
  - "tool/tree-sitter-aura/"
depends_on:
  - "Subsystems/Frontend"
related_contracts:
  []
related_notes:
  - "Language/Syntax And Semantics"
last_reviewed: 2026-04-22
---

# Editor Tooling

## Purpose

Bundle editor-facing language support and the shared parser/query assets used across Aura-aware editors.

## Surfaces

- `tool/tree-sitter-aura/`
- `tool/aura-zed/`
- `tool/aura-nvim/`
- `tool/aura-vscode/`

## Language Identities

- `aura` is the editor language identity for `.aura` source files
- `auon` is the editor language identity for `.auon` data and manifest files
- Aura and AUON share one parser backend in `tool/tree-sitter-aura/`, but editors should expose them as separate languages/filetypes

## Shared Parser

- `tool/tree-sitter-aura/grammar.js` parses both Aura module/source files and AUON documents
- canonical Tree-sitter query source now lives under `tool/tree-sitter-aura/queries/`
- editor integrations should copy from those queries only when an editor needs capture-name or behavior deltas

## Current Syntax Coverage

- Aura coverage tracks the current frontend surface, not the older pre-update syntax
- top-level declarations are `def`, `defmacro`, and `use`
- supported modern forms include `doc[...] def ...`, `defmacro[static_args] name(...) -> T { ... }`, macro application, static args, labeled trailing closures, label expressions, char literals, and current collection/comment forms
- AUON coverage includes primitives, aliases, variants, tuples, structs, dicts, lists, comments, and document-level root wrapper omission for list/struct/dict

## Editor Split

- Zed and Neovim consume the shared Tree-sitter parser for both `aura` and `auon`
- VS Code remains TextMate-based in this phase, with separate Aura and AUON grammars plus snippets and language configuration
- query changes should be made in `tool/tree-sitter-aura/queries/` first, then mirrored into editor-specific folders where needed

## Verification

- parser changes should be checked with `tree-sitter generate` and `tree-sitter test`
- doc-affecting tooling changes should also run `cargo xtask docs sync` and `cargo xtask docs check`
