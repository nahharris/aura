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
last_reviewed: 2026-04-18
---

# Editor Tooling

## Purpose

Bundle editor-facing language support and the Tree-sitter grammar that can be reused across tools.

## Surfaces

- VS Code extension
- Zed extension
- Neovim queries and ftplugin setup
- Tree-sitter grammar and generated parser

