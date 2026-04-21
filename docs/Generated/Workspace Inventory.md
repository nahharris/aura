---
title: Workspace Inventory
kind: generated
generated_by: cargo xtask docs sync
generated_at: 2026-04-21T20:08:17.322742Z
---

# Workspace Inventory

| Path | Role |
| --- | --- |
| `crates/aura-cli` | CLI entry point and end-user commands. |
| `crates/aura-codegen` | Backend and project-layout lowering. |
| `crates/aura-diagnostics` | Shared diagnostics and issue metadata. |
| `crates/aura-frontend` | Tokens, AST, parser, static eval, formatter. |
| `crates/aura-runtime-host` | Runtime boundary required by native execution. |
| `crates/aura-typecheck` | Resolver, type checker, and checked IR emitter. |
| `xtask` | Automation commands for dev, LLVM, and docs. |

## Companion Surfaces

- `aura-stl/` holds the standard library package.
- `tool/` holds editor integrations and the Tree-sitter grammar.
- `examples/` holds compiler-facing sample programs.

