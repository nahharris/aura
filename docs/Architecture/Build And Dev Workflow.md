---
title: "Build And Dev Workflow"
kind: architecture
tags:
  - aura
  - workflow
---

# Build And Dev Workflow

## Default Commands

- `cargo xtask dev check`
- `cargo xtask dev build`
- `cargo xtask dev test`
- `cargo xtask dev lint`
- `cargo xtask dev fmt`
- `cargo xtask dev qa`

## LLVM-Sensitive Work

Run LLVM-backed checks and CLI builds through `cargo xtask llvm ...` so the managed toolchain is injected consistently.

## Documentation Workflow

- Refresh generated vault content: `cargo xtask docs sync`
- Verify generated docs are current: `cargo xtask docs check`
- Record design decisions: `cargo xtask docs new-adr --title "Decision Name"`

## Related Notes

- [[Subsystems/Xtask]]
- [[Generated/Commands Inventory]]
