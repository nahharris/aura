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
- `cargo xtask dev fmt-check` — rustfmt in check mode (CI-safe)
- `cargo xtask dev ci` — same checks as GitHub Actions locally (includes docs + LLVM)
- `cargo xtask dev qa`

Continuous integration in `.github/workflows/ci.yml` runs in parallel: **fmt-check** and **docs check** on Ubuntu only (same inputs on every OS); **workspace** tests on Ubuntu and Windows with **clippy on Ubuntu only**; **llvm** setup + clippy + tests on both Ubuntu and Windows (toolchains and linking differ by OS).

GitHub.com branch protection, required checks, and auto-merge are summarized in [[Architecture/GitHub Repo Settings]] (update that note when settings change).

## LLVM-Sensitive Work

Run LLVM-backed checks and CLI builds through `cargo xtask llvm ...` so the managed toolchain is injected consistently.

## Documentation Workflow

- Refresh generated vault content: `cargo xtask docs sync`
- Verify generated docs are current: `cargo xtask docs check`
- Record design decisions: `cargo xtask docs new-adr --title "Decision Name"`

## Related Notes

- [[Architecture/GitHub Repo Settings]]
- [[Subsystems/Xtask]]
- [[Generated/Commands Inventory]]
