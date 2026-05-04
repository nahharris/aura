---

## title: "Xtask"
kind: subsystem
status: active
owner: repo
source_paths:
  - "xtask/src/main.rs"
  - "xtask/src/docs.rs"
depends_on:
  []
related_contracts:
  []
related_notes:
  - "Architecture/Build And Dev Workflow"
last_reviewed: 2026-05-03

# Xtask

## Purpose

Centralize automation for the workspace, including dev commands, LLVM toolchain management, and vault maintenance.

## Command Families

- `dev` — includes `fmt-check` and `ci` for CI parity with GitHub Actions
- `llvm` — includes `ci` (doctor + clippy + test) after `llvm setup`
- `docs` — `docs sync` / `docs check` walk the repo for inventories; paths like `.opencode/` are skipped so local agent tooling does not affect generated vault tables or CI.

## LLVM toolchain

After extraction, `toolchains/llvm/<major>` is a link to the versioned install. On Unix the link target is **canonical (absolute)** so `bin/llvm-config` resolves correctly (relative targets would be interpreted from the link’s parent directory and could miss the install).

## Related

- [[Architecture/Build And Dev Workflow]]
- [[Generated/Commands Inventory]]
- [[Generated/Workspace Inventory]]
- [[Home]]