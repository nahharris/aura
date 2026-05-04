---
title: Commands Inventory
kind: generated
generated_by: cargo xtask docs sync
generated_at: 2026-05-04T11:20:46.1935762Z
---

# Commands Inventory

## Workspace Dev

| Command | Purpose |
| --- | --- |
| `cargo xtask dev check` | Check the full workspace. |
| `cargo xtask dev build` | Build the full workspace. |
| `cargo xtask dev test` | Run the full workspace test suite. |
| `cargo xtask dev lint` | Run clippy with warnings denied. |
| `cargo xtask dev fmt` | Format the workspace. |
| `cargo xtask dev fmt-check` | Fail if sources are not rustfmt-clean (CI-safe). |
| `cargo xtask dev ci` | Full CI parity: fmt-check, lint, test, docs check, LLVM doctor + clippy + test. |
| `cargo xtask dev qa` | Format, lint, and test. |

## LLVM Flow

| Command | Purpose |
| --- | --- |
| `cargo xtask llvm setup` | Install or validate the managed LLVM toolchain. |
| `cargo xtask llvm doctor` | Check the managed LLVM toolchain. |
| `cargo xtask llvm ci` | Doctor, then clippy and tests (toolchain must already be installed). |
| `cargo xtask llvm check` | Check `aura-codegen` with the LLVM backend feature. |
| `cargo xtask llvm build` | Build `aura-codegen` with the LLVM backend feature. |
| `cargo xtask llvm test` | Test `aura-codegen` with the LLVM backend feature. |
| `cargo xtask llvm clippy` | Lint `aura-codegen` with the LLVM backend feature. |
| `cargo xtask llvm run -- -p aura-cli -- build examples/basic_ops.aura` | Run the CLI under the managed LLVM environment. |

## Docs Vault

| Command | Purpose |
| --- | --- |
| `cargo xtask docs sync` | Refresh generated inventories and scaffold missing vault notes. |
| `cargo xtask docs check` | Fail when generated inventory notes are stale or required curated notes are missing. |
| `cargo xtask docs new-adr --title "Decision Name"` | Create a dated ADR note. |

## QMD (Docker)

| Command | Purpose |
| --- | --- |
| `cargo xtask qmd build` | Build the local Docker image for qmd workflows. |
| `cargo xtask qmd start` | Start qmd MCP in HTTP mode with `docs/` mounted at `http://127.0.0.1:8181/mcp`. |
| `cargo xtask qmd stop` | Stop and remove the qmd MCP container. |
| `cargo xtask qmd cmd -- <args...>` | Pass through arbitrary `qmd` CLI commands to the running qmd container. |
| `cargo xtask qmd mcp` | Ensure MCP HTTP mode is running and print the endpoint URLs. |

