---
title: "CLI"
kind: subsystem
status: active
owner: repo
source_paths:
  - "crates/aura-cli/src/main.rs"
  - "crates/aura-cli/templates/"
depends_on:
  - "Subsystems/Frontend"
  - "Subsystems/Typecheck"
  - "Subsystems/Codegen"
related_contracts:
  []
related_notes:
  - "Language/Examples Index"
last_reviewed: 2026-04-18
---

# CLI

## Purpose

Expose end-user commands such as project init, build, formatting, and doc extraction.

## Main Commands

- `init`
- `build`
- `fmt`
- `doc`

## Testing

CLI-local unit tests live in `crates/aura-cli/src/main.rs`.

## Related

- [[Subsystems/Frontend]]
- [[Subsystems/Typecheck]]
- [[Subsystems/Codegen]]
- [[Language/Examples Index]]
- [[Home]]

