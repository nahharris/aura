---
title: "Runtime Host"
kind: subsystem
status: active
owner: repo
source_paths:
  - "crates/aura-runtime-host/src/lib.rs"
depends_on:
  []
related_contracts:
  []
related_notes:
  - "Subsystems/Codegen"
last_reviewed: 2026-04-18
---

# Runtime Host

## Purpose

Provide the native runtime boundary required by generated code. The current exported surface is intentionally minimal.

## Current Export

- `syscall_exit`
