---
title: "Xtask"
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
last_reviewed: 2026-04-18
---

# Xtask

## Purpose

Centralize automation for the workspace, including dev commands, LLVM toolchain management, and vault maintenance.

## Command Families

- `dev`
- `llvm`
- `docs`

