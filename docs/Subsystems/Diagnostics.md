---
title: "Diagnostics"
kind: subsystem
status: active
owner: repo
source_paths:
  - "crates/aura-diagnostics/src/lib.rs"
  - "crates/aura-diagnostics/src/issue.rs"
  - "crates/aura-diagnostics/src/type_ref.rs"
  - "crates/aura-diagnostics/src/typing_context.rs"
depends_on:
  []
related_contracts:
  []
related_notes:
  - "Subsystems/Frontend"
  - "Subsystems/Typecheck"
  - "Subsystems/CLI"
last_reviewed: 2026-04-18
---

# Diagnostics

## Purpose

Provide shared diagnostic types, severity/stage metadata, issue codes, and type references used across compiler surfaces.

## Key Concepts

- `Diagnostic`
- `Severity`
- `Stage`
- `Span`

## Related

- [[Subsystems/Frontend]]
- [[Subsystems/Typecheck]]
- [[Subsystems/CLI]]
- [[Architecture/Testing Strategy]]
- [[Home]]

