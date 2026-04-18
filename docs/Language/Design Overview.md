---
title: "Design Overview"
kind: language
tags:
  - aura
  - language-design
---

# Design Overview

`DESIGN.md` is the authoritative language specification. The current design emphasizes a small primitive core, macro-driven extensibility, familiar surface syntax, and the absence of reserved structural keywords.

## Themes

- top-level scope is static-only
- macros are first-class surface shapers
- `static` is a reusable compile-time constraint concept
- function-like declarations normalize to assignment semantics

## Related Notes

- [[Language/Syntax And Semantics]]
- [[Subsystems/Frontend]]
- [[Subsystems/Typecheck]]
