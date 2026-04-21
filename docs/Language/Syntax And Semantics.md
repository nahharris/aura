---
title: "Syntax And Semantics"
kind: language
tags:
  - aura
  - syntax
---

# Syntax And Semantics

This note is a reader's map into `DESIGN.md`, not a replacement for it.

## Canonical Rules To Keep In View

- Macro declaration canonical form: `defmacro[static_args] macro_name(ast_node) -> T { ... }`
- Macro application canonical forms: `macro_name node` and `macro_name[args] node`
- Macro application consumes a single operand and chains right-associatively
- `if` and `cases` are inline function calls, not dedicated parser special cases
- trailing closure call arguments are labeled

## Alias Note

- `true`, `false`, and `null` are not reserved keywords; Aura treats them as runtime aliases, matching `.true`, `.false`, and `.null`
- AUON phase 1 reuses those alias spellings as source-level conveniences and normalizes them to dot-variant values

## Where These Rules Land In Code

- tokenization: `crates/aura-frontend/src/token.rs`
- lexing: `crates/aura-frontend/src/lexer.rs`
- parsing: `crates/aura-frontend/src/parser.rs`
- static constraints: `crates/aura-frontend/src/static_eval.rs`
