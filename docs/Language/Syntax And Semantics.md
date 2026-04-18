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

## Where These Rules Land In Code

- tokenization: `crates/aura-frontend/src/token.rs`
- lexing: `crates/aura-frontend/src/lexer.rs`
- parsing: `crates/aura-frontend/src/parser.rs`
- static constraints: `crates/aura-frontend/src/static_eval.rs`
