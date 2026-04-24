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
- `defstub` declares typed extern or builtin contracts at top level; same-name overloads are allowed only for stubs
- `Macro[...]` is valid in `defstub` for declaration-only builtin forms such as `return`, `break`, and `continue`
- `Func[...]` parameter shapes preserve names/labels so builtins such as `if`, `cases`, and `loop` can type labeled trailing closures
- Enum variants still carry at most one payload value; when that payload is a struct, `.variant(field = value, ...)` and `.variant(field = binding, ...)` are surface sugar for the explicit wrapped struct payload.
- Struct-like pattern surfaces use field-first spelling everywhere: `field = pattern`. Import renames follow the same rule with `exported_name = local_alias`.

## Alias Note

- `true`, `false`, and `null` are not reserved keywords; Aura treats them as runtime aliases, matching `.true`, `.false`, and `.null`
- AUON phase 1 reuses those alias spellings as source-level conveniences and normalizes them to dot-variant values

## Control Flow Surface

- `if`, `cases`, and `loop` resolve as callable forms whose signatures are provided by `aura-stl/src/core.aura` stubs re-exported from `aura-stl/src/lib.aura`.
- `return`, `break`, and `continue` resolve as macro-shaped builtin forms with compiler-checked targets; invalid usage outside a function or loop is a typecheck error.
- The checker lowers control flow to dedicated checked-IR nodes, and LLVM lowering emits branches/blocks rather than runtime calls for these forms.

## Where These Rules Land In Code

- tokenization: `crates/aura-frontend/src/token.rs`
- lexing: `crates/aura-frontend/src/lexer.rs`
- parsing: `crates/aura-frontend/src/parser.rs`
- static constraints: `crates/aura-frontend/src/static_eval.rs`
