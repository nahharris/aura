---
title: "Syntax And Semantics"
kind: language
tags:
  - aura
  - syntax
---

# Syntax And Semantics

This note is the quick operational map for Aura's current observable language rules. The detailed source of truth is split across the linked language notes.

## Canonical Rules To Keep In View

- Macro declaration canonical form: `defmacro[static_args] macro_name(ast_node) -> T { ... }`.
- Macro application canonical forms: `macro_name node` and `macro_name[args] node`.
- Macro application consumes a single operand and chains right-associatively.
- Macro symbols are final and non-shadowable.
- Top-level scope is static-only: `def`, `defmacro`, and `use`.
- `static` is a reusable compile-time interface concept shared across features.
- Function-like declaration syntax is assignment sugar and normalizes to assignment semantics.
- `if` and `cases` are inline function calls, not dedicated parser special cases.
- Trailing closure call arguments are labeled.
- `defstub` declares typed extern or builtin contracts at top level; same-name overloads are allowed only for stubs.
- `Macro[...]` is valid in `defstub` for declaration-only builtin forms such as `return`, `break`, and `continue`.
- `Func[...]` parameter shapes preserve names and labels so builtins such as `if`, `cases`, and `loop` can type labeled trailing closures.
- Enum variants carry at most one payload value; struct payload sugar keeps field-first spelling.
- Struct-like pattern surfaces use field-first spelling everywhere: `field = pattern`. Import renames use `exported_name = local_alias`.

## Spec Map

- [[Language/Lexical Rules]]
- [[Language/Type System]]
- [[Language/Literals And Data]]
- [[Language/Bindings And Declarations]]
- [[Language/Functions And Closures]]
- [[Language/Calls Operators And Blocks]]
- [[Language/Control Flow]]
- [[Language/Modules Projects And Runtime]]

## Where These Rules Land In Code

- tokenization: `crates/aura-frontend/src/token.rs`
- lexing: `crates/aura-frontend/src/lexer.rs`
- parsing: `crates/aura-frontend/src/parser.rs`
- static constraints: `crates/aura-frontend/src/static_eval.rs`
- checked IR: `crates/aura-typecheck/src/checked_ir.rs`
- control-flow lowering: `crates/aura-typecheck/src/checker.rs`

## Related

- [[Language/Design Overview]]
- [[Language/AUON]]
- [[Contracts/Typecheck IR]]
- [[Subsystems/Frontend]]
- [[Subsystems/Typecheck]]
- [[Home]]
