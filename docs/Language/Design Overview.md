---
title: "Design Overview"
kind: language
tags:
  - aura
  - language-design
---

# Design Overview

Aura's language design source of truth lives in this vault. Language rules are split into linked notes so syntax, semantics, implementation notes, and onboarding paths stay together.

## Core Principles

1. **Small primitive set.** A minimal collection of orthogonal constructs — expressions, blocks, closures, calls, and assignments — from which all higher-level features are composed.
2. **Self-describing.** Almost every language construct can be defined *in terms of* Aura itself through the macro system, enabling bootstrapping and keeping the compiler core small.
3. **Familiar surface.** Derived constructs should look and feel like the built-in syntax of conventional languages even though they are macros under the hood.
4. **No reserved words.** The lexer should not have a keyword list for structure. Surfaces must be macros (builtin or user-defined) and should stay as contextual identifiers (with the possibility of being auto/implicitly-imported as a prelude).

## Spec Notes

- [[Language/Lexical Rules]]
- [[Language/Type System]]
- [[Language/Literals And Data]]
- [[Language/Bindings And Declarations]]
- [[Language/Functions And Closures]]
- [[Language/Calls Operators And Blocks]]
- [[Language/Control Flow]]
- [[Language/Modules Projects And Runtime]]

## Implementation Anchors

- [[Subsystems/Frontend]] owns tokens, lexing, AST, parsing, formatting, and static interface hooks.
- [[Subsystems/Typecheck]] owns symbol resolution, type rules, builtin callable forms, and checked IR.
- [[Subsystems/Codegen]] owns backend lowering and project compilation.
- [[Architecture/Build And Dev Workflow]] owns routine verification commands.

## Related Notes

- [[Language/Syntax And Semantics]]
- [[Language/AUON]]
- [[Contracts/Typecheck IR]]
