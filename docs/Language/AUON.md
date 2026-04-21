---
title: "AUON"
kind: language
tags:
  - aura
  - auon
  - data-format
---

# AUON

AUON is Aura Object Notation: Aura-shaped serialized data, not full Aura evaluation.

## Phase 1 Scope

- authoritative spec lives in `tool/auon/SPEC.md`
- formal grammar lives in `tool/auon/grammar/auon.ebnf`
- current repo work is spec-first only
- parser, compiler integration, schema language, and tooling support come later

## Ecosystem Surfaces

- `tool/auon/` carries normative AUON language spec and examples
- `tool/auon-rs/` carries serde-compatible Rust parser/serializer support for AUON

## Core Rules

- one `.auon` file encodes exactly one value
- AUON is strict data-only subset of Aura syntax
- supported values: numbers, strings, chars, anonymous variants, tuples, structs, lists, dicts
- comments use Aura comment forms: `//` and `/* ... */`
- root wrapper omission is allowed only for list, dict, and struct documents
- trailing commas are allowed where sequence syntax allows them
- semicolons are never valid AUON

## Alias Normalization

- `true` normalizes to `.true`
- `false` normalizes to `.false`
- `null` normalizes to `.null`

This follows Aura language direction: these spellings are runtime aliases, not reserved keywords.

## Typing Direction

AUON parsers should adapt decoded values to target-platform types, deriving from Aura type shapes where possible. Phase 1 defines syntax and normalization only, not schema policy.

Current Rust support surface in `tool/auon-rs` exposes:

- public AUON `Value` DOM with separate `Int` and `Float`
- parser entrypoints for raw AUON text
- serde encode/decode entrypoints for typed Rust data
- compact and pretty AUON emitters using document-friendly top-level omission where unambiguous

## Related Notes

- [[Language/Design Overview]]
- [[Language/Syntax And Semantics]]
- [[Architecture/Repo Map]]
