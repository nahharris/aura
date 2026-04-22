---
title: "AUON"
kind: language
tags:
  - aura
  - auon
  - data-format
last_reviewed: 2026-04-22
---

# AUON

AUON is Aura Object Notation: Aura-shaped serialized data, not full Aura evaluation.

## Phase 1 Scope

- authoritative spec lives in `tool/auon/SPEC.md`
- formal grammar lives in `tool/auon/grammar/auon.ebnf`
- Aura project manifests now use AUON via `project.auon`
- editor tooling now treats `.auon` as its own language identity instead of folding it into Aura source mode

## Ecosystem Surfaces

- `tool/auon/` carries normative AUON language spec and examples
- `tool/auon-rs/` carries serde-compatible Rust parser/serializer support for AUON
- `tool/auon-py/` carries Python parser/serializer support with Pydantic-first typed decoding
- `tool/auon-ts/` carries ESM-first TypeScript parser/serializer support with schema-based typed decoding

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

## Current Integration

- project roots are discovered by `project.auon`
- `crates/aura-codegen/src/project/manifest.rs` loads manifests through `tool/auon-rs`
- project manifests use an AUON root struct with fields such as `name`, `version`, `kind`, and `dependencies`
- `tool/tree-sitter-aura/` parses AUON documents alongside Aura source so Zed and Neovim can reuse one parser backend
- `tool/aura-vscode/` ships separate AUON TextMate grammar, snippets, and language configuration for `.auon`

## Editor Direction

- `.auon` should open as `auon`, not as generic Aura source
- AUON highlighting should stay data-only: no declarations, calls, interpolation, or type-annotation assumptions
- document-level root omission is first-class and should highlight cleanly in manifest-style files like `project.auon`

Current Python support surface in `tool/auon-py` exposes:

- public AUON DOM values with separate `Int` and `Float`
- `parse_value` / `loads` / `load`
- `dumps` / `dump`
- `to_value` / `encode` and `from_value` / `decode`
- typed decoding for Pydantic v2 plus straightforward dataclass and typing-hint shapes

Current TypeScript support surface in `tool/auon-ts` exposes:

- public discriminated-union AUON `Value` with separate `Int` and `Float`
- `parseValue` / `parse`
- `stringify` / `stringifyPretty`
- `toValue` / `fromValue`
- schema-driven typed decoding via Zod-style `parse` / `safeParse` objects

## Related Notes

- [[Language/Design Overview]]
- [[Language/Syntax And Semantics]]
- [[Architecture/Repo Map]]
