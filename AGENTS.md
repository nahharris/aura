# Aura — Agent Guidelines

This file provides guidance for coding agents working in this repository.

## Project Overview

Aura is a multi-crate compiler workspace with an Obsidian vault in `docs/` that should track the codebase as an engineering second brain.

Agents should treat `docs/` as a maintained second-brain surface, not as optional prose. When a change affects architecture, compiler behavior, syntax, typing rules, codegen behavior, build workflows, project layout, or developer workflows, update the relevant notes in `docs/` in the same task unless the user explicitly says not to.

- Authoritative spec: `DESIGN.md`
- Obsidian vault root: `docs/`
- Workspace crates:
  - `crates/aura-frontend`
  - `crates/aura-typecheck`
  - `crates/aura-codegen`
  - `crates/aura-diagnostics`
  - `crates/aura-cli`
  - `crates/aura-runtime-host`
  - `xtask`
- Companion surfaces:
  - `aura-stl`
  - `examples`
  - `tool`

Key entry files:

- `crates/aura-frontend/src/token.rs` — token model
- `crates/aura-frontend/src/lexer.rs` — source to tokens
- `crates/aura-frontend/src/ast.rs` — AST nodes
- `crates/aura-frontend/src/parser.rs` — parser + parser contract tests
- `crates/aura-frontend/src/static_eval.rs` — compile-time-known/static interface hook
- `crates/aura-frontend/src/lib.rs` — crate module surface
- `crates/aura-typecheck/src/lib.rs` — typecheck entry point
- `crates/aura-codegen/src/lib.rs` — backend entry point
- `crates/aura-cli/src/main.rs` — CLI entry point
- `xtask/src/main.rs` — automation command surface
- `xtask/src/docs.rs` — Obsidian vault automation

## Second Brain Expectations

- Keep `docs/` aligned with the actual codebase and `DESIGN.md`.
- When editing notes in `docs/`, use the `obsidian-markdown` skill so Obsidian-specific Markdown stays valid and linked.
- When the task involves interacting with or verifying the live Obsidian vault, use the `obsidian-cli` skill if Obsidian is available.
- Prefer updating an existing relevant note over creating duplicate notes with overlapping scope.
- If a code change introduces a new concept, workflow, invariant, or notable implementation detail, either document it in an existing note or add a clearly named new note in `docs/`.
- Preserve vault structure and internal links. Use wikilinks for links within `docs/` when appropriate.
- Before closing out doc-affecting work, run the docs sync/check flow when it is relevant to the change.

## Build, Lint, and Test Commands

Use `cargo xtask dev ...` as the default command runner for routine development tasks.

From workspace root:

```bash
cargo xtask dev check
cargo xtask dev build
cargo xtask dev test
cargo xtask dev lint
cargo xtask dev fmt
cargo xtask dev fmt-check
cargo xtask dev ci
cargo xtask dev qa
cargo xtask docs sync
cargo xtask docs check
```

Preferred command runner aliases (defined in `.cargo/config.toml`):

```bash
cargo ci
cargo fmt-check
cargo qa
cargo lint
cargo test-all
cargo check-all
cargo build-all
cargo fmt-all
cargo docs-sync
cargo docs-check
```

### CI parity before ending a session

Before wrapping up non-trivial work (especially codegen, xtask, `docs/` generated inventories, or LLVM paths), run **`cargo xtask dev ci`** (or **`cargo ci`**) so local results match [GitHub Actions](https://github.com/nahharris/aura/actions/workflows/ci.yml): rustfmt check and `docs check` (Linux runners), workspace clippy once plus tests on Linux and Windows, then LLVM doctor, clippy, and tests (Linux and Windows).

Doc-only or inventory edits still use `cargo xtask docs sync` when you change what should be generated; `dev ci` includes `docs check` so a single command catches stale generated notes before you stop.

## Xtask Usage

Use `cargo xtask` for project automation and environment-sensitive routines.

- Prefer `cargo xtask ...` over ad-hoc shell steps when an xtask command exists.
- LLVM setup and LLVM-featured checks/tests should run through xtask so environment variables are injected by xtask at execution time.
- Do not use or reintroduce `llvmenv`; LLVM provisioning is managed in-house via xtask.

Common commands:

```bash
cargo xtask llvm setup
cargo xtask llvm doctor
cargo xtask llvm ci
cargo xtask llvm check
cargo xtask llvm build
cargo xtask llvm test
cargo xtask llvm clippy
cargo xtask llvm run -- -p aura-cli -- build path/to/main.aura
cargo xtask llvm cargo -- test -p aura-codegen --features llvm-backend
cargo xtask docs sync
cargo xtask docs check
cargo xtask docs new-adr --title "Decision Name"
```

On Windows, xtask also applies an LLVM compatibility workaround when needed by creating
`libxml2s.lib` as an empty static stub under the managed LLVM toolchain if the upstream
`llvm-config --system-libs --link-static` reports it but the archive is missing.

Do not rely on globally exported LLVM env vars for regular workflows when xtask provides the command path.
Do not run direct `cargo` commands for LLVM-featured tasks; always use `cargo xtask llvm ...` so `LLVM_SYS_180_PREFIX` is injected consistently.
LLVM-sensitive CLI builds (`--format ll`, `--format obj`, `--format native`) also depend on
the managed Clang/LLVM toolchain; run them only via `cargo xtask llvm run -- ...`.

Docs workflow:

```bash
cargo xtask docs sync
cargo xtask docs check
```

Use `cargo xtask docs sync` to refresh generated inventory notes and scaffold any missing curated notes in the Obsidian vault. Use `cargo xtask docs check` to detect stale generated docs in CI or before closing out doc-related work.

For work that changes the codebase shape or documented workflows, prefer running `cargo xtask docs sync` after edits and `cargo xtask docs check` before completion.

Frontend-only test loop:

```bash
cargo xtask dev test
```

## Design Alignment Rules

- `DESIGN.md` is authoritative for observable syntax and semantics.
- Macro declaration canonical form:
  - `defmacro[static_args] macro_name(ast_node) -> T { ... }`
- Macro application canonical form:
  - `macro_name node`
  - `macro_name[args] node`
- Macro application operand is single-node and chaining is right-associative.
- Macro symbols are final and non-shadowable.
- Top-level scope is static-only (`def`, `defmacro`, `use`).
- Trailing closure call arguments are labeled.
- `if` and `cases` are inline function calls (`cases when { ... }`), not macro-special syntax.
- `static` is a reusable compile-time interface concept shared across features.
- Function-like declaration syntax is assignment sugar and should normalize to assignment semantics.

## Testing Expectations

- New syntax work must include parser tests in `crates/aura-frontend/src/parser.rs` (or dedicated frontend tests).
- Prefer descriptive test names and `assert_eq!` where direct value comparison is suitable.
- If the task changes architecture, workflows, or curated documentation, update the affected Obsidian notes under `docs/` and verify the docs workflow still passes when relevant.
