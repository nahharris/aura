# Aura Agent Ops

Aura = Rust compiler workspace + Aura standard library + editor/tool submodules + Obsidian wiki.

## Start Here

- Wiki home: `docs/Home.md`
- Language source: `docs/Language/Design Overview.md`
- Syntax quick map: `docs/Language/Syntax And Semantics.md`
- Repo map: `docs/Architecture/Repo Map.md`
- Commands: `docs/Architecture/Build And Dev Workflow.md`
- Tests: `docs/Architecture/Testing Strategy.md`

## Style

- Use caveman mode for agent chat: short, exact, no fluff.
- Keep code, commits, PR text, and public docs normal.
- Prefer wiki links inside `docs/`.

## Work Rules

- `docs/` is source-of-truth surface, not optional prose.
- If code changes syntax, typing, compiler behavior, codegen, project layout, workflows, or architecture, update matching wiki note same task.
- Prefer existing notes. Add new note only for new durable concept.
- Preserve vault structure, frontmatter, and wikilinks.
- Before closing doc-affecting work: run `cargo xtask docs sync` when generated inventory can change, then `cargo xtask docs check`.

## Commands

- Routine loop: `cargo xtask dev check`, `cargo xtask dev test`, `cargo xtask dev lint`, `cargo xtask dev fmt-check`.
- CI parity: `cargo xtask dev ci` or `cargo ci`.
- Docs: `cargo xtask docs sync`, `cargo xtask docs check`.
- Docs search/MCP: use QMD when working across `docs/`.
  - `cargo xtask qmd build`
  - `cargo xtask qmd start`
  - MCP endpoint: `http://127.0.0.1:8181/mcp`
  - health: `http://127.0.0.1:8181/health`
- LLVM work: use `cargo xtask llvm ...`; do not rely on global LLVM env vars.
- LLVM CLI builds: `cargo xtask llvm run -- -p aura-cli -- build path/to/main.aura`.

## Repo Boundaries

- Main crates: `crates/aura-frontend`, `crates/aura-typecheck`, `crates/aura-codegen`, `crates/aura-diagnostics`, `crates/aura-cli`, `crates/aura-runtime-host`, `xtask`.
- Companion dirs: `aura-stl`, `examples`, `tool`, `docs`.
- `aura-stl/` and `tool/*` are often submodules with own history and CI. Do not treat superproject checks as their full validation.

## Tests

- Syntax work: parser tests in `crates/aura-frontend/src/parser.rs` or focused frontend tests.
- Type rules: typecheck tests under `crates/aura-typecheck/tests/`.
- Codegen/LLVM: run through `cargo xtask llvm ...`.
- Use descriptive test names and direct `assert_eq!` when suitable.
