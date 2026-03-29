# Aura

Aura is currently a frontend-focused language project. `DESIGN.md` is the authoritative language specification.

## Workspace Layout

This repository is a Cargo workspace.

```text
.
├── Cargo.toml                  # workspace manifest
├── DESIGN.md                   # authoritative language spec
└── crates/
    └── aura-frontend/
        ├── Cargo.toml
        └── src/
            ├── ast.rs
            ├── lexer.rs
            ├── parser.rs
            ├── static_eval.rs
            ├── token.rs
            └── lib.rs
```

The active workspace target is frontend-only (`aura-frontend`). Backend/runtime/compiler VM paths are not part of the active build graph.

## Canonical Macro Forms

- Macro declaration canonical form:
  - `defmacro[static_args] macro_name(ast_node) -> T { ... }`
- Macro application canonical form:
  - `macro_name[args] node`

Macro application consumes a single AST-node operand and chains right-associatively:

```aura
a b node   // a (b node)
```

`static` is a reusable compile-time interface concept shared by declaration bounds and macro static arguments.

## Declaration Normalization

Function-like declaration syntax is assignment sugar:

```aura
name(args...) -> R { ... }   // sugar
name = { args... -> ... }    // normalized assignment semantics
```

The same appearance-sugar rule applies to `defmacro` declarations.

## Development

From repository root:

```bash
cargo fmt --check
cargo clippy -- -D warnings
cargo test
```

Run frontend-only tests directly:

```bash
cargo test -p aura-frontend
```
