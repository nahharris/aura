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
  - `macro_name node`
  - `macro_name[args] node`

Macros are final, non-shadowable symbols. A `def`/function declaration cannot reuse a macro symbol name.

## Calls And Top-level Rules

- Top-level scope is static-only: `def`, `defmacro`, `use`.
- Function calls support:
  - `callee(args)`
  - `callee[static_args](args)`
  - `callee(args) label { ... } label { ... }`
  - `callee[static_args](args) label { ... } ...`
  - `callee label { ... }`
  - `callee label { ... } label { ... }`
  - `callee[static_args] label { ... } label { ... }`
- Method calls support the same forms (`object.method ...`), including `object.method do { ... }`.
- Trailing closures are always labeled.
- `if` and `cases` are inline functions (not macros). Canonical multi-branch form is `cases when { ... }`.

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

## CLI (`aura`)

Build and emit checked IR from a source file:

```bash
cargo run -p aura-cli -- build examples/basic_ops.aura
```

By default this writes pretty IR to `*.ir.aura` next to the input file.

Emit JSON instead:

```bash
cargo run -p aura-cli -- build examples/basic_ops.aura --format json
```

Choose output path explicitly:

```bash
cargo run -p aura-cli -- build examples/basic_ops.aura --out examples/basic_ops.out.ir.aura
```

Try broken examples to inspect diagnostics:

```bash
cargo run -p aura-cli -- build examples/broken_type_mismatch.aura
cargo run -p aura-cli -- build examples/broken_static_bound.aura
cargo run -p aura-cli -- build examples/broken_interface_bound.aura
cargo run -p aura-cli -- build examples/broken_parse.aura
```
