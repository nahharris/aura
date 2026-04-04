# Aura

Aura is a language project with frontend, typecheck, CLI, and LLVM backend-infrastructure crates. `DESIGN.md` is the authoritative language specification.

## Workspace Layout

This repository is a Cargo workspace.

```text
.
├── Cargo.toml                  # workspace manifest
├── DESIGN.md                   # authoritative language spec
├── xtask/                      # automation + LLVM toolchain management
└── crates/
    ├── aura-cli/
    ├── aura-codegen/
    ├── aura-diagnostics/
    └── aura-frontend/
    └── aura-typecheck/
```

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

Use `cargo xtask dev ...` as the default workflow from repository root:

```bash
cargo xtask dev check
cargo xtask dev build
cargo xtask dev test
cargo xtask dev lint
cargo xtask dev fmt
cargo xtask dev qa
```

Cargo aliases are configured in `.cargo/config.toml`:

```bash
cargo qa
cargo lint
cargo test-all
cargo check-all
cargo build-all
cargo fmt-all
```

Run frontend-only tests directly:

```bash
cargo xtask dev test
```

## LLVM Backend Setup

LLVM-backed codegen in `aura-codegen` uses `inkwell` with LLVM 18 (`llvm18-0`).

Use `cargo xtask` for LLVM installation and environment injection:

```bash
cargo xtask llvm setup
cargo xtask llvm doctor
```

The setup is idempotent and self-healing. It downloads the pinned prebuilt LLVM release archive, extracts it under workspace-local `toolchains/`, and keeps a stable major alias at `toolchains/llvm/18`.

Run backend checks/tests through xtask (or cargo aliases that call xtask), so `LLVM_SYS_180_PREFIX` is injected at runtime:

```bash
cargo xtask llvm check
cargo xtask llvm build
cargo xtask llvm test
cargo xtask llvm clippy
cargo xtask llvm run -- -p aura-cli -- build path/to/main.aura
cargo xtask llvm cargo -- test -p aura-codegen --features llvm-backend

# equivalent aliases
cargo check-llvm
cargo build-llvm
cargo test-llvm
cargo clippy-llvm
```

On Windows, xtask automatically applies an LLVM compatibility workaround when needed by creating
`libxml2s.lib` as an empty static stub in the managed LLVM toolchain if upstream `llvm-config`
reports it but the archive is missing.

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
