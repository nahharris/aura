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
    ├── aura-runtime-host/
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

## Runtime Boundary

Phase 4 introduces a minimal runtime syscall boundary oriented around host portability. The STL
builds higher-level behavior on these primitives.

- process: `rt_exit`
- fd I/O: `rt_fd_read`, `rt_fd_write`, `rt_fd_open`, `rt_fd_close`, `rt_fd_seek`
- memory: `rt_mem_map`, `rt_mem_unmap`, `rt_mem_protect`
- time: `rt_time_now_ns`
- entropy: `rt_random_fill`

Runtime ABI conventions:

- file-descriptor style handles use `Int32`
- lengths/counts use `USize`
- read/write byte counts use `ISize`
- seek offsets use `Int64`
- raw memory and byte spans use `Ptr[T]` and `Slice[T]`

Conceptually:

```aura
def[T] Slice = (ptr: Ptr[T], len: USize);
```

Kernel builtins are intentionally low-level (`Ptr`/`Slice` + fixed-width ints); formatting and
high-level I/O remain in Aura STL wrappers.

## CLI (`aura`)

Build from a source file (default format is native executable):

```bash
cargo xtask llvm run -- -p aura-cli -- build examples/basic_ops.aura
```

Supported build formats:

- `native` (default): emits executable and keeps `.ll` + `.obj` intermediates
- `auir`: emits checked IR text as `*.auir`
- `ll`: emits LLVM textual IR as `*.ll`
- `obj`: emits object file as `*.obj`

Examples:

```bash
cargo xtask llvm run -- -p aura-cli -- build examples/basic_ops.aura --format auir
cargo xtask llvm run -- -p aura-cli -- build examples/basic_ops.aura --format ll
cargo xtask llvm run -- -p aura-cli -- build examples/basic_ops.aura --format obj
cargo xtask llvm run -- -p aura-cli -- build examples/basic_ops.aura --format native
```

Choose output path explicitly:

```bash
cargo xtask llvm run -- -p aura-cli -- build examples/basic_ops.aura --format ll --out examples/basic_ops.custom.ll
```

LLVM-backed builds (`--format ll`, `--format obj`, `--format native`) depend on the managed LLVM/Clang toolchain exposed via
`LLVM_SYS_180_PREFIX`. Always run LLVM-sensitive commands via `cargo xtask llvm ...` so
the correct LLVM/Clang installation is provisioned and injected.

Try broken examples to inspect diagnostics:

```bash
cargo run -p aura-cli -- build examples/broken_type_mismatch.aura
cargo run -p aura-cli -- build examples/broken_static_bound.aura
cargo run -p aura-cli -- build examples/broken_interface_bound.aura
cargo run -p aura-cli -- build examples/broken_parse.aura
```
