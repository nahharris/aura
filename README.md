# Aura

[![Status: Pre-Alpha](https://img.shields.io/badge/status-pre--alpha-blue)](#project-status)
[![Rust Workspace](https://img.shields.io/badge/rust-workspace-orange?logo=rust)](#for-developers)
[![CI](https://img.shields.io/badge/ci-not%20configured-lightgrey)](#for-developers)
[![License](https://img.shields.io/badge/license-TBD-lightgrey)](#project-status)

> [!NOTE]
> Aura is under active development. Expect syntax, APIs, crate boundaries, and tooling to evolve.

Aura is a modern systems language designed for clear code, compile-time power, and practical performance.

This README is user-focused: it shows the direction and feel of Aura as a language.

`DESIGN.md` remains the source of truth for formal language rules.

## Why Aura

- Readable by default, with concise expressions and explicit types when you want them.
- Compile-time features (`static`, macros) for safety and zero-cost abstractions.
- Designed to scale from scripts to systems components.

## Language Showcase

### Hello, Aura

```aura
def greet(name: String) -> String {
    "Hello, $(name)!"
}

def main() -> Void {
    println(greet("World"));
}
```

### Small, Typed Functions

```aura
def area(width: Float, height: Float) -> Float {
    width * height
}

def label_area(width: Float, height: Float) -> String {
    let a = area(width, height);
    "Area = $(a)"
}
```

### Pattern-Driven Control Flow

```aura
def classify(n: Int) -> String {
    n ~ n < 0  -> "negative",
    n ~ n == 0 -> "zero",
    n          -> "positive",
};
```

### Collections And Higher-Order Style

```aura
def even_squares(nums: List[Int]) -> List[Int] {
    nums
        .filter by { x -> x % 2 == 0 }
        .map with { x -> x * x }
}
```

## Quick Try

Build an Aura source file:

```bash
cargo xtask llvm setup
cargo xtask llvm run -- -p aura-cli -- build examples/basic_ops.aura
```

Emit intermediate outputs when needed:

```bash
cargo xtask llvm run -- -p aura-cli -- build examples/basic_ops.aura --format auir
cargo xtask llvm run -- -p aura-cli -- build examples/basic_ops.aura --format ll
cargo xtask llvm run -- -p aura-cli -- build examples/basic_ops.aura --format obj
```

## For Developers

Everything in this section is implementation and contributor oriented.

### Workspace Layout

```text
.
├── Cargo.toml                  # workspace manifest
├── DESIGN.md                   # authoritative language spec
├── examples/                   # sample Aura programs
├── xtask/                      # automation + LLVM toolchain management
└── crates/
    ├── aura-cli/
    ├── aura-codegen/
    ├── aura-diagnostics/
    ├── aura-frontend/
    ├── aura-runtime-host/
    └── aura-typecheck/
```

### Development Workflow

Use `cargo xtask dev ...` from repository root:

```bash
cargo xtask dev check
cargo xtask dev build
cargo xtask dev test
cargo xtask dev lint
cargo xtask dev fmt
cargo xtask dev qa
```

Convenience aliases (`.cargo/config.toml`):

```bash
cargo qa
cargo lint
cargo test-all
cargo check-all
cargo build-all
cargo fmt-all
```

### LLVM Toolchain

Aura uses a managed LLVM 18 toolchain through `xtask`.

```bash
cargo xtask llvm setup
cargo xtask llvm doctor
```

Preferred LLVM-backed checks/builds/tests:

```bash
cargo xtask llvm check
cargo xtask llvm build
cargo xtask llvm test
cargo xtask llvm clippy
```

Equivalent aliases:

```bash
cargo check-llvm
cargo build-llvm
cargo test-llvm
cargo clippy-llvm
```

Supported CLI formats:

- `native` (default): emits executable and keeps `.ll` + `.obj` intermediates
- `auir`: emits checked IR text as `*.auir`
- `ll`: emits LLVM textual IR as `*.ll`
- `obj`: emits object file as `*.obj`

### Language Rules (Canonical)

- Top-level scope is static-only: `def`, `defmacro`, `use`.
- Macro declaration canonical form: `defmacro[static_args] macro_name(ast_node) -> T { ... }`.
- Macro application canonical forms: `macro_name node` and `macro_name[args] node`.
- Macro application consumes a single AST node and chains right-associatively.
- Function-like declarations are assignment sugar and normalize to assignment semantics.

### Diagnostics Smoke Checks

```bash
cargo run -p aura-cli -- build examples/broken_type_mismatch.aura
cargo run -p aura-cli -- build examples/broken_static_bound.aura
cargo run -p aura-cli -- build examples/broken_interface_bound.aura
cargo run -p aura-cli -- build examples/broken_parse.aura
```

## Project Status

Aura is currently pre-alpha. The language and implementation are moving quickly, and breaking changes are expected during active design and compiler development.
