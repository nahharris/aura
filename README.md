# Aura

[![Status: Pre-Alpha](https://img.shields.io/badge/status-pre--alpha-blue)](#project-status)
[![Rust Workspace](https://img.shields.io/badge/rust-workspace-orange?logo=rust)](#workspace)
[![CI](https://github.com/nahharris/aura/actions/workflows/ci.yml/badge.svg)](https://github.com/nahharris/aura/actions/workflows/ci.yml)
[![Docs: Obsidian Vault](https://img.shields.io/badge/docs-obsidian%20vault-purple)](docs/Home.md)

Aura is a modern systems language for clear code, compile-time power, and practical performance.

> [!NOTE]
> Aura is pre-alpha. Syntax, APIs, crate boundaries, and tooling are expected to move.

## Why Aura

- Familiar expression syntax backed by a small compiler core.
- Compile-time surfaces through `static` and macros.
- Project-oriented builds with AUON manifests.
- A maintained engineering wiki in `docs/` instead of one giant design file.

## Language Taste

### Hello, Aura

```aura
def greet(name: String) -> String {
    "Hello, $(name)!"
}

def main() -> Void {
    println(greet("World"));
}
```

### Typed Functions

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

### Higher-Order Style

```aura
def even_squares(nums: List[Int]) -> List[Int] {
    nums
        .filter by { x -> x % 2 == 0 }
        .map with { x -> x * x }
}
```

## Quick Try

```bash
cargo xtask llvm setup
cargo xtask llvm run -- -p aura-cli -- build examples/basic_ops.aura
```

Emit intermediate outputs:

```bash
cargo xtask llvm run -- -p aura-cli -- build examples/basic_ops.aura --format auir
cargo xtask llvm run -- -p aura-cli -- build examples/basic_ops.aura --format ll
cargo xtask llvm run -- -p aura-cli -- build examples/basic_ops.aura --format obj
```

## Docs

The language source of truth lives in the Obsidian vault:

- [docs/Home.md](docs/Home.md) - wiki entry point
- [docs/Language/Design Overview.md](docs/Language/Design%20Overview.md) - design doorway
- [docs/Language/Syntax And Semantics.md](docs/Language/Syntax%20And%20Semantics.md) - canonical rule map
- [docs/Architecture/Build And Dev Workflow.md](docs/Architecture/Build%20And%20Dev%20Workflow.md) - commands and CI parity

## Workspace

```text
.
|-- Cargo.toml
|-- AGENTS.md
|-- README.md
|-- docs/                 # Obsidian engineering wiki
|-- examples/             # Aura sample programs
|-- aura-stl/             # Aura standard library package
|-- tool/                 # editor integrations, AUON packages, Tree-sitter grammar
|-- xtask/                # automation and LLVM toolchain management
`-- crates/
    |-- aura-cli/
    |-- aura-codegen/
    |-- aura-diagnostics/
    |-- aura-frontend/
    |-- aura-runtime-host/
    `-- aura-typecheck/
```

## Development

Use `cargo xtask dev ...` from the repository root:

```bash
cargo xtask dev check
cargo xtask dev build
cargo xtask dev test
cargo xtask dev lint
cargo xtask dev fmt-check
cargo xtask dev ci
```

Convenience aliases live in `.cargo/config.toml`:

```bash
cargo qa
cargo lint
cargo test-all
cargo check-all
cargo build-all
cargo fmt-all
cargo docs-check
```

## LLVM Toolchain

Aura uses a managed LLVM 18 toolchain through `xtask`.

```bash
cargo xtask llvm setup
cargo xtask llvm doctor
cargo xtask llvm check
cargo xtask llvm test
cargo xtask llvm clippy
```

Use `cargo xtask llvm run -- ...` for LLVM-sensitive CLI builds.

## Project Status

Aura is pre-alpha. The compiler is useful for design and implementation work, but breaking changes are part of the current development loop.
