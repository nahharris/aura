# Aura

A functional programming language for application development with a focus on expressiveness, type safety, and self-describing syntax.

## Overview

Aura is a statically-typed functional language that compiles to bytecode and runs on a stack-based virtual machine. It features:

- **Unified declaration syntax** — `def` handles values, functions, type aliases, and methods
- **Pattern matching everywhere** — destructuring, multi-arm closures, and control flow
- **Powerful type system** — tuples, structs, unions, enums, interfaces, and generics
- **Macro-based control flow** — `if`, `loop`, `cases` are macros that inline at compile time
- **Trailing-lambda syntax** — closures can be written outside parentheses for fluent APIs

## Core Principles

1. **Small primitive set** — A minimal collection of orthogonal constructs (expressions, blocks, closures, calls, declarations) from which all higher-level features are composed.

2. **Self-describing** — Almost every language construct can be defined *in terms of* Aura itself through the macro system, enabling bootstrapping and keeping the compiler core small.

3. **Familiar surface** — Derived constructs look and feel like built-in syntax from conventional languages, even though they are macros under the hood.

## Example

```aura
// Functions
def add(a: Int, b: Int) -> Int { a + b }

def greet(name: String) -> String {
    "Hello, $(name)!"
}

// Type aliases
def Point = (x: Int, y: Int)
def[T, E] Result = enum(ok: T, err: E)
def[T] Option = enum(some: T, null: ())

// Pattern matching (multi-arm closure + call)
def factorial(n: Int) -> Int {
    {
        0 -> 1,
        _ -> n * factorial(n - 1)
    }(n)
}

// Methods
def Point.distance(self, other: Point) -> Float {
    let dx = self.x - other.x;
    let dy = self.y - other.y;
    ((dx * dx) + (dy * dy)) : Float
}

// Control flow (macros)
def fizzbuzz(n: Int) -> String {
    cases {
        ~ n % 15 == 0 -> "FizzBuzz",
        ~ n % 3 == 0  -> "Fizz",
        ~ n % 5 == 0  -> "Buzz",
        ~ true        -> n.to_string()
    }
}

// Main entry point
def main() -> Void {
    println(greet("World"));
    
    let nums = [1, 2, 3, 4, 5];
    let squares = nums.map { x -> x * x };
    println("squares: $(squares)");
    
    // Range iteration
    loop for (i in 1..=15) {
        println(fizzbuzz(i));
    }
}
```

## Type System

### Primitives

| Type | Description |
|------|-------------|
| `Int` | 64-bit signed integer |
| `Float` | 64-bit floating point |
| `Bool` | Boolean (`true` / `false`) |
| `String` | UTF-8 string |
| `Char` | Unicode character |
| `Void` | Unit / no value |

### Composite Types

```aura
// Tuple
def Coord = (Int, Int)
let origin = Coord(0, 0);

// Struct
def Person = (name: String, age: Int)
let john = Person(name = "John", age = 30);

// Union (anonymous tagged union)
def Number = union(Int, Float)

// Enum (named-variant sum type)
def[T, E] Result = enum(ok: T, err: E)
def[T] Option = enum(some: T, null: ())

// Interface (structural contract)
def ToString = interface(to_string: Func[(), String])
```

### Generics

```aura
def[T] identity(x: T) -> T { x }

def[T: ToString, U: (Eq, Hash)] HashMap = (
    buckets: List[Entry[T, U]],
    size: Int
)
```

## Pattern Matching

```aura
// Multi-arm closure
{
    .ok(value) -> value,
    .err(msg)  -> panic("Error: $(msg)"),
}(some_result)

// With guards
{
    (x, y) ~ x > y -> x,
    (x, y)         -> y,
}(coord)

// Type patterns
{
    i: Int   -> i.to_string(),
    f: Float -> f.to_string(),
    _        -> "unknown"
}(value)
```

## Operators

| Precedence | Operator | Description |
|------------|----------|-------------|
| 1 (lowest) | `=` | Assignment |
| 2 | `?:` | Elvis / null-coalescing |
| 3 | `\|\|` | Logical OR |
| 4 | `&&` | Logical AND |
| 5 | `==` `!=` | Equality |
| 6 | `<` `>` `<=` `>=` | Comparison |
| 7 | `..` | Range |
| 8 | `+` `-` | Addition / Subtraction |
| 9 | `*` `/` `%` | Multiplication / Division |
| 10 | `:` | Cast / type annotation |
| 11 | `++` `--` | Post-increment / decrement |
| 12 | `!!` | Force-unwrap |
| 13 | `?.` | Safe navigation |
| 14 | `.` | Field / method access |
| 15 (highest) | `( )` `[ ]` | Call / index |

## Standard Library

Aura includes a minimal standard library:

- **`@stl/core`** — Core utilities (`match`)
- **`@stl/io`** — I/O operations (`print`, `println`, `eprint`, `eprintln`)
- **`@stl/string`** — String methods (`len`, `upper`, `lower`, `trim`, `split`, `join`, etc.)
- **`@stl/list`** — List methods (`map`, `filter`, `each`, `push`, `pop`, etc.)
- **`@stl/bool`** — Boolean utilities
- **`@stl/option`** — `Option[T]` type and methods
- **`@stl/result`** — `Result[T, E]` type and methods

```aura
use (print, println) = "@stl/io";
use io = "@stl/io";           // Namespace import
use (map = my_map) = "@stl/list";  // Rename on import
```

Kernel bindings inside STL modules use the `builtin` form with bare identifiers:

```aura
def _io_write = builtin io_write;
def _to_str = builtin to_str;
```

The old string form is invalid: `builtin("io_write")`.

## Current Status

### Completed

| Phase | Description | Status |
|-------|-------------|--------|
| 1 | Lexer — all tokens, string interpolation, implicit semicolons, atoms, char literals | ✅ |
| 2 | Parser — all expressions, statements, declarations, patterns, closures, control flow | ✅ |
| 3 | STL core modules (io, string, list, bool, option, result) | ✅ |
| 4a | Typechecker scaffold — `TypeEnv`, scope chains, error collection | ✅ |
| 4b | Type resolution, registration passes | ✅ |
| 4c | Expression/statement type checking | ✅ |
| 4d | Pattern type checking, exhaustiveness checking | ✅ |
| 4e | Cast validation | ✅ |
| 4f | Compiler bug fixes | ✅ |

### In Progress

| Phase | Description | Status |
|-------|-------------|--------|
| 5a | `def` destructuring bindings (global + local) | 🚧 |
| 5b | Enum/Union/Interface alias constructors | 🚧 |
| 5c | `Expr::Cast` hard runtime check | 🚧 |
| 5d | `GetTag` completeness | 🚧 |
| 6 | Module system (`use` declarations) | 🚧 |

### Planned

| Feature | Description |
|---------|-------------|
| **Macro system** | Powerful hygienic macros defined in Aura syntax; macros manipulate entire forms, support type parameters via `[...]` syntax |
| **Project structure** | `aura build`, `aura run`, `aura test`, `aura fmt`, `aura lint`, `aura sync` |
| **Package management** | Dependencies via git, `project.auml` configuration |
| **Test harness** | Built-in `test` macro and `aura test` subcommand |
| **AUML** | Aura Markup Language for configuration files |
| **FFI** | Foreign function interface for interop with C/Rust |

## Macro System (Planned)

Macros will be defined using Aura syntax and process entire forms:

```aura
// Macro application (no parentheses required)
def foo() -> Void { ... }
// Equivalent to: def(foo() -> Void { ... })

// Macros with type parameters
get["/help"] def Server.help() -> Response { ... }

// Macro definition
defmacro def(body: TypedAssignment) { ... }
```

## Project Structure (Planned)

```
project/
├── project.auml      # Project metadata
├── src/
│   ├── main.aura     # Entry point
│   └── .../test/     # Module tests
├── lib/              # Vendored libraries
├── test/             # Integration tests
├── example/          # Runnable examples
└── out/              # Build artifacts
```

## Building

```bash
# Check for compile errors
cargo check

# Build
cargo build

# Run tests
cargo test

# Run the interpreter
cargo run -- path/to/file.aura
```

## License

MIT
