---
title: "Modules Projects And Runtime"
kind: language
tags:
  - aura
  - language
  - architecture
---

# Modules Projects And Runtime

## Modules

Each source file is a module. A module is a named collection of static declarations. In v1, all top-level declarations are exported.

```aura
def greet(name: String) -> String {
    "Hello, $(name)!"
}
```

## `use` — Import Declaration

`use` brings names from another module into the current scope.

```
use_decl ::= "use" use_pattern "=" string_literal ";"

use_pattern ::= identifier                            // namespace: `use io = "@stl/io"`
             |  "(" use_field ("," use_field)* ","? ")"  // destructure: `use (print, read) = "@stl/io"`

use_field   ::= identifier "=" identifier             // rename: exported_name = local_alias
             |  identifier                            // plain: bind under same name
```

**Namespace import** — bind the entire module under a local name:

```aura
use io = "@stl/io";
io.print("hello");
```

**Destructuring import** — bring specific names into scope:

```aura
use (print, read) = "@stl/io";
```

**Rename on import** — `exported_name = local_alias` (field = binding, matching struct-pattern syntax):

```aura
use (print = my_print, read) = "@stl/io";
my_print("hello");
```

Module paths:

- `@name/...` — library reference resolved via the library lookup path.
- `./...` or `../...` — relative path from the importing file's directory.

Import resolution rules (current runtime):

- Modules are loaded lazily at `use` sites.
- Re-importing the same module path reuses a cached module value (single evaluation semantics).
- Cyclic imports are runtime errors with an import-chain diagnostic.

## Runtime extern stubs

Runtime host symbols are exposed through `defstub` declarations in the standard library rather than through a compiler-injected prelude or the removed `builtin` form. The STL entrypoint `aura-stl/src/lib.aura` re-exports `aura-stl/src/core.aura`, so consuming projects see these contracts through the normal library auto-import surface.

Runtime boundary integer and pointer conventions:

- file-descriptor style handles: `Int32`
- lengths/counts: `USize`
- read/write byte count returns: `ISize`
- file offsets: `Int64`
- opaque runtime byte buffers: `Bytes`

`Bytes` is the current kernel-facing buffer type. It is an owned opaque runtime object with:

- `len: USize`
- contiguous mutable byte storage

The public builtin surface for byte-oriented host I/O is:

```aura
defstub syscall_exit: Func[(code: Int), Never];
defstub syscall_write: Func[(fd: Int, bytes: Bytes), ISize];
defstub bytes_new: Func[(size: USize), Bytes];
defstub bytes_get: Func[(bytes: Bytes, index: USize), UInt8];
defstub bytes_set: Func[(bytes: Bytes, index: USize, value: UInt8), Void];
defstub string_into: Func[(text: String), Bytes];
```

`syscall_write` writes the contents of `bytes` to the host file descriptor and returns the number
of bytes written. The current host implementation recognizes `1` as stdout and `2` as stderr; it
returns `-1` on host write failure.

`Bytes.get` and `Bytes.set` perform runtime bounds checks. Out-of-bounds access now routes through
the panic path.

Aura provides panic primitives:

```aura
panic "something went wrong"
let recovered = catch (panic "boom") else { "fallback" }
```

- `panic "message"` raises a runtime panic with a string payload.
- `catch (expr) else { fallback }` evaluates `expr` in a guarded region and returns `fallback` if
  panic is raised while evaluating `expr`.

`String` remains the public string-literal type; converting it to a writeable buffer requires
`String.into()`, which copies the UTF-8 bytes into a fresh owned `Bytes` value.

## Managed memory handles

Aura also has compiler-recognized opaque managed memory handles:

- `RawAlloc[T]`
- `Slice[T]`
- `Ref[T]`

The public safe surface is:

```aura
let alloc = RawAlloc[Int].new(4)
let slice = alloc.slice()

slice.get(0)        // Option[Int]
slice.set(0, 42)    // Bool
slice.ref_at(0)     // Option[Ref[Int]]

let ref = slice.ref_at(0)!!
ref.get()           // Int
ref.set(7)          // Void
```

`RawAlloc[T].new(count)` allocates zero-initialized storage for `count` elements. v1 allocations are
leak-only for the process lifetime, so `Ref[T]` values are non-null and cannot dangle once produced.
`Slice[T]` and `Ref[T]` expose no raw pointer or unchecked source-level API.

GC-prep contract (phase 1) is additive and does not change source semantics: runtime allocations now
carry compiler-derived metadata (`layout_id`, `trace_kind`) in addition to element size/alignment.
Codegen also emits explicit runtime safepoints at call boundaries for future collectors.

`Slice.get(index)` and `Slice.ref_at(index)` return `null` when `index` is out of bounds.
`Slice.set(index, value)` returns `false` when out of bounds and `true` after a successful write.
The compiler lowers these operations to internal runtime-host ABI helpers with concrete element
size/alignment supplied by codegen; those helpers are not Aura-callable `defstub`s.

---

## Projects and `project.auon`

Aura is project-oriented. A project root contains `project.auon` and standard folders:

- `src/` — project source modules
- `vendor/` — vendored dependencies (including STL)
- `target/` — build artifacts

`project.auon` is an AUON root struct document:

```auon
name = "hello",
version = "0.1.0",
kind = .binary,
dependencies = [
    "json" = .git((url = "github.com/acme/aura-json", ref = "v1.2.3")),
]
```

Manifest field contract:

- `name: String`
- `version: String`
- `kind: enum(binary, library)`
- `dependencies: Dict[String, DependencySource]`

Dependency source forms:

- `.path(String)`
- `.git((url = String, ref = String))`

> [!NOTE]
> Vendored dependencies still need to be declared in `project.auon`; `.git(...)` sources resolve to `vendor/<alias>/...`, while `.path(...)` may point into `vendor/` or outside the project tree.

Dependencies are declared under bare aliases (`"json"`, `"stl"`). Aura source code keeps the `@alias` prefix in `use` paths, and import resolution maps that prefix back to the declared manifest alias.

Module imports using alias paths:

```aura
use io = "@stl/io";
use parse = "@json/parser";
```

Import resolution maps `"@alias/some/module"` to:

- `vendor/alias/some/module.aura`

Notes:

- `.test.aura` files are not part of production compilation.
- `x.aura` and `x.test.aura` represent the same module namespace for test builds.
## Related Notes

- [[Language/AUON]]
- [[Subsystems/CLI]]
- [[Subsystems/Codegen]]
- [[Subsystems/Runtime Host]]
