---
title: "Bindings And Declarations"
kind: language
tags:
  - aura
  - language
  - syntax
---

# Bindings And Declarations

## Variables and Bindings

## Local Assignment

`=` assigns a value to an *already declared* variable or assignable place inside a local scope. Assignable places include local names, named struct fields, tuple indexes, and nested combinations of those forms.

```aura
x = 1;
x = x + 1;
person.name = "John Doe";
coord.0 = coord.0 + 2;
```

Attempting to assign to an undeclared name is a compile error.

## `let` — Mutable Local Binding

`let` declares one or more mutable local variables. Multiple bindings can be written in a single `let` separated by commas.

```aura
let x = 1;
let a = 1, b = 2, c = a + b;
```

`let` is a macro that expands to a mutable binding statement. Variables declared with `let` are scoped to the enclosing block.

Macro definition:

```aura
defmacro let(
    assignment: Assignment
) -> Stmt
```

## `def` — Immutable Binding

`def` is identical to `let` except the binding cannot be reassigned after declaration. It is not a reserved keyword — it is an ordinary identifier recognised contextually as a declaration macro.

```aura
def pi = 3.14159;
```

Macro definition:

```aura
defmacro def(
    assignment: Assignment
) -> Stmt
```

It can be used both in global or local scopes

## `defstub` — Static Extern Contract

`defstub` is a top-level static declaration that introduces a typed global symbol without an Aura body. It is used for runtime externs and compiler-lowered builtin forms.

```aura
defstub syscall_exit: Func[(code: Int), Never];
defstub[T] if: Func[(cond: Bool, then: Func[(), T], else: Func[(), T]), T];
defstub[T] return: Macro[T, Never];
```

Same-name overloads are allowed for `defstub` declarations only. `Func[...]` stubs describe callable extern contracts; `Macro[...]` stubs describe macro-shaped builtin forms and are declaration-only, not runtime first-class values.

## Scoping Rules

- Every `{ }` block introduces a new scope.
- A variable declared inside a block is destroyed at the closing `}`.
- Inner scopes may shadow outer names.
- The `;`-scoped sub-expressions inside collection literals (`[let x = 0; x++; x, ...]`) also introduce short-lived scopes: each comma-separated item's preliminary statements are scoped to that item only.

---

## Declarations

## Module-level vs Local

Declarations that use the `def`-family macros (`def`, `defmacro`) are *static* — they exist at module scope, are resolved at compile time, and may also appear inside function bodies. `let` and `const` are *dynamic* — they exist inside local scopes.

## Declaration Normalization

Function-like declaration syntax is surface sugar over assignment semantics. The normalized internal shape is always an assignment of a closure-like value to a name.

```aura
name(args...) -> R { body }
// normalizes to
name = { args... -> body }

defmacro[static_args] m(node) -> T { body }
// normalizes to
m = <macro-closure value with static interface metadata>
```

This rule is semantic, not stylistic: parser/typechecker/compiler phases may use normalized assignment form as the canonical internal representation.

## `def` — Static Value and Type Declarations

`def` is the universal module-level declaration. It handles compile-time constant values, type aliases (named tuples, structs, unions, enums, interfaces), and destructuring assignments with full pattern support.

**Value binding:**

```aura
def pi = 3.14159
def version = "1.0.0"
def MaxRetries = 3
```

**Type alias** — the right-hand side is a type expression (tuple, struct, union, enum, or interface):

```aura
def Coord    = (Int, Int)
def Person   = (name: String, age: Int)
def Number   = union(Int, Float)
def[T, E] Result = enum(err: E, ok: T)
def ToStr    = interface(to_string: Func[(), String])
```

The optional generic type parameter list `[T, E]` immediately follows `def`.
Generic aliases preserve their static parameters as an alias scheme and instantiate when used with
type arguments, e.g. `Box[Int]` for `def[T] Box = (value: T)`.

A `def` with a type-alias right-hand side automatically generates:

- A constructor function with the same name: `Person(name = "Alice", age = 30)` (for structs) or `Person("Alice", 30)` (for tuples)
- Field accessors for struct and enum types.

**Destructuring binding** — a pattern may appear on the left-hand side:

```aura
def (x, y) = compute_coords()     // tuple destructuring
def (name, age) = some_person      // struct destructuring
def (name = some_name, age) = some_person // struct destructuring with rename
def .ok(value) = some_result       // fallible — panics if result is .err
```

Macro definition:

```aura
defmacro def(
    assignment: Assignment
) -> Stmt
```

## Function Declarations

`def` declares both static value bindings and named functions. A function declaration is distinguished by the presence of a parameter list after the name.

```aura
def add(a: Int, b: Int) -> Int {
    a + b
}
```

Function-form declarations are syntax sugar over assignment-form semantics:

```aura
add(a: Int, b: Int) -> Int { a + b }
// normalizes to
add = { a: Int, b: Int -> a + b }
```

The return type after `->` is optional when it can be inferred. The body is a block; its final expression is the return value (a `return` statement is also valid).

**Method declaration:** prefix the name with the receiver type and `.`:

```aura
def Point.distance_to(self, other: Point) -> Float {
    let dx = self.x - other.x;
    let dy = self.y - other.y;
    ((dx * dx) + (dy * dy)) : Float  // cast to Float before sqrt
}
```

`self` is the first parameter by convention; it is not a reserved keyword, but is implicitly the receiver value.

Macro definition:

```aura
defmacro def[T, U](
    name: Identifier,
    body: Expr[Func[T, U]]
) -> Stmt
```

## Macro Declarations

`defmacro` declares a compile-time macro. The macro receives *unevaluated* expressions (`Expr[T]`) and produces an `Expr` or `Stmt` node that is spliced into the AST at the call site.

Canonical declaration form:

```aura
defmacro[static_args] macro_name(ast_node) -> T { ... }
```

Grammar:

```
macro_decl      ::= "defmacro" static_params? identifier "(" param_list? ")" "->" type_expr block
static_params   ::= "[" static_param ("," static_param)* ","? "]"
static_param    ::= identifier | identifier ":" "static" type_expr
```

As with functions, function-like `defmacro` declaration syntax is assignment sugar:

```aura
defmacro[T, n: static Int] m(node: Expr[T]) -> Expr[T] { body }
// normalizes to assignment semantics using a macro-closure value bound to `m`
```

```aura
defmacro unless(
    condition: Expr[Bool],
    body:      Expr[Func[Void, Void]]
) -> Expr[Void] {
    if (!condition) body
}
```

`Expr[T]` is the quasi-quoted type of an expression whose result type is `T`. Parameters of type `Expr[T]` are not evaluated before the macro body runs; this is what enables inlining semantics.

Variadic macro parameters use `...name: List[T]`:

```aura
defmacro def(
    ...assignments: List[Assignment]
) -> Stmt
```

---
## Related Notes

- [[Language/Type System]]
- [[Subsystems/Frontend]]
- [[Subsystems/Typecheck]]
