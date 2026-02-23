# Aura Language Design

Aura is a functional programming language aimed at application development. This document is the authoritative specification for its syntax and semantics.

## Core Principles

1. **Small primitive set.** A minimal collection of orthogonal constructs — expressions, blocks, closures, calls, and declarations — from which all higher-level features are composed.
2. **Self-describing.** Almost every language construct can be defined *in terms of* Aura itself through the macro system, enabling bootstrapping and keeping the compiler core small.
3. **Familiar surface.** Derived constructs should look and feel like the built-in syntax of conventional languages even though they are macros under the hood.

---

## Lexical Rules

### Comments

Line comments begin with `//` and extend to the end of the line.

```aura
// This is a comment
let x = 1; // inline comment
```

Block comments are not supported.

### Identifiers

An identifier starts with a letter or `_`, followed by any number of letters, digits, or `_`. Identifiers may not be reserved keywords.

```
identifier ::= (letter | "_") (letter | digit | "_")*
```

**Reserved keywords:** `let`, `fn`, `type`, `macro`, `pub`, `use`, `return`, `break`, `continue`, `self`

The following are **not** reserved keywords — they lex as plain identifiers and are recognised contextually:
- Declaration starters: `def`, `defmacro`
- Built-in control forms: `if`, `cases`, `loop`, `while`, `do`, `then`, `else`
- Type-expression forms: `union`, `enum`, `interface`
- Other contextual names: `builtin`, `const`, `true`, `false`, `null`

### Dot-identifiers

A dot-identifier is a `.` followed immediately by a regular identifier, with no whitespace between them. It names a variant constructor or a branch label.

```
dot_identifier ::= "." identifier
```

```aura
.ok(value)
.null
.continue(state)
```

### Atoms

An *atom* is a lexical token of the form `'identifier` — a single-quote character immediately followed by a regular identifier, with no whitespace between them.

```
atom ::= "'" identifier
```

Atoms are used exclusively as **scope labels**. They are a distinct token class — not strings, not identifiers, and not part of any expression by themselves.

```aura
'outer
'search
'loop1
```

Atoms are not reserved as keywords; the same identifier may be used both as an ordinary name and as an atom label in different positions without conflict.

### Whitespace and Statement Termination

Whitespace (spaces, tabs, carriage returns, newlines) is insignificant *within* an expression, with one exception:

> **Implicit semicolon rule:** A newline that immediately follows a closing `}` is treated as a `;`, terminating the enclosing statement. This means continuation of a call with more trailing-lambda arguments must be written on the same line as the closing `}`.

Semicolons are required to terminate statements wherever an implicit one is not inserted. The language embraces explicit termination; `; we like semicolons`.

---

## Type System

### Type Expressions

Types are written in `PascalCase`. Generic type arguments use square brackets.

```
type_expr ::= identifier type_args?
           |  "(" type_expr ("," type_expr)* ")"
           |  "(" identifier ":" type_expr ("," identifier ":" type_expr)* ","? ")"
           |  "union" "(" type_expr ("," type_expr)* ","? ")"
           |  "enum"  "(" enum_variant ("," enum_variant)* ","? ")"
           |  "interface" "(" (identifier ":" type_expr ("," identifier ":" type_expr)* ","?)? ")"

enum_variant ::= identifier ":" type_expr   // variant with data: `ok: T`
              |  identifier                  // unit variant:      `null`

type_args  ::= "[" (type_expr | const_expr) ("," (type_expr | const_expr))* ","? "]"
```

Examples of built-in / standard types:

| Type expression | Meaning |
|---|---|
| `Int` | 64-bit signed integer |
| `Float` | 64-bit floating point |
| `Bool` | Boolean |
| `String` | UTF-8 string |
| `Void` | Unit / no value |
| `List[T]` | Homogeneous list |
| `Dict[K, V]` | Key-value dictionary |
| `Func[A, B]` | Function from `A` to `B` |
| `Option[T]` | `enum(some: T, null)` — nullable value |
| `Result[T, E]` | `enum(ok: T, error: E)` — fallible value |
| `Iterable[T]` | Any type that can be iterated |
| `any` | Shorthand for `interface()` — accepts any value |

### Tuples

Tuples are exact positional product types, identical to Rust tuples.

```aura
let coord: (Int, Int) = (5, 4);
coord.0 += 2;

let (x, y) = coord;  // destructuring

{                    // pattern matching
    (_, 0) -> ...,
    (0, _) -> ...,
    (x, y) ~ x < y -> ...,
    _ -> ...,
}(coord);
```

A named tuple alias is declared with `def`:

```aura
def Coord = (Int, Int)

let origin = Coord(0, 0);
let anon_dest = (4, 5);         // (Int, Int), not Coord
let dest: Coord = anon_dest;    // cast from anon→named is allowed

let Coord(x, y) = dest;         // constructor-pattern destructuring
let (x, y)      = dest;         // tuple-pattern destructuring
```

### Structs

Named-field product types. Casting between tuple and struct types is disallowed; casting between anonymous and named structs is allowed; casting between two distinct named structs is disallowed.

```aura
let person: (name: String, age: Int) = (name = "John", age = 20);
person.name = "John Doe";

let (name, age)            = person;          // bind all fields by name
let (name = some_name, age) = person;         // rename: field `name` → `some_name`
let (age = some_age)        = person;         // ignore `name`, rename `age`
```

Named struct alias via `def`:

```aura
def Person = (name: String, age: Int)

let john = Person(name = "John", age = 20);
let marie: Person = (name = "Marie", age = 21);

// Destructuring — the type prefix is optional but clarifies intent:
let Person(age = john_age) = john;   // ignore `name`, get `age` as `john_age`
let (age = marie_age)       = marie; // same without type prefix

// Pattern matching:
{
    (name = "Marie", age = marie_age) ~ marie_age > 18 -> ...,
    Person(name, 20) -> ...,
    Person(name, age) ~ age > 18 -> ...,
}(marie)
```

### Union Types

A `union` type is an anonymous tagged union. Repeated types are collapsed.

```aura
let n: union(Int, Float) = 5;

// Fallible destructuring (panics if n is not Int):
let n2: Int = n;

// Pattern matching:
{
    i: Int            -> ...,
    f: Float ~ f > 0.0 -> ...,
    _                  -> ...,
}(n)
```

Named union alias:

```aura
def Number = union(Int, Float)

let n: Number = 5;
let m: Number = 5.0;
```

Union types automatically support any method that is present on *all* member types (the intersection of their method sets). The dispatch happens at runtime.

### Enum Types

An `enum` is a named-variant sum type, identical to Rust enums but with anonymous support.

```aura
let res: enum(ok: Int, err: String) = .ok(5);

let .ok(val) = res;   // fallible destructuring — panics if res is .err

{
    .ok(val)  -> ...,
    .err(msg) -> ...,
}(res);
```

Named enum alias with generic parameters:

```aura
def[T, E] Result = enum(ok: T, err: E)

let success: Result[Int, String]   = Result.ok(5);
let failure: Result[Void, String]  = Result[Void, String].err("oops");
let from_anon: Result[Bool, String] = .ok(false);   // anon→named cast

let .ok(val)  = success;
let .err(msg) = failure;
```

### Interface Types

Interfaces specify structural contracts, similar to Go interfaces. Implementation is implicit — any type that provides the required methods satisfies the interface.

```aura
// Anonymous interface type:
def any_print(msg: interface(to_string: Func[(), String])) -> Void { ... }

// Named interface alias:
def ToStr = interface(to_string: Func[(), String])
```

The empty interface `interface()` is equivalent to the builtin `any` type and accepts any value.

Union types automatically implement the *intersection* of their member types' interfaces:

```aura
def Number = union(Int, Float)
// Both Int and Float implement to_string, so Number also implements ToStr.
```

Pattern matching on interface values works identically to union matching:

```aura
let x: ToStr = ...;
{
    i: Int  -> ...,
    c: Char -> ...,
    _       -> ...,
}(x)
```

### Type Annotations and Casts

`:` is overloaded for both annotation and cast, distinguished by position:

- In a declaration or parameter list, `: Type` *annotates* without runtime cost.
- In an expression, `expr : Type` is a *cast* (checked or unchecked depending on the types).

```aura
let x: Int = 42;           // annotation
let y = x : Float;         // cast
```

**Casting rules:**

| From → To | Allowed? |
|---|---|
| Anonymous tuple/struct → named | Yes |
| Named → anonymous tuple/struct | Yes |
| Named type A → named type B | **No** — compile error |
| Tuple → Struct | **No** — compile error |
| Struct → Tuple | **No** — compile error |
| Any type → `union(...)` / `interface()` containing it | Yes |
| `union(...)` / `interface()` → contained type | Yes, but may panic at runtime |

### Generics

Type parameters on declarations use square brackets after the `def` name.

```aura
def identity[T](x: T) -> T { x }
def[A, B] Pair = (first: A, second: B)
```

At call sites, type arguments are usually inferred and can be omitted.

### Fallible Patterns in Assignments

Any binding construct (`let`, `const`, `def`) may use a destructuring pattern on its left-hand side. Some patterns are *fallible* — they panic at runtime if the value does not match:

```aura
let .ok(value)    = result;   // panics if result is .err
let Coord(x, y)   = some_val; // panics if some_val is not a Coord
let (a, b)        = tuple_val;
let (name, age)   = struct_val;
```

---

## Literals

### Integers

Decimal integer literals: sequences of digits with no prefix.

```aura
0    42    1_000_000
```

### Floats

Float literals require both an integer part and a fractional part separated by `.`.

```aura
3.14    0.5    1_000.0
```

### Booleans

```aura
true    false
```

### Null

```aura
null
```

`null` is not a valid value of an arbitrary type. It is only valid as a variant of an explicit `Option`-style enum or when constructing a `.null` dot-identifier value.

### Strings

String literals are delimited by `"`. Escape sequences follow the standard conventions (`\n`, `\t`, `\\`, `\"`).

```aura
"Hello, world!"
"Line one\nLine two"
```

String interpolation embeds an expression with `$( )`:

```aura
"Hello, $(name)! You are $(age) years old."
```

The interpolated expression can be any Aura expression; its result is converted to a string via its `Display` representation.

Multi-line strings use standard string literals; literal newlines inside `"..."` are preserved.

---

## Variables and Bindings

### Local Assignment

`=` assigns a value to an *already declared* variable inside a local scope.

```aura
x = 1;
x = x + 1;
```

Attempting to assign to an undeclared name is a compile error.

### `let` — Mutable Local Binding

`let` declares one or more mutable local variables. Multiple bindings can be written in a single `let` separated by commas.

```aura
let x = 1;
let a = 1, b = 2, c = a + b;
```

`let` is a macro that expands to a mutable binding statement. Variables declared with `let` are scoped to the enclosing block.

Macro definition:

```aura
defmacro let(
    ...assignments: List[Assignment]
) -> Stmt
```

### `const` — Immutable Local Binding

`const` is identical to `let` except the binding cannot be reassigned after declaration. It is not a reserved keyword — it is an ordinary identifier recognised contextually as a declaration macro.

```aura
const pi = 3.14159;
```

Macro definition:

```aura
defmacro const(
    ...assignments: List[Assignment]
) -> Stmt
```

### Scoping Rules

- Every `{ }` block introduces a new scope.
- A variable declared inside a block is destroyed at the closing `}`.
- Inner scopes may shadow outer names.
- The `;`-scoped sub-expressions inside collection literals (`[let x = 0; x++; x, ...]`) also introduce short-lived scopes: each comma-separated item's preliminary statements are scoped to that item only.

---

## Data Types

### Lists

Ordered homogeneous sequences, written with `[ ]`.

```aura
[1, 2, 3]                         // List[Int]
["a", "b", "c"]                    // List[String]
[]                                  // List[Nothing] — empty list
```

A trailing comma is permitted.

Items may contain inline scoped statements before their value expression, separated by `;`. The declared names are local to that item:

```aura
[
    let x = 0; x = x + 1; x,      // x is destroyed after the comma
    let y = 10; y = y - 1; y,
    42,
]
```

### Dictionaries

Key-value maps, written with `[ ]` using `=` between key and value.

```aura
["a" = 1, "b" = 2]                 // Dict[String, Int]
[x = 10, y = 20]                   // Dict[String, Int] with identifier keys
```

The key type must be comparable. The inline-scope trick applies to dict values as well.

### Tuples and Structs (Product Types)

Anonymous product types are written with `( )`.

- A *tuple* has positional fields:
  ```aura
  (1, 2)                            // (Int, Int)
  ("hello", 42, true)               // (String, Int, Bool)
  ```

- A *struct* (named-field product) uses `name = value` syntax:
  ```aura
  (x = 1, y = 2)                    // (x: Int, y: Int)
  (name = "Alice", age = 30)
  ```

The inline-scope trick also applies inside `( )`.

### Sum Types — `enum` and `union`

Sum types are constructed as values using dot-identifiers and typed with `enum` or `union` type expressions.

`union` creates an anonymous tagged union:

```aura
let v: union(Int, Float) = 1 : union(Int, Float);
```

`enum` creates a named-variant sum type:

```aura
let result: enum(ok: Int, error: String) = .ok(42);
let opt:    enum(some: Int, null)        = .null;
```

Inline-scope trick applies inside variant constructors:

```aura
.some(let x = compute(); x)
```

Named sum types are declared with `def` (see [Type Declarations](#type-declarations)).

### The `null` Value and Nullable Types

`null` is a bare value literal. It belongs to `enum(some: T, null)` (i.e. `Option[T]`) only. It is not a valid value of `Int`, `String`, etc.

---

## Functions and Closures

Functions are first-class values. There are two closure syntaxes, both using `{ }`.

### Block-style Closure (single arm)

Parameters are listed before `->` inside the braces, with optional type annotations. The return type is inferred.

```aura
{ a: Int, b: Int -> a + b }         // Func[(Int, Int), Int]
{ x -> x * 2 }                      // Func[Int, Int] (inferred)
{ -> 42 }                           // Func[Void, Int]
```

The body is a block: zero or more statements followed by an optional final expression (the return value). If there is no final expression, the closure returns `Void`.

### Multi-arm Closure (pattern matching)

When multiple arms are needed, each arm is a comma-separated entry inside `{ }`. Each arm has a pattern list, an optional guard, and a body expression.

```aura
{
    0, b -> b,
    a, 0 -> a,
    a, b ~ a > b -> a * b,
    a, b           -> a / b
}
```

Pattern syntax per arm:

```
arm      ::= pattern ("," pattern)* guard? "->" expr
guard    ::= "~" expr
pattern  ::= literal
           | "_"
           | identifier
           | identifier ":" type_expr              // type-check pattern: `i: Int`
           | "(" struct_field ("," struct_field)* ","? ")"   // struct pattern
           | identifier "(" pattern ("," pattern)* ","? ")"  // constructor pattern
           | ".." identifier?                       // rest pattern: `..rest` or `..`
           | "." identifier ("(" pattern ")")?      // variant pattern: `.ok(x)` or `.null`
           | "(" pattern ("," pattern)* ","? ")"    // tuple pattern

struct_field ::= identifier "=" identifier          // field rename: `name = alias`
              |  identifier                         // plain field bind
```

- A literal pattern matches the exact value.
- An identifier pattern always matches and binds the value to that name.
- `_` matches and discards.
- A type-check pattern `name: Type` matches if the value is of the given type and binds it to `name`.
- A struct pattern `(field, name = alias)` destructures a struct by field name.
- A constructor pattern `TypeName(p1, p2)` destructures a named tuple or struct, optionally casting.
- A rest pattern `..rest` captures remaining elements into a list; bare `..` discards them.
- A variant pattern `.ok(inner)` matches a dot-identifier enum variant.
- A guard `~ expr` is evaluated only when all patterns match; the arm is taken only if the guard is also `true`.
- Arms are tried in order; the first matching arm is taken.

### External-parameter Closure (named parameters, no pattern matching)

When pattern matching is not needed, the parameter list may be written outside the braces. Return type annotation is optional.

```aura
(a: Int, b: Int) -> Int { a + b }
```

This form is useful when declaring named functions via `def` (see [Function Declarations](#function-declarations)).

### Closures and Captures

Closures capture variables from the enclosing scope by reference. A captured variable's lifetime is extended to at least the lifetime of the closure.

---

## Operators

### Operator Table

Operators are listed from **lowest** to **highest** precedence. All binary operators are left-associative unless noted.

| Precedence | Operator(s) | Description |
|---|---|---|
| 1 (lowest) | `=` | Assignment (right-associative) |
| 2 | `?:` | Elvis / null-coalescing |
| 3 | `\|\|` | Logical OR |
| 4 | `&&` | Logical AND |
| 5 | `==`  `!=` | Equality / Inequality |
| 6 | `<`  `>`  `<=`  `>=` | Comparison |
| 7 | `..` | Range |
| 8 | `+`  `-` | Addition / Subtraction |
| 9 | `*`  `/`  `%` | Multiplication / Division / Remainder |
| 10 | `:` | Cast / type annotation (postfix) |
| 11 | `++`  `--` | Post-increment / Post-decrement (postfix) |
| 12 | `!!` | Force-unwrap (postfix) |
| 13 | `?.` | Safe navigation (postfix) |
| 14 | `.` | Method call / field access (postfix) |
| 15 (highest) | `( )` `[ ]` | Function call / index access (postfix) |

### Special Operators

| Operator | Name | Description |
|---|---|---|
| `=` | Assignment | Assigns to a declared local variable. Also used for named arguments and key-value pairs in literals. |
| `:` | Annotation / Cast | In declarations: type annotation. In expressions: explicit cast. |
| `..` | Range | Creates an inclusive range from left to right operand. Also used in destructuring to ignore a span of elements. |
| `?.` | Safe navigation | Invokes a method on a nullable or fallible value. Propagates `null`/error without unwrapping. |
| `?:` | Elvis | Returns the left operand if it is non-null/non-error, otherwise the right operand. |
| `!!` | Force unwrap | Unwraps an `Option` or `Result`; panics at runtime if the value is `null` or an error. |
| `~` | Guard | Used inside multi-arm closures to attach a boolean condition to a pattern arm. |
| `_` | Wildcard | In patterns: discards a matched value. In calls: placeholder for a future argument (partial application). |
| `++` | Post-increment | Mutates a numeric variable in place; equivalent to `x = x + 1`. Returns the new value. |
| `--` | Post-decrement | Mutates a numeric variable in place; equivalent to `x = x - 1`. Returns the new value. |

### Range Operator `..`

```aura
1..10          // range from 1 to 10 inclusive
[a, b, ..rest] // destructuring: bind first two elements, collect remainder into rest
```

---

## Blocks

A block `{ ... }` is a sequence of statements optionally followed by a final expression. Its value is the final expression, or `Void` if there is none.

```aura
{
    let x = 1;
    let y = 2;
    x + y          // value of the block is 3
}
```

A block can stand alone as an expression:

```aura
let result = {
    let a = compute();
    a * 2
};
```

Blocks introduce a new scope. Variables declared inside are not visible outside.

### Labelled Blocks

A block may be prefixed with an atom label using `'atom: { ... }` syntax. The label attaches to the block itself, not to the surrounding call expression.

```
labelled_block ::= atom ":" block
```

```aura
'outer: {
    // this block is labelled 'outer
}
```

Labelled blocks are used as jump targets for `return`, `break`, and `continue` with explicit atom targets. A single function call may contain multiple labelled lambda arguments, each with its own label:

```aura
task 'worker: { doWork(); } finally 'cleanup: { releaseResources(); }
```

**Implicit label for `def` function bodies.** The body block of a `def` function declaration has an implicit atom equal to the function's name. Writing `return 'fnName value` inside the body is equivalent to `return value` — both target the enclosing function. This means no explicit label is ever needed on a `def` body block.

---

## Function Calls

### Positional Arguments

```aura
add(1, 2)
```

### Named Arguments

Arguments may be passed by name in any order, matching the parameter's internal name:

```aura
add(b = 2, a = 1)
```

### Labelled Parameters

A parameter may have a separate *internal* name (used inside the function body) and an *external label* (used at the call site). The syntax is `internal_name external_label: Type`.

```aura
def add(a first: Int, b second: Int) -> Int {
    a + b
}

add(first = 1, second = 2)
```

When calling, the external label is used, not the internal name.

### Trailing-Lambda Syntax

Closure arguments (`{ }`) may be placed *outside* the parentheses as trailing arguments. This is the mechanism that makes `if`, `loop`, and similar macros feel like built-in syntax.

**Only closures** can be trailing arguments. Lists, dicts, and other values must always be passed inside `( )`.

Rules:

1. **Parentheses are mandatory** for all non-closure arguments, even when there are none: `loop { }` is valid because `loop` takes no non-closure arguments. A call like `foo 42 { }` (passing a non-closure value outside parentheses) is a syntax error.
2. The trailing closure arguments must be the **last** parameters in the function signature.
3. The **first** trailing closure needs no label; subsequent ones require their external parameter label.
4. Continuation trailing closures must begin on the **same line** as the preceding `}` (due to the implicit-semicolon rule after `}`).

```aura
def do2(value: Int, this: Func[Int, Void], that: Func[Int, Void])

// All three forms are equivalent:
do2(1, this = { v -> print(v); }, that = { v -> print(v); })

do2(1) { v -> print(v); } that { v -> print(v); }
```

A single trailing closure with no label:

```aura
loop {
    print("forever");
}

loop do {
    print("forever");        // 'do' is the external label — optional when it's the only lambda
}
```

Multiple trailing closures, each on the same line as the previous `}`:

```aura
do_stuff(12, "hi", value = false) task { doWork(); } finally { cleanup(); }
```

---

## Control Flow

All control flow is implemented as macros. Their bodies are closures that are **inlined** into the call site — `return` inside an `if` branch returns from the enclosing function, not from the `if` itself.

### `if`

```aura
if (condition) {
    // then branch
}

if (condition) {
    // then branch
} else {
    // else branch
}
```

The `then` block is a `Func[Void, T]` trailing lambda. The optional `else` block is a second trailing lambda with the label `else`. Both blocks must have the same type `T`; the version without an `else` branch returns `Void`.

Macro definitions:

```aura
defmacro if(
    condition: Expr[Bool],
    then: Expr[Func[Void, Void]]
) -> Expr[Void]

defmacro if[T](
    condition: Expr[Bool],
    then:      Expr[Func[Void, T]],
    else else: Expr[Func[Void, T]]
) -> Expr[T]
```

`if` is an expression. It can appear anywhere an expression is valid:

```aura
let label = if (x > 0) { "positive" } else { "non-positive" };
```

The `then` label may be written explicitly on the trailing lambda when desired for clarity:

```aura
if (ok) then { doThing(); } else { doOther(); }
```

Multi-branch conditionals are handled by `cases` — see [`cases`](#cases).

### `cases`

`cases` is the multi-branch conditional. It takes no initial argument; instead, each arm is a guard-only pattern (`~ condition -> expr`) evaluated in order. The first arm whose condition is `true` is taken. This replaces the `else if` chain found in other languages.

```aura
cases {
    ~ x > 0  -> "positive",
    ~ x < 0  -> "negative",
    ~ true   -> "zero"
}
```

The final arm's condition is conventionally `~ true` to serve as the default (catch-all) case. Omitting a default is valid but results in a runtime error if no arm matches.

`cases` is an expression and returns the value of the taken arm. All arms must have the same type.

Macro definition:

```aura
defmacro cases[T](
    arms: Expr[Func[Void, T]]
) -> Expr[T]
```

The `arms` argument is a multi-arm closure where every arm has no patterns — only a guard. This is ordinary multi-arm closure syntax with the pattern list omitted:

```aura
// cases desugars to calling its closure argument with no input:
cases {
    ~ cond1 -> expr1,
    ~ cond2 -> expr2,
    ~ true  -> exprDefault
}

// is equivalent to:
{
    ~ cond1 -> expr1,
    ~ cond2 -> expr2,
    ~ true  -> exprDefault
}()
```

### `loop`

`loop` has exactly two forms.

**Indefinite loop** — repeats until a `break` exits it:

```aura
loop {
    print("forever");
}

loop do {
    print("forever");        // 'do' is the external label — optional for a single trailing lambda
}
```

**Conditional loop** — re-evaluates a condition closure before each iteration; continues while the condition returns `true`:

```aura
loop while { x > 0 } do {
    x--;
}
```

The `while` parameter is a `Func[Void, Bool]` — a zero-argument closure so that the condition is re-evaluated each iteration, not just once. The `while` token is the external parameter label, not a keyword.

Iteration over collections uses the `.each` method on `Iterable[T]`:

```aura
[1, 2, 3].each { item ->
    print(item);
}
```

Macro definitions:

```aura
defmacro loop(
    body do: Expr[Func[Void, Void]]
) -> Void

defmacro loop(
    condition while: Expr[Func[Void, Bool]],
    body      do:    Expr[Func[Void, Void]]
) -> Void
```

### `return`

Exits a labelled scope with a value. In the common case, `return` targets the enclosing `def` function body, whose implicit atom is the function's name.

```aura
return value
```

An explicit atom target can be given to exit an outer scope by name:

```aura
return 'label value
```

Because control-flow bodies are inlined, `return` inside an `if` branch or a `.each` closure exits the *enclosing function*, not the branch or closure itself.

```aura
def firstPositive(xs: List[Int]) -> Option[Int] {
    xs.each { x ->
        if (x > 0) {
            return .some(x);
        }
    }
    .null
}
```

Macro definitions:

```aura
defmacro return[T](
    value: Expr[T]
) -> Stmt

defmacro return[T](
    label: Atom,
    value: Expr[T]
) -> Stmt
```

### `break`

Exits a `loop`, producing its result value. `break` is syntactic sugar over `return .break(value)`.

```aura
break             // exit loop, no value (Void result)
break value       // exit loop with value
break 'label      // exit the loop labelled 'label, no value
break 'label value // exit the loop labelled 'label with value
```

`break` desugars as follows:

| Sugar | Desugars to |
|---|---|
| `break` | `return .break(())` |
| `break value` | `return .break(value)` |
| `break 'label` | `return 'label .break(())` |
| `break 'label value` | `return 'label .break(value)` |

The `'label` atom must refer to an enclosing `loop` body block. Using `break` outside a loop is a compile error.

### `continue`

Skips the remainder of the current loop iteration and begins the next one. `continue` is syntactic sugar over `return .continue()`.

```aura
continue          // next iteration of the innermost loop
continue 'label   // next iteration of the loop labelled 'label
```

`continue` desugars as follows:

| Sugar | Desugars to |
|---|---|
| `continue` | `return .continue(())` |
| `continue 'label` | `return 'label .continue(())` |

**Implicit continue.** A loop body block whose final expression evaluates to `Void` has an implicit `.continue()` appended by the compiler. This coercion only applies when the continue-carrier type `C` is `Void` (i.e. no state is being threaded through iterations). The practical effect is that most loop bodies do not need an explicit `continue`:

```aura
loop {
    print("tick");
    // implicit continue — no explicit 'continue' required
}
```

### Scope Resolution for Jumps

`return`, `break`, and `continue` each resolve their target scope using the following rules:

1. **Unlabelled jump** — targets the *nearest* enclosing scope of the appropriate kind:
   - `return` targets the nearest enclosing `def` function body.
   - `break` and `continue` target the nearest enclosing `loop` body.

2. **Labelled jump** (`return 'label`, `break 'label`, `continue 'label`) — walks outward through enclosing scopes and targets the first block whose atom matches `'label`. A compile error is raised if no matching label is found.

3. **Inlining.** The bodies of `loop`, `if`, `cases`, and `.each` (and any other macro whose body parameter is `Expr[Func[...]]`) are **inlined** at the call site by the compiler. No stack frame is created for the closure call. As a result, a `return` or `break` inside a control-flow body compiles to a direct jump instruction rather than a function return — the label resolution above is a compile-time operation. This is what gives these macros the semantics of built-in syntax without any runtime overhead.

---

## Declarations

### Module-level vs Local

Declarations that use the `def`-family macros (`def`, `defmacro`) are *static* — they exist at module scope, are resolved at compile time, and may also appear inside function bodies. `let` and `const` are *dynamic* — they exist inside local scopes.

### `def` — Static Value and Type Declarations

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
def[T, E] Result = enum(ok: T, err: E)
def ToStr    = interface(to_string: Func[(), String])
```

The optional generic type parameter list `[T, E]` immediately follows `def`.

A `def` with a type-alias right-hand side automatically generates:
- A constructor function with the same name: `Person(name = "Alice", age = 30)`.
- Field accessors for struct and enum types.

**Destructuring binding** — a pattern may appear on the left-hand side:

```aura
def (x, y) = compute_coords()     // tuple destructuring
def (name, age) = some_person      // struct destructuring
def .ok(value) = some_result       // fallible — panics if result is .err
```

Macro definition:

```aura
defmacro def(
    ...assignments: List[Assignment]
) -> Stmt
```

### Function Declarations

`def` declares both static value bindings and named functions. A function declaration is distinguished by the presence of a parameter list after the name.

```aura
def add(a: Int, b: Int) -> Int {
    a + b
}
```

The return type after `->` is optional when it can be inferred. The body is a block; its final expression is the return value (a `return` statement is also valid).

**Method declaration:** prefix the name with the receiver type and `.`:

```aura
def Point.distanceTo(self, other: Point) -> Float {
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

### Macro Declarations

`defmacro` declares a compile-time macro. The macro receives *unevaluated* expressions (`Expr[T]`) and produces an `Expr` or `Stmt` node that is spliced into the AST at the call site.

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

## String Templates

The `template` macro converts a string with `$( )` interpolation sites into a reusable template value. Unlike a plain interpolated string (which is eagerly evaluated), a template is evaluated lazily at render time.

```aura
let tpl = template "Hello, $(name)! You are $(age) years old."

tpl.render(name = "Alice", age = 30)
// => "Hello, Alice! You are 30 years old."
```

The fields passed to `.render` must match the interpolation identifiers in the template.

---

## Modules

*(Preliminary — full module system to be specified.)*

Each source file is a module. A module is a named collection of static declarations. Declarations are private by default; `pub` makes them visible to importing modules.

```aura
pub def greet(name: String) -> String {
    "Hello, $(name)!"
}
```

### `use` — Import Declaration

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

**Rename on import** — `exported_name = local_alias` (field = alias, matching struct-pattern syntax):

```aura
use (print = my_print, read) = "@stl/io";
my_print("hello");
```

Module paths:
- `@name/...` — library reference resolved via the library lookup path.
- `./...` or `../...` — relative path from the importing file's directory.

---

## Appendix: Built-in Macro Summary

| Macro | Kind | Purpose |
|---|---|---|
| `let` | Dynamic | Mutable local binding |
| `const` | Dynamic | Immutable local binding (contextual identifier, not a keyword) |
| `return` | Dynamic | Exit a scope (optionally with atom target) |
| `break` | Dynamic | Exit a `loop` with a result value; sugar over `return .break(value)` |
| `continue` | Dynamic | Begin next loop iteration; sugar over `return .continue()` |
| `if` | Control | Two-branch conditional expression (contextual identifier) |
| `cases` | Control | Multi-branch conditional expression (contextual identifier) |
| `loop` | Control | Indefinite or conditional loop (contextual identifier) |
| `def` | Static | Module-level constant, type alias, function, or destructuring binding |
| `defmacro` | Static | Compile-time macro |
| `enum` | Type | Named-variant sum type expression (contextual identifier) |
| `union` | Type | Anonymous union type expression (contextual identifier) |
| `interface` | Type | Structural contract (interface) type expression (contextual identifier) |
| `template` | Value | Lazy string template |
