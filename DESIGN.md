# Aura Language Design

Aura is a functional programming language aimed at application development. This document is the authoritative specification for its syntax and semantics.

## Core Principles

1. **Small primitive set.** A minimal collection of orthogonal constructs — expressions, blocks, closures, calls, and assignments — from which all higher-level features are composed.
2. **Self-describing.** Almost every language construct can be defined *in terms of* Aura itself through the macro system, enabling bootstrapping and keeping the compiler core small.
3. **Familiar surface.** Derived constructs should look and feel like the built-in syntax of conventional languages even though they are macros under the hood.
4. **No reserved words.** The lexer should not have a keyword list for structure. Surfaces must be macros (builtin or user-defined) and should stay as contextual identifiers (with the possibility of being auto/implicitly-imported as a prelude).

## Lexical Rules

### Comments

Line comments begin with `//` and extend to the end of the line.

```aura
// This is a comment
let x = 1; // inline comment
```

Block comments are supported via `/* */`.

```aura
/* 
This is a 
block comment 
*/
```

### Identifiers

An identifier starts with a letter or `_`, followed by any number of letters, digits, or `_`. Identifiers may not be reserved keywords (thankfully, we don't have any at the moment).

```
identifier ::= (letter | "_") (letter | digit | "_")*
```

### Dot-identifiers

A dot-identifier is a `.` followed immediately by a regular identifier, with no whitespace between them. It names a variant constructor or a scope label.

```
dot_identifier ::= "." identifier
```

```aura
.ok(value)
.null
.continue(state)
```

### Brackets Meaning

Brackets can have different meanings depending on the context.

- `( )` are used for data/runtime arguments
- `[ ]` are used for collections/indexing/static arguments
- `{ }` are used for closures/functions

For instance, in the following code:

```aura
let pair: (Int, Int) = (1, 2); // A product type and a product literal
let array = [1, 2, 3]; // A collection literal
let closure: Func[Int, Int] = { x -> x + 1 }; // A closure literal

def foo(x: Int) -> Int { x + 1 }; // A function literal
def bar(x: Int) -> Int { x ~ x > 0 -> x + 1, x ~ x < 0 -> x - 1 }; // A multi-arm function literal with guards
```

#### Semi-colons inside brackets

Semi-colons inside brackets are used to separate statements.

```aura
let array = [
    let x = 0; x = x + 1; x,
    let y = 10; y = y - 1; y,
    42,
]; // Produces [0, 9, 42] where x, and y are local to the array item and are destroyed after the comma
```

### Macro Application

Macro application is written as `macro_name[args] node` and always consumes exactly one AST-node operand.

Grammar:

```
macro_apply_expr ::= macro_head macro_operand
macro_head       ::= identifier static_args?
macro_operand    ::= atom_expr | macro_apply_expr
```

This grammar makes chaining right-associative:

```aura
a b node   // parses as: a (b node)
```

`static_args` accept both type expressions and compile-time-known values (see [Generic parameter constraints](#generic-parameter-constraints)).

```aura
def name = "Aura";
def[T, U] Pair = (T, U);
macro_name node;
macro_name[T, 4] node;
```

### Function Calls

Function calls are written as `callable_expression [static_arguments] (runtime_arguments) label { ... } label { ... }`. Arguments can be positional or named (using `name = value` syntax), arguments whose value is a closure can be passed as trailing arguments.

```aura
println("Hello, world!"); // Function call with a string literal as a static argument
let x = 10.into[Float](); // Method call with a static argument to cast the Int to a Float
if (condition) then { ... } else { ... } // Function call with inline closures as trailing arguments
loop while { condition } do { ... } // Function call with two trailing runtime arguments and no positional arguments
```

### Whitespace and Statement Termination

Whitespace (spaces, tabs, carriage returns, newlines) is insignificant *within* an expression, with one exception:

> **Implicit semicolon rule:** A newline that immediately follows a closing `}` is treated as a `;`, terminating the enclosing statement. This means continuation of a call with more trailing-lambda arguments must be written on the same line as the closing `}`.

Semicolons are required to terminate statements wherever an implicit one is not inserted. The language embraces explicit termination; `; we like semicolons`.

---

## Type System

Aura is a statically type-safe language. Every expression has a type, and types must be known at compile time. Still we provide powerful abstractions to leverage flexibility

### Type Expressions

Types are written in `PascalCase`. Generic static arguments use square brackets.

```
type_expr ::= "static" type_expr
           |  identifier type_args?
           |  "(" type_expr ("," type_expr)* ")"
           |  "(" struct_field_ty ("," struct_field_ty)* ","? ")"

type_args  ::= "[" (type_expr | static_expr) ("," (type_expr | static_expr))* ","? "]"

struct_field_ty ::= identifier (":" type_expr)    // normal field
                 |  identifier                 // sugar for `identifier : Void` (starts with lowercase; same rules as tuple vs struct disambiguation)
```

There are 3 major macros that operate on type expressions: `union`, `enum`, and `interface`.

```aura
def Number = union(Int, Float); // Macro `union` applied on a type expression
def[T, E] Result = enum(ok: T, err: E); // Macro `enum` applied on a type expression with arguments
def ToStr = interface(to_string: Func[(), String]); // Macro `interface` applied on a type expression with a field
```

The macro `implements` can be used on a type definition to ensure that the type implements the methods required by the interface (since interfaces are implicitely implemented by all types that have all the methods required by the interface).

```aura
implements[ToStr] def Person = (name: String, age: Int); // Macro `implements` applied on a type definition to ensure that the type implements the methods required by the interface

def Person.to_string(self) -> String {
    return "$(self.name) is $(self.age) years old";
}
```

### Generic parameter constraints

On `def` and `defmacro` declarations, static parameters may carry interface-like constraints:

- `def[T: Show] ...` — single bound
- `def[T: (Show, Eq)] ...` — multiple bounds as a parenthesised list
- `def[n: static Int] ...` — compile-time constant value as a bound

`static` is a reusable compile-time constraint interface, not feature-specific syntax. A value satisfies `static T` iff it is known at compile time under one shared rule:

1. Literal values of type `T` satisfy `static T`.
2. Bindings proven compile-time-known by the frontend's static-evaluation pass also satisfy `static T`.

The same rule is used for declaration bounds and macro static argument validation.

`static` is a regular type-expression constructor, so it is valid anywhere a type expression is valid, for example `n: static Int`, `-> static Expr[T]`, and `Expr[static Int]`.

`Func` parameter lists preserve names and labels when written as a struct-like shape:

```aura
Func[(cond: Bool, then: Func[(), T], else: Func[(), T]), T]
```

This representation is used by builtin stubs so labeled trailing closure forms can be typed without making those labels part of the runtime calling convention.

Examples of built-in / standard types:

| Type expression | Meaning |
|---|---|
| `Int` | 64-bit signed integer |
| `Float` | 64-bit floating point |
| `Bool` | Boolean |
| `String` | UTF-8 string |
| `Void` | Unit / no value other than `()` |
| `List[T]` | Homogeneous list |
| `Array[T, n: static Int]` | Fixed-size homogeneous array (`n` is a compile-time integer) |
| `Dict[K, V]` | Key-value dictionary (maps are always spelled `Dict`, not `Map`) |
| `Set[T]` | Homogeneous set |
| `Func[A, B]` | Function from `A` (can be a tuple/struct parameter shape) to `B` |
| `Macro[A, B]` | Declaration-only macro signature used by `defstub` for builtin forms |
| `Option[T]` | `enum(null, some: T)` — nullable value |
| `Result[T, E]` | `enum(err: E, ok: T)` — fallible value |
| `Iterable[T]` | Any type that can be iterated |
| `Any` | Shorthand for `interface()` — accepts any value |
| `Never` | Bottom type — `Never` is assignable to every other type |

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

The empty interface `interface()` is equivalent to the builtin `Any` type and accepts any value. On the other hand, the `Never` type would be equivalent to an interface with all the imaginable methods, making it impossible to satisfy, yet castable to any other type.

Union types automatically implement the *intersection* of their member types' interfaces:

```aura
implements[ToStr] def Number = union(Int, Float)
// Both Int and Float implement to_string, so Number also implements ToStr out of the box.
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

Interfaces can define default methods that are auto-implemented for all types that implement the interface.

```aura
def From[T] = interface(from: Func[(other: T), Self]);

def[T, U: From[T]] T.into(self) -> U {
    return U.from(self);
}

def Int.from(other: Float) -> Int { ... }
// Float.into(self) -> Int is auto-implemented
```

### Type Annotations and Casts

`:` is overloaded for both annotation and cast (via the `from` method of the `From[T]` interface), distinguished by position:

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
def[T] identity(x: T) -> T { x }
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

In fact, in the language prelude we have:

```aura
def null = .null;
```

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

The interpolated expression can be any Aura expression; its result is converted to a string via its `ToStr` representation.

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
    assignment: Assignment
) -> Stmt
```

### `def` — Immutable Binding

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

### `defstub` — Static Extern Contract

`defstub` is a top-level static declaration that introduces a typed global symbol without an Aura body. It is used for runtime externs and compiler-lowered builtin forms.

```aura
defstub syscall_exit: Func[(code: Int), Never];
defstub[T] if: Func[(cond: Bool, then: Func[(), T], else: Func[(), T]), T];
defstub[T] return: Macro[T, Never];
```

Same-name overloads are allowed for `defstub` declarations only. `Func[...]` stubs describe callable extern contracts; `Macro[...]` stubs describe macro-shaped builtin forms and are declaration-only, not runtime first-class values.

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

### Arrays

The primitive types behind Lists, the use the `array` macro to create them and have fixed size.

```aura
array[1, 2, 3]                    // Array[Int, 3]
array[1, 2] : Array[Int, 2]        // explicit annotation / cast
```

### Dictionaries

Key-value maps, written with `[ ]` using `=` between key and value.

```aura
["a" = 1, "b" = 2]                 // Dict[String, Int]
let x = "a";
let y = "b";
[x = 1, y = 2]                   // Dict[String, Int], same as ["a" = 1, "b" = 2]
```

The key type must implement the `Hasheable` interface. The inline-scope trick applies to dict values as well.

### Sets

Homogeneous sets, written with the `set` macro.

```aura
set[1, 2, 3]                    // Set[Int]
set[1, 2] : Set[Int]        // explicit annotation / cast
```

The items type must implement the `Hasheable` interface. The inline-scope trick applies to set items as well.

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

In a **struct type**, a field may be written as a bare identifier when it carries no payload — this is **syntax sugar** for `field: Void` (the type is still explicit after desugaring):

```aura
(age: Int, name: String, author: Bool)
(age: Int, name: String, author)      // `author` means `author: Void`
```

The inline-scope trick also applies inside `( )`.

> `(T)` (single-item tuple) is equivalent to `T` in any context

### Sum Types — `enum` and `union`

Sum types are constructed as values using dot-identifiers and typed with `enum` or `union` type expressions.

`union` creates an anonymous tagged union:

```aura
let v: union(Int, Float) = 1;
```

`enum` creates a named-variant sum type:

```aura
let result: enum(err: String, ok: Int) = .ok(42);
let opt:    enum(null, some: Int)        = .null;
```

Inline-scope trick applies inside variant constructors:

```aura
.some(let x = compute(); x)
```

Named sum types are declared with `def` (see [Type Declarations](#type-declarations)).

### The `null` Value and Nullable Types

`null` is an alias to `.null`. It belongs to `enum(null, some: T)` (i.e. `Option[T]`) only. It is not a valid value of `Int`, `String`, etc.

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

struct_field ::= identifier "=" identifier          // field rename: `alias = field`
              |  identifier                         // plain field bind
```

- A literal pattern matches the exact value.
- An identifier pattern always matches and binds the value to that name.
- `_` matches and discards.
- A type-check pattern `name: Type` matches if the value is of the given type and binds it to `name`.
- A struct pattern `(alias = field, name)` destructures a struct by field name.
- A constructor pattern `TypeName(p1, p2)` destructures a named tuple or struct, optionally casting.
- A rest pattern `..rest` captures remaining elements into a list; bare `..` discards them.
- A variant pattern `.ok(inner)` matches a dot-identifier enum variant.
- A guard `~ expr` is evaluated only when all patterns match; the arm is taken only if the guard is also `true`.
- Arms are tried in order; the first matching arm is taken.

To match on a scrutinee, apply the closure (parentheses around the closure value are optional when the parser can see the call clearly):

```aura
{ 0 -> 1, n -> n * factorial(n - 1) }(n)
```

> Notice the pattern (part before the `->` and the guard `~ expr`) is the exact same AST node that is the left side of the `=` operator

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

A block may be prefixed with an atom label using `label[.label_name] { ... }` syntax. The label attaches to the block itself, not to the surrounding call expression.

```
labelled_block ::= dot_identifier ":" block
```

```aura
.outer: {
    // this block is labelled 'outer
}
```

Labelled blocks are used as jump targets for `return`, `break`, and `continue` with explicit atom targets. A single function call may contain multiple labelled lambda arguments, each with its own label:

```aura
task do .worker: { doWork(); } finally .cleanup: { releaseResources(); }
```

**Implicit label for `def` function bodies.** The body block of a `def` function declaration has an implicit atom equal to the function's name. Writing `return[.fn_name] value` inside the body is equivalent to `return value` — both target the enclosing function. This means no explicit label is ever needed on a `def` body block.

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

### Trailing-Lambda Syntax

Closure arguments (`{ }`) may be placed *outside* the parentheses as trailing arguments.

**Only closures** can be trailing arguments. Lists, dicts, and other values must always be passed inside `( )`.

Rules:

1. **Parentheses are mandatory** for all non-closure arguments, even when there are none: `loop do { }` is valid because `loop` takes no non-closure arguments. A call like `foo 42 { }` (passing a non-closure value outside parentheses) is a syntax error.
2. The trailing closure arguments must be the **last** parameters in the function signature.
3. All trailing closures must be labeled by their external parameter name.
4. Continuation trailing closures must begin on the **same line** as the preceding `}` (due to the implicit-semicolon rule after `}`).

```aura
def do2(value: Int, this: Func[Int, Void], that: Func[Int, Void])

// Equivalent forms:
do2(1, this = { v -> print(v); }, that = { v -> print(v); })

do2(1) this { v -> print(v); } that { v -> print(v); }
```

A single trailing closure still uses its label:

```aura
loop do {
    print("forever");
}
```

Multiple trailing closures, each on the same line as the previous `}`:

```aura
do_stuff(12, "hi", value = false) task { 
    doWork(); 
} finally { 
    cleanup(); 
}
```

---

## Control Flow

`if` and `cases` are inline functions. Their bodies are closures that are **inlined** into the call site — `return` inside an `if` branch returns from the enclosing function, not from the `if` itself.

### `if`

```aura
if (condition) then {
    // then branch
}

if (condition) then {
    // then branch
} else {
    // else branch
}
```

The `then` block is a `Func[Void, T]` trailing lambda. The `else` block is a second trailing lambda with the label `else`. Both blocks must have the same type `T`; the version without an `else` branch returns `Void`.

`if` is compiler-lowered control flow with a `defstub` typing surface:

```aura
defstub if: Func[(cond: Bool, then: Func[(), Void]), Void];
defstub[T] if: Func[(cond: Bool, then: Func[(), T], else: Func[(), T]), T];
```

`if` is an expression. It can appear anywhere an expression is valid:

```aura
let label = if (x > 0) then { "positive" } else { "non-positive" };
```

The `then` label may be written explicitly on the trailing lambda when desired for clarity:

```aura
if (ok) then { doThing(); } else { doOther(); }
```

Multi-branch conditionals are handled by `cases` — see [`cases`](#cases).

### `cases`

`cases` is the multi-branch conditional. It takes no initial argument; instead, each arm is a guard-only pattern (`~ condition -> expr`) evaluated in order. The first arm whose condition is `true` is taken. This replaces the `else if` chain found in other languages.

```aura
cases when {
    ~ x > 0  -> "positive",
    ~ x < 0  -> "negative",
    ~ true   -> "zero"
}
```

The final arm's condition is conventionally `~ true` to serve as the default (catch-all) case. Omitting a default is valid but results in a runtime error if no arm matches.

`cases` is an expression and returns the value of the taken arm. All arms must have the same type.

`cases` is compiler-lowered control flow with a `defstub` typing surface:

```aura
defstub[T] cases: Func[(when: Func[(), T]), T];
```

The `arms` argument is a multi-arm closure where every arm has no patterns — only a guard. This is ordinary multi-arm closure syntax with the pattern list omitted:

```aura
// cases desugars to calling its closure argument with no input:
cases when {
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
loop do {
    print("forever");
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

Stub definitions:

```aura
defstub loop: Func[(do: Func[(), Void]), Never];
defstub loop: Func[(while: Func[(), Bool], do: Func[(), Void]), Never];
```
****
### `return`

Exits a labelled scope with a value. In the common case, `return` targets the enclosing `def` function body, whose implicit atom is the function's name.

```aura
return value
```

An explicit atom target can be given to exit an outer scope by name:

```aura
return[.label_name] value
``` 

Because control-flow bodies are inlined, `return` inside an `if` branch or a `.each` closure exits the *enclosing function*, not the branch or closure itself.

```aura
def first_positive(xs: List[Int]) -> Option[Int] {
    xs.each { x ->
        if (x > 0) then {
            return .some(x);
        }
    }
    .null
}
```

Stub definitions:

```aura
defstub[T] return: Macro[T, Never];
```

### `break`

Exits a `loop`, producing its result value. `break` is syntactic sugar over `return .break(value)`.

```aura
break             // exit loop, no value (Void result)
break value       // exit loop with value
break[.label_name]      // exit the loop labelled 'label, no value
break[.label_name] value // exit the loop labelled 'label with value
```

`break` desugars as follows:

| Sugar | Desugars to |
|---|---|
| `break` | `return .break(())` |
| `break value` | `return .break(value)` |
| `break[.label_name]` | `return[.label_name] .break(())` |
| `break[.label_name] value` | `return[.label_name] .break(value)` |

The `label_name` dot-identifier must refer to an enclosing `loop` body block. Using `break` outside a loop is a compile error.

### `continue`

Skips the remainder of the current loop iteration and begins the next one. `continue` is syntactic sugar over `return .continue()`.

```aura
continue          // next iteration of the innermost loop
continue[.label_name]   // next iteration of the loop labelled 'label
```

`continue` desugars as follows:

| Sugar | Desugars to |
|---|---|
| `continue` | `return .continue(())` |
| `continue[.label_name]` | `return[.label_name] .continue(())` |

Since the `do` closure return type is `union(Void, Control[B, C])`, if no continue exists, the function returns `()` which (under the hood) is the same as `return .continue(())`

```aura
loop do {
    print("tick");
    // implicit continue — no explicit 'continue' required
}
```

### Scope Resolution for Jumps

`return`, `break`, and `continue` each resolve their target scope using the following rules:

1. **Unlabelled jump** — targets the *nearest* enclosing scope of the appropriate kind:
   - `return` targets the nearest enclosing `def` function body.
   - `break` and `continue` target the nearest enclosing `loop` body.

2. **Labelled jump** (`return[.label_name]`, `break[.label_name]`, `continue[.label_name]`) — walks outward through enclosing scopes and targets the first block whose atom matches `'label`. A compile error is raised if no matching label is found.

3. **Inlining.** The bodies of `loop`, `if`, `cases`, and `.each` (and any other macro whose body parameter is `Expr[Func[...]]`) are **inlined** at the call site by the compiler. No stack frame is created for the closure call. As a result, a `return` or `break` inside a control-flow body compiles to a direct jump instruction rather than a function return — the label resolution above is a compile-time operation. This is what gives these macros the semantics of built-in syntax without any runtime overhead.

The jump forms also have declaration-only macro stubs:

```aura
defstub break: Macro[(), Never];
defstub[T] break: Macro[T, Never];
defstub continue: Macro[(), Never];
```

---

## Declarations

### Module-level vs Local

Declarations that use the `def`-family macros (`def`, `defmacro`) are *static* — they exist at module scope, are resolved at compile time, and may also appear inside function bodies. `let` and `const` are *dynamic* — they exist inside local scopes.

### Declaration Normalization

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
def[T, E] Result = enum(err: E, ok: T)
def ToStr    = interface(to_string: Func[(), String])
```

The optional generic type parameter list `[T, E]` immediately follows `def`.

A `def` with a type-alias right-hand side automatically generates:

- A constructor function with the same name: `Person(name = "Alice", age = 30)` (for structs) or `Person("Alice", 30)` (for tuples)
- Field accessors for struct and enum types.

**Destructuring binding** — a pattern may appear on the left-hand side:

```aura
def (x, y) = compute_coords()     // tuple destructuring
def (name, age) = some_person      // struct destructuring
def (some_name = name, age) = some_person // struct destructuring with rename
def .ok(value) = some_result       // fallible — panics if result is .err
```

Macro definition:

```aura
defmacro def(
    assignment: Assignment
) -> Stmt
```

### Function Declarations

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

### Macro Declarations

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

## String Templates

The `template` macro converts a string with `$( )` interpolation sites into a reusable template value. Unlike a plain interpolated string (which is eagerly evaluated), a template is evaluated lazily at render time.

**Implementation status:** the reference parser does not yet treat `template` as a dedicated form; treat this section as the target surface (call as a macro once `template` exists in the prelude or STL).

```aura
let tpl = template "Hello, $(name)! You are $(age) years old."

tpl.render(name = "Alice", age = 30)
// => "Hello, Alice! You are 30 years old."
```

The fields passed to `.render` must match the interpolation identifiers in the template.

---

## Modules

Each source file is a module. A module is a named collection of static declarations. In v1, all top-level declarations are exported.

```aura
def greet(name: String) -> String {
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

**Rename on import** — `local_alias = exported_name` (alias = field, matching struct-pattern syntax):

```aura
use (my_print = print, read) = "@stl/io";
my_print("hello");
```

Module paths:

- `@name/...` — library reference resolved via the library lookup path.
- `./...` or `../...` — relative path from the importing file's directory.

Import resolution rules (current runtime):

- Modules are loaded lazily at `use` sites.
- Re-importing the same module path reuses a cached module value (single evaluation semantics).
- Cyclic imports are runtime errors with an import-chain diagnostic.

### Runtime extern stubs

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

`Bytes.get` and `Bytes.set` are intentionally unchecked for now. Out-of-bounds access is undefined
behavior until panic handlers exist.

`String` remains the public string-literal type; converting it to a writeable buffer requires
`String.into()`, which copies the UTF-8 bytes into a fresh owned `Bytes` value.

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
