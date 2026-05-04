---
title: "Literals And Data"
kind: language
tags:
  - aura
  - language
  - syntax
---

# Literals And Data

## Literals

## Integers

Decimal integer literals: sequences of digits with no prefix.

```aura
0    42    1_000_000
```

## Floats

Float literals require both an integer part and a fractional part separated by `.`.

```aura
3.14    0.5    1_000.0
```

## Booleans

```aura
true    false
```

## Null

```aura
null
```

`null` is not a valid value of an arbitrary type. It is only valid as a variant of an explicit `Option`-style enum or when constructing a `.null` dot-identifier value.

In fact, in the language prelude we have:

```aura
def null = .null;
```

## Strings

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

## Data Types

## Lists

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

## Arrays

The primitive types behind Lists, the use the `array` macro to create them and have fixed size.

```aura
array[1, 2, 3]                    // Array[Int, 3]
array[1, 2] : Array[Int, 2]        // explicit annotation / cast
```

## Dictionaries

Key-value maps, written with `[ ]` using `=` between key and value.

```aura
["a" = 1, "b" = 2]                 // Dict[String, Int]
let x = "a";
let y = "b";
[x = 1, y = 2]                   // Dict[String, Int], same as ["a" = 1, "b" = 2]
```

The key type must implement the `Hasheable` interface. The inline-scope trick applies to dict values as well.

## Sets

Homogeneous sets, written with the `set` macro.

```aura
set[1, 2, 3]                    // Set[Int]
set[1, 2] : Set[Int]        // explicit annotation / cast
```

The items type must implement the `Hasheable` interface. The inline-scope trick applies to set items as well.

## Tuples and Structs (Product Types)

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

## Sum Types — `enum` and `union`

Sum types are constructed as values using dot-identifiers and typed with `enum` or `union` type expressions.

`union` creates an anonymous tagged union:

```aura
let v: union(Int, Float) = 1;
```

`enum` creates a named-variant sum type:

```aura
let result: enum(err: String, ok: Int) = .ok(42);
let opt:    enum(null, some: Int)        = .null;
let err:    enum(err: (message: String, code: Int)) =
    .err(message = "oops", code = 500);
```

Inline-scope trick applies inside variant constructors:

```aura
.some(let x = compute(); x)
```

Named sum types are declared with `def` (see [Type Declarations](#type-declarations)).

## The `null` Value and Nullable Types

`null` is an alias to `.null`. It belongs to `enum(null, some: T)` (i.e. `Option[T]`) only. It is not a valid value of `Int`, `String`, etc.

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
## Related Notes

- [[Language/Type System]]
- [[Subsystems/Frontend]]
