---
title: "Functions And Closures"
kind: language
tags:
  - aura
  - language
  - syntax
---

# Functions And Closures

Functions are first-class values. There are two closure syntaxes, both using `{ }`.

## Block-style Closure (single arm)

Parameters are listed before `->` inside the braces, with optional type annotations. The return type is inferred.

```aura
{ a: Int, b: Int -> a + b }         // Func[(Int, Int), Int]
{ x -> x * 2 }                      // Func[Int, Int] (inferred)
{ -> 42 }                           // Func[Void, Int]
```

The body is a block: zero or more statements followed by an optional final expression (the return value). If there is no final expression, the closure returns `Void`.

## Multi-arm Closure (pattern matching)

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

struct_field ::= identifier "=" pattern             // field pattern: `field = binding`
              |  identifier                         // plain field bind
```

- A literal pattern matches the exact value.
- An identifier pattern always matches and binds the value to that name.
- `_` matches and discards.
- A type-check pattern `name: Type` matches if the value is of the given type and binds it to `name`.
- A struct pattern `(field = binding, name)` destructures a struct by field name.
- A constructor pattern `TypeName(p1, p2)` destructures a named tuple or struct, optionally casting.
- A rest pattern `..rest` captures remaining elements into a list; bare `..` discards them.
- A variant pattern `.ok(inner)` matches a dot-identifier enum variant.
- A variant pattern whose payload is a struct may use `.err(message = msg, code = status)`, which desugars to `.err((message = msg, code = status))`.
- A guard `~ expr` is evaluated only when all patterns match; the arm is taken only if the guard is also `true`.
- Arms are tried in order; the first matching arm is taken.

To match on a scrutinee, apply the closure (parentheses around the closure value are optional when the parser can see the call clearly):

```aura
{ 0 -> 1, n -> n * factorial(n - 1) }(n)
```

> Notice the pattern (part before the `->` and the guard `~ expr`) is the exact same AST node that is the left side of the `=` operator

## External-parameter Closure (named parameters, no pattern matching)

When pattern matching is not needed, the parameter list may be written outside the braces. Return type annotation is optional.

```aura
(a: Int, b: Int) -> Int { a + b }
```

This form is useful when declaring named functions via `def` (see [Function Declarations](#function-declarations)).

## Closures and Captures

Closures capture variables from the enclosing scope by reference. A captured variable's lifetime is extended to at least the lifetime of the closure.

---
## Related Notes

- [[Language/Calls Operators And Blocks]]
- [[Subsystems/Typecheck]]
