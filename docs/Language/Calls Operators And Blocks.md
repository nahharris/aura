---
title: "Calls Operators And Blocks"
kind: language
tags:
  - aura
  - language
  - syntax
---

# Calls Operators And Blocks

## Operators

## Operator Table

Operators are listed from **lowest** to **highest** precedence. All binary operators are left-associative unless noted.


| Precedence   | Operator(s)       | Description                               |
| ------------ | ----------------- | ----------------------------------------- |
| 1 (lowest)   | `=`               | Assignment (right-associative)            |
| 2            | `?:`              | Elvis / null-coalescing                   |
| 3            | &#124;&#124;      | Logical OR                                |
| 4            | `&&`              | Logical AND                               |
| 5            | `==` `!=`         | Equality / Inequality                     |
| 6            | `<` `>` `<=` `>=` | Comparison                                |
| 7            | `..`              | Range                                     |
| 8            | `+` `-`           | Addition / Subtraction                    |
| 9            | `*` `/` `%`       | Multiplication / Division / Remainder     |
| 10           | `:`               | Cast / type annotation (postfix)          |
| 11           | `++` `--`         | Post-increment / Post-decrement (postfix) |
| 12           | `!!`              | Force-unwrap (postfix)                    |
| 13           | `?.`              | Safe navigation (postfix)                 |
| 14           | `.`               | Method call / field access (postfix)      |
| 15 (highest) | `( )` `[ ]`       | Function call / index access (postfix)    |


## Special Operators


| Operator | Name              | Description                                                                                                     |
| -------- | ----------------- | --------------------------------------------------------------------------------------------------------------- |
| `=`      | Assignment        | Assigns to a declared local variable. Also used for named arguments and key-value pairs in literals.            |
| `:`      | Annotation / Cast | In declarations: type annotation. In expressions: explicit cast.                                                |
| `..`     | Range             | Creates an inclusive range from left to right operand. Also used in destructuring to ignore a span of elements. |
| `?.`     | Safe navigation   | Invokes a method on a nullable or fallible value. Propagates `null`/error without unwrapping.                   |
| `?:`     | Elvis             | Returns the left operand if it is non-null/non-error, otherwise the right operand.                              |
| `!!`     | Force unwrap      | Unwraps an `Option` or `Result`; panics at runtime if the value is `null` or an error.                          |
| `~`      | Guard             | Used inside multi-arm closures to attach a boolean condition to a pattern arm.                                  |
| `_`      | Wildcard          | In patterns: discards a matched value. In calls: placeholder for a future argument (partial application).       |
| `++`     | Post-increment    | Mutates a numeric variable in place; equivalent to `x = x + 1`. Returns the new value.                          |
| `--`     | Post-decrement    | Mutates a numeric variable in place; equivalent to `x = x - 1`. Returns the new value.                          |


## Range Operator `..`

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

## Labelled Blocks

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

## Positional Arguments

```aura
add(1, 2)
```

## Named Arguments

Arguments may be passed by name in any order, matching the parameter's internal name:

```aura
add(b = 2, a = 1)
```

## Trailing-Lambda Syntax

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
## Related Notes

- [[Language/Functions And Closures]]
- [[Subsystems/Frontend]]
