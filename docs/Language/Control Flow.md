---
title: "Control Flow"
kind: language
tags:
  - aura
  - language
  - syntax
---

# Control Flow

`if` and `cases` are inline functions. Their bodies are closures that are **inlined** into the call site — `return` inside an `if` branch returns from the enclosing function, not from the `if` itself.

## `if`

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

Multi-branch conditionals are handled by `cases` — see [cases](#cases).

## `cases`

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

## `loop`

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

---

## `return`

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

## `break`

Exits a `loop`, producing its result value. `break` is syntactic sugar over `return .break(value)`.

```aura
break             // exit loop, no value (Void result)
break value       // exit loop with value
break[.label_name]      // exit the loop labelled 'label, no value
break[.label_name] value // exit the loop labelled 'label with value
```

`break` desugars as follows:


| Sugar                      | Desugars to                         |
| -------------------------- | ----------------------------------- |
| `break`                    | `return .break(())`                 |
| `break value`              | `return .break(value)`              |
| `break[.label_name]`       | `return[.label_name] .break(())`    |
| `break[.label_name] value` | `return[.label_name] .break(value)` |


The `label_name` dot-identifier must refer to an enclosing `loop` body block. Using `break` outside a loop is a compile error.

## `continue`

Skips the remainder of the current loop iteration and begins the next one. `continue` is syntactic sugar over `return .continue()`.

```aura
continue          // next iteration of the innermost loop
continue[.label_name]   // next iteration of the loop labelled 'label
```

`continue` desugars as follows:


| Sugar                   | Desugars to                         |
| ----------------------- | ----------------------------------- |
| `continue`              | `return .continue(())`              |
| `continue[.label_name]` | `return[.label_name] .continue(())` |


Since the `do` closure return type is `union(Void, Control[B, C])`, if no continue exists, the function returns `()` which (under the hood) is the same as `return .continue(())`

```aura
loop do {
    print("tick");
    // implicit continue — no explicit 'continue' required
}
```

## Scope Resolution for Jumps

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
## Related Notes

- [[Contracts/Typecheck IR]]
- [[Subsystems/Typecheck]]
- [[Subsystems/Codegen]]
