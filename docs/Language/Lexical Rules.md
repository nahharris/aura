---
title: "Lexical Rules"
kind: language
tags:
  - aura
  - language
  - syntax
---

# Lexical Rules

## Comments

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

## Identifiers

An identifier starts with a letter or `_`, followed by any number of letters, digits, or `_`. Identifiers may not be reserved keywords (thankfully, we don't have any at the moment).

```
identifier ::= (letter | "_") (letter | digit | "_")*
```

## Dot-identifiers

A dot-identifier is a `.` followed immediately by a regular identifier, with no whitespace between them. It names a variant constructor or a scope label.

```
dot_identifier ::= "." identifier
```

```aura
.ok(value)
.null
.continue(state)
```

## Brackets Meaning

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

## Semi-colons inside brackets

Semi-colons inside brackets are used to separate statements.

```aura
let array = [
    let x = 0; x = x + 1; x,
    let y = 10; y = y - 1; y,
    42,
]; // Produces [0, 9, 42] where x, and y are local to the array item and are destroyed after the comma
```

## Macro Application

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

## Function Calls

Function calls are written as `callable_expression [static_arguments] (runtime_arguments) label { ... } label { ... }`. Arguments can be positional or named (using `name = value` syntax), arguments whose value is a closure can be passed as trailing arguments.

```aura
println("Hello, world!"); // Function call with a string literal as a static argument
let x = 10.into[Float](); // Method call with a static argument to cast the Int to a Float
if (condition) then { ... } else { ... } // Function call with inline closures as trailing arguments
loop while { condition } do { ... } // Function call with two trailing runtime arguments and no positional arguments
```

## Whitespace and Statement Termination

Whitespace (spaces, tabs, carriage returns, newlines) is insignificant *within* an expression, with one exception:

> **Implicit semicolon rule:** A newline that immediately follows a closing `}` is treated as a `;`, terminating the enclosing statement. This means continuation of a call with more trailing-lambda arguments must be written on the same line as the closing `}`.

Semicolons are required to terminate statements wherever an implicit one is not inserted. The language embraces explicit termination; `; we like semicolons`.

---
## Related Notes

- [[Language/Syntax And Semantics]]
- [[Subsystems/Frontend]]
