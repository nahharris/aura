---
title: "Type System"
kind: language
tags:
  - aura
  - language
  - typecheck
---

# Type System

Aura is a statically type-safe language. Every expression has a type, and types must be known at compile time. Still we provide powerful abstractions to leverage flexibility

## Type Expressions

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

## Generic parameter constraints

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

| Type expression           | Meaning                                                              |
| ------------------------- | -------------------------------------------------------------------- |
| `Int`                     | 64-bit signed integer                                                |
| `Float`                   | 64-bit floating point                                                |
| `Bool`                    | Boolean                                                              |
| `String`                  | UTF-8 string                                                         |
| `Void`                    | Unit / no value other than `()`                                      |
| `List[T]`                 | Homogeneous list                                                     |
| `Array[T, n: static Int]` | Fixed-size homogeneous array (`n` is a compile-time integer)         |
| `Dict[K, V]`              | Key-value dictionary (maps are always spelled `Dict`, not `Map`)     |
| `Set[T]`                  | Homogeneous set                                                      |
| `Func[A, B]`              | Function from `A` (can be a tuple/struct parameter shape) to `B`     |
| `Macro[A, B]`             | Declaration-only macro signature used by `defstub` for builtin forms |
| `Option[T]`               | `enum(null, some: T)` — nullable value                               |
| `Result[T, E]`            | `enum(err: E, ok: T)` — fallible value                               |
| `Iterable[T]`             | Any type that can be iterated                                        |
| `Any`                     | Defined in `aura-stl` as `def Any = interface();` — the empty interface; accepts any value. The compiler also pre-registers this name like `Int`/`Float` so single-file programs resolve `Any` without importing the stdlib. |
| `Never`                   | Bottom type — `Never` is assignable to every other type              |

## Tuples

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

## Structs

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

## Union Types

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

## Enum Types

An `enum` is a named-variant sum type, identical to Rust enums but with anonymous support.

```aura
let res: enum(ok: Int, err: String) = .ok(5);
let http: enum(err: (message: String, code: Int)) = .err(message = "oops", code = 500);

let .ok(val) = res;   // fallible destructuring — panics if res is .err
let .err(message = msg, code = status) = http;

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

When a variant's single payload type is a struct, the constructor and pattern may elide the extra struct wrapper:

```aura
def HttpError = enum(err: (message: String, code: Int))

let e = .err(message = "oops", code = 500);
let same = .err((message = "oops", code = 500)); // explicit wrapped form
let content = (message = "oops", code = 500);
let also_same = .err(content);                    // explicit payload value

let .err(message = msg, code = status) = e;
```

This is sugar only. The variant still carries exactly one payload value, and the sugar desugars to the existing single struct payload representation.

## Interface Types

Interfaces specify structural contracts, similar to Go interfaces. Implementation is implicit — any type that provides the required methods satisfies the interface.

```aura
// Anonymous interface type:
def any_print(msg: interface(to_string: Func[(), String])) -> Void { ... }

// Named interface alias:
def ToStr = interface(to_string: Func[(), String])
```

The compiler models `interface(...)` as a first-class type node through frontend AST and typecheck IR (not as a nominal fallback), preserving each declared member signature. Interface constraints are checked structurally against the receiver method set, including named aliases and anonymous `interface(...)` constraints. The empty interface `interface()` is the type named `Any` in the standard library (`aura-stl/src/any.aura`); it accepts any value. On the other hand, the `Never` type would be equivalent to an interface with all the imaginable methods, making it impossible to satisfy, yet castable to any other type.

For runtime behavior, interface-typed values are lowered as interface objects (data pointer + witness/vtable pointer). Calls on interface-typed receivers lower through dynamic dispatch slots, while calls on concrete receiver types keep the direct static-call path.

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

## Type Annotations and Casts

`:` is overloaded for both annotation and cast (via the `from` method of the `From[T]` interface), distinguished by position:

- In a declaration or parameter list, `: Type` *annotates* without runtime cost.
- In an expression, `expr : Type` is a *cast* (checked or unchecked depending on the types).

```aura
let x: Int = 42;           // annotation
let y = x : Float;         // cast
```

**Casting rules:**


| From → To                                             | Allowed?                      |
| ----------------------------------------------------- | ----------------------------- |
| Anonymous tuple/struct → named                        | Yes                           |
| Named → anonymous tuple/struct                        | Yes                           |
| Named type A → named type B                           | **No** — compile error        |
| Tuple → Struct                                        | **No** — compile error        |
| Struct → Tuple                                        | **No** — compile error        |
| Any type → `union(...)` / `interface()` containing it | Yes                           |
| `union(...)` / `interface()` → contained type         | Yes, but may panic at runtime |


## Generics

Type parameters on declarations use square brackets after the `def` name.

```aura
def[T] identity(x: T) -> T { x }
def[A, B] Pair = (first: A, second: B)
```

At call sites, type arguments are usually inferred and can be omitted.

## Fallible Patterns in Assignments

Any binding construct (`let`, `const`, `def`) may use a destructuring pattern on its left-hand side. Some patterns are *fallible* — they panic at runtime if the value does not match:

```aura
let .ok(value)    = result;   // panics if result is .err
let Coord(x, y)   = some_val; // panics if some_val is not a Coord
let (a, b)        = tuple_val;
let (name, age)   = struct_val;
```

---
## Related Notes

- [[Subsystems/Typecheck]]
- [[Contracts/Typecheck IR]]
