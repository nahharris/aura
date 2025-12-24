Design the entire grammar for a programming language called Aura a functional programming language aimed for application development. The core principles for the syntax are:

1. We should have a small set of patterns of how the language constructs are organized and everything should be buildable out of these 
2. Not only that, but all (or almost all) the constructs should be possible to be described in terms of the language constructs for bootstraping
3. The constructs (derived from the small set of primitives) should be simple and familiar (most of the times)


Here are some of the core constructs that must are desirable to be available for this programming language:

> `;` we like semicolons
> 

## Assignments

Assignments will be defined using `=` operator.

```aura
// An assignment of a variable that is declared
x = 1;
```

On the static world, the `let` macro will be used to define variables, while the `const` macro will be used to define constants.

```aura
// A let binding
let x = 1;
// A const binding
const y = 2;
```

In the dynamic world (within a function body), the `let` declarations can be re-assigned.

## Data Types

> `:` is the type annotation operator

Collections will be defined using `[ ]` brackets.

```aura
// A list of numbers List[Int]
[1, 2, 3]
// A dictionary of strings to numbers
["a" = 1, "b" = 2, "c" = 3]
```

We can use `;` to have a local scope for a component of a collection.

```aura
// A list of numbers List[Int]
[
    let x = 0; x++; x, // x is destroyed after the comma
    2, 
    3
]
Product types will be defined using `( )` parentheses.

```aura
// A tuple of two integers (Int, Int)
(1, 2)
// An struct with two fields (x: Int, y: Int)
(x = 1, y = 2)
```

The semicolon trick is also available for product types.

```aura
// A tuple of two integers (Int, Int)
(
    let x = 0; x++; x, // x is destroyed after the comma
    2
)
```

Sum types will be defined with the `enum` or `union` macros

```aura
// A sum type of two integers or a string
1: union(Int, Float)
// A result enum with two variants
.ok(1): enum(ok: Int, error: String)
// An option enum
.null: enum(some: Int, null)
```

The semicolon trick is also available for sum types.

Functions closures will be defined using `{ }` curly braces, `~` guard operator and `->` arrow.

```aura
// A function Func[(Int, Int), Int]
{ (a: Int, b: Int) -> a + b }

// A function with pattern matching Func[(Int, Int), Int]
{ 
    (0, b) -> b,
    (a, 0) -> a,
    (a, b) ~ a > b -> a * b,
    (a, b) -> a / b
}
```

It can be also defined with the arrow outside the function body if no pattern matching is needed.

```aura
// A function Func[(Int, Int), Int]
(a: Int, b: Int) -> Int { a + b }
```

## Control Flow

Control flow will be defined using the `if` macro.

```aura
// An if statement
if (x > 0) {
    print("x is positive");
} else {
    print("x is negative");
}
```

The macro definition is:

```aura
macro if[T](
    condition: Expr[Bool], 
    then: Expr[Func[Void, T]], 
    else: Nullable[Expr[Func[Void, T]]] = null
) -> Expr[T]
```

## Loops

Loops can be defined using the `while` macro.

```aura
// A while loop
while (x > 0) do {
    x--;
}
```

The macro definition is:

```aura
macro while(
    condition: Expr[Bool], 
    body do: Expr[Func[Void, Void]] // Body is the internal name, while do is the external label
) -> Void
```

There's also the `for` macro to iterate over a collection.

```aura
// A for loop
for [1, 2, 3] do { x ->
    print(x);
}
```

The macro definition is:

```aura
macro for[T](
    collection: Expr[Collection[T]], 
    body: Expr[Func[T, Void]]
) -> Void
```

There's also the `each` method to iterate over a collection.

```aura
// A for loop
[1, 2, 3].each { x ->
    print(x);
}
```

This method is defined as:

```aura
fn Collection[T].each(body do: Func[T, Void]) -> Void
```

Finally we got the immutable loop `loop`:

```aura
// A loop
loop {
    print("Hello, world!");
}
```

Or 

```aura
let res = loop 0 do { i ->
    if (i < 10) then {
        .continue(i + 1)
    } else {
        .break(i)
    }
};
```

The macro definition is:

```aura
macro loop[B, C](
    initial: Expr[C], 
    body do: Expr[Func[C, Control[B, C]]]
) -> Expr[B]

macro loop[B](
    body do: Expr[Func[Void, Control[B, Void]]]
) -> Expr[B]
```

## Static Declarations

Constants and variables can be declared using the `const` and `let` macros.

```aura
// A constant
const x = 1;
// A variable
let y = 2;
```

The macro definition is:

```aura
macro const[T](
    ...assignments: List[Assignment]
) -> Stmt
macro let[T](
    ...assignments: List[Assignment]
) -> Stmt
```

Functions can be declared using the `fn` macro.

```aura
// A function
fn add(a: Int, b: Int) -> Int {
    a + b
}
```

The macro definition is:

```aura
macro fn[T](
    name: Identifier,
    body: Expr[Func[T, U]]
) -> Stmt
```

Macros can be declared using the `macro` macro.

```aura
// A macro
macro union(ty: TyExpr[TupleType]) -> TyExpr[UnionType]
```

Type declarations can be declared using the `type` macro.

```aura
// A type
type Point(x: Int, y: Int)
```

The macro definition is:

```aura
macro type[T](
    name: Identifier,
    ty: TyExpr[TupleType]
) -> Stmt
```

Methods can be declared using the `fn` macro but with the type name prefixing the method name.

```aura
// A method
fn Point.add(self, other: Point) -> Point {
    Point(x = self.x + other.x, y = self.y + other.y)
}
```

The macro definition is:

```aura
macro fn[T](
    name: Identifier,
    body: Expr[Func[T, U]]
) -> Stmt
```

> For all the above, the body function will be inlined. So when calling a return in a then branch of an if, it will return from the function that is using the if, not from the if branch it self.

## Dynamic Statements

There is the `return` macro to return from a function.

```aura
// A return statement
return 1;
```

The macro definition is:

```aura
macro return[T](
    value: Expr[T]
) -> Stmt
```

## Operators

We got all the usual operators. The special ones are:

- `..` is the range operator (for lists, collections, or destructuring ignoring some values)
- `?.` is the safe navigation operator (invoking a method on a nullable/failing value)
- `?:` is the elvis operator (for null/error coalescing)
- `!!` is the force unwrap operator (panic if the value unwrap is not possible)
- `:` is used to annotate or to cast a value to a type
- `_` is used to ignore a value

## String interpolation

String interpolation will be defined using the `$()` syntax.

```aura
// A string interpolation
"Hello, $(name)! You are $(age) years old."
```

A templated string can be defined using the `template` macro.

```aura
// A templated string
let tpl = template "Hello, $(name)! You are $(age) years old."
```

This string can be rendered later by giving it a struct with the fields to be interpolated.

```aura
tpl.render(name = "John", age = 30)
```

## Function Calling

A function can be called by giving it it's arguments in the order of the parameters.

```aura
// A function 
fn add(a: Int, b: Int) -> Int {
    a + b
}

// Calling a function
add(1, 2)
```

It can be also called with named arguments.

```aura
// Calling a function with named arguments
add(b = 2, a = 1)
```

Named arguments can also have a label.

```aura
fn add(a first: Int, b second: Int) -> Int {
    a + b
}

// Calling a function with named arguments and a label
add(second = 2, first = 1)
```

The later arguments can be passed outside the parentheses if they are a function, a list or a dictionary. The external label is not needed for the first external argument.

```aura
// A function
fn do(value: Int, func: Func[Int, Void])

// Calling a function with named arguments and a label
do(1, { value ->
    print(value);
})

do(1) { value ->
    print(value);
}

do(1) func { value ->
    print(value);
}

fn do2(value: Int, this: Func[Int, Void], that: Func[Int, Void])

// Calling a function with named arguments and a label
do2(1, this = { value ->
    print(value);
}, that = { value ->
    print(value);
})

do2(1) { value ->
    print(value);
} that { value ->
    print(value);
}
```

> Notice that after a `}`, a `\n` has the same effect as a `;`. So to pass more external arguments, you cannot break the line after the `}`.

