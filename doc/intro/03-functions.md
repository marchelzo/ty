# Functions

Functions are defined with `fn` or constructed by evaluating an `fn` expression or lambda. They're called with the usual syntax and support positional and named arguments. 

In the absence of an explicit `return`, the last expression is the implicit return value.

```ty
fn double(x) {
    x * 2
}

pp(double(21))
```

## Multiple dispatch

Top-level function definitions and class methods may be overloaded by providing multiple definitions in sequence, which implicitly creates a dispatcher that selects the first matching definition based on argument types and constraints. This means that more specific definitions should be placed before more general ones.

```ty
fn area(r: Float)            { 3.14159 * r * r }
fn area(w: Float, h: Float)  { w * h }
fn area(s: 'unit circle')    { 3.14159 }
fn area(s: String)           { "not a shape: {s}" }

print(area(5.0))
print(area(3.0, 4.0))
print(area('unit circle'))
print(area('triangle'))
```

This works on class static methods too.

## Operator overloading

Binary operators are a bit of a special case since the set of overloads has no particular order and expands as modules are loaded. To resolve this, Ty uses a more complex dispatch algorithm that considers all applicable overloads and selects the most specific one based on argument types. Binary operators are dispatched solely on the classes of their operands at runtime. That is, they don't support arbitrary constraints like regular functions do.

```ty
class Vec2 {
    x: Float;
    y: Float;

    +(other: Vec2) -> Vec2 {
        Vec2(x + other.x, y + other.y)
    }
}

fn *(x: Float, v: Vec2) -> Vec2 {
    Vec2(x * v.x, x * v.y)
}

let v1 = Vec2(1.0, 2.0)
let v2 = Vec2(3.0, 4.0)

pp(v1 + v2)
pp(2.0 * v1)
```

## Named and default arguments

```ty
fn greet(who, greeting: String = 'Hello', loud: Bool = false) {
  let msg = "{greeting}, {who}!"
  if loud { msg.upper() } else { msg }
}

print(greet('world'))
print(greet('world', loud=true))
print(greet('world', greeting='Hey'))
```

## Variadic arguments

`*args` collects extra positional arguments into an array, and `%kwargs` collects extra named arguments into a dict.

Iterables can spread into argument lists as positional arguments with `*iterable`. Records and dictionaries can spread into argument lists as named arguments with `**record-or-dict`.

```ty
fn print-all(*args, %kwargs) {
    for arg in args {
        print(arg)
    }
    for key, value in kwargs {
        print("{key}={value}")
    }
}

print-all(1, 2, 3, *'xyz', foo='bar', baz=42, **%{'qux': 'quux'})
```

## Lambdas

Lambdas are expressed with the infix `->` operator and work like you'd expect:

```ty
pp([1, 2, 3].map(x -> {x, sq: x * x}))
```

Any expression can be preceeded by `\` to produce a lambda whose parameters are derived from the holes denoted by `_` in the expression. Longer strings of `_` can be used like de Bruijn indices to refer to parameters further out:

```ty
let add = (\_ + _)
print(add(2, 3))

let _const = \__
let always42 = _const(42)
print(always42())
```

## Partial application

`f@(args)` creates a partial application. `_` marks the holes:

```ty
fn add(a, b) { a + b }
let add10 = add@(10, _)
pp(add10(5))
```

```ty
let hex-digits = ['a', 'ff', '1b']
pp(hex-digits.map(int@(_, 16)))
```

`*` and `**` can be used if you want to spread extra arguments or keyword arguments into the partial application:

```ty
let shout = print@(*, **, end='!!!\n')
shout('hello', 'world', sep=' ')
```

## Function composition

`|>` composes functions left-to-right, and `.` composes functions right-to-left:

```ty
let nums = [7, 8, 3, 1, 4, 5, 0, 2]

let fun1 = &[;5] |> &sort
let fun2 = &[;5] .  &sort

pp(fun1(nums))
pp(fun2(nums))
```

Backticks can be used to refer to operators as functions:

```ty
let sum-ints = [&sum, \_.map(int), \_.scan(/\d+/)].fold(`.`)
pp(sum-ints('the answer is 32 plus 10'))
```
