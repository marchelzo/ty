# Pattern Matching

## Overview

Several language constructs in Ty support pattern matching, which allows you to match values against complex patterns and destructure them in the process. Patterns are used in the following contexts:

- `match` expressions and `match` statements
- `while let`, `while match` loops and `for match` loops
- `if let` and `if not let` conditionals
- `use match` extractor definitions

Let's go through the different kinds of patterns and how they work in these contexts.

## The not-nil pattten

`$var` matches any non-nil value and binds it to `var`:

```ty
const my-int = x -> match int(x) {
    $n => n,
    _  => -1
}

pp(my-int('42'))
pp(my-int('not a number'))
```

## Destructuring

Array, record, and tuple expressions can appear in pattern context to destructure values. `*var` matches the rest of whatever is being destructured:

```ty
tag One, Two, Three, Four;

fn f(x) {
    return match x {
        [a, *bs, c]  => One({a, bs, c}),
        {a, ?b, *c}  => Two({a, b, c}),
        (a, b, c)    => Three({a, b, c}),
        %{'a': a}    => Four({a}),
        _            => None
    }
}

dbg(
    f([1, 2, 3, 4]),
    f({a: 1, d: 4, e: 5}),
    f((1, 2, 3)),
    f(%{'a': 42, 'b': 100}),
    f('not a match')
)
```

Record patterns match by field name. `?` makes a field optional (binds to `nil` if absent):

```ty
let people = [
    {name: 'Alice', age: 30, role: 'admin'},
    {name: 'Bob', age: 25},
    {name: 'Charlie', age: 35, role: 'user'}
]

for match people {
    {name, role: 'admin', ?email} => {
        print("{name} is admin, email={email ?? 'N/A'}")
    },

    {name, *info} => print("{name}: {pretty(info)}")
}
```

## Choice patterns

Commas or `or` separate alternatives. These may appear in nested patterns as well:

```ty
const f = match {
    [0 or 1 or nil, x] or {val: x, *} => x,
    _                                 => -1
} 

dbg(
    f([0, 42]),
    f([1, 42]),
    f([nil, 42]),
    f({val: 42}),
    f({val: 42, extra: 123}),
    f([2, 42])
)
```

## Range patterns

```ty
fn grade(score) {
    match score {
        90...100 => 'A',    // 90 up to and including 100
        80..90   => 'B',    // 80 up to (not including) 90
        70..80   => 'C',
        _        => 'F'
    }
}
pp([95, 85, 75, 60].map(grade))
```

## Pattern constraints

`<pattern> :: <constraint>` succeeds when `pattern` matches **and** `constraint.__match__(subject)` holds:

```ty
fn describe(x: Int | String | Array[Int]) {
    match x {
        x :: Int     => "int: {x}",
        x :: String  => "str: \"{x}\"",
        x :: #x <= 3 => "small array: {x}",
        x            => "big array ({#x} elements)"
    }
}
print(describe(42))
print(describe('hi'))
print(describe([1, 2]))
print(describe([1, 2, 3, 4, 5]))
```

## Ref patterns

`>var` in a pattern assigns to an existing variable instead of creating a new binding:

```ty
let found = nil
match [10, 20, 30] {
    [_, _, >found, *] => ()
}
pp(found)
```

## Use-match (extractors)

`use match` defines named extractors — patterns that can destructure values with arbitrary logic:

```ty
use match IntLike {
    k: Int => k,

    (x: Float) and (x == round(x))
        => int(x),

    /\d+/ => int($0)
}

for match [15, 3.0, '42', 1.3, 'not a number'] {
   IntLike(n) => print("got an int-like value: {n}"),
   _          => print("not int-like")
}
```

## Alias patterns

`pattern as var` creates a new binding `var` for the value matched by `pattern`:

```ty
match [1, 2, 3] {
    [first, *rest] as whole => {
        pp({first, rest, whole})
    }
}
```

## Gotchas with identifiers in patterns

```ty
const UID = 40
let   x   = 42

let go = match {
    (UID, _) => print("first element is equal to UID, UID={UID}"),
    (x, x)   => print("both elements are equal: {x}"),
    (::x, _) => print("first element is equal to x, x={x}"),
    _        => print("no match")
}

for [(42, 42), (42, 43), (42, 44), (40, 42)] {
    go(it)
}
```
