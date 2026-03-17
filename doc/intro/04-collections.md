# Collections

The two primary collection types in Ty are `Array` and `Dict`. They both work more or less as you'd expect and support all of the usual operations. Sets can be mimicked with dicts that have `nil` values.

## Arrays

### Slicing

Ty uses `[i;j;step]` slicing syntax, only because `:` conflicts with namespace resolution. Otherwise it works like you'd expect, with negative indices counting from the end and omitted indices defaulting to the start or end of the array:

```ty
let a = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
pp(a[2;5])
pp(a[;5])
pp(a[-4;])
pp(a[;;2])
pp(a[;;-1])
```

By convention, mutating methods end with `!`:

```ty
let xs = [3, 1, 4, 1, 5]
xs.sort!()
pp(xs)

xs.map!(\_ * 10)
pp(xs)
```

Conditional elements — `if` inside an array literal includes the element only when true:

```ty
let debug = true
let verbose = false

let flags = [
  '--output' if true,
  '--debug' if debug,
  '--verbose' if verbose
]
pp(flags)
```

Comprehensions:

```ty
pp([x * x for x in ..10 if x % 2 == 0])
pp([(x, y) for x in 1...3 for y in 1...3 if x != y])
```

## Dicts

Dict literals use `%{}`. Keys can be any expression. Lookup is performed using circumfix `[]` and returns `nil` if the key is not found:

```ty
let ages = %{'Alice': 30, 'Bob': 25}
pp(ages['Alice'])
pp(ages['Charlie'])

for name, age in ages {
  print("{name} is {age}")
}
```

Dict comprehensions:

```ty
let squares = %{x: x*x for x in 1...5}
pp(squares)
```

## Sets

```ty
let a = %{1, 2, 3, 4}
let b = %{3, 4, 5, 6}

pp(a & b)   // intersection
pp(a + b)   // union
pp(a - b)   // difference
```
