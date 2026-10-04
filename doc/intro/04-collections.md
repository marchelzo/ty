# Collections

The three primary collection types in Ty are `Array`, `Dict`, and `Set`. They all work more or less as you'd expect and support all of the usual operations.

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

Set literals use `%[]`. Like dicts, sets remember insertion order, and like arrays they support conditional elements, spreads, and comprehensions:

```ty
let a = %[1, 2, 3, 4]
let b = %[3, 4, 5, 6]

pp(a & b)   // intersection
pp(a | b)   // union
pp(a - b)   // difference
pp(a ^ b)   // symmetric difference

pp(%[x % 3 for x in ..10])
pp(%[1, 2] <= a)
```

`<<` adds an element, `insert` reports whether it was new, and a set can be called (or passed) as a membership predicate:

```ty
let seen = %[]
for word in ['to', 'be', 'or', 'not', 'to', 'be'] {
  if seen.insert(word) {
    print(word)
  }
}

let vowels = %['a', 'e', 'i', 'o', 'u']
pp('sequoia'.chars().filter(vowels))
```

## Heaps

A `Heap` is a priority queue. Its ordering is fixed when it is built, using the same `by:`, `cmp:`, and `desc:` options as `sort`:

```ty
let tasks = Heap([(3, 'write'), (1, 'plan'), (2, 'build')], by: &0)
pp(tasks.pop())
pp(tasks.peek())

let biggest = Heap([5, 1, 9], desc: true)
pp([*biggest.drain()])
```

Read-only array methods work on heaps too (`map`, `filter`, `sum`, `in`, ...), and `top`/`bottom` pick the extreme elements of any iterable:

```ty
pp([5, 1, 9, 3].top(2))
pp(['ccc', 'a', 'bb'].bottom(1, by: \#_))
```

## Queues

`Queue` is a double-ended queue. Give it a `max-len` and it becomes a ring buffer that drops from the opposite end:

```ty
let recent = Queue(max-len: 3)
for x in ..5 {
  recent.push(x)
}
pp(recent)
pp(recent[0])
pp(recent.rotate(1))
```

## Ranges

Ranges support the same slicing syntax as arrays, and slicing a range gives back a range:

```ty
let r = 0..20
pp(r[;;5])
pp([*r[;;-5]])
pp(r.step-by(4) & r.step-by(6))
```
