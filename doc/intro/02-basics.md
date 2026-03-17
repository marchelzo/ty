# Basics

## Binding variables

```ty
// Simple variable binding
let x = 10

// Immutable binding (`pi` cannot be reassigned after this)
const pi = 3.14159

// Public variables (exported by the enclosing module / namespace)
pub const VERSION = '1.0.0'

// Kebab-case is allowed and treated as equivalent to camelCase
// so the following declaration is valid and creates a variable
// named `logLevel` that can be accessed as `log-level`:
pub log-level = 'debug'

// Destructuring arrays, tuples, records, and dicts
let [a, b] = [1, 2]
let (a, b) = (1, 2)
let {name, age} = {name: 'Alice', age: 30}
let %{123: a, 'abc': b} = %{123: 'foo', 'abc': 'bar'}
```
## Built-in types

Ty has a typical set of built-in types for a dynamic language: numbers, strings, collections, and so on. The type annotations in the following examples are optional and only used for static type checking and inference; they have no effect on runtime behavior.

Note: `Int` is a 64-bit signed integer, not an arbitrary-precision integer. `Float` is a 64-bit floating point value.

```ty
let x:  Int     = 42
let y:  Float   = 3.14
let s:  String  = 'hello'
let b:  Bool    = true
let r:  Regex   = /[a-z]+/i
let z:  nil     = nil

let xs: Array[Int]        = [1, 2, 3]
let d:  Dict[String, Int] = %{'a': 1, 'b': 2}

let rect = {height: 10.0, width: 5.0}
let point: (Float, Float) = (1.0, 2.0)

let succ: (Int -> Int) = (n -> n + 1)

let id = fn [T](x: T) -> T { x }
```

## Control flow

Ty has most of the usual control flow constructs you'd expect in an imperative language, including `if` statements, `while` loops, and `for` loops. They all try to follow standard syntactic conventions but with some extra sugar here and there.

### If statements

The controlling expression of an `if` statement can be an ordinary expression, which will be evaluated and checked for truthiness, or it can be a refutable variable binding, which will attempt to match the controlling expression against the pattern on the left-hand side of the `if` statement and only execute the body if the match succeeds. In either case, `else if` and `else` branches are supported.

```ty
fn factorial(n: Int) -> Int {
    if n <= 1 {
        1
    } else {
        n * factorial(n - 1)
    }
}
```

```ty
import json

use MyConfig = {
    ports: {
        http: Int,
        https: Int
    }
}

fn parse-config(config: String) -> MyConfig {
    if let %{'ports': [http: Int, https: Int]} = json.parse(config) {
        return {ports: {http, https}}
    } else {
        throw ValueError('...')
    }
}
```

These two forms of conditions can be chained together, so you can have a refutable pattern match followed by an ordinary expression, and so on:

```ty
import path (Path)

fn write-log(config: Dict[String, Any]) {
    // $<id> is a non-nil pattern that matches any non-nil value and binds it to the variable <id>
    if let $dir = config['log_dir'] and Path(dir as String).dir? {
        // ...
    }
}
```

The `if` statement can also be inverted with the `not` keyword, which negates the truthiness of the controlling expression or the success of the pattern match. This is especially useful for refutable pattern matches, since it allows you to easily handle the failure case without deep nesting:

```ty
import json

fn load-config(path: String) {
    if not let $contents = slurp(path) or contents == '' {
        throw RuntimeError("no config present at {path}")
    }

    if not let %{'ports': [http, https]} = json.parse(contents) {
        throw ValueError('invalid config format')
    }

    // ...
}
```

### While loops

`while` loops work exactly like `if` statements, except that they repeat the body as long as the controlling expression is truthy or the pattern match succeeds:

```ty
fn count-down(n: Int) {
    while n > 0 {
        print(n--, end='...')
    }
    print('blastoff!')
}

count-down(5)
```

```ty
import os

fn download(sock: Int) {
    while let $chunk = os.read(sock, 1024) {
        // ...
    }
}
```

### For loops

`for` loops come in two flavors. There are `for <binding> in <iterable>` loops, which iterate over the elements of a collection, and C-style `for` loops, which have an initializer, a condition, and an incrementer.

```ty
// Iterating over a collection
for x in [1, 2, 3] {
    pp(x);
}

// Iterating over a collection with index (note: The index is produced as
// part of the loop itself, not by the iterable. Thus, it is always
// available, but when iterating over a dict, it will be the 3rd element in the
// binding list instead of the 2nd.)
for x, i in [1, 2, 3] {
    pp((i, x))
}

for key, value, i in %{'a': 1, 'b': 2} {
    pp((i, key, value))
}

// Skipping some elements
for c in 'hello, world!' if c.match?(/[a-z]/) {
    pp(c)
}
```

```ty
// C-style for loop
for let i = 0; i < 3; i++ {
    pp(i)
}

// Loop unconditionally
for (;;) {
    break if rand() < 0.1
}
```
