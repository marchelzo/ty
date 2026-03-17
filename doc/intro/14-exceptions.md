# Handling Exceptions

## throw

Any value can be thrown at any time, but the convention in Ty is to throw instances of `RuntimeError` or its subclasses, or to throw tags for simple error conditions. When an exception is thrown, control is transferred to the first active `try` block encountered when unwinding the stack. If no `try` block catches the exception, the program prints the exception and exits with a nonzero status:

If an exception is not caught, the program prints the exception's value and stack trace, then exits with a nonzero status:

```ty
fn main() {
    print((..100).any?(fn (i) {
        if i == 42 { throw "unlucky number: {i}" }
        false
    }))
}

main()
```

## try / catch

`catch` clauses support pattern matching. Multiple clauses are tried in order:

```ty
tag NotFound, Forbidden;

fn get-page(url: String) {
    match url {
        '/secret'  => throw Forbidden,
        '/missing' => throw NotFound,
        _          => "<h1>{url}</h1>"
    }
}

for url in ['/', '/secret', '/missing'] {
    try {
        print(get-page(url))
    } catch NotFound {
        print('404')
    } catch Forbidden {
        print('403')
    }
}
```

### Catching by type

Use `: ClassName` to catch exceptions of a particular class:

```ty
fn parse(s: String) -> Int {
    Int(s) ?? throw ValueError("not an integer: '{s}'")
}

try {
    print(parse('abc'))
} catch e: ValueError {
    print("ValueError: {e.what}")
}
```

### Catch with guards

The `::` operator can test properties of the caught value. Here it checks that the caught exception's `.what` string contains a specific substring:

```ty
fn flaky() {
    throw RuntimeError('connection refused: host unreachable')
}

try {
    flaky()
} catch ex :: 'connection refused' in ex.what {
    print('network error')
}
```

### Catch-all

`catch _` catches anything. `catch e` catches anything and binds it to `e`:

```ty
fn risky() { throw 42 }

let result = try { risky(); 'ok' } catch e { "caught: {e}" }
print(result)
```

### Standalone `catch`

When `catch` appears without a preceding `try`, the remainder of the current block is treated as an implicit `try` block. This is useful for wrapping an entire function body:

```ty
fn process(id: String) {
    catch _ {
        return -1
    }

    let id = int(id) ?? throw ValueError("invalid id: '{id}'")

    id * 2
}

print(process('123'))
print(process('abc'))
```

## finally

`finally` blocks run regardless of whether the `try` block succeeded, threw, or was exited via `break`/`continue`/`return`:

```ty
fn process(name: String) {
    print("opening {name}")
    try {
        if name == 'bad' { throw 'corrupt file' }
        print("processing {name}")
    } catch e {
        print("error: {e}")
    } finally {
        print("closing {name}")
    }
}

process('good')
process('bad')
```

## `try let`

`try let ... else ...` attempts to match a pattern against the result of a block. If the block throws or the pattern doesn't match, the else branch runs:

```ty
try let x = do { throw 'oops' } else {
    print('failed to compute x')
    0
}
```

## ?? throw

The null-coalescing operator `??` pairs naturally with `throw` for concise validation:

```ty
fn must-parse(s: String) -> Int {
    Int(s) ?? throw ValueError("expected integer, got '{s}'")
}

print(must-parse('42'))
try {
    must-parse('abc')
} catch e: ValueError {
    print(e.what)
}
```

## defer

`defer` schedules a statement to run when the enclosing scope exits — whether normally, via return, or via exception. Multiple defers execute in reverse order (LIFO):

```ty
fn example() {
    defer print('third: cleanup')
    defer print('second: more cleanup')
    print('first: do work')
}

example()
```

A common use is closing resources:

```ty
import os

fn read-some(path: String) -> String {
    let fd = os.open(path, os.O_RDONLY)
    defer os.close(fd)

    let buf = Blob()
    os.read(fd, buf, 128)
    buf.str()
}

print(read-some('/dev/urandom').size())
```

## Custom exception classes

Extend `RuntimeError` to define custom exception types. The `what` property provides the error message, and `trace()` returns a stack trace:

```ty
class ParseError < RuntimeError {
    __line: Int
    __col: Int

    init(msg: String, line: Int, col: Int) {
        super(msg)
        __line = line
        __col = col
    }

    location -> String { "{__line}:{__col}" }
}

try {
    throw ParseError('unexpected token', 10, 5)
} catch e: ParseError {
    print("{e.location}: {e.what}")
}
```

## Error tags

For lightweight error values, tags work well. Unlike classes, they carry no stack trace overhead:

```ty
tag InvalidInput, Timeout;

fn validate(x: Int) {
    if x < 0 { throw InvalidInput(x) }
}

try {
    validate(-1)
} catch InvalidInput(n) {
    print("bad input: {n}")
}
```

## Resource management with `with`

The `with` statement calls `__enter__` on entry and `__exit__` on exit (even if an exception is thrown):

```ty
import io

with f = io.open('/dev/null', 'w') {
    f.write('gone')
    print('wrote to /dev/null')
}
// f is automatically closed here
```

## Deterministic cleanup with `^`

Binding a variable with `^` ensures its `__drop__` method is called when the variable goes out of scope:

```ty
class Guard {
    __name: String

    init(name: String) {
        __name = name
        print("acquired {__name}")
    }

    __drop__() {
        print("released {__name}")
    }
}

do {
    let ^a = Guard('lock-A')
    let ^b = Guard('lock-B')
    print('working')
}
```
