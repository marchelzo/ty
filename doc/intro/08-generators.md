# Generators 

Ty has stackful coroutines, referred to as `Generator`s. They can be created using the `generator` keyword, or more commonly, by calling a generator factory function. Such functions are denoted by a trailing `*` in their name, and when called, they return a `Generator` object which is initially suspended at the start of their body.

## Generator basics

Generators are resumed by invoking them like a function. When a generator is resumed, it executes until it encounters a `yield` expression, at which point it is suspended, and the `yield` expression's operand is wrapped with the `Some` tag and returned to the caller. The next time the generator is resumed, it continues execution from the point where it last yielded, and if an argument was provided in the resume call, that value is used by the `yield` expression (otherwise it evaluates to `nil`). Once a generator function returns, the generator is considered exhausted, and any subsequent resume calls will return `None`.

### A simple example

```ty
let gen = generator {
    dbg(yield 1)
    dbg(yield 2)
    dbg(yield 3)
    dbg(yield 4)
    dbg(yield 5)
}

dbg(gen())
dbg(gen('a'))
dbg(gen('b'))

for x in gen {
    dbg(x)
}

dbg(gen())
dbg(gen())
```

## Advanced generator usage

Let's look at a more complex example where we `yield` from deeper in the generator's call stack and make use of the resume values. In this example, we have a `RecordParser` that uses a generator to transparently suspend and wait for more data to be pushed into its internal buffer until it has enough data to return a complete record. The `_next` method is responsible for ensuring that the buffer contains at least `n` bytes, and it does so by yielding control back to the caller whenever more data is needed. This allows us to write the parsing logic in a straightforward manner, as if we were working with a blocking API, while still maintaining the non-blocking nature of the generator.

```ty
import ffi as c

use Record = {
    id:   Int
    time: Int
    data: Array[Float]
}

class RecordParser {
    _buf: Blob
    _co:  Generator[Record, Blob | nil]

    init() {
        _buf = Blob()
        _co = _run()
        (_co)() // Run the generator to the first yield
    }

    _next(n: Int) -> Blob  {
        while #_buf < n {
            _buf.push(yield nil)
        }
        _buf.splice(0, n)
    }

    _run*() -> Generator[Record, Blob | nil] {
        for (;;) {
            let id  = c.load(c.u32, _next(4))
            eprint("Parsing record with id={id}")
            let time  = c.load(c.u32, _next(4))
            let count = c.load(c.u32, _next(4))
            let data  = [c.load(c.float, _next(4)) for ..count]

            yield { id, time, data }
        }
    }

    push(chunk: Blob) -> Array[Record] {
        let records = []
        while let Some($record) = _co(chunk) {
            records.push(record)
        }
        records
    }
}

// === Create some dummy data to parse ===
fn make-record(id: Int, time: Int, data: Array[Float]) -> Blob {
    let size = 12 + #data * 4
    let buf  = c.alloc(size)

    let header = buf.as(c.u32)
    header[0] = id
    header[1] = time
    header[2] = #data

    let samples = (buf + 12).as(c.float)
    for x, i in data {
        samples[i] = x
    }

    Blob(c.blob(buf, size))
}

let data = Blob(
    make-record(42, 1234567, [1.0, 2.0, 3.0, 4.0, 5.0]),
    make-record(43, 2345678, [6.0, 7.0, 8.0, 9.0, 10.0])
)

// === Run it through our parser in chunks ===
let parser = RecordParser()

for chunk in data.groups-of(9) {
    dbg(parser.push(Blob(*chunk)))
}

// === Or all at once ===
dbg(parser.push(data))
```
