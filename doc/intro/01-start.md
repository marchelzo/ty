# Hello, Ty!

## What is Ty?

Ty is a dynamically-typed* imperative programming language with extensible syntax and a batteries-included standard library. It is designed for one thing: having fun!

```ty
fn go(rule) {
    fn step(x) {
        [(rule >> (4*x[i - 1] + 2*x[i] + x[(i + 1) % #x]) & 1) for i in ..#x]
    }

    for step.iter([int(it == 16) for ..33]).take(16) {
        print(it.map(%{0: ' ', *: '█'}[]).join())
    }
}

go(90)
```

> Looking for the standard library? See the [Standard Library Reference](pkg-prelude.html).

## Getting Ty

On arm64 macOS and amd64 Linux, you can install Ty with the following command:

```console
$ curl -fSsL https://based.lol/ty/install.sh | sh
```

On other platforms, you can try building [from source](https://github.com/marchelzo/ty).

## A note on the type system

Ty is dynamically typed, but it has a modest gradual type system that is used for type inference and static type checking. This is optional and can be disabled by running Ty with the `-q` option. Inferred types are used by the JIT compiler to guide optimizations, but otherwise have no effect on runtime behavior.

You can use `typeof` (or `:t` in the REPL) to experiment and see what the type checker infers for different expressions. For example:

```ty
let fun = (a, b) -> a.x + b(a.y)
print(typeof fun)
print(typeof fun({x: 37, y: 'hello'}, &len))
print(typeof fun({x: 'abc', y: {path: './test.log'}}, slurp@(_.path)))
```

```ty
print(typeof max)
print(typeof max(1, 2.0))
```

```ty
print(typeof max(1, 2.0, 'three'))
```
