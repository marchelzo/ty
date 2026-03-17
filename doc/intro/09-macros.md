# Macros

Ty macros are ordinary functions that operate on AST nodes at compile time. There's no separate macro language — pattern matching, closures, and recursion all work inside macros. Macros come in two forms: function-like macros that receive parsed AST arguments, and reader macros that consume raw tokens to define new syntax.

## Quasiquoting

`$$[ ... $$]` constructs an AST node from the code inside. Within a quasiquote, there are three kinds of splice:

- `$$(expr)` — splice an AST node into the template
- `$$::(expr)` — same, but hygienic: names in `expr` are resolved in the macro's scope, not the caller's
- `$${expr}` — splice a value into the template as a *value literal*

## Function-like macros

A function-like macro receives its arguments as AST nodes — unevaluated syntax — and returns an AST node to be compiled in its place.

Here's an `assert` macro that captures the source text of the condition it's given:

```ty
import ty.parse (show)

macro assert(cond) {
    let src = show(cond)
    $$[ $$cond || die("assertion failed: {$${src}}") $$]
}

assert(2 + 2 == 4)
assert([1, 2, 3].sum() == 5)
```

`show(cond)` converts the AST to its source representation at compile time. `$${src}` embeds that string as a literal in the generated code. A function could check a condition, but it couldn't tell you *what the condition was* — that information is lost after parsing. Macros see the syntax before it's compiled.

The `=` shorthand defines a macro whose body is implicitly a quasiquote template:

```ty
macro assert(cond) = $$cond || die("assertion failed")
```

## Pattern splicing

Quasiquoting is context-aware: a spliced node is inserted in whatever syntactic position it appears — including pattern positions:

```ty
macro matches?(e, p) {
    $$[ match $$e { $$p => true, _ => false } $$]
}

print(matches?(42, 40..50))
print(matches?([1, 2, 3], [1, *rest]))
```

`p` is the AST for a pattern like `40..50`, and it's spliced directly into the pattern arm of a `match`.

## Decorator macros

A macro that accepts a function definition can inspect and transform it. The `@` syntax applies it as a decorator.

This `@traced` decorator injects logging that prints the function name and its argument values on entry, and a message on exit:

```ty
import ty

macro traced(def) {
    let ty.FuncDef(f) = def

    let args = [
        $$[ "{$$(ty.String(name))}={$$name}" $$]
        for ty.Param({name, *}) in f.params
    ]

    let sig = args.fold((a, b) -> $$[ "{$$a}, {$$b}" $$])
    let lvl = [0]

    ty.FuncDef({*f, body: ty.Multi([
        $$[ eprint("{'':{4 * $${lvl}[0]++}}→ {$$(ty.String(f.name))}({$$sig})") $$],
        $$[ defer eprint("{'':{4 * --$${lvl}[0]}}← {$$(ty.String(f.name))}") $$],
        f.body
    ])})
}

@traced
fn tak(x, y, z) {
    if y < x {
        tak(
            tak(x - 1, y, z),
            tak(y - 1, z, x),
            tak(z - 1, x, y)
        )
    } else {
        z
    }
}

print(tak(5, 3, 1))
```

The macro destructures the function definition with `let ty.FuncDef(f) = def`, iterates over `f.params` to build a format string for each parameter, and reassembles the function with logging prepended via `ty.Multi`. `defer` ensures the exit message prints even if the function throws. The parameter names are embedded as string literals at compile time, while their values are evaluated at runtime.

## Reader macros

Reader macros take control of the parser and consume tokens directly using `ty.token.next()` and `ty.token.peek()`, or parse sub-expressions with `ty.parse.expr()` and `ty.parse.stmt()`.

```ty
import ty.parse (expr, show)

macro assert! {
    let e = expr(0)
    let src = show(e)
    $$[ $$e || die("failed: {$${src}}") $$]
}

assert! 2 + 2 == 4
assert! "hello".upper() == "HELLO"
print("all passed")
```

Unlike function-like macros, `assert! 2 + 2 == 4` has no parentheses — the macro itself decides how much of the token stream to consume.

## Compile-time evaluation

`static!` evaluates an expression once at compile time. The result is shared across all references:

```ty
fn go() {
    let table = static!(%{x: x * x for x in ..100})
    dbg(table[42])
    table[42] = 123
}

go()
go()
```

Both calls to `go()` see the same table. The mutation in the first call is visible in the second — the dict was created once during compilation and reused.

Under the hood, `static!` uses `ty.eval()` to evaluate the AST and `$${...}` to splice the result back in. You can use these primitives directly when defining your own macros.

## Inspecting AST structure

When writing macros, it helps to see how Ty represents code internally. Quasiquote an expression and pretty-print it:

```ty
pp($$[
    fn fib(n: Int) {
        (n <= 1) ? n : fib(n - 1) + fib(n - 2)
    }
$$])
```

Every syntactic form has a corresponding constructor in the `ty` module: `ty.Add`, `ty.Mul`, `ty.FuncDef`, `ty.Id`, `ty.Int`, `ty.Call`, etc. You can pattern-match on these to inspect and transform code.

## Putting it all together

Here's a reader macro that implements a Forth-style DSL. It reads tokens in postfix notation, builds expression ASTs on a compile-time stack using quasiquoting, and returns the final expression — which seamlessly references Ty variables from the surrounding scope:

```ty
import ty.token (next)

macro forth {
    let s = []
    next()
    while match next() {
        {int, *}       => s.push($$[ $${int} as Int $$]),
        {id,  *}       => s.push($$[ $$id $$]),
        {type: '+', *} => { let b = s.pop(); s.push($$[ $$(s.pop()) + $$b $$]) },
        {type: '-', *} => { let b = s.pop(); s.push($$[ $$(s.pop()) - $$b $$]) },
        {type: '*', *} => { let b = s.pop(); s.push($$[ $$(s.pop()) * $$b $$]) },
        {type: ']', *} => break
    }
    s[-1]
}

let f = (x, y) -> forth[x y + x y * *]

dbg(f(2, 2), f(3, 4), f(7, 8), f(10, 11))
```

`forth[x y + x y * *]` compiles to `(x + y) * (x * y)`. Each token is consumed with `next()` inside a `while match` loop. Integer and identifier tokens push AST nodes onto the stack; operators pop two nodes, wrap them in a quasiquoted expression, and push the result back. When `]` is reached, the stack holds a single AST node — the compiled expression. No Forth interpreter runs at runtime.

## Built-in macros

The prelude defines several macros:

- `dbg(expr, ...)` — prints module, function, line, source, and value for each expression; returns the last value
- `assert(cond)` — assertion with detailed failure messages showing both sides of comparisons
- `static!(expr)` — evaluates an expression once at compile time and shares the result
- `time!(expr)` — measures execution time, prints if > 100ms
- `matches?(expr, pattern)` — returns `true`/`false` for pattern match test
- `enum! { A, B, C = 5, D }` — generates auto-incrementing integer constants
