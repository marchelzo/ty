# Testing

## Writing tests

Tests live in their own files, normally under `tests/`. In a test file, every top-level `pub fn` is a test:

```ty
fn three() -> Array[Int] {
    [1, 2, 3]
}

pub fn push-pop() {
    let xs = three()
    xs.push(4)
    assert(xs.pop() == 4)
}

ns parser {
    pub fn rejects-empty() { ... }
}
```

Functions that are not `pub` are helpers and never run. If a non-`pub` function takes no arguments and nothing in the file calls it, or if it has a `ty.test` decorator, the runner warns that it is probably missing `pub`.

Namespaces group tests. Every test gets a stable ID built from the file path, the enclosing namespaces and the function name: `tests/array.ty::push-pop`, `tests/x.ty::parser::rejects-empty`.

Only the file being tested contributes tests. Functions in modules it imports, such as shared helpers under `tests/support/`, never run as tests, even if they are `pub`.

## Running tests

```
ty --test FILE                    run one file
ty --test FILE::ID-PREFIX         run the tests whose ID starts with the prefix
ty --test FILE:LINE               run the test that contains LINE
ty --test [TARGET...]             run a suite: directories and files, in parallel
ty -c --test FILE                 list a file's tests without running anything
ty --test --help                  list runner options
```

Common options:

| Option | Meaning |
|---|---|
| `-k PAT`, `--exclude PAT` | select by ID substring, or `/regex/` |
| `-t EXPR` | select by tag: `slow and not (net or db)` |
| `--list[=json]` | list the selected tests instead of running them |
| `-x`, `--max-fail N` | stop early |
| `--shuffle[=SEED]`, `--seed N` | randomise order; every test is also reseeded from the seed and its ID |
| `--timeout S` | per-test timeout (suites default to 10 s; single files have none) |
| `-s` | don't capture output |
| `-r pretty\|dot\|json[=PATH]`, `--events PATH` | choose reporters; write the JSONL event stream |
| `--strict` | files without tests are errors |
| `--retries N` | rerun a failing test up to N times; a test that passes on a retry is reported as `flaky` |
| `--repeat N` | run each test N times; it fails if any run fails |
| `--lf`, `--last-failed` | run only the tests (and files) that failed in the previous run |
| `--ff`, `--failed-first` | run them first, then everything else |
| `--shard I/N` | run the I-th of N slices of the files, for splitting a suite across machines |
| `--durations N` | list the N slowest tests in the summary (default 5; 0 hides them) |
| `--tracked-only` | skip files that git doesn't track |

Exit codes: 0 success, 1 test failures, 2 usage errors, 5 nothing selected, 130 interrupted.

Flaky tests don't fail the run, but the summary lists them. `@retries(n)` from `ty.test` gives one test its own retry count. Crashes and hard timeouts in a suite end the worker process, so they are not retried.

The runner keeps per-test durations and the last run's failures in `.ty-test-cache/` in the current directory. Durations decide which files a suite starts first, and the failures drive `--lf` and `--ff`. Only the outermost `ty --test` writes the cache, so a test that runs `ty --test` itself doesn't overwrite it. `--shard` assigns files round-robin by path, so every machine computes the same split without sharing the cache.

Output written by a test is captured and shown only if the test fails. Failures show the assertion, the values of its operands, a trace pointing into your code, logs and captured output, followed by a summary with the slowest tests and a command to rerun each failure.

## Assertions

`assert(cond)` and `assert(cond, message)` throw an `AssertionError` when `cond` is false. The error shows the values that went into the condition:

```
tests/demo.ty:14: assertion failed
    assert(total == 10)
      total: 9
```

- **Comparisons** (`==`, `!=`, `<`, `in`, `::` and so on) show each operand that isn't a literal.
- **Calls** show their arguments, and method calls show their receiver: a failing `assert(bag.has?(item))` lists `bag` and `item`. `!call(...)` works the same way.
- **`&&` chains** are checked one part at a time, and the failure names the part that failed, so `assert(#xs == 3 && xs[0] == 2)` reports `xs[0] == 2` with `xs[0]: 1`. Later parts are not evaluated once one fails.

Every operand is evaluated exactly once, in order, and `assert(x != nil)` still narrows `x` for the code after it, including inside an `&&` chain.

When `==` fails on strings or on structured values, the report includes a diff:

```
FAIL tests/users.ty::loads-users
  tests/users.ty:9: assertion failed
    assert(users == want)
      users: [{id: 1, tags: ["a", "b"]}, {id: 2, tags: ["a"]}]
      want: [{id: 1, tags: ["a", "b"]}, {id: 2, tags: ["b"]}]
  diff (- users, + want):
    [1].tags[0]: 'a' != 'b'
```

Single-line strings get a caret under the first difference, multi-line strings get a line diff, and large arrays, dicts, records and objects get the paths that differ followed by a line diff of their pretty-printed forms, with unchanged runs elided. `lib/diff.ty` provides the same views to other code.

`assert` must be called. A bare `assert x == y` is a compile error rather than a silent no-op.

`check(cond)` and `check(cond, message)` are soft assertions: a failing check is recorded and the test keeps running. The test fails at the end, and the report lists every failed check with its line. Outside a test, `check` behaves like `assert`.

`approx(v, rel: 1e-9, abs: 0.0)` compares numbers, and arrays of numbers, within a tolerance: `assert(0.1 + 0.2 == approx(0.3))`. A failure shows the expected value as `0.31 ± 3.1e-10`.

`assert-compile-error(src, pattern?)` checks that `src` fails to compile, optionally with a message matching `pattern` (a string or regex), and returns the `CompileError`.

`assert-throws` checks that an expression throws, and returns what was thrown:

```ty
import json
import ty.test (assert-throws)

pub fn rejects-bad-input() {
    let e = assert-throws(json.parse('{'), JSONError)
    assert(e.what != '')
}
```

## The test context

A test whose first parameter is named `t` receives a `Test` object:

```ty
import ty.test (Test)

pub fn writes-a-file(t: Test) {
    let dir = t.tmp-dir()
    (dir / 'a.txt').write('hi')
    assert((dir / 'a.txt').read-text() == 'hi')
}

pub fn needs-postgres(t: Test) {
    let $url = getenv('TY_PG_URL') or t.skip('TY_PG_URL not set')
    let db = connect(url)
    t.cleanup(-> db.close())
    t.log("connected to {url}")
}
```

| Member | Meaning |
|---|---|
| `t.skip(reason)` | stop here and report the test as skipped |
| `t.cleanup(f)` | run `f` after the test, even if it fails; cleanups run last-in, first-out |
| `t.tmp-dir()` | a fresh directory, removed if the test passes and kept if it fails |
| `t.log(msg)` | a message shown alongside a failure |
| `t.step(name, f)` | run `f` as a named step; see below |
| `t.setenv(k, v)`, `t.unsetenv(k)` | change the environment until the test ends |
| `t.chdir(dir)` | change the working directory until the test ends |
| `t.capture(f)` | run `f` and return `{stdout, stderr, result}` with what it printed |
| `t.id`, `t.name`, `t.file`, `t.line`, `t.seed` | information about the running test |

### Steps

`t.step(name, f)` runs part of a test as a named step. A failing step fails the test, but the remaining steps still run, so one run reports every broken step. `t.skip` inside a step skips only that step. `t.step` returns whether the step passed.

```ty
pub fn session(t: Test) {
    let s = start-session()
    t.step('hover', -> assert(s.hover(1, 4) != nil))
    t.step('definition', -> assert(s.definition(1, 4).line == 0))
}
```

Failures list each step and its outcome. In the event stream, steps appear in the `test-end` event with IDs like `tests/lsp.ty::session/hover`.

## Parametrised tests

`@cases(rows)` runs a test once per row. A record or dict row sets parameters by name, a tuple sets them by position, and any other value is the first parameter:

```ty
import ty.test (Case, cases)

@cases([
    {a: 1, b: 2, want: 3},
    (-1, 1, 0),
    Case({a: 0, b: 0, want: 1}, id: 'zero', xfail: 'off-by-one in add'),
])
pub fn adds(a: Int, b: Int, want: Int) {
    assert(a + b == want)
}
```

Each row is a separate test, with IDs `adds[0]`, `adds[1]` and `adds[zero]`. `Case(values, id:, skip:, xfail:, tags:)` names a row or gives it its own metadata. `FILE::adds` selects every row, and `FILE::adds[zero]` selects one. A row that sets an unknown parameter or leaves a required one unset, and isn't covered by a fixture, is reported as an error.

## Fixtures and hooks

A fixture is a function marked `@fixture`. A test receives one by naming it as a parameter:

```ty
import ty.test (Test, fixture)

@fixture
fn db*(t: Test) {
    let d = Db.open(t.tmp-dir() / 'x.db')
    yield d
    d.close()
}

pub fn inserts(db: Db) {
    db.insert('k', 'v')
    assert(db.get('k') == 'v')
}
```

- A generator fixture runs up to its `yield` before the test. The yielded value is passed to the test, and the rest of the generator runs afterwards, even if the test failed. A plain function fixture just returns its value.
- Fixtures can take `t` and other fixtures as parameters. A cycle is reported as an error.
- `@fixture(scope: 'file')` sets the fixture up once per file and tears it down after the file's last test. File-scoped fixtures can't take `t` or use test-scoped fixtures.
- Fixtures defined in an imported module, such as one under `tests/support/`, are available to every test file that imports it.
- If a fixture fails, the test is reported as an error that names the fixture.

Hooks run around every test in a file:

| Decorator | Runs |
|---|---|
| `@before-each` | before each test, after the test's own `skip` checks |
| `@after-each` | after each test, even if it failed; in reverse order |
| `@after-all` | once after the file's last test |

A hook may take `t`. Per-file setup belongs at the file's top level, which runs once before any test.

The order around a test is: `before-each` hooks, fixtures, the test, `after-each` hooks, then fixture teardown and `t.cleanup` functions, last-in, first-out. A failing `after-all` hook or file-scoped teardown is reported as an error on `FILE::(teardown)`.

## Patching and spies

`patch(target, replacement)` replaces a value for the rest of the test. The target can be a function, including one in another module, a builtin such as `time.now`, a global, an object field or a dictionary entry. Everything that refers to the target sees the replacement, including code in other modules and code the JIT has already compiled. The original is put back when the test ends, or at the end of a `with` block, or when you call `restore()` on the value `patch` returns.

```ty
import time
import ty.test (patch)
import billing

pub fn invoices-are-dated() {
    patch(time.now, () -> 1700000000.0)
    assert(billing.invoice().date == '2023-11-14')
}

pub fn retries-once() {
    with patch(billing.charge, (amount: Int) -> throw TimeoutError()) {
        assert(billing.pay(5) == 'retry later')
    }
}
```

`patch-method(Class, name, f)` replaces a method on a class. The replacement takes the receiver as an explicit first parameter:

```ty
patch-method(Client, 'fetch', (self: Client, url: String) -> "fake {url}")
patch-method(Client, 'label', (self: Client) -> 'fake', kind: 'getter')
patch-method(Client, 'make', () -> FakeClient(), kind: 'static')
patch-method(Client, 'init', (self: Client, *args) -> (self.user = 'test'))
patch-method(Client, 'fetch', (self: Client, url: String) -> '', only: client)
```

`kind` is `'method'` (the default), `'getter'`, `'static'` or `'static-getter'`. Patching `init` replaces the constructor. With `only:`, other instances keep calling the original. Inherited methods can be patched too; the subclass goes back to inheriting when the patch ends.

A `Spy` records its calls:

```ty
import ty.test (Spy, spy, stub, spy-method)

let s = spy(billing.charge)          // calls through to the real function
patch(billing.charge, s)
billing.pay(5)
s.assert-called-with(5)
assert(s.count == 1)

let fetch = Spy().returns('{}')     // the same value on every call
let rolls = Spy().returns-each(1, 6) // these values, then an error
let fail = Spy().throws(TimeoutError())
let m = spy-method(Client, 'fetch')  // records (self, args...) and calls through
```

| Member | Meaning |
|---|---|
| `calls`, `count`, `last`, `called?` | the recorded calls; each `Call` has `args` and `kwargs` |
| `returns(v)`, `returns-each(*vs)`, `throws(e)`, `does(f)` | what the spy does when called |
| `assert-called(n?)`, `assert-not-called()` | check how often it was called |
| `assert-called-with(...)`, `assert-any-call(...)` | check the last call, or any call |
| `reset()` | forget the calls |

`stub(v)` is `Spy().returns(v)`.

### How tests run

`ty --test` hands over to `tytest`, a build of the interpreter with testing support compiled in. `make test` builds it, and it is installed next to `ty`. The `ty` binary itself has none of this support, so ordinary programs pay nothing for it.

Under `tytest`, the test file passed to `--test` is still type-checked, but its type errors are not reported, and its constants and functions can be reassigned. Modules it imports are checked as usual. Patching a builtin turns off the JIT's direct call to that builtin, and patching a constructor turns off the JIT's inlined constructor for that class.

## Metadata

Decorators from `ty.test` attach metadata to a test. They must be the outermost decorators.

```ty
import ty.test (skip, skip-if, platform, xfail, todo, tags, timeout, slow, only)

@skip-if(!__linux__, 'io_uring is Linux-only')
pub fn uring-roundtrip() { ... }

@skip-if(-> !HAVE-ZSTD, 'libzstd not found')
pub fn zstd-roundtrip() { ... }

@xfail('count(/\b/) double-counts the final boundary')
pub fn count-word-boundaries() { ... }

@tags('slow', 'net')
@timeout(30.0)
pub fn fetches-index() { ... }

@todo('needs a fake clock')
pub fn expires-session() { }
```

- `skip-if` takes a `Bool` or a function. Decorators run before the file's top level, so use a function when the condition depends on a global.
- `platform('darwin', 'linux')` skips the test on other platforms.
- `xfail` turns a failure into `xfail` and a pass into `xpass`, which fails the run (`strict: false` relaxes that).
- `todo` tests are reported but never run.
- `only` runs just the marked tests in that file. It is an error under `--forbid-only`, which is the default when `CI` is set.
- `slow` adds the `slow` tag and multiplies the timeout by 5.

To skip a whole file, call `skip-file(reason)` or `skip-file-unless(cond, reason)` at the top level. For code that won't even compile on some platforms, put the alternative in the `#|else` arm:

```ty
#|if __apple__
import apple (..)

pub fn bulk-roundtrip() { ... }
#|else
import ty.test (skip-file)

skip-file('Apple-only APIs')
#|]
```

## Suites and directory configuration

`ty --test tests` finds every `*.ty` file under `tests/` and runs each one in its own worker process, several at a time (`-J N`). Each file's top level runs once in its worker before its tests, so it is the place for per-file setup. Files named `_*.ty` or `__*__.ty`, and directories named `fixtures`, `support`, `examples` or `testdata`, are skipped. A crash, an `exit()` or a hard timeout is pinned on the test that was running, and the file is restarted after it.

A directory can contain a `__test__.ty` that configures it and everything below it:

```ty
import ffi as c
import ty.test.config (configure, skip-dir)

configure(opt-in: true, serial: true, timeout: 120.0, tags: ['db'])

if c.open('pq') == nil {
    skip-dir('libpq is not installed')
}
```

`skip-dir(reason)` skips the directory and everything below it. It also exits, so call `configure` first if the directory's settings should still apply.

| Key | Meaning |
|---|---|
| `opt-in: true` / `opt-in: 'NAME'` | only run when named explicitly, with `--all`, or with `--with NAME` |
| `serial: true` | never run two of this directory's files at once |
| `timeout`, `load-timeout` | defaults for tests in this directory |
| `tags` | tags added to every test |
| `env` | environment variables for the workers |
| `scripts` | files that are plain programs; each passes if it exits 0 and is skipped if it exits 77 |
| `exclude` | file names to leave out |

`make test` runs `ty --test tests --strict`.
