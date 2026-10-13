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

Exit codes: 0 success, 1 test failures, 2 usage errors, 5 nothing selected, 130 interrupted.

Output written by a test is captured and shown only if the test fails. Failures show the assertion, the values of its operands, a trace pointing into your code, logs and captured output, followed by a summary with the slowest tests and a command to rerun each failure.

## Assertions

`assert(cond)` and `assert(cond, message)` throw an `AssertionError` when `cond` is false. For comparisons, the error records each operand's source and value:

```
tests/demo.ty:14: assertion failed
    assert(total == 10)
      total: 9
      (sum of 1..4)
```

`assert` must be called. A bare `assert x == y` is a compile error rather than a silent no-op.

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
| `t.id`, `t.name`, `t.file`, `t.line`, `t.seed` | information about the running test |

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
