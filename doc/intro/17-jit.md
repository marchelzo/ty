# Generating native functions

The `jit` module builds callable native functions at runtime. It supports
ARM64 and SysV x64, with a portable interpreter available through `jit.interp`.
Import it like any other module:

```ty
import jit as j
```

## The builder

An `Asm` describes a function's parameters, result and instructions. Registers
are mutable: `set` changes the value used by subsequent instructions.
Generation-time Ty loops can unroll work into the generated function.

```ty
import jit (Asm, F64)

fn make-poly(cs: Array[Float]) -> Float -> Float {
    let a = Asm('poly', params: [F64], ret: F64)
    let [x] = a.params
    let acc = a.reg(F64, 0.0)

    for cs.reverse() {
        acc.set(acc * x + it)
    }

    a.ret(acc)
    a.finish() as (Float -> Float)
}

assert(make-poly([1.0, 2.0, 3.0])(2.0) == 17.0)
```

Integer types are `I8`, `U8`, `I16`, `U16`, `I32`, `U32`, `I64` and `U64`.
Floating types are `F32` and `F64`. `BOOL`, `PTR`, `REF`, `VAL` and `VOID`
describe booleans, pointers, GC references, Ty values and no result.

Use `a.label`, `a.bind`, `a.jmp` and `a.br` for control flow. Pointer registers
have `off(T, displacement)` and `at(T, index, disp: displacement)` methods;
the resulting memory operand can be passed to `a.load` or `a.store`. Indexes
are scaled by the size of `T`.

`a.ccall` accepts a generated function, an FFI function, a runtime helper or
an address with an explicit signature. A function's `.ptr` exposes its body
address for C callbacks. Keep the function alive while C retains that address.

## The `asm!` macro

`asm!` offers C-style expressions, declarations, memory access and control
flow. The body is lowered, validated and serialized when Ty compiles the
enclosing source. Expressions in braces are Ty expressions evaluated when the
macro expansion runs.

```ty
import jit (asm!)

fn make-scale(k: Float) -> (Ptr[Any], Int) -> nil {
    asm! scale(p: ptr, n: i64) {
        i: i64 = 0
        while i < n {
            f64[p + i*8] = f64[p + i*8] * {k}
            i += 1
        }
    }
}
```

Scalar type names use lowercase letters inside `asm!`. A cast such as
`x as i32` converts between scalar types. Unsigned operators use the `u`
prefix, for example `u<`, `u/` and `u>>`. Statements end at a newline or `;`.

Foreign functions can appear in callee holes:

```ty
import jit (asm!)
import ffi as c

let total-len = asm! total-len(ps: ptr, n: i64) -> i64 {
    t: i64 = 0
    i: i64 = 0
    while i < n {
        t += {c.strlen}(ptr[ps + i*8])
        i += 1
    }
    return t
}
```

## Ty values and execution modes

`finish` infers an execution mode. Scalar functions with calls that cannot
collect use detached mode: their entry thunk releases the VM lock while the
native body runs. Detached loops have no interrupt polls.

Functions using Ty values, GC references or collecting calls use attached
mode. The VM lock stays held, and backward branches receive interrupt polls.
`Asm(..., mode: 'attached')` and `Asm(..., mode: 'detached')` request a mode
explicitly; incompatible instructions produce `jit.Error`. The same mode
names can follow an `asm!` signature.

`VAL` parameters point to Ty `Value` slots. `a.unbox` guards a value's tag and
branches to a supplied label on failure. `a.box` writes a result into a
GC-visible slot:

```ty
import jit as j

let a = j.Asm('increment', params: [j.VAL], ret: j.VAL)
let bad = a.label()
let n = a.unbox(a.params[0], Int, `else`: bad)
a.ret(a.box(n + 1, Int))
a.bind(bad)
a.ret(a.const(nil))

let increment = a.finish()
assert(increment(41) == 42)
assert(increment('bad') == nil)
```

`a.vslot()` reserves a GC-visible value slot. `a.const(value)` retains a Ty
value as a rooted constant, and `a.ref(object)` produces a GC reference.
`a.call-ty(function, arguments)` calls a Ty function and returns a pointer to
its result slot. Collecting calls preserve live references and rebase pointers
into the VM stack if that stack grows.

`jit.layout` exposes value and container offsets. `jit.tag` exposes value
tags. `jit.rt` contains typed runtime helpers for arithmetic, comparison,
containers, member access, calls and exceptions. These helpers carry their
signatures and collection/exception flags into generated calls.

## Inspecting generated code

`a.dump(stage: 'lir')` shows portable instructions. The `'legal'` and `'alloc'`
stages show legalized instructions and register or spill assignments.
`f.code.lir()` shows the original LIR of a finished function, and
`f.code.dis()` shows assembly when Capstone is available through `ffi`,
and a hex dump otherwise. Both outputs include site IDs at native offsets.

Set `TY_JIT_DUMP='^poly$'` to print the LIR, legalization and allocation stages
for matching function names. This also works for bytecode JIT functions.
Set `TY_JIT_PERF_MAP=1` to append generated function addresses and names to
`/tmp/perf-<pid>.map`.

`j.interp(a)` returns a callable interpreter version of a builder. It is useful
for comparing results with native execution; it does not support `RAW`.
Validation errors are reported as `jit.Error`, with instruction and source
span information when available.

The full instruction set and C interface are described in
[the JIT module reference](../jit-module.md).
