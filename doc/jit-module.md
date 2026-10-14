# The `jit` module and the shared LIR backend

Status: implementation started. The shared C contract, portable builder,
CFG/liveness, validator, serialization, interpreter, register allocation,
code-memory allocator, and ARM64/SysV x64 scalar backends are wired into Make
and CMake.
Native entry thunks are generated as LIR, with argument guards, conversions,
lock handling, value-slot reservation and pointer rebasing. Attached calls and
polls rebase live VM-stack pointers, including spilled pointers. Native REF
spill slots preserve references and their children across runtime calls and GC.
`VALUE_JIT_FUNCTION` and GC-owned code are connected to VM calls, value
operations and reclamation. The `jit.Asm`/`Reg`/`Mem`/`Label`/`Fn`/`Code` API,
frozen runtime helper catalog, layout constants, guards, boxing, callbacks,
atomics and raw register bindings are available. The exact polynomial example
works. The module has 58 integration tests; both full Ty suite modes currently
pass with 1,337 passed and 6 xfail. C tests include 2,000 interpreter/native
differential programs per run; an extended 20,000-program run also passed.
The public `Encoding`/`Hole`/`serialize`/`load` API retains GC-owned captures
and validates callee signatures. `jit.interp` returns a callable `jit.Fn`, with
LIR entry guards, GC roots and VM-stack pointer rebasing. Foreign functions
retain their call-interface owners and expose fixed/variadic signatures.
Nested calls reserve separate callee slot frames, preserve the caller's slot
base and roots, and retain returned Values in caller-owned slots. Native and
interpreter calls and tailcalls are covered in every backend combination.
The first `asm!` frontend parses and lowers at compile time, validates and
serializes LIR, splices runtime holes, and expands with a typed FuncType and Fn
members. The scale, strlen and qsort examples work. Complete macro coverage, final documentation and performance gates remain
open. The x64 native scalar fixture passes 62,069 checks and an extended
20,000-program differential run under Rosetta. Its 769-check entry fixture
also passes with ASan and UBSan.
The bytecode-to-LIR path now handles scalar literals, local loads and
assignments, duplication, arithmetic, comparisons, branches, short-circuit
expressions, loops and returns. A bytecode CFG propagates operand depths and
creates dynamic LIR labels. Integer, float and truthiness fast paths use typed
virtual registers; collecting runtime slow paths retain call-site metadata.
Backward edges have poll/deopt points that preserve the bytecode return
protocol. Poll return sites and ENTRY tags survive version 2 serialization;
version 1 streams remain supported. Global and indirect calls now suspend and
resume through ENTRY blocks and SWITCH dispatch, preserving JIT_PACK and
resume-offset metadata. Keyword
calls, object/self method calls and global loads also lower to LIR. Captured
reads, references, function/generator literals, capture setup, assignments,
compound mutations, yields and throw paths now lower through the same path.
Forty-two integration tests cover numeric/control-flow execution, code lifetime,
collecting callbacks, call resumption, 400-level recursion, keywords and
method dispatch, mutable closures under GC, generator resumption and throws
through resumed calls. Array, dictionary, set and tuple literals, member and
subscript assignments, scalar runtime operations, ordinary iteration and
comprehensions now lower to LIR. Optional and static method calls, keyword
arguments on implicit-self calls, and argument and literal spreads also use
LIR. Dynamic member names have explicit stack effects; spreads preserve actual
operand positions as iteration grows the stack. A 400-element spread exercises
stack growth. Code and builders adopted during GC sweeping retain their roots
through that sweep, including code first compiled by a finalizer.
Array, tuple, record, tag, string, dictionary, regex, range and nonlinear
patterns now lower to LIR, as do strict destructuring operations. The CFG
includes every tag/string dispatch-table edge and the distinct operand depths
of pattern success and failure paths. Collecting comparisons retain operands
until the comparison finishes. Class field patterns and unapply calls use
runtime helpers that preserve the VM's no-match return convention. The shared
instruction walker now includes TRY_UNAPPLY's jump operand.
Global and thread-local loads, targets and assignments, dynamic/static member
targets, nil-coalescing assignment, and pre/post increment/decrement now lower
to LIR. Method/getter/setter/class bindings, decoration and method conversion
also lower through runtime helpers. Converting a compiled function into a
method clears the copied native-code cache before changing its layout.
Resource enter/drop groups and defer/cleanup preserve callback ordering and
protected native frames through collecting callbacks and exceptions.
Initialization branches now lower to LIR; the instruction walker covers the
operands of thread-local targets, static access and method conversion.
Generic operators, slicing, interpolated regexes, template rendering, scoped
eval, multiple-value stack normalization and additional stack/control operations
now lower to LIR. Template rendering accounts for consumed holes; local
reference loads follow complete reference chains. The CFG tracks sentinel
segments through saved-stack restoration and exception cleanup, and emits
labels only at branch, handler and resume targets. Fixed-depth functions keep
their operand base static. Register allocation indexes call positions and
registers that cross calls; native pointer rebasing uses the same candidate
set. The prelude walk function's measured compile time fell from roughly
540 ms to 143 ms. Full runtime and compile-time performance gates remain open.
A fresh seven-run comparison averages 3.52 s versus 1.73 s for Richards and
4.86 s versus 3.18 s for the template benchmark. These regressions still fail
the runtime gate. The latest 100-op Ty `finish()` average is 53.6 us, above
the 50 us target.
Class and tag declarations, static initialization, tail calls, constrained
unapply failures and generator delegation now lower to LIR. Delegation handles
fresh and started children, nested generators, GC and exceptions. Generators
with try handlers keep their native frames across yields. Static operand stacks
reserve their measured capacity; the 240-slot limit is gone. Three unused
instruction names with no compiler or VM implementation were removed.
The profiler uses LIR and records instruction ticks and compilation statistics.
The legacy emitter, architecture templates and build rules are removed.
Bytecode compilation now uses LIR exclusively; final runtime optimizations
remain open.
Loop-local Int and Float values now live in LIR registers. The frontend writes
them back before observing calls, polls and returns, and reloads them after
writing calls, ENTRY resumption and exception recovery. Captured variables
retain their existing slot semantics. There is no runtime cache-validity mask;
`TY_JIT_NO_REGISTERIZE` disables this path. Scalar local assignments and
compound mutations can update cached registers directly.
Object field reads have a native path guarded by the value tag and current
field layout. Known method calls retain rooted callee values, guard runtime
method identity, and respect built-in method priority. Simple ordinary calls
use fast frame setup while retaining ENTRY/SWITCH suspension and resumption.
Comparison branches avoid boxing temporary booleans and compare nil directly.
Native emission indexes moves and constraints by instruction; spill workspace
allocation indexes constraints and physical-register occupancy. Try/catch/finally now lower through direct RETURNS_TWICE `_setjmp`
calls. Protected calls keep the native try frame live; saved-stack operations
and dynamic operand positions preserve catch cleanup and finally return
values. Exception recovery reloads VM-stack addresses from a pinned fp offset.
Nested handlers, early returns and throws after 400 calls plus GC are covered.
The shared emitter also handles RETURNS_TWICE calls with SITE metadata directly,
preserving their return address when later calls overwrite the site slot.
ARM64 conditional branches expand through unconditional branches for distant
targets. Large bodies place floating literals and switch tables in nearby
islands. A native fixture verifies targets and literals across a 1.2 MB body
on ARM64 and x64. Emission indexes labels by instruction position.
`Code.dis()` loads Capstone 4, 5 or 6 through `ffi` when available, and falls
back to a hex dump otherwise. Both outputs annotate native site offsets.
`TY_JIT_DUMP` prints the LIR, legal and allocation stages for matching names;
[the introductory guide](intro/11-jit.md) covers the builder and macro.
Scope: one contiguous body of work. Nothing in here is a stepping stone that a
later step tears down.

## 1. Summary

Ty gets a built-in `jit` module. Ty programs use it to build specialized native
functions at runtime and then call them. The module sits on a new shared
compiler backend, **LIR**, which has these parts:

- a portable, non-SSA, three-address IR with virtual registers and labels;
- a per-architecture legalizer;
- a linear-scan register allocator that spills;
- emission through new DynASM templates (`src/lir_arm64.dasc`,
  `src/lir_x64.dasc`).

**The existing bytecode JIT moves onto LIR as part of this work.**
`src/jit_arm64.dasc`, `src/jit_x64.dasc` and every `jit_emit_*` wrapper are
deleted. When the work is done, Ty has exactly one native code generator.

There are three ways to build code, layered on top of LIR:

1. **The `jit.Asm` builder.** Ty acts as the metalanguage, so loops and
   constants at generation time unroll and specialize the generated code.
2. **The `asm!` token macro.** It uses C-like syntax with `{expr}` holes. It is
   parsed and validated when the enclosing Ty code compiles, and its result has
   a static type.
3. **The Ty-value layer.** Generated code can guard, unbox and box Ty `Value`s,
   keep GC-visible value slots, and call a frozen catalog of runtime helpers
   (`jit.rt`).

## 2. Decisions (settled; do not revisit)

| Question | Decision |
|---|---|
| Gating | Unrestricted. `import jit` works like `import ffi`. |
| Value layout as API | Frozen. `jit.layout` and `jit.rt` are public and stable. |
| Converge with the bytecode JIT | Yes. The bytecode JIT is ported to LIR in this scope. |
| Win64 | Out of scope. Target SysV x86-64 (Linux, FreeBSD, macOS) and AAPCS64 (Linux, plus the Apple arm64 variant). |
| Optimizer | None. The only rewrites allowed are legalization peepholes: imm folding, cmp+branch fusion, addressing-mode folding. |
| Sandboxing / verification | None beyond the structural validator in section 5.3. Native code is unsafe in the same way `ffi` is. |

The following are **out of scope**. Do not stub them, and do not leave hooks for
them.

- Win64
- V128/SIMD
- A persistent on-disk code cache
- The GDB/LLDB JIT interface
- Struct-by-value arguments and returns in `ccall`
- Pure-Ty instruction encoders

## 3. Background: what exists today

Line numbers are approximate as of when this doc was written. Use grep.

- **Bytecode JIT.** `src/jit.c` (~14k lines) compiles a whole function from
  bytecode straight to DynASM calls on first call (`try_jit`,
  `include/jit.h`). It has no IR.
  - Fixed register map: `BC_TY`, `BC_RESUME`, `BC_LOC`, `BC_ENV`, `BC_OPS`
    pinned; scratch `BC_S0..S3`; `BC_A0..A5`, `BC_CALL`, `BC_RET`
    (`src/jit.c:~2339`). Register use is limited to a 2-slot integer-local
    cache (`bc_plan_raw_cache`, `bc_raw_*`), whose validity is tracked at
    runtime in `BC_CACHE_MASK`.
  - Values are 32-byte tagged structs (`struct value`, `include/ty.h`) that live
    in `ty->stack`. Locals are at `args[0..bound)` and operands at
    `[BC_OPS + i*32]`.
  - About 150 `jit_rt_*` C helpers handle slow paths; most have the convention
    `(Ty *, Value *out, Value *a, Value *b)`.
  - Interrupt and GC safepoints are `bc_emit_interrupt_check`, which calls
    `vm_jit_handle_interrupt`.
  - Exceptions: `_setjmp` is called directly from JIT frames.
  - Resume dispatch serves calls that trampoline and generators
    (`JIT_PACK(reason, idx)`).
  - `JitSite{pc, bc}` tables and the `*pc` return-slot protocol feed
    `jit_frame_ip` for backtraces.
  - Deopt happens only at interrupt checks, for the debugger
    (`bc_deopt_info`, `DeoptFrame`).
- **DynASM templates.** `src/jit_{arm64,x64}.dasc` each expose the same set of
  ~65 `jit_emit_*` primitives. They contain hidden clobbers: on x64, shifts
  clobber `rcx` and division clobbers `rax`/`rdx`, and the float ops take
  Value-slot `base + off` operands. `jit_emit_update_fp` is dead and its
  signatures differ between the two files. The generated headers are gitignored
  and built with system `luajit` (`Makefile:~128`, `CMakeLists.txt:~308`).
- **Code memory.** `src/jit.c:~13605`. It is one 128 MB bump region:
  - macOS: `MAP_JIT` plus `pthread_jit_write_protect_np`.
  - Linux: `memfd` with two views (RW and RX) and an `atfork` reset.
  - Fallback: `JitMapOne`.

  Nothing is ever freed (`jit_free` TODO).
- **FFI.** `VALUE_FOREIGN_FUNCTION` and `ffi.fun`, `ffi.cif`, `ffi.closure`,
  `ffi.dlsym`. GC-owned foreign pointers with destructors use `GC_FFI_AUTO`
  (`src/ffi.c` `ffi_auto`, `src/gc.c`).
- **Macros.** These run at compile time in the same VM.
  - Token macros read `ty.token.peek/next` and raw characters through
    `ty.lex.peekc/getc`, and parse sub-expressions with `ty.parse.expr`.
  - `C!` (`lib/ffi.ty`) and `clap!` (`lib/clap.ty`) are the models to follow.
  - Expansions can embed runtime values with `$${v}` / `ty.Value(v)`, and can
    cast with `ty.Cast`.
- **Builtin registration.**
  - Annotate a C function with `// jit.foo(...) -> T` above
    `TY_BUILTIN(jit_foo)`, in a file listed in `GEN_SOURCES` (`Makefile:178`).
  - Add `"jit"` to `BuiltinSourceModules` (`src/compiler.c:368`) so that
    `lib/jit.ty` merges with the C builtins, the same way `ffi` does.
  - New `src/*.c` files are picked up by the Makefile wildcard. CMake lists its
    sources explicitly (`CMakeLists.txt:~355`).
- **GC.** Mark-sweep and non-moving. Embedded object pointers stay valid as long
  as they are marked.

## 4. Architecture

| Component | Contents |
|---|---|
| `lib/jit.ty` | `Asm`/`Reg`/`Mem`/`Label` classes, operators, Ty-value helpers, the `asm!` macro |
| `src/jitmod.c` | `jit.*` builtins: the handle-based builder API, `jit.layout`, `jit.rt`, `Fn`/`Code` |
| `src/jit.c` | bytecode → LIR (the ported bytecode JIT) |
| `include/lir.h` | the C contract shared by everything below |
| `src/lir.c` | builder, CFG, validator, serialization, entry-thunk generator |
| `src/lir_ra.c` | liveness, intervals, linear scan, spills, parallel moves |
| `src/lir_interp.c` | reference interpreter (test oracle and the `JIT_ARCH_NONE` backend) |
| `src/lir_emit.c` | arch dispatch, legalize driver, `dasm_*` link/encode, site and resume tables |
| `src/lir_arm64.dasc`, `src/lir_x64.dasc` | target description, legalization, templates |
| `src/jitmem.c` | code memory: region allocator with free lists, W^X, icache flush, perf map |

The dependencies:
- `lib/jit.ty` calls into `src/jitmod.c`.
- `src/jitmod.c` and `src/jit.c` both target `include/lir.h`.
- The `src/lir*.c` files and `src/jitmem.c` implement `include/lir.h`.

## 5. LIR specification

### 5.1 Value classes

Every register holds a value of one of these classes:

| Class | Width | Lives in | Notes |
|---|---|---|---|
| `I32` | 32 | GPR | Upper bits are undefined; narrow ops only |
| `I64` | 64 | GPR | The default integer class |
| `F32` | 32 | FPR | |
| `F64` | 64 | FPR | |
| `PTR` | 64 | GPR | Raw address; the GC ignores it |
| `REF` | 64 | GPR | GC object pointer; must be kept alive across `MAY_GC` calls (see 5.6) |

Signedness belongs to the operations, not to the registers.

**C types** appear only in signatures (`ccall`, function params/returns, and
memory access widths):
`i8 u8 i16 u16 i32 u32 i64 u64 f32 f64 bool ptr`, plus `val` (a 32-byte Ty
`Value`, always passed by pointer).
- Arguments arriving as narrow C types are extended to `I64` at entry.
- Narrow returns are truncated or extended as the ABI requires.

### 5.2 Operands and operations

**Operands:**
- `Reg` (a virtual register)
- `Imm` (an i64)
- `FImm` (an f64)
- `Mem{base: Reg, index: Reg | none, scale: 1|2|4|8, disp: i32}`
- `Label`
- `Const(Value)`: a Ty value rooted by the owning code object. It materializes
  as a `PTR` to a 32-byte copy that the code object owns.
- `RefConst(obj)`: rooted, materializes as a `REF`.

**Operations.** The destination comes first. Builders return a fresh
destination register unless a `*_to` form is used.

| Group | Ops |
|---|---|
| Moves | `MOV d,s` · `LI d,imm` · `FLI d,fimm` · `LEA d,mem` |
| Integer | `ADD SUB MUL MULHS MULHU SDIV UDIV SREM UREM AND OR XOR SHL SHR SAR ROTR` (d,a,b; b may be imm) · `NEG NOT CLZ CTZ POPCNT BSWAP` (d,a) · `SEXT8 SEXT16 SEXT32 ZEXT8 ZEXT16 ZEXT32` (d,a) |
| Checked | `ADDO SUBO MULO d,a,b,Lovf`: wraps and branches to `Lovf` on signed overflow |
| Float | `FADD FSUB FMUL FDIV FMIN FMAX` (d,a,b) · `FSQRT FABS FNEG` (d,a) · `FMA d,a,b,c` |
| Conversions | `I2F U2F F2I` (truncate toward zero; out of range or NaN gives an implementation-defined value and does not trap) · `FEXT FTRUNC` · `BITCAST` (I64↔F64, I32↔F32) |
| Memory | `LD.{i8,u8,i16,u16,i32,u32,i64,f32,f64} d,mem` · `ST.{8,16,32,64,f32,f64} mem,s` |
| Compare | `SETCC d,cc,a,b` · `FSETCC d,fcc,a,b` · `SELECT d,cc,a,b,x,y` · `FSELECT d,fcc,a,b,x,y` |
| Control | `BR cc,a,b,L` · `FBR fcc,a,b,L` · `BRZ a,L` · `BRNZ a,L` · `JMP L` · `SWITCH a,[L…],Ldefault` (jump table) · `RET [a]` |
| Calls | `CALL [d],target,args,sig,flags` · `TAILCALL target,args,sig` |
| Atomics | `CAS d,mem,expected,new` (returns the old value) · `XADD d,mem,v` · `XCHG d,mem,v` · `FENCE`. arm64 uses `ldaxr`/`stlxr` loops; no LSE requirement. |
| Frame | `ALLOCA d,size,align`: constant size, a frame slot, not dynamic |
| VM | `POLL` (interrupt/GC safepoint) · `SITE tag` (records the PC → tag mapping) · `ENTRY L` (an extra entry point; see 5.6) |
| Raw | `RAW {arm64: words \| x64: bytes}, in:{phys: Reg}, out:{phys: Reg}, clobber:[phys]` |

**Condition codes:**
- Integer `cc`: `EQ NE LT LE GT GE ULT ULE UGT UGE`.
- Float `fcc`: `FEQ FLT FLE FGT FGE` (ordered), `FNE` (unordered or not equal),
  `FUN` (unordered).

**Call targets:**
- a `PTR` register;
- an absolute address immediate;
- another LIR function (a direct call to its native body);
- a `jit.rt` helper (signature known).

`sig` lists the C types of the arguments and the return value, plus `nfixed`
for variadic calls. Apple arm64 passes variadic arguments on the stack; the ABI
table handles that.

**Call flags:**
- `MAY_GC`
- `MAY_THROW`
- `RETURNS_TWICE` (setjmp): every non-pinned register is treated as dead across
  the call, so nothing may be live in a register at that point. The validator
  enforces this.
- `NORETURN`
- `SITE(tag)`: also records a site at the return address.

### 5.3 Validator (runs in `finish`, before anything else)

The validator rejects a function with a `jit.Error` (Ty) or a `LirError` (C)
that carries the op index and, if attached, the source span. It rejects:

- a register used before it is defined on some path (iterative liveness: the
  live-in set at any entry contains something other than params and pinned
  registers);
- operand class mismatches (`FADD` on `I64`, `Mem.base` not `PTR`/`REF`, and
  so on);
- labels that are unbound or bound twice, and `SWITCH` with no targets;
- a `RET` that doesn't match the signature, or a non-`void` function where
  control can fall off the end;
- anything live across a `RETURNS_TWICE` call, and anything live into an
  `ENTRY` other than pinned registers;
- immediate ranges the legalizer can't materialize. Today that's only `SWITCH`
  tables larger than 64k.
- in **detached** mode (5.7): any `REF`, `Const`, `RefConst`, `POLL`, or call
  flagged `MAY_GC`.

### 5.4 Legalization (per arch, in `lir_<arch>.dasc`)

Legalization runs before register allocation and rewrites into target-legal
forms. Fixed-register needs are **explicit constraints**, never hidden
clobbers.

- **x64:**
  - two-operand form (tie `d` to `a`; reuse when `a` dies);
  - shift count in `cl`;
  - `idiv`/`div` in `rax`/`rdx`;
  - no mem→mem moves;
  - 64-bit immediates only through `mov r64, imm64`;
  - `SETCC` through `setcc` + `movzx`;
  - float constants from the per-function literal pool.
- **arm64:**
  - imm12 (optionally shifted) for add/sub/cmp, otherwise materialize the
    constant;
  - logical-immediate encodability for and/or/eor;
  - scaled `ldr` offsets versus `ldur` ±256, otherwise `add` into scratch;
  - `POPCNT` through `fmov`/`cnt`/`addv`;
  - `SREM` through `sdiv` + `msub`.
- **Both:**
  - fuse `SETCC`/`BR` pairs that compare the same operands;
  - fold `LEA`-shaped address arithmetic into `Mem` when the target can encode
    it.

### 5.5 Register allocation (`src/lir_ra.c`)

- Build the CFG from labels and branches, compute block liveness iteratively,
  then build live intervals. Registers are mutable (not SSA), so an interval
  covers every range where the register is live, including loop back-edges.
- Linear scan runs over the GPR and FPR pools from the target description.
  - When a value must be evicted, spill the interval with the furthest next
    use.
  - Spill slots live in a fixed-size frame area that the prologue allocates.
  - Split an interval at a call boundary when it would otherwise need a
    callee-saved register that is already in use.
- **Hints:**
  - tie two-operand destinations to their first operand when it dies;
  - prefer argument registers for values that flow straight into a call;
  - prefer callee-saved registers for intervals that span calls.
- **Call argument setup** is a parallel move with cycle breaking through the
  scratch register: `x16`/`x17` on arm64, `r11` on x64.
- **Caller-saved registers** that are live across a call are saved and restored
  around it automatically.
- **Pinned registers** are physical registers removed from the pool for the
  whole function. They are used by the bytecode JIT and by the entry thunks.
- **Target pools (excluding pinned and scratch):**
  - arm64: GPR `x0–x15, x19–x28` (`x18` is reserved on Apple, `x16`/`x17` are
    scratch, `x29`/`x30` are the frame); FPR `v0–v31` (`d8–d15` callee-saved,
    low 64 bits).
  - x64 SysV: GPR `rax rcx rdx rsi rdi r8 r9 r10 rbx r12–r15` (`r11` is
    scratch, `rbp` is the frame, `rsp`); FPR `xmm0–xmm15` (all caller-saved).
- **Compile-time budget:** see section 9 (acceptance).

### 5.6 Hooks the bytecode JIT needs (first-class LIR features)

- **Pinned registers.** `lir_pinned(L, LIR_PIN_n)` returns a register bound to a
  fixed callee-saved physical register named by the target description. On
  entry the pins come from parameters; the frame saves and restores them.
- **`ENTRY L`.** Additional entry points used for resume dispatch. Only pinned
  registers may be live into them. `lir_finish` returns their code offsets.
- **`SITE tag`, and `SITE` on calls.** These produce the `(pc, tag)` table that
  replaces `JitSite`.
- **The `*pc` protocol.** A function can mark one parameter as the pc-slot out
  parameter. The prologue then stores the address of the return-address slot
  into it (current behavior in `jit_emit_prologue`). On arm64, every `SITE`
  call goes through a per-code-object `runtime_call` thunk, so the slot is
  valid. This must keep `jit_frame_ip` working unchanged.
- **Global exits.** A shared epilogue that restores state and returns
  `JIT_PACK(reason, idx)`. Express it as an ordinary label plus `RET`; it needs
  no special op.
- **`POLL`.** Expands to the `JitInterruptFlag` check and a slow-path call to
  `vm_jit_handle_interrupt`. If that returns nonzero, the code branches to a
  label the caller supplies (deopt).

### 5.7 Execution modes for user functions

`finish` infers the mode. The user can force it with `mode:`.

- **Detached:** only scalars, `PTR` and non-`MAY_GC` calls are used.
  - The entry thunk releases the VM lock around the body (`UnlockTy`/`LockTy`,
    as in `ffi.call`).
  - No `POLL` is inserted, so long loops cannot be interrupted.
- **Attached:** anything else.
  - The VM lock is held for the whole call.
  - `POLL` is inserted automatically on every backward branch (a jump to a
    label bound earlier in emission order).
  - `REF` intervals that are live across `MAY_GC` calls are stored to GC-visible
    vslots before the call. The GC doesn't move objects, so no reload is
    needed.

**Vslots** are `Value` slots reserved on `ty->stack` by the entry thunk:
- The count comes from the maximum used, and the slots are zeroed.
- The thunk restores `ty->stack.count` on exit.
- When a `jit.rt` helper throws, the exception longjmps through native frames.
  That is safe because LIR frames have no cleanup to run, and the catch site
  restores the stack count.

### 5.8 Code objects, entry thunks and calling from Ty

`lir_finish` produces a `LirCode`. It contains:
- the native body;
- an optional **entry thunk** generated from the Ty-facing signature;
- the literal pool;
- the rooted values;
- the site and entry tables.

**User code** is allocated as GC kind `GC_JIT_CODE`:
- Its mark function marks every rooted `Value`.
- Its destructor returns the chunk to `jitmem`.

**Bytecode-JIT code** is permanent, as today.

**New value type `VALUE_JIT_FUNCTION`** with payload
`{ LirCode *code; void *entry; FunUserInfo *xinfo; }`. Handle it next to
`VALUE_FOREIGN_FUNCTION` everywhere that type is handled (show, type name,
equality, hashing, `DoCallEx`, `vm_call_ex` and siblings, the type checker's
runtime class mapping). Marking it marks `code`.

The **entry thunk** ABI is:

```c
typedef void JitEntry(Ty *ty, Value *out, Value const *args, i32 argc);
```

The thunk is itself LIR, generated by `lir_build_entry(sig)`. It:
1. checks `argc`, throwing through `jit_rt_arity_error`;
2. unboxes each argument with a type guard:
   - `Int` → `i*`/`u*`;
   - `Float` (or `Int`, converted) → `f*`;
   - `Bool` → `bool`;
   - `Ptr`/`Blob`/`String`/`nil` → `ptr`, with a fast path for `Ptr` and
     `Blob`, and anything else through `ptr_from_ty`;
   - `val` → a pointer into `args`;
   - on a guard failure it calls `jit_rt_arg_type_error`;
3. reserves vslots in attached mode, or unlocks in detached mode;
4. calls the body;
5. boxes the result into `*out`.

**Fast path from the bytecode JIT.** When the type checker statically knows a
callee is a `jit.Fn` (a `VALUE_JIT_FUNCTION` global or local whose type is a
`FuncType` with scalar params), the bytecode JIT calls the body directly with
unboxed registers. Use the existing `JIT_OPT_*` and `bc_try_*` patterns for
this, with a guard on the code pointer.

### 5.9 Code memory (`src/jitmem.c`)

Move the region code out of `src/jit.c` and replace the bump allocator:

- Keep the reservation scheme:
  - macOS: one `MAP_JIT` region with `pthread_jit_write_protect_np`
    bracketing, done per thread.
  - Linux: `memfd` with RW/RX views and the `atfork` handler.
  - Fallback: `mmap` + `mprotect` per chunk.
- **Allocator:** power-of-two size classes from 64 B to 64 KB with free lists;
  larger requests use first-fit over a free-extent list with coalescing. Guard
  it with the existing spin lock.
- **API:** `jm_alloc(size) -> {rw, rx}`, `jm_write_begin()`,
  `jm_write_end(rx, size)` (which flushes the icache), and `jm_free(rx)`.
- **Perf map:** `TY_JIT_PERF_MAP=1` appends `"%lx %zx %s\n"` lines to
  `/tmp/perf-<pid>.map` for every finished function, in both JITs. Bytecode
  functions use their Ty-qualified name; user functions use their `Asm` name.

### 5.10 Serialization

`lir_serialize(L) -> bytes` and `lir_deserialize(bytes, holes[]) -> Lir *`
form a compact, versioned encoding of a validated, un-legalized LIR function.
Hole operands are placeholders: `HOLE_IMM`, `HOLE_FIMM`, `HOLE_PTR`,
`HOLE_CONST`, `HOLE_CALLEE`, each with an index. They are filled in at
deserialize time, and filling them re-runs only the class checks that depend
on the holes. `asm!` uses this (see 6.3).

The C encoding uses `TYLR` plus a version number and unsigned varints;
signed integers use zigzag encoding and floating literals preserve their
IEEE bits. `LirBytes.holes` holds explicit input holes first, followed by
captured values and callees. `ninputs` separates the caller-owned input
bindings from captures owned by `LirBytes`. Captured `Value`s remain visible
to the owning handle's GC marker. The byte stream refers to these bindings
by index; it contains no hidden object or callee pointers. Deserialization
copies captured values into the new function's root pool.

## 6. Ty API

### 6.1 Module surface (`lib/jit.ty` + `src/jitmod.c`)

**Types, which are also the class tokens:** `jit.I8 … jit.U64`, `jit.F32`,
`jit.F64`, `jit.BOOL`, `jit.PTR`, `jit.REF`, `jit.VAL`, `jit.VOID`.

**Condition tokens:** `jit.EQ NE LT LE GT GE ULT ULE UGT UGE`,
`jit.FEQ FNE FLT FLE FGT FGE FUN`.

**`jit.Asm(name: String, params: Array[jit.Type], ret: jit.Type = jit.VOID, mode: ?String = nil)`**

| Member | What it does |
|---|---|
| `a.params` | `Array[jit.Reg]` |
| `a.reg(T, init = nil) -> Reg` | a fresh mutable register |
| `r.set(x)` | `MOV`/`LI` into `r` |
| `a.label() -> Label`, `a.bind(L)` | labels |
| `a.jmp(L)`, `a.br(cc, x, y, L)`, `a.brz(x, L)`, `a.brnz(x, L)`, `a.switch(x, Array[Label], default)` | control flow |
| `a.setcc(cc, x, y)`, `a.select(cc, x, y, then, other)` | compares and select |
| `p.at(T, i, disp: 0) -> Mem` | base + i·sizeof(T) + disp |
| `p.off(T, disp) -> Mem` | base + disp |
| `a.load(m) -> Reg`, `a.store(m, x)`, `a.lea(m) -> Reg` | memory |
| every op in 5.2 | a kebab-case method (`a.mulhu`, `a.clz`, `a.addo(x, y, L)`, `a.f2i`, `a.cas(m, e, n)`, `a.alloca(n, align: 8)`, `a.fence()`, …) |
| `a.ccall(target, args, ret: T = VOID, sig: ?Array[jit.Type] = nil, may-gc: false, may-throw: false)` | target is a `Reg`, `Int` address, `jit.Fn`, ffi foreign function (signature taken from its cif), or `jit.rt.*` |
| `a.tailcall(...)` | same targets as `ccall` |
| `a.ret(x = nil)` | return |
| `a.raw(arm64: ?Array[Int], x64: ?Blob, in: Dict[String, Reg], out: Dict[String, Reg], clobber: Array[String])` | the escape hatch |
| `a.const(v) -> Reg (PTR)`, `a.ref(obj) -> Reg (REF)` | rooted constants |
| `a.dump(stage: 'lir' \| 'legal' \| 'alloc') -> String` | inspection |
| `a.finish() -> jit.Fn` | validate and compile |

**Operators** are free functions in `lib/jit.ty` that emit into the operand's
`Asm`:
- `+ - * / % & | ^ << >>` on `Reg × (Reg | Int | Float)`.
- On integers, `/` and `%` are signed and `>>` is arithmetic. Unsigned variants
  are methods.
- Unary `-` is defined as well.

**`jit.Fn`** is callable. It also has:
- `.ptr`: the raw body address, usable as a C callback;
- `.code`: a `jit.Code`;
- `.name`;
- `.sig`.

**`jit.Code`** has:
- `.size`;
- `.dis() -> String`: Capstone through `ffi.dlopen` when it is available,
  otherwise a hex dump with site annotations;
- `.lir() -> String`.

**Other module members:**

| Member | What it is |
|---|---|
| `jit.ARCH` | `'arm64' \| 'x64' \| 'none'` |
| `jit.OS` | `'macos' \| 'linux' \| 'freebsd'` |
| `jit.interp(a: Asm) -> jit.Fn` | runs through the interpreter |
| `jit.Error` | the validation and legalization error class |

### 6.2 Ty-value layer (frozen ABI)

**`jit.layout`** holds constants:
- `VALUE_SIZE`, `OFF_TYPE`, `OFF_TAGS`, `OFF_Z`, `OFF_REAL`, `OFF_BOOL`,
  `OFF_PTR`, `OFF_CLASS`, `OFF_OBJECT`, `OFF_STR`, `OFF_BYTES`, `OFF_COUNT`,
  `OFF_ITEMS`;
- the `Array`, `Blob` and `Dict` header offsets (`items`, `count`,
  `capacity`);
- `TyObject` `OFF_SLOTS`;
- `jit.tag.{INT, FLOAT, BOOL, NIL, STRING, ARRAY, DICT, BLOB, TUPLE, OBJECT, PTR, FUNCTION, …}`
  mirroring `VALUE_*`.

**Builder helpers:**

| Helper | What it does |
|---|---|
| `a.vslot() -> Reg (PTR)` | a GC-visible `Value` slot; forces attached mode |
| `a.tag-of(v: Reg (PTR to Value)) -> Reg` | reads the type tag |
| `a.unbox(v, Int \| Float \| Bool \| Ptr \| Blob \| String \| Array, else: Label) -> Reg` | a guarded field load |
| `a.box(x, Int \| Float \| Bool \| Ptr, into: ?Reg = nil) -> Reg (PTR)` | writes into a vslot |
| `a.call-ty(f, args: Array[Reg]) -> Reg (PTR)` | args are PTRs to Values; calls through `jit_rt_call_value`; `MAY_GC \| MAY_THROW` |

**`jit.rt`** is a frozen catalog of helpers, each a `jit.rt.Helper` with a known
signature and flags. Most are thin renames of existing `jit_rt_*` helpers with
the convention `(Ty *, Value *out, Value const *a, Value const *b)`:
- `add sub mul div mod pow eq ne lt le gt ge cmp`
- `subscript subscript-set member member-set`
- `call call-method`
- `array-new array-push dict-new dict-get dict-set`
- `str-concat to-string hash`
- `throw`
- `alloc-object`
- `arity-error` and `arg-type-error`

Every one is `MAY_GC | MAY_THROW` except `eq ne lt le gt ge cmp hash`, which
are `MAY_THROW` only when they can dispatch to user operators. Document each
signature in `lib/jit.ty` with `///` doc comments; these are the only comments
allowed.

### 6.3 The `asm!` macro

Its shape is `asm! name(params) [-> type] [detached|attached] { body }`. It is
exported as `import jit (asm!)`. It reads the body as raw characters through
`ty.lex.getc`, as `clap!` does, so statements can end at a newline or `;`.

```
param   := ident ':' ctype
ctype   := i8|u8|i16|u16|i32|u32|i64|u64|f32|f64|bool|ptr|ref|val
stmt    := ident ':' ctype ['=' expr]
         | lval ('='|'+='|'-='|'*='|'/='|'%='|'&='|'|='|'^='|'<<='|'>>=') expr
         | 'if' expr block ['else' (block | stmt-if)]
         | 'while' expr block | 'loop' block | 'break' | 'continue'
         | ident ':'                         -- label
         | 'goto' ident
         | 'return' [expr]
         | expr                              -- call for effect
         | '.' mnemonic operand {',' operand} -- any LIR op verbatim
lval    := ident | ctype '[' addr ']'
expr    := C precedence and operators; unsigned via u-prefixed ops (u/ u% u< u<= u> u>= u>>)
         | ctype '[' addr ']'                -- load
         | expr 'as' ctype                   -- conversion
         | callee '(' args ')'
         | '{' ty-expr '}'                   -- hole
addr    := expr matched into base + index*scale + disp
callee  := hole | 'rt.' ident
```

**Holes.** A hole's Ty expression is parsed with `ty.parse.expr` and spliced
into the expansion, so it resolves at the call site. It is evaluated each time
the expansion runs. What the hole becomes depends on its runtime type:

| Hole value | Becomes |
|---|---|
| `Int` | an immediate |
| `Float` | a float immediate |
| `Bool` | `0`/`1` |
| `Ptr` | a pointer immediate |
| `jit.Fn`, ffi foreign function, `jit.rt.*` | a callee |
| any other value | `Const` |

**Expansion.** At Ty compile time the macro:
1. lowers the body to LIR;
2. validates it, reporting errors at Ty source spans;
3. serializes it.

It expands to roughly:

```ty
jit.load($${blob}, [hole-0, hole-1, ...]) as ((Ptr[Any], Int) -> Float)
```

The cast is the `FuncType` derived from the signature, using the same type ffi
uses for untyped pointers. Only the hole-dependent checks, legalization,
register allocation and emission run at runtime.

### 6.4 Examples (acceptance tests should include these)

Example 1: a polynomial unrolled at generation time.

```ty
import jit (Asm, F64)

pub fn make-poly(cs: Array[Float]) -> Float -> Float {
    let a = Asm('poly', params: [F64], ret: F64)
    let [x] = a.params
    let acc = a.reg(F64, 0.0)

    for cs.reverse() {
        acc.set(acc * x + it)
    }

    a.ret(acc)
    a.finish() as (Float -> Float)
}
```

Example 2: `asm!` with a hole that is a foreign function.

```ty
import jit (asm!)
import ffi as c

pub fn make-scale(k: Float) -> (Ptr[Any], Int) -> nil {
    asm! scale(p: ptr, n: i64) {
        i: i64 = 0
        while i < n {
            f64[p + i*8] = f64[p + i*8] * {k}
            i += 1
        }
    }
}

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

Example 3: a qsort comparator generated as a C callback.

```ty
let cmp = asm! cmp-i64(a: ptr, b: ptr) -> i32 detached {
    x: i64 = i64[a]
    y: i64 = i64[b]
    return ((x > y) - (x < y)) as i32
}

c.qsort(buf, n, 8, cmp.ptr)
```

## 7. Bytecode JIT port (`src/jit.c`)

The target end state:

**Emission.** `bc_emit` and its helpers emit LIR through `include/lir.h`. All
of these are deleted:
- `jit_emit_*`;
- `src/jit_{arm64,x64}.dasc` and their generated headers;
- the build rules for them;
- the `BC_S*`/`BC_A*`/`BC_CALL`/`BC_RET` defines.

**Pinned registers.** `BC_TY`, `BC_LOC`, `BC_ENV`, `BC_OPS` and the fp-offset
register (x24/rbp today) become LIR pins. The resume index is a parameter
that is only consumed by the dispatch `SWITCH` at entry. The pin is no longer
needed after that.

**Locals in registers.** The 2-slot raw cache and `BC_CACHE_MASK` go away.
Locals typed `Int` or `Float` that are used in loops (reuse the scoring in
`bc_plan_raw_cache`) are held in LIR registers. Each such register is written
back to its `Value` slot at every **observation point**:
- any call not flagged as reading no locals;
- `POLL` / deopt;
- yields;
- `SITE`s that can throw;
- function exit;
- edges into `ENTRY` blocks (a no-op, since only pins survive).

The write-back is statically placed, because LIR's liveness and the bytecode
CFG make validity known at compile time; validity is no longer tracked at
runtime. The register is reloaded after any call that can write locals:
captured-variable writes through `env`, and the debugger.

**Scratch values.** Every value that used `BC_S*` becomes a fresh LIR register.

**Constructs that keep their exact semantics:**
- resume dispatch, through `ENTRY` + `SWITCH`;
- `try`, through a `RETURNS_TWICE` call to `_setjmp`;
- `JitSite`/`jit_frame_ip`, through `SITE` and the `*pc` protocol;
- deopt, through `POLL` with a deopt label and `bc_deopt_info` unchanged;
- the `JIT_PACK` return protocol;
- `__jit__`/`must_jit`;
- `TY_JIT_AUDIT`;
- `jit_stats_report`;
- the `TY_JIT_NO_*` kill switches. Remove `TY_JIT_NO_RAW_CACHE`; make
  `TY_JIT_NO_REGISTERIZE` disable keeping locals in registers.

**Limits.** `MAX_BC_LABELS` and the operand-depth limits are removed or raised
wherever they existed only because of DynASM PC-label preallocation. LIR
labels grow dynamically.

**Debug dumps.** `TY_JIT_DUMP=<regex>` dumps the LIR stages for matching
functions (bytecode and user) to stderr.

## 8. Work breakdown

Workstreams can run in parallel once **WS0** lands. File ownership is
exclusive; coordinate through `include/lir.h`.

| WS | Owner files | Depends on | Deliverable |
|---|---|---|---|
| **WS0** Contract | `include/lir.h` | — | The entire C API from section 5 as declarations, the `LIR_OPS` X-macro with operand signatures, the `LirSig`/`LirMem`/`LirOpnd` structs, flags, and the target-description struct. Land this first and keep it small. |
| **WS1** Core | `src/lir.c` | WS0 | Builder, CFG, validator, serialization with holes, `lir_build_entry` |
| **WS2** RA | `src/lir_ra.c` | WS0 | Liveness, intervals, linear scan with spilling and hints, parallel moves, vslot spilling of `REF`s |
| **WS3a** arm64 | `src/lir_arm64.dasc`, `src/lir_emit.c` (shared with WS3b) | WS0 | Target description (pools, pins, ABI for AAPCS64 and Apple), legalizer, templates, frame/prologue/`*pc` protocol, `runtime_call` thunk |
| **WS3b** x64 | `src/lir_x64.dasc` | WS0 | The same for SysV x64 |
| **WS4** Interp + fuzz | `src/lir_interp.c`, `tests/lir_*.ty` | WS0, WS1 | Reference interpreter (libffi for `CALL`; `RAW` unsupported) and a differential fuzzer |
| **WS5** Memory + values | `src/jitmem.c`, `include/ty.h`, `src/gc.c`, `src/value.c`, `src/vm.c` (call sites only) | WS0 | `jitmem` with free lists, `GC_JIT_CODE`, `VALUE_JIT_FUNCTION`, VM dispatch, perf map |
| **WS6** Ty module | `src/jitmod.c`, `lib/jit.ty`, `src/compiler.c` (`BuiltinSourceModules` only), `Makefile` `GEN_SOURCES`, `CMakeLists.txt` | WS1, WS5 | Builder API, operators, `jit.layout`/`jit.tag`/`jit.rt`, `Fn`/`Code`, `dis`, `interp` |
| **WS7** `asm!` | `lib/jit.ty` (macro section) | WS6 (API), WS1 (serialization) | Parser, lowering, compile-time validation with spans, typed expansion |
| **WS8** BC port | `src/jit.c`, `include/jit.h`, dasc build rules in `Makefile`/`CMakeLists.txt` | WS1, WS2, WS3a/b, WS5 | Everything in section 7, plus the direct-call fast path into `jit.Fn` |

**Integration order** for the final merge: WS0 → (WS1, WS2, WS3a, WS3b, WS4,
WS5) → WS6 → WS7 → WS8. WS8 can develop against the LIR interfaces in parallel
and only needs the backends working in order to test.

## 9. Acceptance criteria

**Correctness:**
- `./ty --test tests` passes with and without `-j` on macOS arm64. This
  includes every existing `tests/jit_*.ty`.
- New tests cover:
  - every LIR op;
  - the validator's error cases;
  - spilling under register pressure (more than 40 simultaneously live
    registers, both classes);
  - calls with 0–12 arguments of mixed classes, including variadics;
  - `RETURNS_TWICE`;
  - `ENTRY`;
  - detached versus attached mode;
  - vslot rooting under forced GC (`gc()` from a `call-ty` callback);
  - exceptions thrown through native frames;
  - code freed after drop plus `gc()` (assert through a `jitmem` stats
    builtin);
  - every example in 6.4.
- The differential fuzzer (interpreter versus native) runs 2,000 random
  programs per test-suite run with a fixed seed. `TY_LIR_FUZZ=N` runs more.
  Zero mismatches. `F2I` on out-of-range values is excluded.

**Performance** (measure with `typrof` and `hyperfine`, using `bench/*.ty` as the
benchmark set):
- Runtime does not regress more than 3% on any benchmark; the geometric mean is
  equal or better.
- Total bytecode JIT compile time over the test suite (`jit_total_compile_ns`)
  is at most 1.5× today's.
- User `finish()` for a 100-op function is under 50 µs on an M2.

**Cleanliness:**
- No `jit_emit_*`, `jit_{arm64,x64}.dasc`, `BC_CACHE_MASK`, `JitRegionUsed`
  bump pointer, or `jit_free` TODO remains.
- Code follows `AGENTS.md`: C style, Ty style, no comments except `///` docs
  in `lib/jit.ty`.

## 10. Docs

- Add `doc/intro/11-jit.md`: the builder, `asm!`, modes, `jit.layout`/`jit.rt`,
  debugging (`dump`, `dis`, `TY_JIT_DUMP`, `TY_JIT_PERF_MAP`).
- Remove this file's "Background" section once the work lands. Keep the rest as
  the LIR reference.
