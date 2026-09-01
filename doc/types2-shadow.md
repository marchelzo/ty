# types2 shadow mode

`src/types2.c` is the independent replacement typechecker's integration
boundary.  It is intentionally non-authoritative: the compiler continues to
use only `src/types.c` for diagnostics, inferred types, emitted code, JIT
guidance, reflection, exit status, and runtime behavior.

The shadow pass is enabled by default and runs native declaration and
expression inference at the same declaration, statement, and class-operator
checkpoints as the legacy checker.  Results live in an AST-keyed side table;
they are never written to `Expr._type`, symbols, classes, bytecode, or JIT
state.  The shadow owns its allocations and is abandoned if legacy checking
exits early.

The compiler-independent core in `src/types2_core.c` provides the first native
types2 representation and solver layer.  It currently includes hash-consed
immutable terms, canonical unions/intersections, distinct gradual sentinels,
strict subtype and gradual-consistency relations, nominal variance (invariant
by default), lower/upper-bound metavariables, subtype-edge wakeups, retained
term-backed deferred obligations, row and pack metavariables, weak variables,
guarded recursive terms, progress-aware coinductive comparisons, and
rollbackable solver transactions.  Equality roots use ranked union-find with
path compression; subtype inference retains lower and upper bounds instead of
binding a variable to the first incoming type.  The core is allocated per
shadow compilation and is the only type universe consumed by types2 expression
inference.  Legacy compilation does not consume its answers.

The core also has canonical computed-type promises, a single-result memo
contract, and an opaque solver-free type snapshot.  These are dormant adapter
boundaries for computed types, reflection, and JIT facts.  A shadow pass never
executes a type function a second time.  It may import an already materialized,
concrete computed result through a narrow read-only adapter; unresolved or
solver-dependent legacy results remain native computed promises and are
reported as deferred.  Ordinary inference is never seeded from a legacy type.
The JIT boundary currently exposes only conservative runtime-shape facts (for
example, exact `Int`, nullable `Int`, function, record, or one nominal symbol)
and is not connected to code generation.  The finish event reports how many
inferred nodes have such a fact as `runtime_fact_nodes`.

Native shadow inference currently covers literals and contextual mutable
literals, functions and complete call shapes, overload transactions, retained
member/operator/subscript predicates, nominal hierarchy and variance,
trait/override validation, exact tuples, heterogeneous and repeated packs,
strict subscript reads and writes, generator call effects, and conservative
flow invalidation.  Compound assignments, unary operators, membership, ranges,
defaults, and writable subscript/member targets are checked against the same
native protocols used for their ordinary expression forms.  Built-in runtime
methods are supplied as native contracts rather than imported legacy answers;
the current native interfaces include the callable top, strings, arrays, and
dictionaries needed by the standard-library corpus.

Nominal declarations import only stable compiler facts: class identity,
declared parameters, superclasses, and traits.  Supertype templates preserve
generic arguments, and member instantiation projects a concrete receiver
through that hierarchy before applying its immutable scheme.  Constructors are
inherited independently of instance-method subtyping.  Private members are
class-local and do not participate in public override or trait conformance;
ordinary methods still require full call-shape-compatible overrides.  Generic
parameters are invariant unless their nominal declaration has validated
variance metadata.

Function bounds are installed as scoped upper-bound assumptions for operations
inside the body and as immutable scheme predicates for later calls.  Several
bounds on one variable are combined rather than overwritten.  Receiver
substitution and scheme predicates enter one call-local solver, so obligations
wake after receiver arguments become known.  A failed candidate, failed view
call, or failed protocol probe cancels only obligations created by that trial.
Any active obligation left at the end of a compilation unit is retained in the
log and also reported as a source-located `unresolved-constraint` error; it is
never silently discarded by normalization.

Structural records use native rows and presence information.  Record spreads
preserve known fields and open row tails, including through generic copy
functions; record destructuring jointly filters union arms.  Dictionary
spreads accept both `Dict` values and structural records, converting known row
field names to `String` keys and conservatively accounting for open tails.
Positional call splats expand exact tuples and retain non-fixed iterables as
pack expansions.  A pack parameter can precede keyword-only parameters without
losing the keyword call shape.  Mapped pack expansions such as
`...Iterable[U]` project every actual nominal argument through `Iterable`, then
solve `U` as a heterogeneous sequence.  Consequently a call with
`Array[Int]` and `Array[String]` can preserve the result sequence `(Int,
String)` rather than collapsing it to one element type or leaking a deferred
constraint.  Unsupported pack placement and generic arity are diagnosed
explicitly.

Pattern inference distinguishes irrefutable destructuring from refutable
matching.  Refutable tuple patterns do not constrain their subject merely by
being tried, array and dictionary patterns filter union arms, class patterns
narrow the subject before extracting members, and custom `use match` values
are checked through their native callable schemes.  Resolved class annotations
remain distinct from value guards, and a not-nil view pattern narrows its input
before invoking the view.  Refutable payloads from a still-open runtime subject
are Dynamic rather than disconnected inference variables.  Named structural
aliases participate in pattern narrowing and exhaustiveness, source-order arm
coverage is preserved, and a runtime type-union expression produces a native
type value instead of borrowing its legacy `Type` graph.

Fixed tuples require exact arity.  Structural records separately track field
presence, writability, exactness, and row tails.  Optional reads include `nil`,
writable fields are invariant, and row-preserving generic functions retain
unmentioned fields and their correlations.  Refutable record patterns combine
compatible evidence from reachable union arms without turning literal fields
into optional fields.

Set `TY_TYPES2_LOG` to a file path to append JSON Lines progress events.  The
special values `stderr`, `-`, and `1` write them to standard error.  With the
variable unset, shadow mode emits no output.  `TY_TYPES2_SHADOW=0` disables the
pass for behavioral-equivalence tests; it does not select alternate language
semantics.

Set `TY_TYPES2_TRACE_NODES=1` together with `TY_TYPES2_LOG` to add a `node_type`
event for every inferred side-table entry.  This is intended for focused
debugging and can make logs much larger.  These events also include the dormant
runtime-shape fact when one can be computed.

Run the permanent smoke/equivalence check after building with:

```sh
tests/types2-shadow-equivalence.sh ./ty
make test-types2-core
```

This interface must remain one-way.  Code in `types2` may observe resolved
syntax and read-only compiler facts.  The only legacy-type translation is the
explicit materialized-computed-result boundary described above.  Legacy typing
and code generation must never inspect a shadow result before the atomic
cutover.

## Initial overhead baseline

On revision `a5746a3`, the `gcc-ninja` build compiling the small equivalence
fixture measured 53.5 ms with shadowing disabled and 56.7 ms with it enabled
(10 warm runs each, roughly 6% overhead).  Peak RSS was indistinguishable at
about 74 MiB in three runs.  These numbers are an early smoke baseline, not a
budget for later inference milestones.

## Project status at this handoff

The replacement is well beyond the inert-observer stage, but it is still a
shadow checker. It has an independent type universe, solver, environments,
side tables, native-interface model, diagnostics, and structured counters. It
can traverse the current startup corpus without reporting an unsupported AST
node, and the core unit suite exercises the principal representation choices
from the audit. None of that changes the authority boundary described above.

The last known clean validation run used an ASan build and produced:

- `test.ty`: 77/77 tests passed;
- the types2 core unit suite: passed;
- shadow-on/shadow-off equivalence: passed;
- the startup/prelude corpus: 16 observed units, 0 unsupported nodes, 3,106
  deferred nodes, and 2 pending terminal obligations;
- 126 raw types2 diagnostic events: 119 errors and 7 warnings, reducing to 122
  unique `(file, line, column, code)` diagnostics.

This snapshot was taken on 2026-09-01 from the working tree descended from the
audited revision `a5746a3`. It is a navigation aid, not an acceptance baseline:
the corpus command only loads the normal startup modules, not every module under
`lib/`, and many reported differences are not yet classified.

The most common diagnostic codes in that snapshot were:

| Code | Count | First question to answer |
|---|---:|---|
| `generic-arity` | 17 | Is the declaration genuinely malformed, or has native generic metadata not been imported completely? |
| `bad-call` | 13 | Is the call invalid under the intended complete call-shape rules, or is the callee interface incomplete? |
| `union-method-coverage` | 12 | Does every reachable union arm really need the method, or is prior narrowing missing? |
| `union-member-coverage` | 10 | Is this a real unsafe field access, an optional access, or a lost row/refinement fact? |
| `missing-field` | 9 | Is the field absent, or missing from the types2 native/class interface? |
| `not-callable` | 7 | Is this a real dynamic boundary, an overload-set issue, or an incomplete imported declaration? |
| `invalid-trait-member` | 7 | Does the implementation violate the trait, or is trait member lowering incomplete? |
| `invalid-override` | 6 | Is the complete call protocol incompatible, or is inherited metadata incomplete? |
| `union-operator-coverage` | 6 | Is a reachable operand pair unsupported, or should control flow have removed it? |

The largest unit-level hot spots were:

| Unit | Errors | Warnings | Deferred | Pending obligations |
|---|---:|---:|---:|---:|
| `prelude` | 63 | 1 | 793 | 2 |
| `ffi` | 2 | 0 | 502 | 0 |
| `unibilium` | 5 | 0 | 389 | 0 |
| `term` | 15 | 4 | 306 | 0 |
| `path` | 3 | 1 | 265 | 0 |
| `readln` | 18 | 0 | 202 | 0 |
| `chalk` | 4 | 1 | 171 | 0 |

These numbers help locate clusters, but they have the same caveat as the global
totals: one incomplete shared interface can create many downstream events.

Do not optimize for reducing these numbers mechanically. In particular, do not
replace an unexplained result with `Dynamic` merely to remove a diagnostic.
Each difference must be classified against the intended semantics in
`type_system.md` and, where relevant, runtime behavior.

The two retained terminal obligations currently come from the known `Dict`
runtime-type predicate around `lib/prelude.ty:1030`. It iterates `x.keys()` and
then reads `p.0` and `p.1` as though each value were a key/value pair. Types2 now
keeps and reports those failed subscript obligations instead of erasing them.
The likely library repair is to iterate items, but that change needs its own
runtime and static regression test because it changes library behavior rather
than shadow infrastructure.

## What is implemented, and what still needs proof

The table below distinguishes the existence of an implementation from cutover
readiness. “Implemented” means the mechanism exists and has focused tests; it
does not mean the full language and library corpus has validated it.

| Area | Present in types2 | Work still required before cutover |
|---|---|---|
| Immutable type terms and solver metas | Canonical terms; separate flexible, rigid, quantified, weak, row, and pack variables; equality union-find; lower/upper bounds; subtype edges; watchers; provenance | Stress incremental propagation, verify all public entry points preserve immutability, add peak-state/resource diagnostics, and prove independence from legacy metavariable answers |
| Core relations | Separate equality, subtyping, consistency, join, meet, narrowing, and normalization paths | Expand algebraic/property tests, cover all nominal/row/pack/recursive combinations, and turn resource exhaustion into a stable complexity diagnostic |
| Transactions | Solver marks and rollback are used by overload, match-view, and other speculative paths | Add integration-level leak tests for every candidate kind and verify failure leaves types, obligations, refinements, and diagnostics unchanged |
| Functions and overloads | Full call-shape representation, defaults, positional/keyword arguments, rest parameters, overload trials, lazy union coverage | Finish keyword-row inference, audit every native callable signature, measure pathological union/overload scaling, and stabilize per-candidate diagnostics |
| Schemes and constraints | Generalization/instantiation, weak metas, immutable obligations, scoped and terminal diagnosis, receiver-dependent wakeups | Validate environment free-variable subtraction across all capture forms, exercise constraints through methods/overloads/packs, and classify every unresolved corpus obligation |
| Nominal types | Independent class/interface table, inheritance, constructors, traits, overrides, private-member handling | Complete native and imported interfaces, decide how source variance is declared, validate declared variance against the complete public member contract, and run a full class/trait library matrix |
| Variance and mutation | Invariant-by-default nominal arguments; explicit covariance exists for known readonly producers and tags; occurrence validation exists in the core | Specify/import surface variance metadata, audit every mutable standard-library type, add readonly interfaces where covariance is wanted, and test aliasing writes end to end |
| Records and tuples | Row/presence representation, exact tuples, writable-field checks, row preservation, tuple/record patterns | Finish tuple-expression spreads, distinguish all required/optional/absent paths in the library, validate mutation through aliases, and add large-row performance tests |
| Packs | Heterogeneous and repeated packs, mapped-pack expansion, placement and arity diagnostics | Finish sequence constraints for all call/keyword-spread forms, cover empty/prefix/suffix cases, and audit standard-library zip/unzip/transpose/thread helpers |
| Operations | Union-wide calls/members/operators; subscript reads and writes; compound assignments; unary/count/range/default checks | Remove incomplete nominal/operator fallbacks, make native contracts match runtime dispatch, and classify intentional Dynamic operations separately from missing implementations |
| Flow and control outcomes | Local/path refinement, invalidation across effects, return/fallthrough tracking, match reachability and coverage | Complete effect boundaries for getters, aliases, captures, await/yield and unknown calls; validate loops and partial matches on generated control-flow cases |
| Recursive types | Guarded recursive core terms, occurs rejection, progress-aware coinductive relation support | Complete declaration-level alias SCC validation, add mutually recursive integration fixtures, and verify every depth/resource limit fails diagnostically rather than proving a relation |
| Computed types | Native computed promises and read-only import of an already materialized concrete result | Build the single-evaluation broker, define caching/dependency rules, handle invalid/nonterminating computations, and prove no macro, VM callback, or FFI operation runs twice |
| Reflection and consumers | Canonical printers, snapshots, and dormant runtime/JIT fact structures | Implement dormant `typeof`, type-value, `ty.types`, reflection round-trip, and JIT adapters for every public constructor without exposing them before cutover |
| Diagnostics and telemetry | JSON-lines events, source locations, provenance, candidate/union/solver counters | Add stable snapshots, deduplication/classification tooling, deferred-reason counts, phase timers, peak state and memory, and user-quality messages without raw internal metas |

## The major remaining workstreams

### 1. Specify the final semantic contract

The implementation should not become authoritative while fundamental names
still inherit their meaning accidentally from legacy representation details.
Write executable examples and user documentation for:

- `Never`, `Unknown`, `Dynamic`, `Any`, `Object`, `Error`, and the absence of a
  type;
- underscore annotations, including whether underscore is the surface spelling
  of `Dynamic`;
- strict subtyping versus gradual consistency;
- unchecked `as T`, including the important rule that the operand is still
  checked normally and only the conversion is asserted;
- ordinary member access versus safe `.?` access;
- static type tests versus runtime `::`, which remains a general matcher;
- nil and pointers;
- partial indexing, matching, and other throwing operations;
- rank-1 polymorphism as the initial supported boundary;
- the meaning of `-q` and whether it should eventually be exposed more clearly
  as `--no-typecheck`.

These decisions belong in checked-in fixtures as well as prose. The expected
types2 result, not legacy behavior for known defects, is the oracle.

### 2. Split “deferred” into actionable reasons

`deferred_nodes` is presently too broad to use as a readiness metric. It mixes
valid runtime escape hatches with missing checker coverage. Introduce a stable
reason enum and emit per-reason counts, with an optional event at the affected
source location. At minimum distinguish:

- deliberate `Dynamic` elimination or runtime-only constructs;
- incomplete native/class interface information;
- unresolved import, nominal, tag, or custom pattern information;
- unknown-arity positional spread;
- keyword dictionary spread awaiting keyword-row inference;
- tuple-expression spread;
- computed/compile-time work awaiting the single-evaluation broker;
- type-level `typeof` whose operand has no types2 result;
- dynamic member or method names;
- unsupported operator protocol or operator value construction;
- template, hole, and pack-fold expression variants;
- macros and type-setting statements;
- hierarchy or bound syntax that could not be lowered;
- internal recovery after an earlier types2 failure.

Some constructs such as `unsafe`, `eval`, trace/context values, and genuinely
dynamic calls may remain intentionally dynamic forever. Give them an explicit
reason such as `runtime-dynamic`; do not count them as unfinished. Conversely,
an incomplete interface or tuple spread must not disappear into that category.
The cutover gate is zero unclassified/incomplete deferrals on the supported
corpus, not necessarily zero total deferrals.

### 3. Build a reproducible differential-validation corpus

The current startup run is useful but insufficient. Add a checked-in driver
that runs:

- the repository test suite;
- every supported module under `lib/`, with an explicit list of platform-only
  exclusions;
- all focused types2 positive and negative fixtures;
- real scripts and representative applications;
- generated union, overload, row, pack, constraint, recursion, flow, and
  mutation stress cases;
- programs that legacy rejects before the normal shadow pass finishes, through
  a types2-only test driver.

Normalize each difference by stable unit, source location, construct, and
diagnostic code. Store its expected classification next to the test:

- agreement;
- expected types2 correction;
- known bad standard-library declaration or implementation;
- intentional Dynamic/runtime boundary;
- incomplete types2 feature;
- unexplained divergence.

The comparison code must remain outside inference. Types2 may be compared with
the legacy answer after both complete, but it must never read a legacy inferred
type to decide its own result. A test mode should perturb or suppress legacy
type answers and prove that types2 output remains unchanged.

### 4. Finish language and native-interface coverage

After deferred reasons exist, work down the genuinely incomplete categories.
The likely highest-value items are:

1. complete native member, method, operator, subscript, constructor, trait, and
   inheritance descriptions;
2. tuple-expression spread inference;
3. keyword-row inference for nonliteral and generic keyword spreads;
4. the remaining template, hole, pack-fold, operator-value, custom matcher, and
   type-setting forms;
5. declaration-level guarded alias SCC checking and diagnostics;
6. complete source variance import and validation;
7. call/effect summaries needed to retain only sound flow refinements.

For every item, add a positive fixture, a negative fixture, a canonical inferred
type assertion, and—where speculation is involved—a rollback assertion. Avoid
feature-specific fallback to legacy inference.

### 5. Reconcile standard-library contracts

The standard library is part of the type-system specification. Run it as a
first-class conformance suite and resolve at least these audit findings:

- repair and test the `Dict` runtime-type predicate near
  `lib/prelude.ty:1030`;
- keep mutable `Array`, `Dict`, queues, pointers/references, futures, and
  user-defined mutable containers invariant; introduce readonly producer
  interfaces when covariance is useful;
- decide whether missing/out-of-range `Dict`, `String`, `Array`, and tuple
  indexing returns an optional result or is an explicitly throwing operation,
  then make declarations and documentation agree;
- make optional record reads yield a presence-aware result and repair callers
  that relied on the old overpromise;
- restrict iteration to generators whose send type admits nil, or split the
  iterator and coroutine interfaces;
- validate `ThreadPool.submit`, `Future`, and related pack/result constraints;
- replace SQLite result-only generic promises with an explicit decoder, schema
  witness, dynamic row, or visible cast;
- resolve conflicting `os.listdir` declarations;
- test `Array.sum`, depth-sensitive flattening, zip/unzip/transpose, dictionary
  mapping, and tuple arity against runtime behavior;
- update the previously observed `llhttp`/`http` and platform-module failures
  from a fresh full-library matrix rather than assuming the audit list is still
  exhaustive.

Library repairs can change observable legacy behavior. Keep them as reviewable
changes with runtime tests; do not hide them inside a shadow-checker refactor.

### 6. Broker computed types exactly once

Types2 must not independently execute a type macro, VM callback, FFI call, or
other compile-time computation. The remaining design needs one compiler-owned
evaluation broker:

1. assign the computation a stable identity and canonical argument snapshot;
2. evaluate it once in the existing compile-time phase;
3. validate and freeze the result;
4. expose read-only native snapshots to both checkers;
5. memoize according to explicit purity/dependency rules;
6. report invalid results, recursion, fuel exhaustion, and side effects without
   mutating a speculative solver transaction.

Until this exists, a computed node should remain explicitly deferred. Reusing
an already materialized concrete result is allowed; copying legacy metavariable
solutions or executing the computation again is not.

### 7. Complete dormant output adapters

Before cutover, implement but do not activate adapters for:

- expression and symbol types;
- `typeof` display;
- type values and every operation in `ty.types`;
- encoder/decoder round trips for every public type constructor;
- class/type metadata exposed at runtime;
- JIT guidance and any bytecode specialization facts.

Round-trip tests should enforce
`decode(encode(T)) == normalize(T)`. Internal solver metas that cannot be
reified must produce an explicit error rather than nil or a dynamic-looking
placeholder. The adapters remain dormant until the atomic cutover; ordinary
shadow runs must continue to expose legacy results only.

### 8. Harden diagnostics and resource behavior

Candidate failures should retain their own provenance without leaking solver
state. A final diagnostic should explain lower and upper bounds, missing union
coverage, row presence, writable invariance, call-shape incompatibility, or the
specific unsatisfied obligation in source terms. It should not display an
unexplained `$m42` unless a debug log was requested.

Add lightweight telemetry for:

- phase time;
- candidate trials and rollback counts;
- union splits and covered arms/pairs;
- canonical term count and cache hit rate;
- active and peak solver roots, subtype edges, watchers, and obligations;
- work-queue wakeups;
- computed-type broker evaluations/cache hits;
- deferred counts by reason;
- peak resident memory.

Resource exhaustion must result in a deterministic complexity diagnostic. It
must never return success from subtype checking or silently produce `Dynamic`.

### 9. Establish performance budgets

Use the release CMake build for performance work:

```sh
cmake --build --preset gcc-ninja
_install/gcc-ninja/bin/ty --version
```

Measure shadow-off, shadow-on without logging, and shadow-on with structured
logging separately. Re-run the audit workloads for Cartesian union arguments,
growing overload sets, reverse-ordered structural unions, large records,
reverse dependency chains, generic instantiation, mapped packs, and recursive
types. Verify the intended shapes, not just one absolute time:

- candidate-first overload checking does not materialize the full Cartesian
  product;
- overload construction is batched and normalized once;
- union and intersection lookup is canonical/indexed rather than quadratic;
- fixed-record field lookup is indexed;
- obligations wake through dependencies rather than whole-list rescans;
- instantiation memoizes source nodes;
- no global “fuel exhausted means true” path exists.

Agree on wall-time and peak-memory budgets before cutover. The historical
observer-only baseline is not representative of the current active checker and
should not be used as the target.

## Immediate next steps

The next work session should proceed in this order.

### Step 1: reproduce and archive the current baseline

Start from a fresh ASan build and run the permanent gates:

```sh
make clean && CC=clang make -j10 DEBUG=1
ASAN_OPTIONS=intercept_strndup=0:detect_leaks=0 \
    CC=clang make test-types2-core DEBUG=1
ASAN_OPTIONS=intercept_strndup=0:detect_leaks=0 \
    ./tests/types2-shadow-equivalence.sh ./ty
ASAN_OPTIONS=intercept_strndup=0:detect_leaks=0 ./ty test.ty
```

Then create a fresh log. `TY_TYPES2_LOG` appends, so never reuse an old path:

```sh
types2_log=$(mktemp /tmp/types2-shadow.XXXXXX.jsonl)
ASAN_OPTIONS=intercept_strndup=0:detect_leaks=0 \
    TY_TYPES2_LOG="$types2_log" ./ty -c -e nil
echo "$types2_log"
```

Record the revision, compiler, build flags, command, exit status, finish-event
totals, and unique diagnostic keys. Do not commit a host-specific `/tmp` path.

### Step 2: replace the scalar deferred counter with reasoned telemetry

Add one enum and one accounting function rather than incrementing
`shadow->deferred_nodes` directly throughout `src/types2.c`. Keep a total for
compatibility, add per-reason totals to the finish event, and optionally emit
location-bearing detail events under a verbose logging switch. Update the
equivalence fixture to assert that logging remains the only observable change.

Acceptance for this step:

- every deferral site has a named reason;
- reasons are divided into intentional runtime boundaries, incomplete features,
  missing external facts, and recovery;
- the startup corpus has zero unclassified deferrals;
- no reason is selected solely to suppress a diagnostic;
- shadow-on/off stdout, stderr, status, and runtime behavior remain identical.

### Step 3: add a checked-in corpus summary and classifier

Create a small test/tooling script that consumes JSON lines, deduplicates stable
diagnostic identities, totals deferred reasons and solver counters, and compares
the result with a checked-in classification file. It should reject malformed
events and unknown classifications. Avoid using textual rendered types as the
only identity; include canonical structural hashes where available.

Seed the classifier with the current high-volume groups, then examine each one
against source and runtime behavior. The 122 unique diagnostics are the initial
triage queue, not expected permanent failures.

### Step 4: resolve the known terminal obligation

Write a focused test for the `Dict` runtime-type predicate, verify the actual
shape produced by `keys()` and `items()`, and repair `lib/prelude.ty:1030` if the
audit diagnosis is confirmed. Assert both runtime matching and the types2
obligation log. After the repair, the startup corpus should finish with no
pending terminal obligation unless a newly discovered real error is documented.

### Step 5: implement the largest incomplete deferred categories

Use the reasoned counts rather than guesswork. Start with incomplete native
interfaces, tuple spreads, and keyword rows because they affect many downstream
call/member errors. For each category, add fixtures before changing inference,
and confirm transactional rollback and canonical inferred types afterward.

### Step 6: add the full library matrix and types2-only driver

The library matrix should identify supported versus platform-excluded modules
explicitly. The types2-only driver is for compile-pass cases that legacy rejects
too early to reach a normal shadow checkpoint; it is not a semantic switch for
the interpreter and must not emit or execute code based on types2 results.

### Step 7: implement the computed broker and dormant consumers

Only after ordinary coverage and differential classification are stable should
the work cross the compile-time/runtime fact boundary. Build single evaluation
first, then reflection/`typeof`, then JIT facts. Keep all consumers dormant until
the cutover gate is satisfied.

### Step 8: stabilize diagnostics and run performance gates

Snapshot user-facing diagnostics, add complexity errors and peak counters, then
measure the release build on the audit stress corpus. Performance work before
deferred classification risks optimizing fallback paths that should instead be
deleted.

## Routine validation while developing

Use the narrowest relevant test while editing, then finish every material change
with the permanent gates above. Useful focused commands include:

```sh
# Core representation and solver only.
ASAN_OPTIONS=intercept_strndup=0:detect_leaks=0 \
    CC=clang make test-types2-core DEBUG=1

# Prove the shadow checker cannot alter ordinary behavior.
ASAN_OPTIONS=intercept_strndup=0:detect_leaks=0 \
    ./tests/types2-shadow-equivalence.sh ./ty

# Inspect a single fixture's events without contaminating stderr.
types2_log=$(mktemp /tmp/types2-fixture.XXXXXX.jsonl)
ASAN_OPTIONS=intercept_strndup=0:detect_leaks=0 \
    TY_TYPES2_LOG="$types2_log" \
    ./ty -c tests/fixtures/types2-shadow-valid.ty.txt
```

Use `git diff --check` before handing off. Also confirm that no accidental edit
to `src/types.c` is present:

```sh
git diff --check
git diff -- src/types.c
```

When ASan overhead obscures a scaling problem, use `make clean && make -j10`
for a debug-symbol build. Use the CMake preset, not the Makefile build, for final
interpreter performance measurements.

## Architectural invariants to preserve

These rules are stronger than implementation preferences. A change that breaks
one of them undermines the replacement strategy even if its local test passes.

- `src/types.c` remains untouched and authoritative throughout shadow
  development.
- Types2 owns its terms, metas, schemes, obligations, caches, environments,
  diagnostics, and AST-node side tables.
- Types2 never writes legacy `Type` nodes, expression `_type` fields, symbol
  types, class/operator metadata, refinements, bytecode, or JIT decisions.
- Types2 never falls back to a legacy inferred answer. Read-only nominal
  identities, literal values, resolved names, and brokered computed results are
  allowed external facts; legacy metavariable solutions are not.
- A types2 error, mismatch, or recoverable internal failure is logged data and
  cannot change compilation success, diagnostics, output, exit status, emitted
  code, or runtime behavior.
- With logging disabled, shadow-on and shadow-off behavior is byte-for-byte
  equivalent for every stable observable the test harness can compare.
- Compile-time code is evaluated once. Shadow observation must not repeat a
  macro, type function, VM callback, or FFI effect.
- Type normalization is pure. It cannot solve or delete an ambient obligation.
- Speculative inference starts at a transaction mark and commits only the chosen
  result. A failed candidate cannot alter later candidates or final inference.
- Dynamic consistency is not used as subtyping, and neither relation is used as
  equality.
- No recursion or resource guard proves a type relation merely because a depth
  or fuel limit was reached.
- No individual syntax feature becomes types2-authoritative early. The cutover
  is atomic, with no automatic fallback period.

## Source map for future work

- `type_system.md` is the audit, intended semantic direction, phase plan, and
  acceptance list. It remains the primary rationale for deliberate legacy
  disagreements.
- `include/types2_core.h` defines the independent term, solver, scheme,
  snapshot, row, pack, variance, and obligation APIs.
- `src/types2_core.c` implements the compiler-independent type core. Keep AST
  and legacy-checker dependencies out of this layer.
- `include/types2.h` is the narrow lifecycle/checkpoint interface used by the
  compiler.
- `src/types2.c` contains AST lowering and inference, native interface modeling,
  shadow environments, diagnostics, counters, and lifecycle integration.
- `src/compiler.c` should contain only shadow lifecycle/checkpoint calls and
  explicit read-only fact bridges. Treat additional coupling here with care.
- `tests/types2_core.c` is the algebra/solver regression suite.
- `tests/types2-shadow-equivalence.sh` is the permanent noninterference gate;
  its fixtures also check selected structured events.
- `tests/fixtures/types2-shadow-*.ty.txt` and
  `tests/fixtures/types2-alias-basic.ty.txt` cover focused integration behavior.
  Add a small fixture instead of expanding one file into an opaque omnibus
  test.
- `doc/types2-shadow.md` is this operational handoff. Update its baseline,
  remaining-work list, and commands whenever a milestone materially changes
  them.

## Cutover readiness checklist

Do not switch authority until all boxes below can be supported by checked-in
tests, logs, and agreed performance data.

- [ ] The final meanings of gradual sentinels, casts, nil, matching, optional
      access, partial operations, and rank-1 polymorphism are specified.
- [ ] Every type-relevant AST form and public type constructor is implemented or
      deliberately rejected with a stable diagnostic.
- [ ] There are no unclassified or implementation-incomplete deferrals on the
      supported corpus.
- [ ] Every Cutover row in `type_system.md` has positive, negative, and—where
      relevant—runtime regression coverage.
- [ ] Union/intersection arm order, independent statement order, and specified
      overload ordering satisfy metamorphic tests.
- [ ] Failed speculative work is proven not to leak across every candidate and
      pattern path.
- [ ] Bounds, rows, packs, variance, recursion, reflection, flow, and mutable
      generalization have integration coverage without fallback.
- [ ] The full repository suite and supported-library matrix have classified,
      expected outcomes and no unexplained divergence.
- [ ] A perturbation test proves types2 inference is independent of legacy
      inferred types.
- [ ] Computed types and compile-time callbacks execute exactly once.
- [ ] Dormant `typeof`, reflection, type-value, runtime metadata, bytecode, and
      JIT adapters round-trip all public types.
- [ ] Shadow-on/off equivalence passes with logging disabled.
- [ ] Diagnostics are stable and actionable enough to replace the legacy user
      experience.
- [ ] Release compile time, pathological scaling, and peak memory meet agreed
      budgets.
- [ ] The post-cutover deletion plan has been rehearsed on a branch and the full
      correctness, runtime, JIT, ASan, and performance suites pass there.

## Atomic cutover procedure

The eventual semantic switch and legacy removal should be one integration
change, easy to revert as a whole:

1. make types2 authoritative for acceptance, diagnostics, expression/symbol
   types, `typeof`, reflection/type values, runtime metadata, and JIT guidance;
2. remove the compiler's legacy lifecycle and typechecking calls rather than
   retaining fallback;
3. delete `src/types.c`, its global state and declarations, obsolete build
   entries, translation/comparison adapters, and tests that intentionally assert
   known-bad legacy behavior;
4. mechanically rename types2 files only if the final source layout benefits;
5. run the entire correctness, library, runtime, JIT, ASan, and performance
   matrix on the post-deletion tree.

Do not route individual constructs early, keep both checkers as selectable
language modes, or allow a legacy answer to override a types2 answer. A
long-lived hybrid would reintroduce the shared-state and relation-boundary
problems this work is intended to eliminate.

## Common traps when resuming the work

- Zero `unsupported_nodes` in the startup corpus does not mean complete language
  coverage; it says nothing about unvisited AST forms and currently hides broad
  deferred categories.
- A lower diagnostic count is not automatically progress. It may mean a real
  error was replaced with `Dynamic`, a constraint was dropped, or a branch was
  skipped.
- Legacy agreement is not the oracle for a known audit defect. Preserve an
  explicit expected-improvement classification instead.
- Conversely, a types2 disagreement is not automatically an improvement. Check
  the declared contract and runtime semantics.
- Avoid fixing a shadow mismatch in `src/types.c`; that makes the comparison
  target move and creates an incremental migration.
- Do not expose types2 through `typeof`, `ty.types`, or JIT “for testing.” Use
  dormant adapter tests or a types2-only nonexecuting harness.
- Do not evaluate computed types independently from shadow inference.
- Keep structured logs out of normal stderr. Equivalence depends on logging
  being an explicit, isolated side effect.
- Preserve unrelated user changes in the working tree and inspect the diff by
  path before formatting or bulk rewrites.
- Update this document after each milestone with the new clean baseline, newly
  classified gaps, and the exact next command. That is what makes a later
  continuation reliable rather than archaeological.
