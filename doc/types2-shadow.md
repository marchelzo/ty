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

Every deferral has a named reason.  The `finish` event carries
`deferred_reasons` (nonzero counts by reason) and `deferred_classes`, which
totals the reasons into four classes: `runtime` for intentional gradual or
runtime-only boundaries (`dynamic-callee`, `dynamic-operand`, `unsafe-eval`,
`runtime-value`, dynamic member names, ...), `incomplete` for unfinished types2
features (`template`, `keyword-row`, `tuple-spread`, `set-type`,
`operator-protocol`, ...), `external` for facts the shadow could not obtain
(`unresolved-binding`, `unresolved-nominal`, `unresolved-tag`,
`unresolved-matcher`), and `recovery` (`hierarchy-rejected`).  The reason
table lives at the top of `src/types2.c`; `tools/types2-corpus-summary.ty`
mirrors it and fails when the two disagree.  Set `TY_TYPES2_TRACE_DEFERRED=1`
to add one `deferred` event per deferral with its reason, class, location,
construct, and, for bindings, the symbol name and module, plus one `import`
event per cross-unit binding import attempt.  Deferrals and diagnostics that
occur while an imported definition is being re-lowered are attributed to the
defining unit and are not counted in the importing unit.

Diagnostic events also carry `actual_hash` and `expected_hash`, the canonical
structural hashes of the two types when they exist, so tooling can dedupe
without relying on rendered text alone.

Run the permanent gates after building with:

```sh
tests/types2-shadow-equivalence.sh ./ty
tests/types2-corpus.sh ./ty
make test-types2-core
```

`tests/types2-corpus.sh` compiles the startup corpus with deferral tracing and
runs `tools/types2-corpus-summary.ty --strict` against
`tests/types2-corpus-classification.json`.  It fails on malformed events,
unknown reasons or classifications, unclassified or stale diagnostics,
internal errors, and aborts.  `make test-types2-corpus` runs the same gate.
Regenerate the classification skeleton with `--seed` (merging an existing
`--classification` file) after inference changes move diagnostics.

This interface must remain one-way.  Code in `types2` may observe resolved
syntax and read-only compiler facts.  The only legacy-type translation is the
explicit materialized-computed-result boundary described above.  Legacy typing
and code generation must never inspect a shadow result before the atomic
cutover.

## Experimental authoritative mode (`-t`)

`ty -t FILE` runs the interpreter with the legacy typechecker's diagnostics
disabled (as `-q` does) and types2 reporting instead.  Every unit compiled
after startup prints its types2 diagnostics to standard error, sorted by
location, with a source excerpt, the actual and expected types, and colour
when standard error is a terminal (or `--color=always`).  Only errors in the
entry unit (`main`, or `(repl)` for `-e`) abort compilation, so a script can
import library modules that still carry classified diagnostics; those are
printed but not fatal.  Set `TY_TYPES2_REPORT=all` to also print the startup
units (prelude and friends), and `TY_TYPES2_DEBUG_OPERATORS=1` to trace
operator candidate selection.  Multi-line solver explanations are folded into
dimmed `note:` lines under the headline.

This flag changes acceptance and diagnostics only.  Inferred types, emitted
code, runtime constraints, reflection, and the JIT still come from the legacy
path (with `CheckTypes` off), so it is a playground for reading types2's
verdicts against real code, not the cutover described below.  The
architectural invariants in this document still hold with `-t` off, which is
the default and the mode the equivalence gate covers.

## Initial overhead baseline

On revision `a5746a3`, the `gcc-ninja` build compiling the small equivalence
fixture measured 53.5 ms with shadowing disabled and 56.7 ms with it enabled
(10 warm runs each, roughly 6% overhead).  Peak RSS was indistinguishable at
about 74 MiB in three runs.  These numbers are an early smoke baseline, not a
budget for later inference milestones.

On 2026-09-01, with cross-unit binding import in place, the clang ASan build
compiled the startup corpus (`./ty -c -e nil`) in 0.95 s with 267 MiB peak RSS
with shadowing enabled and 0.47 s with 144 MiB with `TY_TYPES2_SHADOW=0`
(three warm runs each).  ASan inflates both numbers; the release preset has
not been remeasured since imports landed.

## Project status at this handoff

The replacement is well beyond the inert-observer stage, but it is still a
shadow checker. It has an independent type universe, solver, environments,
side tables, native-interface model, diagnostics, and structured counters. It
can traverse the current startup corpus without reporting an unsupported AST
node, and the core unit suite exercises the principal representation choices
from the audit. None of that changes the authority boundary described above.

Steps 1 through 4 of the previous handoff are complete, and Step 5 has begun.
Since the audited revision `a5746a3` the shadow gained:

- reasoned deferral telemetry (35 reasons in four classes) with per-site trace
  events, and structural hashes on diagnostic events;
- `tools/types2-corpus-summary.ty`, the checked-in classification file, and
  the strict corpus gate `tests/types2-corpus.sh`;
- cross-unit binding import: an identifier whose symbol has no binding in the
  current unit is resolved by re-lowering the defining top-level statement
  (function, prototype, definition, class, or tag) from the defining module's
  syntax, with diagnostics and deferral accounting suppressed during the
  re-lowering; prototypes for module builtins are matched by name inside the
  symbol's home module, and the referencing symbol aliases the definition's
  binding;
- builtin module constants (for example `os.O_CREAT`) typed through the
  compiler's literal fact bridge, which now also accepts builtin symbols;
- regex patterns (captures `$0..$n` and named groups are bound to `String` in
  the arm scope), `pattern and cond, let-part, ...` patterns, and negated
  `if not let` bindings for the continuation;
- unreachable tag patterns still bind their sub-patterns as Dynamic;
- tag values and calls: a bare tag is `Tag[Never]`, `Tag(a)` is `Tag[A]`,
  `Tag(a, b)` wraps a tuple, and every tag nominal has `Tag` as a supertype;
  the `None` type is the tag, not `nil`, because the runtime distinguishes them;
- `__missing__` protocols: a read of an absent member calls the class's
  `__missing__(name)` method and a write of an absent member calls its
  `__missing__=(name, value)` setter, which is how `chalk.red = '#f00'` is
  typed (`chalk` is a `Chalk` object, not the module);
- member access on a bare tag (`Some.from(x)`) resolves the tag's static
  members, as the runtime's tag dispatch does;
- cross-unit operator import: the legacy compiler nulls operator parameter
  constraints after symbolizing them, so `symbolize_statement` now keeps a copy
  in `retained_constraints` on the function node and types2 reads that copy;
  candidates whose every parameter is still Dynamic are skipped, and ties
  between equally specific candidates go to the first declared one, as the
  legacy prototype order does;
- bare generic application (`Array`, `Class`, `Iter`) lowers with Dynamic
  arguments, and annotation patterns narrow gradually instead of forming an
  intersection with the subject;
- fresh record and array literals passed as call arguments are typed against
  the parameter (contextual typing), so writable-field invariance no longer
  rejects `f({count: nil})` against `{count: nil | Int}`;
- comparisons and arithmetic on still-open operands (metas, pack folds) defer
  as `operator-open-operand` instead of failing;
- flow typing for implicit member fields: `__path != nil && __path.exists?`,
  `if __path == nil { return }`, and `if x != nil { ... }` narrow a private
  field read (`__path`) the way they narrow a local, through a transient
  member binding seeded at the first read, invalidated by any call or write,
  and scoped to the enclosing method (`types2-shadow-nil-guards` fixtures).

Three runtime defects were found and repaired along the way:

- `lib/prelude.ty` `Dict.[](K, V)` iterated `keys()` and indexed each key as a
  pair, so `%{1: 2} :: Dict[Int, Int]` threw at runtime; it now iterates
  `items()` (`tests/dict_type_predicate.ty`). This also removed the two
  pending obligations the previous handoff documented.
- `src/jit.c` baked the metaclass's `[](_) { self }` fallback for method calls
  on class-valued receivers, so `Dict[Int, Int]` inside JIT-compiled code
  evaluated to the bare class and matched every dictionary. `bc_emit_call_method`
  now declines static-type method resolution for class and tag receivers, which
  dispatch through their static tables first at runtime.
- `lib/os.ty` declared `listdir` as `-> [Float] | nil` (the audit's conflicting
  declaration); the runtime returns strings or nil, so it is now
  `[String] | nil`, which made `Path.ls()` type correctly.  `TempDir.__drop__`
  called `rmtree` on a `Path | nil` field without a guard; it now checks
  `__path != nil` first, as `TempFile.__drop__` already did.

Since revision `c8a148c` the session that worked through `ty -ct lib/term.ty`
(16 errors and 7 warnings at the start, none at the end) added:

- loop divergence: `for (;;)` and `while true` only fall through when the
  body breaks out of that loop; `Types2Flow` carries a `break_depths` bitmask
  so `break break` is attributed to the enclosing loop and `while match`
  consumes its arms' breaks (`types2-shadow-loops` fixtures);
- `self` inside a tag method is the payload type `T`, as the runtime unwraps
  it (`K(1).f()` sees `1`; implicit sibling calls do not exist in tag methods);
- a call through a still-forward binding (a later top-level function used
  from an earlier class or tag body) widens rigid argument variables through
  the scoped `where` assumptions before recording the callee's upper bound, so
  the obligation checked at the definition no longer mentions a bound that has
  left scope (`assumed_supertype`);
- `pattern as name` binds the pattern's narrowed type, not the whole subject;
- a bare tag pattern (`None`, `Plain`) is `EXPRESSION_MUST_EQUAL` on a tag
  symbol and now covers exactly the payload-less arm `Tag[Never]`, matching the
  runtime, which does not let `None` match `None(3)`;
- a typed iterable spread (`handler(*captures)` with `captures: [String]`) fills
  zero or more remaining positional slots when every reachable slot accepts the
  element type; the arity stays a runtime check recorded as the new
  `spread-length` runtime deferral;
- contextual typing for assignments: a fresh record or array literal written
  to a declared field (`__cursor = {...}`, `self.x = [...]`) or to a binding
  with a non-meta type is typed against the declared type inside its own
  solver transaction, so writable-field invariance no longer rejects
  `{y: nil}` against `{y: ?Int}`;
- reading a mutable binding resolves its weak meta one level (the stored
  lower bound) instead of deep-zonking, so `let q = SharedQueue(); q.put(5)`
  keeps the element meta open and `f(q)` with `SharedQueue[Int]` still unifies
  it instead of freezing the literal `5`; the same change resolved the
  `help.ty:166` literal-default call;
- `[?T]` annotations: `symbolize_expression` rewrites `[T]` to `Array[T]` in
  type context and silently dropped the optional marker for both checkers;
  the rewrite now wraps the element in `?` so `[?Int]` is `Array[Int | nil]`
  (`src/compiler.c`, not `src/types.c`);
- the `-t` diagnostic printer read one byte past a type string while colouring
  identifiers (`paint_type`), caught by ASan on the first `term` run.

Library contracts corrected in the same pass, each checked against the
runtime first:

- `lib/prelude.ty`: `Dict` gained the `__call__(k: K) -> Some[V] | None`
  prototype that the VM implements natively (`%{'a': 1}('a')` is `Some(1)`),
  and `Generator.__call__` takes `arg: ?S` because a generator may be called
  with no argument;
- `lib/os.ty`: `poll` returned pairs for plain descriptors and triples only
  when user data was attached, but was declared as `(Int, Int, ?T)` triples;
  it is now two overloads, `[Int | (Int, Int)] -> Ok[[(Int, Int)]]` and the
  user-data form, both with `timeout` defaulting to nil as the builtin does;
- `lib/term.ty`: `title` sliced `s[0]` (nil on an empty string) and now uses
  `s[;1]`; the `_size` helpers wrote the thread-local `size` and then read it
  after `ioctl`, which the conservative call invalidation cannot see through,
  so they share a `query(fd) -> WinSize` helper that works on a local;
- `test.ty:24` called `some?()` after the prelude made it a getter, and the
  legacy checker rejects `.some?` on `Some[T] | None` because `None` only has a
  static getter, so the harness now tests `:: Some`.

Since revision `f3675af` the session that worked through `ty -tc lib/readln.ty`
(21 errors at the start, none at the end; `lib/sh.ty` went from 3 to none)
added:

- multiple return values: `return a, b` has the core type `|A, B|`
  (`T2_TYPE_MULTI`, printed with the surface syntax).  Subtyping and solver
  constraints compare it item by item as an infinitely nil-padded sequence:
  `|Int, String| <: |Int, ?String|`, a single value `T` is `|T|`, and a
  multi-value result is not a subtype of a single-valued declared result (the
  legacy checker rules the same way).  `t2_multi` trims trailing `nil` items
  and collapses one item to the item itself.  A call result collapses to its
  first item everywhere except in `let a, b = ...`, `a, b = ...`, `return`,
  and the tail expression of a function body, the only sites through which
  the runtime propagates the extra values (`shadow->multi_value_site`); the
  value list `0, f(), 3` splices a call's values in place as the VM's
  `GET_EXTRA` does.  `let a, b = (1, 2)` binds the tuple and `nil`, and
  `let a, b = x` binds `x` and `nil`, matching the runtime
  (`types2-shadow-multi-values` fixtures);
- `for` targets receive a value list: dictionaries yield `|K, V|`; arrays,
  strings, and generators yield `|T, Int|` (element and index); a single
  target takes the first value, so `for x in dict` is the key and
  `for pair, i in pairs` is not a destructuring;
- the postfix `!` assertion strips `nil` from the operand's type; the runtime
  does not check it, and the legacy checker made the expression `Unknown`;
- annotation patterns accept any type expression (`parts: Array[Text | nil]`,
  `x: A | B`, `?T`) and narrow the subject through `narrow_type_to`, so match
  arms and match lambdas see the narrowed binding and the remaining subject;
- `pattern as name` binds the pattern's possible subject
  (`pattern_narrowed_subject`), an over-approximation that selects the tag or
  class arms even when the payload pattern is refutable, instead of the exact
  coverage that previously fell back to the whole union;
- `-1` in a pattern is a literal (`literal_pattern_type`), so `-1 or nil`
  covers the `nil` arm;
- `if` condition parts are inferred in order with each part's refinements and
  bindings applied to the next, so `(key :: String) and let $f = table[key]`
  sees `key: String`; `while` conditions refine the loop body; private-member
  bindings mentioned by a condition are seeded before the refinement snapshot
  (`touch_condition_bindings`) so the continuation after an early `return`
  keeps its narrowing;
- loops: before a loop body is inferred, the compiler's AST visitor (with
  identity transforms and no scope, which makes it read-only) scans the loop
  for assignments (`=`, compound assignments, `++`/`--`) to bindings declared
  outside it and clears their flow refinements, because the first iteration's
  view of a binding the body reassigns is unsound.  If such a binding is an
  unannotated optional (`let x = nil`: a weak meta whose current solution
  admits `nil`), the loop is inferred twice.  The muted first pass (no
  diagnostics, deferrals, or unsupported-node counts) collects the assigned
  value types as lower bounds; its obligations are cancelled, the side-table
  entries it touched are forgotten, its bindings are deactivated, and the
  second pass reports normally.  Refinements are restored after every loop.
  Refinements resolve a weak binding's current solution before narrowing,
  and branch merges snapshot resolved effective types, so a refinement never
  captures the storage meta itself (`types2-shadow-evolving` fixture);
- `a += b` on arrays is the in-place append the VM performs: the appended
  element type must fit the receiver's element type and the receiver's type
  is unchanged, so an accumulator `let xs = []; xs += ys` keeps one array
  type instead of a growing union of concatenation results;
- fresh array and record literals passed to a union-typed parameter are typed
  against the first union arm that accepts them;
- `pack-placement` now also rejects a pack inside `|...|`.

Library contracts corrected in the same pass, each checked against the
runtime first:

- `lib/prelude.ty`: `+[T, U](Array[T], Array[U]) -> Array[T | U]` and
  `*[T](Array[T], Int) -> Array[T]`, which the VM implements natively
  (`[1] + ['a']`, `[1] * 3`); `-` on arrays is not implemented and stays
  undeclared;
- `lib/os.ty`: the three-argument `poll` takes `pollfds-in: Iterable[...]`
  because it only reads that argument, while `pollfds-out` stays an invariant
  array because the builtin fills it; a variable of type
  `Array[(Int, Int, Blob)]` is not `Array[Int | (Int, Int, T)]` under
  invariance;
- `lib/sh.ty`: `ls` returns nil when the shell could not be spawned instead of
  calling `split` on nil;
- `lib/readln.ty`: `sum()` and `max()` on possibly empty arrays get explicit
  defaults, `print-items` takes `select: ?Int`, the highlighted completion row
  stores a `String` (`str(chalk"...")`) as its siblings do, the history file
  is rebound with `if let $file = __history-file` before two calls, the
  `label and (j == 0)` arm is `(label: Text)` because an empty array label
  reached `width`, and the history matcher used `entry.0.str()` on a record
  entry (stale tuple-era code) and compared `(line, i)` with a record; both
  now use a `text-of(lines)` helper.

Known gaps noted while reading these modules: records support positional
access at runtime (`{a: 1}.0` is `1`) and types2 does not model it; the
backtick operator value `` `#` `` reaches types2 as a computed-type deferral
(`Dynamic`); `[].sum()` and `[].max()` are `nil` at runtime, so callers must
supply a default.

The session that followed worked through `ty -tc lib/log.ty`, `lib/chalk.ty`
(8 errors and 1 warning), and `lib/help.ty` (3 errors and 2 warnings), all of
which now report nothing, and added:

- dictionaries with a default entry: `%{nil: 2, *: log-open(it)}` lowers the
  `*: expr` callback (the parser's `it -> expr` lambda) so that the key type is
  the union of the literal keys and the callback's parameter meta, and the value
  type joins the literal values with the callback's result.  Reads with a wider
  key widen the parameter (`nil | String <: nil | $it` sends `String` to `$it`),
  which is how `global-log-fds` becomes `DefaultDict[nil | String, Int]` while
  `it` is `String` inside `log-open(it)`.  A callback parameter the body leaves
  unconstrained (`%{*: 0}`, `%{*: #it}`) defaults to Dynamic like any other
  callback meta, so a literal nobody reads does not leave a pending predicate.
  The literal's type is the prelude class `DefaultDict[K, V] < Dict[K, V]`,
  whose `[](key: K) -> V` says that a read never yields `nil` because the
  runtime computes the value on a miss; `counts[k] += 1` on `%{*: 0}` therefore
  checks, and every `Dict` special case (subscripts, membership, `#`,
  iteration, spreads) accepts either class.  Plain dictionary literals keep
  exact key and value types and optional reads;
- a parameter with a default accepts `nil` at every call shape, because the VM
  substitutes the default when `nil` is passed (`f(1, nil)` is `f(1)`), while
  the body still sees the declared type and the default expression must still
  satisfy it (`select: Int = nil` remains an error).  `apply_callable_candidate`
  widens such parameters to `T | nil`, and the core's `contravariant_parameter`
  and `constrain_parameter_types` ignore `nil` arms of the expected type when
  the actual parameter has a default, so the `&[i;]` section's
  `[;;](1, nil, nil)` call matches `k: Int = 1` without changing the prototype.
  The legacy checker rejects an explicit `nil` argument, so this is an expected
  correction that fixtures cannot execute directly;
- tail hints: a fresh record, array, or dictionary literal in tail position
  (the value of `return`, the last expression of a body with a declared result,
  and recursively the arms of `match`, both branches of `if` and `?:`, and the
  last statement of a block) is typed against the declared result through
  `contextual_fresh_literal`, keyed by the exact node (`shadow->hint_site`) so
  the hint never reaches operands or arguments.  This is what lets
  `parse-style` return `({fg: [...]})` against `TermStyle | nil`;
- lambda hints: a lambda literal passed positionally to a method whose
  parameter is a closed callable, or to a function named by a binding with such
  a parameter, has its unannotated parameters seeded with the expected types
  before its body is inferred (`shadow->lambda_hint_site`), so
  `make-gradient(t -> iround(r1 + (r2 - r1) * t))` sees `t: Float`;
- callable objects: an argument whose nominal (or refinement of a nominal,
  such as `Regex[0]`) declares `__call__` is checked through that method's
  instantiated type when the parameter is a callable, and calling such a value
  resolves `__call__` through the refinement too; `class Regex` gained the
  `__call__(s: String) -> String | Array[String | nil] | nil` prototype the VM
  implements, so `lines.dropWhile!(/^\s*$/)` and `words.filter(Longer(1))`
  check;
- overload calls with a Dynamic argument join the results of every applicable
  candidate instead of committing to the first, so a `nil` arm after
  `match doc(x)` stays reachable;
- `match` and `for match` resolve the subject's head before coverage; the
  desugared `for match` reuses the loop target's node, whose cached type was
  the storage meta, so class-pattern arms never subtracted;
- a class value exposes instance methods as members (`Array.sort` inside the
  `doc!` template), typed as the method itself rather than an unbound function.

Library contracts corrected in the same pass, each checked against the
runtime first:

- `lib/prelude.ty`: `class DefaultDict[K, V] < Dict[K, V]` with
  `[](key: K) -> V` names the type of a dictionary literal with a default entry
  (its parameter name must match `Dict.[]` because overrides are checked by
  call shape); `doc` returns `String | nil` documentation strings and `nil` for
  an undocumented function (`doc(print)`), while a class result is never `nil`,
  which `tests/xinfo.ty` relies on; a `?T` inside a tuple type is an optional
  element marker, not `T | nil`, so the prototypes spell the union out;
- `lib/chalk.ty`: `{groups: [$escaped]}` rejects a nil capture before slicing,
  the capture count view uses the not-nil `$~>` form, and a compound style
  asserts `__styles[w]!` because `{*nil}` throws at runtime;
- `lib/help.ty`: the `doc!` template matches `{str, *}` on the token union
  (the legacy checker rejects an irrefutable destructuring of the intersection),
  and the common-indent scan defaults a non-matching line to `''`.

The session that worked through `ty -tc lib/ty/repl.ty` (6 errors and 1
warning at the start, none at the end) added:

- record patterns on an intersection subject (`Token` is `TokenData & {...}`
  where `TokenData` is a union of open records) take the field from the arms
  that define it (`record_field_definition`), so `{end, *}` binds `end` to
  `TokenLocation` instead of joining in a disconnected unknown from the open
  rows; a refutable record pattern on an open row binds `Dynamic` rather than a
  fresh meta, as the runtime domain is open;
- a tag pattern's coverage checks its payload pattern against the payload type
  (`tag_payload_covered`) instead of trusting syntactic irrefutability, so
  `Ok((_, {tokens, *}))` on an optional `tokens?` field no longer claims the
  whole arm and the following `err =>` arm stays reachable;
- literal relaxation recurses into tuples, so `[(it, '') for source]` is
  `Array[(String, String)]` and a later `(s, color)` write checks;
- an annotated `let` forwards its declared type as a tail hint, so
  `let label: CompletionLabel | nil = match item { ... => [chalk"..."] }` types
  each arm's literal contextually;
- keyword arguments receive callback hints too, and a hint can come from any
  candidate of an overload set (`sort!(by=\key(_.1))`);
- class operator methods of an imported class are found through the compiler's
  operator dispatch table (`op_definition_count`/`op_definition`, a read-only
  bridge added to `src/operators.c`), restricted to fully annotated operators
  whose class matches an operand, so `Path.home() / '.ty'` resolves outside
  `lib/path.ty`; unannotated class operators such as `Sync.<` stay out because
  their signature-only schemes would poison unrelated comparisons.

Library contracts corrected in the same pass, each checked against the
runtime first:

- `lib/prelude.ty`: `Array.enumerate!` is a VM builtin that lacked a
  prototype;
- `lib/ty/repl.ty`: `chr(source.byte(end.byte))` can receive `nil` past the
  end of the source and now defaults to `0`; `mod-completions` builds
  `(CompletionLabel, String)` pairs and widens to `Array[CompletionItem]`
  with a fresh `[*...]` literal at the boundary, because arrays are invariant.

The last clean validation run used the clang ASan build and produced:

- `./ty test.ty`: 78 passed;
- the types2 core unit suite: passed, including the multi-value checks;
- shadow-on/shadow-off equivalence: passed, including the `multi-values`,
  `multi-values-invalid`, `evolving`, `contextual`, `defaults`, and `repl`
  fixtures;
- the strict corpus gate: passed;
- the startup corpus: 16 units, 0 unsupported nodes, 1,619 deferred nodes
  (1,141 runtime, 161 incomplete, 317 external, 0 recovery), and no pending
  terminal obligation (the `chalk.ty:609` pack obligation resolved once its
  view pattern narrowed to `Int`);
- 79 raw types2 diagnostic events (77 errors, 2 warnings) reducing to 78
  unique `(unit, line, column, code)` diagnostics, all classified (54
  unexplained, 18 library defects, 4 incomplete features, 2 expected
  corrections); `chalk`, `help`, `term`, `sh`, `readln`, `ty/repl`, `io`, and
  `os` contribute none, and the remaining units are `prelude` (54), `ffi`
  (19), `pretty` (3), and `os` (1);
- `ty -tc lib/path.ty` reports only the intended unreachable-pattern warning;
  `lib/term.ty`, `lib/sh.ty`, `lib/readln.ty`, `lib/log.ty`, `lib/chalk.ty`,
  `lib/help.ty`, and `lib/ty/repl.ty` report nothing; outside the startup
  corpus `lib/curl.ty` (24), `lib/ffi.ty` (19), `lib/pretty.ty` (3),
  `lib/ety.ty` (1), and `lib/sqlite.ty` (1) are the next modules with errors;
- the clang ASan build compiles the startup corpus in 1.10 s with 268 MiB
  peak RSS with shadowing enabled and 0.48 s with 146 MiB with it disabled
  (three warm runs each).

`tests/types2-corpus-classification.json`, `tests/types2-corpus.sh`,
`tools/types2-corpus-summary.ty`, `tests/dict_type_predicate.ty`, and the
`deferred`, `nil-guards`, `loops`, `multi-values`, `evolving`, `contextual`,
`defaults`, and `repl` fixtures are still untracked in the working tree;
commit them with the next milestone.
The classification file was reseeded on 2026-09-02; entries whose line moved
after the prelude gained two operator prototypes were remapped by unit,
column, code, and message with meta names and locations normalized.

The deferral totals fell from 3,106 to about 1,700 because imported bindings
replaced Dynamic at 700 call sites, and the diagnostic count first rose from
122 to 209 for the same reason (precise imported types reach call, member, and
field-write checks that previously saw Dynamic) and then fell to 156 as the
tag, operator, `__missing__`, contextual-argument, narrowing, and member
nil-guard fixes above landed.  Do not treat either number as a score.

The most common deferral reasons in that snapshot were:

| Reason | Class | Count | Notes |
|---|---|---:|---|
| `dynamic-callee` | runtime | 706 | mostly downstream of the `external` gaps below; Dynamic provenance is not tracked yet |
| `unresolved-binding` | external | 322 | AST constructors from `ty` referenced by `prelude` before that module is compiled; builtins without prototypes such as `show`, `ptr`, `int`, and `members`; nested mutually recursive functions |
| `runtime-value` | runtime | 278 | raw VM values spliced by macros |
| `dynamic-operand` | runtime | 115 | |
| `template` | incomplete | 72 | |
| `set-type` | incomplete | 22 | all in `ffi` |
| `keyword-row` | incomplete | 18 | |
| `callable-top` | runtime | 17 | |
| `computed-type` | incomplete | 12 | |
| `spread-arity` | incomplete | 9 | spreads whose element is still an open meta |
| `spread-length` | runtime | 3 | typed spreads whose length is a runtime check |

The remaining pending obligation is the `<=>` pack obligation from
`min`/`max` at `lib/chalk.ty:609`; it is classified as an incomplete pack
feature, not a library error.

The classification file records 2 expected corrections, 20 library defects,
9 incomplete features, and 95 unexplained diagnostics.  Keys carry line
numbers, so an edit that inserts lines in a library file moves every later
key; reseed with `--seed --classification` and restore the moved entries'
classes before treating them as new.  The unexplained
group is the triage queue.  Its largest codes are `missing-field` (23),
`bad-call` (21), `union-method-coverage` (9), `invalid-trait-member` (7), and
`invalid-override`, `not-callable`, `union-operator-coverage`, and
`unsupported-operator` (6 each).  Most `missing-field` entries read `.id`/`.str`
on tokens produced by the `ty/token` lexer builtins, whose interface is
unavailable until that module is compiled.  Three `bad-call` entries appeared
when operator ties started resolving by declaration order; a union operand
such as `Int | Float` should be split per arm before candidate selection.

Do not optimize for reducing these numbers mechanically. In particular, do not
replace an unexplained result with `Dynamic` merely to remove a diagnostic.
Each difference must be classified against the intended semantics in
`type_system.md` and, where relevant, runtime behavior.

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

Done.  `defer_node`/`defer_symbol` in `src/types2.c` are the only accounting
entry points; `retract_deferral` handles the materialized computed-type case.
Every reason belongs to exactly one class, and the finish event reports both
per-reason and per-class totals.  Keep the invariants when adding a reason:

- add it to `TYPES2_DEFER_REASONS` and to `REASON_CLASSES` in
  `tools/types2-corpus-summary.ty`, or the corpus gate fails;
- never pick a reason merely to suppress a diagnostic;
- `runtime` is for constructs that are intentionally dynamic; an incomplete
  interface, spread, or keyword row must stay `incomplete`;
- `external` is for facts the compiler has not made available to the shadow
  (a module compiled later, a builtin without a prototype, a macro-provided
  name); it is the next category to drive down.

Two known imprecisions remain.  `dynamic-callee` and `dynamic-operand` count
every elimination of a Dynamic value, whether the Dynamic came from an
annotation or from an earlier `external` gap; tracking Dynamic provenance
would let the runtime class exclude the latter.  Deferrals inside imported
definitions are not counted by the importing unit at all.

### 3. Build a reproducible differential-validation corpus

The startup corpus, summary tool, classification file, and strict gate exist
(`tests/types2-corpus.sh`).  The remaining driver work is to add:

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

### Step 1: reproduce the current baseline

Start from a fresh ASan build and run the permanent gates:

```sh
make clean && CC=clang make -j10 DEBUG=1
ASAN_OPTIONS=intercept_strndup=0:detect_leaks=0 \
    CC=clang make test-types2-core DEBUG=1
ASAN_OPTIONS=intercept_strndup=0:detect_leaks=0 \
    ./tests/types2-shadow-equivalence.sh ./ty
ASAN_OPTIONS=intercept_strndup=0:detect_leaks=0 \
    ./tests/types2-corpus.sh ./ty
ASAN_OPTIONS=intercept_strndup=0:detect_leaks=0 ./ty test.ty
```

For a readable summary of the corpus without the strict gate:

```sh
types2_log=$(mktemp /tmp/types2-shadow.XXXXXX.jsonl)
ASAN_OPTIONS=intercept_strndup=0:detect_leaks=0 \
    TY_TYPES2_LOG="$types2_log" TY_TYPES2_TRACE_DEFERRED=1 ./ty -c -e nil
./ty tools/types2-corpus-summary.ty \
    --classification tests/types2-corpus-classification.json "$types2_log"
```

`TY_TYPES2_LOG` appends, so never reuse an old path.

### Step 2: triage the unexplained diagnostics

`ty -t -c lib/<module>.ty` prints a module's own diagnostics in source order
and is the fastest way to read one group at a time.

Work through `tests/types2-corpus-classification.json` by code, largest group
first, and replace `unexplained` with the correct class and a note.  Read the
source line and, where behavior is in question, run the construct.  Group
notes are cheaper than per-site notes when a code has one cause.  Decisions
that turn out to be language contract questions (implicit fields assigned in
`init`, bare generic application, optional indexing, parameter names in
overrides) belong in Workstream 1 fixtures rather than in the classification
file alone.

### Step 3: drive down the `external` deferrals

Use `TY_TYPES2_TRACE_DEFERRED=1` and the `deferred`/`import` events grouped by
`name` and `module`.  The known groups are:

- symbols of modules compiled after the referencing unit (the `ty` AST
  constructors used by `prelude` and `ffi`): decide whether the shadow may
  re-lower a parsed but not yet compiled module, or whether those references
  stay external until compile order changes;
- macro-provided builtins (`peek`, `next`, `expr`, `stmt`) and builtins without
  prelude prototypes (`type`, `show`, `unlock`, `sigmask`, `fdopen`): add native
  contracts or prototypes as library changes with their own tests;
- nested mutually recursive functions inside a block: pre-register forward
  bindings for nested function definitions the way top-level declarations are;
- `if not let` inside `break if`/`continue if` and other condition positions.

### Step 4: implement the largest incomplete categories

Use the reasoned counts: templates and holes, open-operand operator
obligations, `__set_type__`, operator protocol fallbacks, keyword rows, then
hierarchy syntax, computed types, spread arity, and tuple spreads.  For each,
add a positive fixture, a negative fixture, a canonical inferred type
assertion, and, where speculation is involved, a rollback assertion.

### Step 5: track Dynamic provenance

Give the `runtime` class an honest meaning by distinguishing a Dynamic that
came from an annotation, `unsafe`, or `eval` from one that came from an
`external` or `incomplete` gap, so that `dynamic-callee` and
`dynamic-operand` no longer hide unfinished work.

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
measure the release build on the audit stress corpus.  Cross-unit import
re-lowers each imported definition once per importing unit; measure that cost
on the release preset before adding a cross-unit scheme cache.

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

# Check the startup corpus against the classification file.
ASAN_OPTIONS=intercept_strndup=0:detect_leaks=0 \
    ./tests/types2-corpus.sh ./ty

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
- `tools/types2-corpus-summary.ty` summarizes JSON Lines logs, validates
  events and classifications, and seeds the classification file.
- `tests/types2-corpus.sh` is the strict corpus gate;
  `tests/types2-corpus-classification.json` is its expected-classification
  file.
- `tests/dict_type_predicate.ty` is the runtime regression for the `Dict`
  type predicate and the JIT class-receiver dispatch repair.
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
- A class or tag method body is inferred at the class statement's checkpoint,
  before later top-level functions are symbolized, so a forward call sees only
  the callee's flexible meta.  Keep call-site bounds free of scoped `where`
  assumptions (widen through `assumed_supertype`) rather than trying to lower
  the later signature early; its annotations have no symbols yet.
- Read a mutable binding through `t2_solver_solution`, never a deep zonk: a
  zonk freezes every nested open meta at its current lower bound, which turns
  `SharedQueue[$e]` with one `put(5)` into `SharedQueue[5]`.
- `??=` is not an operator in the language or the prelude; `x ??= y` lexes as
  a user operator and throws at runtime.  Write `x = x ?? y`.
- `symbolize_expression` rewrites `[T]` to `Array[T]` in type context; any
  new array-type surface syntax must survive that rewrite, as the optional
  element marker now does.
- `shadow->multi_value_site` names the one call or value-list node whose raw
  `|...|` result is wanted; every other call collapses to its first value at
  the end of `infer_expression`.  Set it only around the exact node.
- A loop's muted first pass relies on `shadow->muted`; any new diagnostic,
  deferral, counter, or log line emitted during inference must honour it, and
  anything cached per node must go through `set_node_type` so the touched
  list can forget it before the second pass.
- The compiler's `visit_statement` is read-only only with `visit_identity`
  callbacks and a NULL scope; never hand it a scope from the shadow.
- At runtime `for a, b in pairs` binds the pair and the index; destructure
  with `for (a, b), i in pairs`.  `let a, b = (1, 2)` binds the tuple and
  nil.  A multi-value result collapses to its first value in every other
  position, including as a call argument.
- `shadow->hint_site` and `shadow->lambda_hint_site` are consumed by node
  identity; forward a hint only to a tail child right before inferring it.
- A bare `Class` parameter is `Class[Dynamic]`, which a `Function` argument
  satisfies gradually; `doc(f: Function)` therefore still selects the class
  overload for a `Function`-typed argument (a Dynamic argument joins both).
  Two unrelated nominal classes are not yet treated as disjoint.
- An unannotated parameter is a flexible meta, not Dynamic: a call through
  it commits to the first applicable overload and constrains the parameter.
- `{captures, *}` inside a class pattern is not yet counted as covering the
  class arm; `RegexMatch({captures})` is.
- Passing `nil` for a defaulted parameter is accepted by types2 and rejected
  by the legacy checker, so a fixture that both checkers run cannot contain
  it directly; the `&[i;]` section exercises the rule at the type level.
- A prelude class that overrides a method must reuse the inherited parameter
  names (`[](key: K)`), or the override is reported as a call-shape mismatch.
- Class operator methods are hoisted by the compiler into `STATE.class_ops`
  and registered with `op_add`; they are not in `module->prog`, so
  `import_operator_definitions` cannot see them.  Import them from the
  dispatch table, and only when their signature is fully annotated.
- `Path` has no `str` method; render a path with `"{path}"`.
- Update this document after each milestone with the new clean baseline, newly
  classified gaps, and the exact next command. That is what makes a later
  continuation reliable rather than archaeological.
