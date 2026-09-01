# Ty Type System Audit

Audited revision: a5746a3

Scope: the compiler/typechecker implementation, its observable static semantics, the standard library under lib/, the documentation, and focused interpreter experiments.

## Executive summary

Ty already has a surprisingly broad type language for a small interpreter: literal types, unions and intersections, structural records, nominal classes and traits, recursive aliases, rank-1 generics, heterogeneous and repeated type packs, constrained functions, overloads, flow refinement, generator send/yield types, and compile-time type functions. The same-process facilities around typeof, type values, macros, and ty.types are unusually good foundations for experimentation and tooling.

The current implementation is nevertheless past the point where more local cases can safely be added to the existing destructive unifier. Several central operations use the same mutable Type graph for four different jobs:

1. equality unification;
2. directional subtype constraint solving;
3. gradual compatibility;
4. join/meet construction and flow refinement.

That conflation is the root cause of most of the inconsistencies found in this audit. An unsolved variable has one val slot and is normally bound to the first type that reaches it. A failed speculative comparison may still have mutated the graph. Later code then attempts to recover precision by constructing unions or intersections, relaxing literals, fixing variables, or rerunning constraints. The result is order-dependent inference, rejection of valid programs with multiple upper bounds, acceptance of invalid programs through impossible intersections, and solver behavior that is difficult to make transactional or memoize.

The direct answer to the audit's main representation question is therefore:

> Ty should move from early single-type binding to a constraint representation that retains lower bounds, upper bounds, and subtype edges until a solution is actually required. Equality variables may still use union-find, but equality and subtyping must not share the current single val operation.

This is not merely an opportunity for better precision. Some desired behavior cannot be implemented in full generality with first-bound-wins variables. For example, a parameter used once where Int | String is accepted and once where String | Bool is accepted has the principal upper bound String. Conversely, a repeated generic parameter called with Int and String has the principal lower bound Int | String. Binding either occurrence early destroys one of those answers.

There are also several independent, high-impact correctness problems that the replacement checker must handle correctly before cutover:

- nominal generic arguments are treated covariantly even for mutable Array, Dict, writable records, Box-like classes, Future, queues, and pointers;
- operations on unions often succeed if any arm works rather than requiring every reachable arm to work;
- tuple arity, optional-field reads, subscript writes, compound assignments, several unary operators, membership, ranges, and default arguments are not consistently checked;
- function subtyping omits parts of the callable contract, including parameter names and required/default call shapes;
- trait declarations and method overrides are recorded without checking conformance;
- a recursion-depth guard makes subtype checks succeed unconditionally past depth 64;
- recursive aliases are not checked for guardedness, allowing hangs and false proofs;
- contextual typing can turn contradictions into inhabited intersections such as String & Int;
- captured mutable state can be generalized, producing classic polymorphic-reference failures;
- several constraint and variadic paths erase or fail to re-instantiate obligations;
- records need real row and presence information; the current tuple-backed representation loses both fields and correlations;
- eager Cartesian expansion of union-valued call arguments is exponential in time and memory.

The recommended direction is an immutable, canonical type-term layer plus a per-compilation solver with:

- equality union-find with path compression;
- metavariables carrying lower and upper bounds;
- explicit subtype edges and dependency watchers;
- isolated/rollbackable overload trials;
- row variables and field-presence constraints;
- first-class pack/sequence variables;
- variance metadata;
- explicit type schemes and weak variables/value restriction;
- guarded recursive types and progress-aware coinductive comparison.

The implementation strategy should be a clean parallel replacement, not an incremental repair or migration of the existing checker. Leave src/types.c and its behavior untouched. Build the new checker independently in src/types2.c, have the compiler run both in shadow mode, and keep the legacy checker exclusively authoritative for compilation, inferred types, JIT guidance, bytecode, exit status, and runtime behavior. The only permitted shadow-mode effect is explicitly enabled diagnostic/progress logging. Once the new checker independently produces the intended results across the test and library corpus, switch authority to it and remove the legacy checker in one cutover.

## Method and confidence

The audit combined:

- source inspection, primarily [include/types.h](include/types.h), [src/types.c](src/types.c), [src/compiler.c](src/compiler.c), [src/class.c](src/class.c), and parser/symbol code;
- the language guide, especially [doc/intro/01-start.md](doc/intro/01-start.md) and [doc/intro/03-functions.md](doc/intro/03-functions.md);
- inspection of declarations and implementations throughout lib/, with particular attention to [lib/prelude.ty](lib/prelude.ty), [lib/sqlite.ty](lib/sqlite.ty), [lib/os.ty](lib/os.ty), and [lib/tp.ty](lib/tp.ty);
- focused compile-time probes using typeof, ty.types.check, annotations, constrained calls, and deliberately mirrored runtime uses;
- the repository test program;
- synthetic performance workloads for unions, overloads, structural records, generic instantiation, and deferred constraints.

Unless stated otherwise, examples described as accepted or rejected were observed with the current interpreter, not inferred from source alone. Runtime failures are used only to demonstrate a mismatch between the accepted static contract and actual language behavior. Performance numbers use the pre-existing non-ASan GCC/mimalloc binary and include startup/prelude work; they are comparative measurements, not release-build headline numbers.

## What Ty currently models

### Type forms

The central Type enum is in [include/types.h:58](include/types.h#L58). It includes:

- functions;
- tuple/list/sequence forms;
- tags;
- nominal classes and objects;
- unions and intersections;
- variables;
- type-level subscripts and slices;
- integer, string, and boolean literals;
- integer ranges;
- nil, none, bottom, error, aliases, computed types, and type values.

The representation is compact and flexible, but several unrelated forms share union fields in one mutable structure. The important flags are fixed, concrete, variadic, forgive, and packed. There is no first-class variance, mutability, row, presence, quantifier, weak-variable, lower-bound, or upper-bound metadata.

Type variables are represented by an id, level, bounded flag, and one val pointer at [include/types.h:120](include/types.h#L120). BindVar replaces that single value destructively at [src/types.c:878](src/types.c#L878), and ResolveVar follows the chain without path compression at [src/types.c:2326](src/types.c#L2326).

Constraints have only three forms at [include/types.h:33](include/types.h#L33):

- binary operator;
- subtype;
- subscript.

That is enough to express several useful standard-library signatures, but obligations live inside mutable function types and are solved, cloned, culled, and sometimes deleted during normalization. They are not stable proof obligations with identity or provenance.

### Static semantics in practice

Ty describes itself as having a modest gradual type system whose checking can be disabled with -q. That is accurate at the user-experience level, but the implementation does not yet have a single, coherent gradual-typing relation.

The observable escape hatches are useful:

- underscore is a quiet dynamic/unknown annotation in many positions;
- as T is an unchecked cast: the operand is symbolized with types disabled and the result is assigned fixed T at [src/compiler.c:4759](src/compiler.c#L4759);
- prelude cast functions expose a generic spelling of the same idea;
- safe member syntax such as .? can avoid a runtime missing-field access;
- -q disables checking;
- Any permits dynamic member lookup and acts top-like in some input positions.

However, Any, underscore, bottom, unknown, error recovery, and never-like behavior are partially encoded by the same nodes and flags. For example, Any is accepted as a supertype of concrete values but does not consistently flow back into a narrower parameter, while underscore is bidirectionally compatible in more places. Fixed bottom is also used as a dynamic-looking unknown and as the result of failed occurs checks. Users therefore see multiple subtly different meanings for apparently imprecise types.

A coherent gradual design should distinguish at least:

- Never: no runtime values;
- Unknown: some value exists, but it must be narrowed before type-specific operations;
- Dynamic: operations are permitted and checked at runtime;
- Any/top: every value is a subtype, but it does not authorize arbitrary elimination;
- Error: suppress cascading diagnostics after a prior failure.

The solver should also distinguish strict subtyping from gradual consistency. Dynamic consistency is symmetric and deliberately non-transitive; subtyping is directional and transitive. Using destructive unification for both makes predictable rules impossible.

The representation-level conflation is concrete. BOTTOM_TYPE and UNKNOWN_TYPE both use TYPE_BOTTOM and differ mainly by fixedness; a null Type pointer is also reported as TYPE_BOTTOM by [include/types.h:213](include/types.h#L213). Both sides of type_check have bottom-like compatibility fast paths, so neither node consistently behaves like mathematical bottom/Never. TYPE_ERROR is a third sentinel, but it is not integrated into the same lattice and is not completely round-tripped through type metadata.

Focused probes demonstrate the resulting distinctions:

~~~text
types.check(Unknown, Object)  = true
types.check(Object, Unknown)  = true
types.check(Bottom, Object)   = true
types.check(Object, Bottom)   = true

let a: Any = 1
let i: Int = a              # rejected

let a: _ = 's'
let i: Int = a              # accepted; i contains a String
~~~

Any is implemented as the nominal top class, underscore resolves to fixed unknown/bottom, and Object is a third concept intended to describe ordinary non-nil values. Runtime class matching often treats Object as the root while static object subtyping does not cover every runtime value category in the same way. Nil matches Any at runtime but not Object.

Union/intersection algebra is consequently order-dependent. The two spellings _ | Int and Int | _ can normalize to different displayed types because type_unfixed converts fixed unknown to ordinary bottom before Uniq performs mutable, directional containment checks. Any & Int, _ & Int, and the reversed arm orders also do not obey one commutative algebra.

There are currently three independently implemented relations:

1. compiler assignment, which usually attempts unification and may widen or bind variables;
2. exported ty.types.check, which calls the static subtype checker;
3. runtime ::, which is a general pattern/matcher operator and can dispatch to __match__.

They are observably different. For example, assigning literal 1 to Int | String succeeds, runtime membership in that type succeeds, but ty.types.check can return false because the literal fast path runs before union handling at [src/types.c:8726](src/types.c#L8726). Intersection assignments can disagree similarly. Runtime :: is useful as a general matcher, but it should not be documented or used internally as if it were the authoritative subtype relation.

The unchecked as escape hatch is reasonable for a gradual language, but its current scope is wider than the cast boundary: the entire operand subtree is symbolized with types disabled. Thus an unrelated missing member inside the operand can pass compilation before the final value is relabeled. If as remains unchecked, its operand should still be checked normally; only the conversion from the operand type to T should be suppressed. A separately named unsafe construct can retain subtree-wide suppression if that behavior is wanted.

The -q option likewise disables more than function signature checking: it turns off the general checking/constraint machinery and changes diagnostic behavior. A clearer name such as --no-typecheck and separately controlled diagnostic detail would make the escape hatch more predictable.

### Inference pipeline

The compiler starts type state, injects declarations, runs a type-iteration pass after every top-level statement, symbolizes every statement with another iteration after each, processes class operators, and finishes at [src/compiler.c:13392](src/compiler.c#L13392). This gives declarations and overloads a chance to converge, but makes global mutable state and repeated rescans part of normal compilation.

Generalization is level-based. GatherFree walks a type graph at [src/types.c:3873](src/types.c#L3873); Generalize and the later fixup pass quantify variables based on occurrence-count heuristics. Instantiation recursively clones type structures at [src/types.c:4312](src/types.c#L4312). The static checker, pending-constraint vectors, current level, work indexes, function stack, environment stack, recursion counters, and fuel are global or effectively global state. Saving typecheck state does not provide a transaction over mutations already made to Type nodes.

The architecture works well for small, direct cases, but it has three consequences:

1. speculative checking is not safely reversible;
2. memoization is unsafe because the apparent identity and meaning of a type can change;
3. the cost of retrying and cloning grows quickly in advanced cases.

### Generics and constraints

Ty supports ordinary inferred generics and explicit type parameters, subtype bounds, operator constraints, subscript constraints, heterogeneous packs, and repeated element packs. Simple cases work well:

- a noncapturing identity function generalizes and can be used at several types;
- a directly called heterogeneous variadic function can preserve each argument's type;
- standalone bounded functions reject obvious violations;
- subscript constraints can preserve tuple projection;
- direct generator send types are checked.

Where bounds are converted to function constraints in [src/types.c:3633](src/types.c#L3633). For an identifier bound, the bound is also installed as the identifier's type in the function body. Repeating bounds for the same variable overwrites that environment view rather than constructing their meet.

Function instantiation clones t0, t1, and t2 for each constraint at [src/types.c:4394](src/types.c#L4394), but not every auxiliary field is treated consistently on every instantiation path. Constraint solving repeatedly retries the full pending list at [src/types.c:6599](src/types.c#L6599). CullConstraints may solve and remove obligations while reducing a type at [src/types.c:5937](src/types.c#L5937), making normalization impure.

### Subtyping and overloads

Nominal class inheritance and declared trait implementation coexist with structural record subtyping. Function inputs are checked contravariantly and results covariantly in the basic case at [src/types.c:8936](src/types.c#L8936). Ordinary overload sets are intersections of function types and, as documented, dispatch in definition order with more-specific cases expected first. Binary operator overloads use a different most-specific algorithm because their set is open and unordered.

Those choices are reasonable, but the current implementation omits enough callable metadata that a function can pass a subtype check while not supporting calls allowed by the expected type. It also expands union-valued arguments before trying overloads, which makes both correctness and performance harder.

### Records, tuples, and flow

Records and positional tuples share TYPE_TUPLE. Names, required bits, repeat, closed, and fixed flags try to distinguish the variants. Literal construction uses non-required entries, so value tuples and record literals can accidentally acquire optional-field semantics. There is no row-tail variable to represent fields preserved through a structural generic function.

Flow refinement handles many valuable local cases: nil guards, early returns, conjunction/disjunction branches, and some direct member assignments. Refinement paths can nevertheless outlive mutations through aliases, calls, getters, captured state, await/yield-like boundaries, or other heap writes because there is no location/effect model or conservative invalidation boundary.

## What is working well

The following should be preserved during a redesign:

- Direct missing-field errors work for simple closed records. A function that reads r.z infers an open structural requirement for z, and calling it with only x and y is rejected.
- Basic function input contravariance and result covariance work.
- Common local nil refinements and early-return narrowing work and are covered by existing tests.
- Direct heterogeneous packs preserve correlations better than many small typecheckers.
- Subscript constraints are capable of expressing useful tuple projection and, in focused tests, require coverage of union arms more consistently than general binary operators.
- Guarded recursive aliases and tags support practical algebraic data structures.
- Literal types and integer-range syntax are a strong base for future refinements.
- Type values, typeof, compile-time macros, and ty.types make the type system observable from inside the language. This is a major ergonomic advantage.
- Ordered ordinary overloads are clearly documented. The problem is not that order exists; it is that static applicability, erased constraints, and callable-subtyping metadata can diverge from runtime dispatch.
- The checker is fast enough on ordinary small scripts. The severe costs are concentrated in identifiable pathological algorithms rather than every generic instantiation.

## Principal correctness findings

The findings in this section either admit a program whose inferred/declared contract is contradicted at runtime, make checking depend on irrelevant source order, or reject programs for which the current type language already has a clear principal answer.

### 1. First-bound-wins variables cannot represent subtype inference

TryBind binds an unsolved variable to one reduced Type immediately at [src/types.c:5123](src/types.c#L5123). The bounded boolean records only a hint about direction; it is not a retained bound set.

Consider:

~~~ty
fn accepts-a(x: Int | String) {}
fn accepts-b(x: String | Bool) {}

fn f(x) {
    accepts-a(x)
    accepts-b(x)
    x
}
~~~

The valid inferred parameter domain is String. The current checker rejects the second use, whichever call is written second. Reversing the statements only reverses which constraint wins.

The dual case occurs for lower bounds:

~~~ty
fn second[T](x: T, y: T) -> T { y }
second(1, 's')
~~~

Both Int and String flow into T, so the least common supertype is Int | String. With nested mutable literals, the current solver can instead create impossible intersections or order-dependent mixed unions.

An inference variable α needs an interval:

- lower bound LB(α), formed by joins of values flowing into α;
- upper bound UB(α), formed by meets of contexts in which α must be usable;
- edges α <: β where neither side is ready to collapse;
- provenance for diagnostics.

Every update checks LB(α) <: UB(α). Equality is a separate operation that unions equality metavariables. A concrete type is chosen only when required for overload commitment, annotation checking, generalization, or final display. A variable with both kinds of bounds is not equal to either bound.

This model also explains polarity cleanly:

- an actual argument flowing into a generic parameter adds Actual <: α;
- using α where Expected is required adds α <: Expected;
- a function parameter introduces contravariant constraints;
- a result introduces covariant constraints.

Explicit where bounds expose the same current problem. Changing the order of T <: Array[U] and U <: Int | String can change whether U becomes Int or remains Int | String. Repeated structural bounds for one variable do not combine inside the body because PutEnv installs only one visible bound at [src/types.c:3666](src/types.c#L3666).

### 2. Speculative unification mutates state without rollback

Conditional typing first tries UnifyX in one direction, then the other, then constructs a union at [src/types.c:11216](src/types.c#L11216). Those probes are not observational: they can bind variables before failing.

For example, the inferred type of a function equivalent to:

~~~ty
(b, x) -> b ? x : 's'
~~~

specializes x to String instead of inferring x -> x | String. Reversing structurally similar branches can change literal precision.

The same issue appears in:

- join construction in unify2_ at [src/types.c:9974](src/types.c#L9974);
- overload applicability trials;
- union and intersection comparisons;
- operator resolution;
- object unification;
- constraint culling.

This cannot be made reliable with save/restore of only the pending vectors and current level. Candidate trials need an undo log, persistent solver state, or cloned solver variables with commit-on-success. Immutable type terms plus transactional solver nodes are the simplest long-term boundary.

### 3. Mutable generic types are treated covariantly

Nominal object arguments are compared in the same direction at [src/types.c:8899](src/types.c#L8899). There is no variance declaration, so Array[Int] is accepted where Array[Int | String] is expected. The wider reference can append a String; the original reference still has static type Array[Int].

The same pattern applies to Dict, writable records, user-defined Box-like containers, queues, references/pointers, and any Future/promise object whose result or state is writable. This is a fundamental mutability rule, not a collection special case.

Recommended rule:

- generic parameters are invariant by default;
- readonly producers such as Iterable[T] may opt into covariance;
- consumers may opt into contravariance;
- a type with both read and write use remains invariant;
- writable structural fields are invariant unless the object is readonly;
- variance declarations are validated against member signatures.

The replacement checker should implement invariance by default and representation-level variance metadata from the outset. Hard-coding a partial rule into the legacy checker would create another temporary semantic variant and is outside the migration plan.

### 4. Contextual literal checking can inhabit impossible intersections

Fresh literal assignment uses bidirectional unification paths that can turn a contradiction into an intersection rather than reject it. Observed examples include:

~~~ty
let a: Array[String] = [1]
fn take(xs: Array[Int]) {}
let xs = ['s']
take(xs)
~~~

The first can be accepted while a[0] is statically String but actually 1. The second can leave xs with an element type resembling String & Int. Similar behavior occurs for nested tuple and dictionary literals.

An intersection of disjoint primitive classes is Never; it is not a coercion and must not make a literal satisfy both sides. Fresh mutable literals may use weak element metavariables for contextual inference, but a final constraint conflict must fail. This should be solved by lower/upper-bound consistency, not by synthesizing intersections after destructive equality attempts.

### 5. Generalization is unsafe around captured mutable state

The current level/occurrence heuristic can generalize variables reachable from mutable closure state. A representative shape is:

~~~ty
let f = do {
    let saved = []
    x -> do {
        saved.push(x)
        saved[0]
    }
}

let a: Int = f(1)
let b: String = f('s')
~~~

Both uses can typecheck even though the second call can retrieve the earlier Int through a result typed String.

Generalization must quantify FV(type) minus FV(environment), not simply variables at a level that occur enough times. Variables reachable through mutable allocations or captured mutable bindings must be weak/non-generalized. Standard options are:

- an ML-style value restriction;
- relaxed value restriction using variance;
- weak metavariables for expansive expressions and mutable cells.

Ty's scripting ergonomics favor a relaxed restriction: freely generalize syntactic values and covariant variables, but keep variables under mutable/invariant constructors weak.

### 6. Union operations use existential success in several paths

For an operation on a value of A | B, every inhabited arm that can reach the operation must support it. The result is the join of each arm's result. For a binary operation on (A | B) and (C | D), every reachable pair needs coverage unless control-flow information rules a pair out.

Current member access loops over union arms and skips failures at [src/types.c:7846](src/types.c#L7846). Union calls similarly combine successful results and ignore noncallable arms at [src/types.c:7403](src/types.c#L7403). Inferred binary-operator constraints are commonly non-exhaustive, so one valid pair can justify a union operation.

Observed consequences include:

- reading .a from {a: Int} | {b: String} and treating the result as Int;
- calling a value typed (Int -> Int) | Int and accepting the Int arm;
- accepting + on unions for which only some operand combinations exist;
- accepting an Int | Float operation with result Int even when the Float path produces Float;
- ordinary member access on T | nil being typed as T's field, even though nil throws before a later coalescing operator can run.

Safe navigation is a distinct operation and should yield Field | nil. Ordinary navigation must require the field on every arm. Overload resolution should return a coverage result, not just the first successful candidate trial.

### 7. Structural intersections are both unsound and incomplete

There is a direct indexing defect in intersection field checking: the loop is bounded by t0->types but indexes t1->types at [src/types.c:8422](src/types.c#L8422). A value typed {a: Int} & {b: String} can therefore be accepted where {a: String} is expected, allowing a String method on an Int.

Even after fixing that typo, intersection semantics need normalization. The checker also rejects valid evidence combination such as:

~~~ty
{a: Int} & {b: String} <: {a: Int, b: String}
~~~

An intersection introduction/elimination policy should be explicit:

- X <: A & B iff X <: A and X <: B;
- A & B <: X is not generally equivalent to either arm alone, but structural evidence from compatible record arms can be merged;
- incompatible field intersections normalize to Never;
- overload intersections must remain distinguishable from value intersections, or at least carry ordered-overload metadata.

### 8. Record rows and field presence are not preserved

The current tuple-backed record representation cannot express:

- exact versus open rows independently of fixedness;
- a row tail preserved through a generic function;
- required, optional, and known-absent fields with distinct read behavior;
- correlation between union arms.

Observed effects:

- [{x: 1}, {y: 's'}] can infer only one optional field depending on element order;
- accessing the absent field on the first element can compile and then fail;
- disjoint-record conditionals can collapse toward one branch;
- a function that accepts an object with field a and returns that same object loses unrelated field b, which later becomes an unconstrained fresh type;
- optional field reads return T rather than T | nil;
- both x.a and x.?a may have the same static type even though the first can fail and the second can return nil.

Use row types:

~~~text
{ a: A, b?: B | ρ }
~~~

where ρ is a row variable and fields carry presence constraints: required, optional, absent, or unknown. A function preserving its input can quantify ρ:

~~~text
forall A, ρ. { a: A | ρ } -> { a: A | ρ }
~~~

Do not encode openness by silently making literal fields optional. Requiredness is about presence; mutability and exactness are separate axes.

### 9. Fixed tuple arity is not enforced

Tuple literals are constructed with entries marked non-required at [src/types.c:9093](src/types.c#L9093). As a result:

- a two-element value can satisfy a three-element annotation;
- a longer tuple can satisfy a shorter annotation while the runtime value retains extra elements;
- tuple-mapping overloads can infer the arity of one case while runtime iteration processes another.

Fixed tuples need exact length and required positional entries. Variable length should require an explicit pack/repeat tail. Optional positional parameters in function calls are not the same as optional elements in a runtime tuple.

### 10. Several surface operations bypass their declared contracts

These are independent compiler/checker integration requirements for types2. They should be implemented and logged by the shadow checker without changing what the legacy checker accepts:

- Subscript assignment is not checked. Expression-context subscripts call type_subscript at [src/compiler.c:5103](src/compiler.c#L5103), but lvalue assignment has no corresponding setter/subscript constraint in type_assign. Array[Int][0] = 's', wrong Dict keys/values, and custom []= calls with wrong arguments can compile.
- Compound assignments only symbolize both sides and reuse the target type at [src/compiler.c:5177](src/compiler.c#L5177). They do not validate the underlying operator or assignment back to the target.
- Prefix minus, question, at, increment, and decrement copy the operand type at [src/compiler.c:4965](src/compiler.c#L4965) without validating an operator.
- Membership and non-membership return Bool without checking the container operation at [src/compiler.c:4869](src/compiler.c#L4869).
- Range construction assigns Range without validating endpoint types at [src/compiler.c:4901](src/compiler.c#L4901).
- Bad default arguments can be accepted because default validation uses a nonchecking unification path and some call paths do not force it. A function declared x: Int = 's' can return a runtime String through a result typed Int.

All of these should desugar, for type purposes, to the same operator/member calls used at runtime. Compound x += y additionally requires ResultOfPlus <: TypeOfWritableTarget.

### 11. Function subtyping omits call-shape information

The basic variance directions are correct, but paired parameters are compared mainly by type and rest/keyword flags. Names and required/default status are not checked as a complete call capability at [src/types.c:8936](src/types.c#L8936).

This admits callbacks that do not support calls permitted by the expected function type. For example, an expected function whose parameter is named x can be invoked with x=1; a supplied function accepting only y may pass the subtype check, then receive no y at runtime. Similarly, a callback expected to allow omission can be replaced by one with a required parameter.

Function types should describe a call protocol:

- required positional prefix;
- optional positional parameters;
- accepted keyword names and their types;
- positional-rest type or pack;
- keyword-rest row;
- return/yield/send types;
- effects if Ty later tracks them.

Subtype checking then asks whether the actual callback accepts every call the expected callback permits, and whether its result is compatible.

### 12. Trait and override conformance is not validated

Declaring a trait merely sets a nominal implementation bit in [src/class.c:471](src/class.c#L471), and class subtyping trusts that bit at [src/class.c:489](src/class.c#L489). AddClassTraits performs no member validation at [src/compiler.c:17552](src/compiler.c#L17552). Superclass processing can inherit an omitted return annotation but does not validate an explicitly incompatible override at [src/compiler.c:12585](src/compiler.c#L12585).

Observed results:

- a class can declare a trait while omitting a required method;
- a method with an incompatible return can satisfy a trait bound statically;
- a subclass can replace a method with an incompatible signature.

Validate trait conformance once the class body is resolved. Validate overrides with function subtyping, including call shape. If traits can contain defaults, distinguish required members from supplied implementations. If abstract/incomplete classes are desired, represent that explicitly and reject their construction.

### 13. Recursive checking fails open

type_check_x returns true whenever recursive depth exceeds 64 at [src/types.c:9001](src/types.c#L9001). Focused nested generic checks show unequal types becoming subtypes at depth 64 and beyond.

A depth limit may abort with a diagnostic or conservatively fail, but it must not prove arbitrary subtyping. The correct technique is a visited pair table:

- memoize normalized (expected, actual, relation) pairs;
- accept a repeated pair coinductively only after at least one contractive constructor step;
- distinguish in-progress from proven/failed;
- impose a separate resource budget that reports complexity rather than returning true.

The main type-check memo is currently disabled at [src/types.c:9075](src/types.c#L9075), largely because mutable types make cached answers unstable.

### 14. Recursive aliases are not required to be guarded

Common guarded aliases such as a Node containing Node | nil work. Unguarded recursion does not:

- use Loop = Loop can hang;
- mutually recursive aliases with only union indirection can cause revisit logic to accept an unrelated type.

Build an alias dependency graph, find strongly connected components, and require every recursive cycle to pass through a contractive runtime constructor such as a tag, tuple/record, function, or nominal object. Alternatively introduce explicit μ-types. Pairwise subtype recursion should use the progress-aware rule above, not a blanket already-visiting success.

### 15. Failed occurs checks silently become dynamic-like bottom

Occurs has a duplicated IsConcrete test and treats an already visited node as an occurrence at [src/types.c:4147](src/types.c#L4147). More importantly, TryBind responds to an occurs failure by binding the variable to BOTTOM and returning success at [src/types.c:5130](src/types.c#L5130).

Self-application can therefore infer a function containing a green/dynamic-looking placeholder rather than reporting an infinite type or requiring an explicit dynamic escape. Passing an incompatible function then fails only at runtime.

Choose one policy:

- reject infinite inferred types with a clear diagnostic;
- support explicit equi-recursive types;
- allow the programmer to insert Dynamic/underscore.

Silently erasing the constraint is neither predictable nor principled.

### 16. Literal integer range subtyping is incorrect

The range/int case in IsLitSubtype compares the upper bound with t0->z even though t0 is the range at [src/types.c:3003](src/types.c#L3003). Current probes reject integer literals that runtime range membership accepts, and the code also disagrees with the runtime's half-open endpoint semantics.

Fix the operand reference, define whether a..b is [a,b) and a...b is [a,b], and use the same convention in:

- literal subtyping;
- runtime membership;
- iteration;
- exhaustiveness;
- displayed range types.

### 17. Constraint normalization can erase obligations

CullConstraints calls BindConstraint while reducing a function type and deletes obligations it can currently solve at [src/types.c:5937](src/types.c#L5937). Because types and solver variables are mutable, the apparent proof can depend on unrelated current state or even on the obligation itself.

Combining a constrained generic function with an overload can make the constraint disappear. A function restricted to Int plus a Float overload can then accept a String and fail in the function body. A standard-library example is Array.sum: a boolean array can be inferred to have a Bool sum even though runtime addition produces an Int.

Make normalization pure and idempotent. Obligations should have stable identities and be retained until discharged against a committed substitution. Do not let an obligation prove itself. Overload construction should copy or share immutable schemes, not reduce them in ambient solver state.

There is also a direct probable typo in BindConstraint: t1 is reduced twice and t2 is not reduced at [src/types.c:6453](src/types.c#L6453).

### 18. Receiver-dependent method constraints do not reliably propagate

Constraints relating a class type parameter to method parameters often fail to solve the method variables after receiver instantiation. A concrete Array[(Int, String)].unzip2() can leave the second result as Array[$a], after which arbitrary methods on its elements may compile.

Affected prelude families include transpose, unzip2/3/4, chain-like flattening, remove!, and some synchronization/subscript helpers. Equivalent standalone constrained functions often work, which points to ordering/substitution rather than an expressiveness limit.

Instantiate the receiver and method scheme into one call-local solver, add all receiver equalities first, then enqueue method obligations keyed to those variable roots. Dependency watchers should wake them after substitution.

### 19. Flow refinements survive mutations that can invalidate them

Local immutable-looking refinements are useful, but heap paths are treated as stable across calls and aliases. A field narrowed from T | nil to T can be cleared by a called function or captured closure and still be used as T. A getter can be evaluated once for the condition and again for the body even if the second call returns nil.

Initial types2 rule:

- refine stable locals and immutable fields;
- invalidate member/path refinements after an unknown call, write through a possibly aliased reference, await/yield, or captured mutation;
- never assume repeated getter calls return the same value unless the getter is marked pure/stable.

Later, effect and escape summaries can retain more refinements without sacrificing correctness.

### 20. Match exhaustiveness is not represented

A match on a known literal or union may omit all reachable cases, yet its result is typed only from the written arms. Runtime then raises MatchError. Exceptions are not generally tracked in function types, so this may be an intentional partial-operation policy, but it conflicts with the goal of rejecting provably wrong programs.

At minimum:

- reject or warn on a statically known non-exhaustive match over closed literal/tag/union domains;
- report unreachable arms;
- require a default for open domains;
- make an explicit partial-match expression available if throwing is desired.

### 21. Return/fallthrough analysis can prove impossible returns

Loop statements copy the body's will_return flag even when the loop may execute zero times. Consequently:

~~~ty
fn f() -> Int {
    for x in [] {
        return 1
    }
}
~~~

can compile, return nil, and be consumed as Int. A C-style loop with an initially false condition behaves the same way. The function finalizer skips its implicit-fallthrough check because the loop claims to return.

Only constructs that execute their body unconditionally may propagate a definite-return fact directly. A for or ordinary while returns on all paths only when the checker can prove at least one iteration and a returning body, or when every exit path returns/throws. Otherwise its outgoing control-flow set includes fallthrough.

A related case occurs for if without else when its only written branch returns: nil/bottom accumulation can lose the implicit fallthrough even though the statement's will_return flag itself is false. Return analysis should operate on explicit control-flow outcomes rather than overloading expression result types and bottom sentinels:

~~~text
Flow = FallsThrough | Returns(Type) | Throws | Breaks | Continues
~~~

Branch combination then unions outcome sets. Function checking rejects FallsThrough when the declared result excludes nil.

### 22. Static nil/pointer and runtime matching disagree

The static subtype checker has a special case accepting nil where Ptr or IntoPtr is expected at [src/types.c:8649](src/types.c#L8649), while runtime nil :: Ptr[Any] is false. Pointer arithmetic can consequently be accepted on nil and fail through an operator lookup.

Choose one contract:

- nullable pointer is represented by Ptr[T] | nil and must be narrowed;
- Ptr[T] deliberately includes null, in which case runtime matching and every pointer operation must implement that contract;
- introduce NonNullPtr[T] and Ptr[T] as distinct nominal types.

The first option is the most consistent with the rest of Ty's union-based nil handling.

### 23. Type reflection does not round-trip all type forms

The type-value API is an important strength, so representation round trips should be treated as conformance tests. Current defects include:

- decoding TyListT as TYPE_INTERSECT instead of TYPE_LIST;
- no type_to_ty cases for TYPE_RANGE and TYPE_ERROR;
- bottom/unknown metadata that exposes flags rather than stable semantic categories;
- the intersection field-indexing defect described above.

Observed consequences include a reflected List being recognized as Intersect and type metadata for ranges/errors becoming nil. Add a round-trip test for every Type constructor:

~~~text
decode(encode(T)) ≡ normalize(T)
~~~

where intentionally non-reifiable internal solver variables are rejected explicitly instead of silently turning into nil.

## Advanced generic and expressivity findings

### Variadic generics

Ty has two useful pack modes:

- heterogeneous packs that preserve an argument sequence;
- repeated element packs used for dynamic spreads and homogeneous variadics.

Direct calls demonstrate that the core idea is viable. The limitations are in representation and validation:

- only one final pack is implemented coherently, but the grammar accepts multiple or non-final packs and can produce nonsensical types;
- packs in overload sets are unreliable;
- Array.zip works for some single heterogeneous companions but loses or rejects combinations with several inputs;
- empty older-style packs can produce bottom-like tuple elements;
- generic type application does not validate arity, so too many arguments are retained and too few leave unresolved class variables;
- variadic operator constraints can be ineffective: max(1, 's') and min() can compile and fail at runtime;
- at least one instantiation path clones the operator object but does not consistently rebind all constraint operands.

For its first complete pack implementation, types2 should diagnose unsupported pack placement and enforce generic arity. Its final representation should use sequence metavariables with prefix, suffix, element, and length constraints. A pack solver should be able to express:

~~~text
P = [A, B] ++ Q
len(P) >= 2
map(Array, P)
~~~

without converting the sequence to one ordinary Type variable.

### Bounds and constraint propagation

Subtype bounds, operator bounds, and subscript bounds are valuable, but they should be immutable scheme predicates instantiated with the quantified variables. A function scheme should resemble:

~~~text
forall T, U. (T) -> U where T <: Array[U]
~~~

Instantiation creates fresh metas for T and U and fresh obligations. Bounds visible inside the function body should be the conjunction/meet of all declared predicates, not the last environment binding.

Parser/surface issues also need tightening:

- inline forms such as T: Bound in type-parameter lists can be accepted but ignored in some declaration kinds;
- an advertised and separator can drop later bounds while comma-separated constraints work;
- declared generic application arity is unchecked;
- unsupported pack arrangements are parsed instead of diagnosed.

These should become syntax errors or real constraints; silently accepted no-ops are especially damaging to consistency.

### Higher-order polymorphism

Ty supports useful rank-1 let polymorphism. It does not have a first-class forall/scheme type that can be passed as a value. Passing a polymorphic identity function to a consumer that calls it at Int and String usually monomorphizes the callback and returns broad unions, losing the per-call input/result relationship. An overloaded function that collectively covers a union may also fail as a callback even though direct calls work.

This is a genuine expressivity limit rather than an urgent bug. If rank-1 is the intended boundary, document it and improve diagnostics. If higher-rank callbacks are desired, add an explicit scheme/forall type and bidirectional checking at annotated boundaries rather than attempting full impredicative inference.

Higher-kinded type parameters, associated types, and conditional trait implementations are also absent. The standard library currently approximates some of them with computed type functions, output-only generics, underscore, and special constraints. They are lower priority than making rank-1 inference and mutable variance correct.

### Computed types

TYPE_COMPUTED invokes Ty code while resolving a type at [src/types.c:2343](src/types.c#L2343). The prelude uses this to flatten arrays and unpack type sequences. This is powerful and fits Ty's same-process design, but arbitrary type computation raises predictability concerns:

- termination and fuel;
- side effects during compilation;
- cacheability and determinism;
- diagnostics when the returned value is not a valid type;
- dependency invalidation;
- performance on repeated normalization.

Treat type functions as an explicit compile-time phase with memoization keyed by canonical type arguments. Prefer pure functions and diagnose side effects if practical. Do not let computed-type evaluation mutate inference variables belonging to a speculative overload branch.

## Standard-library audit

The standard library is both a client and an informal specification of the type system. It demonstrates real expressive strengths, but also contains signatures that currently rely on unchecked assumptions.

### Collections

Array and Dict are mutable but currently participate in covariant nominal checking. This is the most consequential library-wide issue.

Other collection findings:

- Dict.[](K) is declared to return V, but a missing key returns nil. The type should be V | nil unless the dictionary carries a total/default contract.
- String indexing can return nil out of range while being typed String.
- Array and tuple indexing are partial. A known constant out-of-range index can be rejected statically; otherwise the operation should be documented as throwing or return an optional form.
- Dict's runtime type predicate checks keys and then reads p.0 and p.1 from each key in [lib/prelude.ty:1030](lib/prelude.ty#L1030), instead of iterating items. It can therefore disagree with the static Dict[K,V] relation.
- Dict.map can lose the key type under inference and be coerced to an incompatible dictionary annotation.
- flat(n) computes a return type that removes all array nesting even when runtime n removes only part of it. This needs either a depth-indexed/dependent helper, a finite overload family, or a deliberately less precise result.
- tuple arity bugs affect tuple mapping and zip-like APIs.
- Array.sum overload/constraint erasure permits booleans and can report the wrong result type.

Introduce readonly interfaces for most higher-order consumers:

~~~text
Iterable[+T]
Sequence[+T]
MutableArray[T] : Sequence[T]
ReadonlyDict[+K,+V] or Iterable[(K,V)]
MutableDict[K,V]
~~~

The exact names are less important than separating covariant observation from invariant mutation.

### Optional records and parser APIs

The prelude uses optional record fields for real data, including parser information whose tokens/free fields may be missing. Because optional reads currently produce T rather than T | nil, these declarations overpromise. Fixing optional presence may initially surface many library errors; that is evidence that the current representation was hiding necessary checks.

APIs should choose among:

- required field;
- optional field read as T | nil;
- tagged presence such as Some[T] | None;
- exact alternate record variants as a discriminated union.

### Generators

Generator[T,S] nominally implements Iter[T] for every S, while iteration resumes it with nil. A generator that requires a non-nil send value can therefore be used in for and fail when resumed.

Options:

- Generator[T,nil] alone implements Iter[T];
- split Iterator[T] from Coroutine[T,S];
- add conditional conformance when S admits nil.

This is a concrete motivation for conditional trait implementation, but a hard-coded built-in rule is acceptable until that feature exists.

### Threads and futures

ThreadPool.submit declares a relation between the pool's function F, an Args pack, and result T, but current pack/constraint solving does not reliably validate the submitted arguments. Future/result types are also mutable-state-bearing and should not be covariant unless their interface is strictly readonly after construction.

### SQLite and output-only generics

fetchOne[a], fetchAll[a], and similar query APIs let the caller choose an output type not derivable from runtime schema. This is effectively a hidden unchecked cast. It is convenient, but it should be explicit:

- return Dict[String, Dynamic] or row values;
- accept a decoder function;
- require a schema/type witness;
- expose a concise cast at the call site.

An unconstrained result-only generic has no principal inferred value and should not pretend to validate the database result.

### Contradictory declarations and module health

There are conflicting os.listdir declarations: [lib/prelude.ty:299](lib/prelude.ty#L299) returns [String], while [lib/os.ty:213](lib/os.ty#L213) says [Float] | nil. The prelude declaration can mask the latter.

A sample compile of library modules also found:

- llhttp fails a deferred dictionary-subscript check around its request handling; http inherits the failure;
- some modules only load with -q;
- tree, tickit, and sdl expose parse, missing FFI helper, or type/main issues.

This was not an exhaustive module matrix, so it should be treated as a request for automated library checking rather than a complete defect list. Add a test that compiles every supported lib module with types enabled and records intentional platform exclusions.

## Performance audit

### Measured behavior

Measurements used the existing GCC 14.2/mimalloc binary at a5746a3, without ASan or TY_PROFILE_TYPES. Commands used -b -c so the synthetic programs were compiled but not executed. Warm-cache times include parsing and prelude compilation.

| Workload | Size | Total time | Peak RSS |
|---|---:|---:|---:|
| Version only | — | 0.919 ± 0.041 ms | — |
| Basic compile of nil | — | 212.9 ± 11.5 ms | about 63 MiB |
| Full compile of nil | — | 333.9 ± 17.2 ms | — |
| Union-argument overloaded call | 128 combinations | 228.2 ± 9.6 ms | 75.5 MiB |
| same | 256 | 244.8 ± 7.3 ms | 91.5 MiB |
| same | 512 | 284.8 ± 10.6 ms | 126.7 MiB |
| same | 1,024 | 385.7 ± 5.1 ms | 203.4 MiB |
| same | 2,048 | 627.1 ± 34.4 ms | 370.6 MiB |
| same | 4,096 | fuel exhausted after 1.08 s | 701.7 MiB |
| 100 structural calls | 400 fields | 312.9 ± 11.3 ms | — |
| same | 800 fields | 565.1 ± 38.5 ms | — |
| same | 1,600 fields | 1.450 ± 0.037 s | — |
| reverse-ordered structural union | 500 arms | 379 ± 76 ms | — |
| same | 1,000 arms | 843 ± 27 ms | — |
| same | 2,000 arms | 2.897 ± 0.061 s | — |
| same | 3,200 arms | 8.70 s, one run | — |
| same | 4,000 arms | 13.41 s, one run | — |

A single unique-record union, without a call, took roughly 0.20, 0.28, 0.58, and 1.98 seconds at 500, 1,000, 2,000, and 4,000 arms. This confirms quadratic normalization independently of overload matching.

Building 75, 100, 125, 150, and 180 same-name static overloads without calling them took 0.24, 0.34, 0.45, 0.72, and 1.14 seconds. At 185 overloads the global 999,999-step fuel budget was exhausted. A reverse dependency chain of deferred operator constraints succeeded at 790 constraints but exhausted fuel at 800; the same 800 constraints in dependency order compiled in about 0.21 seconds.

Ordinary generic instantiation scaled comparatively well. Ten calls involving 500, 1,000, and 1,500 used type parameters took about 0.21, 0.25, and 0.29 seconds. Thousands of unused parameters reveal a weaker repeated-reference-scan cost, but this is not the first optimization target.

### Root causes

1. Eager Cartesian call expansion. ExpandCallSignatures at [src/types.c:6937](src/types.c#L6937) materializes the product of all union arms across positional and keyword arguments. InferCall then tests overloads and repeatedly clones candidates for every combination. Binary operators contain a separate left-union × right-union × overload loop.

2. Effectively cubic overload-set construction. Each appended overload is combined and Reduced; Reduce invokes Uniq at [src/types.c:3243](src/types.c#L3243), which performs linear containment/subtyping searches for each arm. Repeating quadratic normalization over every growing prefix yields cubic construction.

3. Quadratic union normalization and matching. Union containment scans linearly; union-vs-union subtype checking nests scans at [src/types.c:8661](src/types.c#L8661). Union arms are not canonicalized or hash-indexed.

4. Quadratic structural-record matching. Field lookup scans names for each expected field. Fixed records do not have a field-name index.

5. Whole-list constraint retries. TryProgress copies and retries every unresolved constraint whenever any one progresses at [src/types.c:6599](src/types.c#L6599). Reverse dependency order therefore becomes quadratic and fuel-sensitive.

6. Deep cloning and repeated free-variable scans. NewInst0, Propagate, and Inst1 recursively clone without a source-node-to-clone memo. Generalization repeatedly traverses graphs with CountRefs. ResolveVar lacks path compression.

7. Disabled general memoization. Type comparison memoization is disabled because mutation makes cached results unsafe. This is another reason the immutable-term/solver-state split is a performance change as well as a semantic one.

### Profiling infrastructure

PROFILE_TYPES=1 enables TY_PROFILE_TYPES through [Makefile:55](Makefile#L55), but the hook is highly perturbative. It clones type pairs and linearly searches timing entries using deep AlmostSameType comparisons before timing the interesting operation. Its overhead and fuel use can dominate the event being measured. DumpTypeTimingInfo has no repository caller, and accumulated TypeCheckTime is not consumed.

Replace this with:

- lightweight counters for unifications, subtype pairs, candidate trials, union products, clones, and constraint wakeups;
- phase timers written to stderr or structured output;
- slow-event snapshots captured only after a threshold is crossed;
- per-compilation peak solver-node and pending-obligation counts.

### Optimization order

This is the implementation order for types2, not a retrofit sequence for the legacy checker:

1. Candidate-first lazy overload traversal. Split a union only when a candidate's viability differs by arm; prune early; memoize candidate/argument-index/substitution state; clone only on commit.
2. Batch overload construction and normalize once.
3. Canonical hash/index union and intersection arms; fast-path nominally disjoint constructors.
4. Index fields in fixed/closed records.
5. Replace rescans with variable-root dependency watchers.
6. Add source-node memoization and copy-on-write substitutions during instantiation.
7. Cache free-variable sets for immutable schemes.

## Recommended architecture

Everything in this section is a design for src/types2.c. It should not be retrofitted piecemeal into src/types.c, nor should individual language constructs be gradually switched from the old checker to the new one. During shadow development, types2 owns a completely separate type universe, inference state, caches, diagnostics, and AST-node side tables. The legacy Type graph remains the sole source consumed by the compiler and runtime until the atomic cutover.

### 1. Separate immutable types from solver variables

Use immutable/hash-consed terms for stable structure:

~~~text
Int
LiteralInt(1)
Object(Array, [T])
Function(CallShape, Return)
Union(sorted unique arms)
Record(fields, row tail, exactness, mutability)
Mu(id, body)
~~~

Keep mutable inference state in a compilation-local solver:

~~~text
MetaRoot {
    parent, rank,
    lower_bound,
    upper_bound,
    subtype_successors,
    subtype_predecessors,
    watchers,
    level,
    rigidity,
    weakness,
    provenance
}
~~~

Type syntax refers to Meta(id), RowMeta(id), or PackMeta(id), but terms themselves do not change. Equality uses union-find with path compression. Joining roots merges bounds and watchers. Subtype constraints update bounds or add edges. This makes hashing, memoization, transactions, and diagnostics tractable.

### 2. Use distinct variable kinds

At minimum:

- flexible equality/subtype metavariable;
- rigid declared/skolem variable;
- quantified scheme variable;
- weak metavariable that cannot be generalized;
- row variable;
- pack/sequence variable.

Do not encode these distinctions with combinations of val, fixed, bounded, variadic, and packed. Illegal operations should be impossible or explicit in the API.

### 3. Define the core relations independently

Implement and test separately:

- equals/unify for equality constraints;
- subtype;
- consistent for gradual compatibility;
- join for least common supertypes;
- meet for greatest common subtypes;
- narrow for flow refinement;
- normalize for pure canonicalization.

Each relation should have algebraic laws in tests: reflexivity where applicable, idempotent joins/meets, commutativity of unordered unions/intersections, source-order independence, and monotonic solver progress.

### 4. Make overload trials transactional

Each candidate trial starts from a solver snapshot/undo-log mark. It produces one of:

- applicable with substitution and obligations;
- definitely inapplicable with a reason;
- deferred on specified metas;
- partially covers specified union arms.

Only the selected candidate or agreed join of candidates commits. Ordinary overloads may keep documented first-match behavior; binary operators may keep specificity ordering. Both should use the same applicability engine and universal union-coverage rule.

### 5. Treat schemes and obligations as immutable

A generalized function value owns a scheme:

~~~text
forall [T, P, ρ].
  parameters -> result
  where predicates
~~~

Instantiation creates fresh metas and copies predicate references through a substitution map. Predicates are solved in call-local state and retain provenance. Pure normalization never deletes them.

### 6. Add rows, packs, and variance as first-class concepts

These are not optional embellishments:

- rows preserve structural information necessary for return correlation and optional presence;
- pack variables preserve sequence information necessary for heterogeneous variadics;
- variance is necessary to make mutable generics correct.

Trying to recover any of these from ordinary Type variables after binding will continue to require special cases.

### 7. Make recursion explicit and guarded

Normalize recursive aliases to guarded μ-terms or reject unguarded SCCs. Use visited relation-pairs with constructor progress for coinduction. Keep a resource limit, but make exhaustion a diagnostic rather than success.

### 8. Define gradual escape hatches deliberately

A syntactically quiet proposal compatible with current style:

- underscore: Dynamic, operations permitted with runtime checking;
- Any: top type, useful for storage/consumption but not arbitrary member elimination;
- unknown or a named alternative: requires narrowing;
- as T / cast[T]: explicit unchecked assertion;
- .?field: safe optional access yielding T | nil;
- -q: whole-program opt-out.

If backwards compatibility requires underscore to retain current behavior, document that it is Dynamic rather than calling every bottom-colored placeholder unknown.

## Parallel replacement implementation plan

The findings above are acceptance criteria for a replacement, not a patch list for src/types.c. The legacy checker should remain unchanged throughout development. No construct should be gradually routed to types2, and types2 should never fall back to legacy inference for a difficult case. A hybrid checker would preserve the very order dependencies and semantic boundaries this replacement is intended to remove.

### Shadow-mode contract

The compiler should drive the legacy checker and the new implementation in src/types2.c at the same stable compilation-unit/declaration/statement checkpoints. During this period:

- the legacy checker remains the only authority for accepting or rejecting a program;
- legacy Type pointers remain the only types written to Expr, Symbol, Class, bytecode, JIT, typeof, type reflection, or runtime-facing state;
- types2 owns a separate type universe, solver arena, environments, caches, diagnostics, and side tables keyed by AST nodes or stable source IDs;
- types2 must not mutate legacy Type nodes, AST _type fields, symbol types, class metadata, operator tables, refinement state, or pending legacy constraints;
- a types2 mismatch or inferred error is data, never a compiler error, longjmp, exit-status change, fallback decision, or reason to alter emitted code;
- with shadow logging disabled, program stdout/stderr, diagnostics, exit status, bytecode/JIT choices, and runtime results must be identical to a build without types2;
- with logging enabled, the log is the only intended semantic output difference;
- a recoverable internal types2 failure should abandon that shadow pass, record an internal-error event, and allow the legacy compilation to continue;
- normal compilation must never expose a types2 type through typeof or ty.types before cutover.

Running a second checker necessarily consumes development-build time and memory. Measure that overhead and keep logging opt-in. A test-only switch may disable the shadow pass to prove behavioral equivalence, but normal development/CI builds during this project should drive both checkers. That switch must never select language semantics.

Computed types and compile-time type functions need special care. Shadow mode must not execute a type macro, VM callback, FFI operation, or other compile-time computation a second time, because duplicate execution could be observable. Until a single-evaluation broker exists, types2 should consume a read-only snapshot of the already materialized result or report the node as deferred. That is an allowed external input boundary, not permission to seed ordinary inference from legacy Type answers.

### Phase 0: freeze behavior and define the oracle

Before adding the shadow invocation:

- record the current test-suite and supported-library compilation outcomes;
- add focused fixtures for every confirmed issue in this report;
- classify each fixture by desired types2 behavior, independently of what legacy currently does;
- name the intended meanings of Any, underscore, Never, Unknown, Dynamic, Error, Object, and runtime :: matching;
- record representative typeof output, diagnostics, runtime behavior, JIT-facing type facts, and performance baselines;
- add metamorphic/property cases for arm-order independence, statement-order independence, failed-candidate rollback, union coverage, disjoint meets, guarded recursion, and fuel exhaustion.

The legacy result is useful differential data, but it is not the oracle for known defects. Every intentional future disagreement needs a checked-in expected outcome explaining why the types2 result is correct.

### Phase 1: add an inert types2 skeleton

Create src/types2.c with a narrow lifecycle API called by the compiler. The first implementation should do no inference:

1. allocate an independent per-compilation context;
2. observe the resolved AST/scope events it will eventually need;
3. assign stable source/node identifiers;
4. emit optional structured heartbeat/coverage events;
5. free all shadow state at the end of compilation.

Add a shadow-on/shadow-off equivalence test. With logging disabled, compare exit status, diagnostics, program output, and any stable compiled artifact or JIT-decision trace available. This test remains a permanent guard against accidental influence.

Compiler integration should consist only of these shadow lifecycle calls and logging configuration. Do not add hooks inside src/types.c or reuse its mutable global state. If types2 needs facts from parsing, name resolution, class construction, or macro expansion, expose read-only compiler facts at a stable boundary.

### Phase 2: build the independent type core

Implement the replacement representation directly in types2:

- immutable canonical type terms;
- distinct Never, Unknown, Dynamic, Any/top, Object, Error, and no-type sentinels;
- equality union-find with rank and path compression;
- lower/upper bounds and subtype edges;
- dependency watchers and provenance;
- pure subtype, gradual-consistency, join, meet, narrowing, and normalization relations;
- transactional candidate state using an undo log or persistent snapshots;
- explicit quantified, rigid, weak, row, and pack variables;
- guarded recursive terms and progress-aware coinductive comparison;
- deterministic printers and structural hashes.

This phase should be testable without the compiler through a types2-specific unit harness. In particular, test solver laws and deliberately adversarial constraint graphs before expression inference depends on them.

No legacy Type node should appear in the types2 core API. A read-only adapter may translate externally declared nominal class identities, literal constants, or already evaluated computed-type results, but it must construct native types2 terms and must never copy legacy metavariable solutions.

### Phase 3: add language coverage in shadow-only milestones

Implement expression and declaration inference in dependency order while keeping every result confined to the types2 side table:

1. literals, primitive annotations, variables, assignments, blocks, and control-flow outcomes;
2. functions, complete call shapes, calls, returns, defaults, and local generalization;
3. unions, intersections, nil handling, operators, member access, subscript reads/writes, and all compound/unary surface forms;
4. exact tuples, structural rows, optional presence, row preservation, nominal classes, inheritance, traits, and override validation;
5. type schemes, mutable invariance/declared variance, weak variables, captured state, and value restriction;
6. immutable obligations, bounds, operator/subscript predicates, overload applicability/coverage, and receiver-dependent constraints;
7. heterogeneous/repeated packs, variadic calls, keyword rows, and generic arity;
8. flow refinement with conservative effect/alias invalidation;
9. tags, guarded recursive aliases, match coverage/exhaustiveness, generators, yield/send, and conditional conformance needed by the library;
10. computed types, type values, typeof-compatible display, reflection round trips, and the facts eventually needed by the JIT.

Each milestone adds:

- positive and negative types2 fixtures;
- canonical inferred-type snapshots;
- diagnostic snapshots with source/provenance;
- shadow coverage counters showing which AST/type forms remain unimplemented;
- differential events against legacy, classified as agreement, expected improvement, known incomplete feature, or unexplained divergence.

Do not make an implemented milestone authoritative for its subset. Partial routing would create two interacting type systems and make cutover behavior impossible to predict.

### Phase 4: differential validation and hardening

Run both checkers across:

- the full repository test suite;
- every supported module under lib/;
- real scripts and benchmarks;
- the focused correctness fixtures from this audit;
- generated union, record, overload, constraint, recursion, row, and pack stress cases;
- mutation/alias and flow-refinement scenarios;
- compile-pass programs that legacy wrongly rejects, using a types2-only test driver when legacy aborts before the normal shadow pass can finish.

Use a structured log, preferably JSON lines, with stable fields such as:

~~~text
unit
node/source location
construct
types2 status and canonical type
types2 diagnostics and provenance
legacy status/type, when available
classification
solver counters, time, and peak state
~~~

The comparison layer should live outside inference. It may read both final answers after each checker has finished, but types2 must not consult the legacy answer while solving.

Triage every unexplained divergence. Agreement is not automatically success, because both checkers can share an incorrect library declaration or runtime assumption. Validate disputed cases against the specified semantics and, where useful, actual runtime behavior.

### Phase 5: cutover readiness gate

Do not switch authority until all of the following hold:

- every type-relevant AST form and public type constructor is either implemented or deliberately rejected with a specified diagnostic;
- the full types2 suite and supported-library matrix meet their expected outcomes;
- every Cutover finding in the replacement acceptance table has a types2 regression test with the desired result;
- union/intersection order, independent statement order, and overload-candidate order obey their specified invariants;
- failed speculative work is proven not to leak through targeted transaction tests;
- generic bounds, rows, packs, variance, recursion, reflection, and flow behavior have explicit coverage rather than fallback paths;
- there are no unexplained shadow divergences in the accepted corpus;
- types2 inference is independent of legacy inferred types; disabling or perturbing legacy type answers in a test harness does not change types2 output;
- typeof/type reflection/JIT adapters for the new representation exist and are tested, although still dormant in normal compilation;
- computed types execute exactly once;
- compiler behavior is identical with inert shadowing enabled and disabled, apart from requested logs and measured resource usage;
- release-mode compile time, peak memory, and pathological scaling meet agreed budgets;
- diagnostics are stable enough to replace existing user-facing errors.

The readiness decision should be based on checked-in logs/snapshots and tests, not an aggregate agreement percentage.

### Phase 6: atomic cutover and removal

Perform the semantic switch and legacy deletion as one integration change:

1. make types2 results authoritative for acceptance, Expr/Symbol types, typeof, reflection, JIT guidance, and compiler diagnostics;
2. remove the compiler's legacy lifecycle calls rather than retaining fallback;
3. delete src/types.c and the legacy type state, declarations, build entries, compatibility adapters, diagnostic comparison code, and tests that assert known-bad legacy behavior;
4. rename src/types2.c mechanically if the final source layout should use the original filename;
5. run the entire correctness, library, runtime, JIT, ASan, and performance suite on the post-deletion tree.

There should be no per-feature switch, automatic fallback, or period in which a legacy answer can override a types2 answer. Keep the cutover easy to revert as a whole until it has soaked, but do not keep both implementations in the resulting source tree.

### Phase 7: optional extensions after replacement

Only after the rank-1 replacement is authoritative and stable consider:

- explicit higher-rank schemes for callbacks;
- broader conditional trait implementations;
- associated types or type families;
- finer effect annotations that retain more refinements;
- depth/shape-indexed collection helpers where their value justifies complexity.

## Suggested diagnostic model

The bounded solver can substantially improve errors. A failed call should be able to say:

~~~text
T has lower bounds:
  Int       from argument 1
  String    from argument 2

and upper bound:
  Comparable[T] from max's operator constraint

No solution satisfies all bounds.
~~~

An overload diagnostic should list why each candidate failed without leaking mutations from one candidate into the next. A row error should distinguish missing required field, optional field used without a nil check, and incompatible writable field. A fuel/complexity error should report the construct and relevant counts rather than behaving as a type proof.

## Replacement acceptance table

| Gate | Area | Current failure mode | Required types2 behavior |
|---|---|---|---|
| Cutover | subtype recursion | unequal deep types accepted | visited-pair coinduction; never fail open |
| Cutover | mutable generics | writes invalidate narrower aliases | invariance by default, variance metadata |
| Cutover | writes/operators/defaults | unchecked surface constructs | runtime-equivalent static contracts |
| Cutover | constraints | live bounds erased or fail to wake | immutable obligations and dependency wakeups |
| Cutover | traits/overrides | nominal promise without members | conformance and override validation |
| Cutover | contextual literals | impossible intersections accepted | reject disjoint meets; weak literal metas |
| Cutover | unsolved variables | order dependence; valid bounds rejected | retained LB/UB and subtype edges |
| Cutover | union operations | only some arms supported | universal coverage and joined results |
| Cutover | generalization | mutable captured state polymorphic | FV(type)-FV(env), weak vars/value restriction |
| Cutover | records/tuples | lost fields, presence, and arity | rows/presence; exact fixed tuples |
| Cutover | recursion/occurs | hangs or erased infinite types | guarded alias SCCs; explicit occurs failure |
| Cutover | overload transactions | failed trials mutate later inference | undo log or persistent solver |
| Cutover | exponential calls | product explosion and fuel exhaustion | lazy candidate-first union traversal |
| Cutover | variadic packs | unsupported shapes silently accepted | pack metas and explicit placement/arity rules |
| Cutover | flow | stale heap/getter refinements | conservative invalidation; later effects may refine |
| Optional later | higher-order polymorphism | lost per-call correlations | document rank-1 first; add explicit forall later |
| Cutover | computed types | repeated/effectful type evaluation | single evaluation, memoization, clear limits |
| Cutover | stdlib contracts | partial APIs declared total | optional/throwing contracts and decoders |

## Final assessment

Ty's type system is not lacking ambition or useful surface features. Its central limitation is that the representation does not preserve the information those features need. Single destructive bindings are adequate for equality-oriented Hindley-Milner inference over immutable terms. They are not adequate for a gradual language combining subtyping, unions/intersections, mutable nominal generics, structural rows, overloads, constraints, and variadic sequences.

The strongest path forward is therefore a clean replacement in src/types2.c, not more construct-specific branches or repairs in src/types.c. The new implementation should preserve constraints longer, separate relations, make trials transactional, and represent rows/packs/variance explicitly. Doing so should improve all three stated goals at once:

- fewer correct programs rejected, because compatible lower and upper bounds can meet at a principal solution;
- more provably wrong programs rejected, because contradictions can no longer be hidden in impossible intersections, erased obligations, or existential union success;
- lower compilation overhead on hard cases, because immutable canonical terms allow memoization, indexed lookup, dependency-driven work, and lazy overload traversal.

The existing introspection facilities and library signatures provide a strong corpus for a shadow implementation. Running both checkers lets types2 accumulate independent evidence without risking compilation behavior. Once the cutover gates are met, replacing the authority and deleting the legacy implementation in one change avoids a long-lived hybrid whose semantics would be even harder to explain than either checker alone.
