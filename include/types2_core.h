#ifndef TYPES2_CORE_H_INCLUDED
#define TYPES2_CORE_H_INCLUDED

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

typedef uint32_t T2Type;

enum { T2_TYPE_INVALID = 0 };

typedef enum t2_type_kind {
        T2_TYPE_NEVER,
        T2_TYPE_UNKNOWN,
        T2_TYPE_DYNAMIC,
        T2_TYPE_ANY,
        T2_TYPE_OBJECT,
        T2_TYPE_ERROR,
        T2_TYPE_NIL,
        T2_TYPE_BOOL,
        T2_TYPE_INT,
        T2_TYPE_FLOAT,
        T2_TYPE_STRING,
        T2_TYPE_LITERAL_BOOL,
        T2_TYPE_LITERAL_INT,
        T2_TYPE_LITERAL_STRING,
        T2_TYPE_INT_RANGE,
        T2_TYPE_REFINEMENT,
        T2_TYPE_COMPUTED,
        T2_TYPE_NOMINAL,
        T2_TYPE_TYPE_VALUE,
        T2_TYPE_FUNCTION,
        T2_TYPE_TUPLE,
        T2_TYPE_FIELD,
        T2_TYPE_RECORD,
        T2_TYPE_PARAMETER,
        T2_TYPE_PACK,
        T2_TYPE_ROW,
        T2_TYPE_ROW_EMPTY,
        T2_TYPE_ROW_ANY,
        T2_TYPE_PACK_EMPTY,
        T2_TYPE_PACK_ANY,
        T2_TYPE_PACK_EXPANSION,
        T2_TYPE_PACK_FOLD_UNION,
        T2_TYPE_PACK_FOLD_INTERSECTION,
        T2_TYPE_VARIADIC_TUPLE,
        T2_TYPE_MULTI,
        T2_TYPE_RECURSIVE,
        T2_TYPE_RECURSIVE_VARIABLE,
        T2_TYPE_OVERLOAD,
        T2_TYPE_UNION,
        T2_TYPE_INTERSECTION,
        T2_TYPE_VARIABLE,
        T2_TYPE_META,
        T2_TYPE_KIND_COUNT
} T2TypeKind;

typedef enum t2_variable_kind {
        T2_VARIABLE_FLEXIBLE,
        T2_VARIABLE_RIGID,
        T2_VARIABLE_QUANTIFIED,
        T2_VARIABLE_WEAK,
        T2_VARIABLE_ROW,
        T2_VARIABLE_PACK
} T2VariableKind;

typedef enum t2_variance {
        T2_INVARIANT,
        T2_COVARIANT,
        T2_CONTRAVARIANT
} T2Variance;

typedef enum t2_presence {
        T2_PRESENCE_REQUIRED,
        T2_PRESENCE_OPTIONAL,
        T2_PRESENCE_ABSENT,
        T2_PRESENCE_UNKNOWN
} T2Presence;

typedef enum t2_field_capability {
        T2_FIELD_READONLY,
        T2_FIELD_WRITABLE
} T2FieldCapability;

typedef enum t2_record_exactness {
        T2_RECORD_OPEN,
        T2_RECORD_EXACT
} T2RecordExactness;

typedef enum t2_parameter_kind {
        T2_PARAMETER_POSITIONAL_ONLY,
        T2_PARAMETER_POSITIONAL_OR_KEYWORD,
        T2_PARAMETER_KEYWORD_ONLY,
        T2_PARAMETER_POSITIONAL_REST,
        T2_PARAMETER_KEYWORD_REST,
        T2_PARAMETER_PACK
} T2ParameterKind;

typedef struct t2_field_spec {
        char const *name;
        T2Type type;
        T2Presence presence;
        T2FieldCapability capability;
} T2FieldSpec;

typedef struct t2_parameter_spec {
        char const *name;
        T2Type type;
        T2ParameterKind kind;
        bool required;
} T2ParameterSpec;

typedef struct t2_quantifier {
        uint32_t id;
        T2VariableKind kind;
} T2Quantifier;

typedef enum t2_predicate_kind {
        T2_PREDICATE_SUBTYPE,
        T2_PREDICATE_OPERATOR,
        T2_PREDICATE_SUBSCRIPT_READ,
        T2_PREDICATE_SUBSCRIPT_WRITE,
        T2_PREDICATE_MEMBER_READ,
        T2_PREDICATE_MEMBER_WRITE,
        T2_PREDICATE_KEYWORD_SPREAD
} T2PredicateKind;

typedef struct t2_predicate {
        T2PredicateKind kind;
        T2Type subtype;
        T2Type supertype;
        T2Type operand;
        char const *name;
        char const *provenance;
} T2Predicate;

typedef enum t2_relation {
        T2_RELATION_NO,
        T2_RELATION_YES,
        T2_RELATION_DEFERRED,
        T2_RELATION_COMPLEXITY
} T2Relation;

typedef enum t2_solution_preference {
        T2_PREFER_LOWER_BOUND,
        T2_PREFER_UPPER_BOUND,
        T2_PREFER_KNOWN_VALUE
} T2SolutionPreference;

typedef enum t2_runtime_kind {
        T2_RUNTIME_UNKNOWN,
        T2_RUNTIME_NEVER,
        T2_RUNTIME_NIL,
        T2_RUNTIME_BOOL,
        T2_RUNTIME_INT,
        T2_RUNTIME_FLOAT,
        T2_RUNTIME_STRING,
        T2_RUNTIME_FUNCTION,
        T2_RUNTIME_TUPLE,
        T2_RUNTIME_RECORD,
        T2_RUNTIME_NOMINAL,
        T2_RUNTIME_TYPE_VALUE
} T2RuntimeKind;

typedef struct t2_runtime_facts {
        T2RuntimeKind kind;
        uint64_t nominal_symbol;
        bool exact;
        bool nullable;
} T2RuntimeFacts;

typedef struct t2_universe T2Universe;
typedef struct t2_solver T2Solver;
typedef struct t2_scheme T2Scheme;
typedef struct t2_type_snapshot T2TypeSnapshot;

typedef T2Relation T2PredicateResolver(
        void *context,
        T2Solver *solver,
        T2Predicate const *predicate
);

typedef struct t2_solver_mark {
        size_t undo_count;
        size_t meta_count;
        size_t edge_count;
        size_t obligation_count;
        size_t work_count;
        size_t work_index;
        size_t cause_count;
        unsigned transaction_depth;
        bool failed;
} T2SolverMark;

T2Universe *
t2_universe_new(void);

void
t2_universe_free(T2Universe *universe);

bool
t2_universe_ok(T2Universe const *universe);

size_t
t2_universe_type_count(T2Universe const *universe);

uint32_t
t2_universe_fresh_recursive_binder(T2Universe *universe);

T2Type
t2_primitive(T2Universe *universe, T2TypeKind kind);

T2Type
t2_literal_bool(T2Universe *universe, bool value);

T2Type
t2_literal_int(T2Universe *universe, int64_t value);

T2Type
t2_literal_string(T2Universe *universe, char const *value);

T2Type
t2_integer_range(
        T2Universe *universe,
        T2Type lower,
        T2Type upper,
        bool upper_inclusive
);

T2Type
t2_refinement(T2Universe *universe, T2Type base, T2Type argument);

T2Type
t2_computed_type(
        T2Universe *universe,
        uint64_t identity,
        char const *name,
        T2Type const *arguments,
        size_t argument_count
);

/*
 * Computed terms are canonical promises.  The compile-time broker may attach
 * exactly one immutable result after evaluating the promise once.  Binding a
 * different result, a solver metavariable, or a cyclic result is rejected.
 */
bool
t2_computed_type_set_result(
        T2Universe *universe,
        T2Type computed,
        T2Type result
);

T2Type
t2_computed_type_result(T2Universe const *universe, T2Type computed);

T2Type
t2_type_resolve_computed(T2Universe const *universe, T2Type type);

T2Type
t2_variable(T2Universe *universe, T2VariableKind kind, uint32_t id);

bool
t2_declare_nominal(
        T2Universe *universe,
        uint64_t symbol,
        char const *name,
        size_t arity,
        T2Variance const *variance
);

T2Type
t2_nominal_type_parameter(T2Universe *universe, uint32_t index);

bool
t2_nominal_add_super(
        T2Universe *universe,
        uint64_t symbol,
        T2Type supertype_template
);

bool
t2_primitive_bind_nominal(T2Universe *universe, T2TypeKind kind, T2Type nominal);

bool
t2_nominal_mark_interface(T2Universe *universe, uint64_t symbol);

T2Type
t2_nominal_project(
        T2Universe const *universe,
        T2Type subtype,
        uint64_t target_symbol
);

bool
t2_nominal_validate_variance(
        T2Universe const *universe,
        uint64_t symbol,
        T2Type public_contract
);

T2Type
t2_nominal(
        T2Universe *universe,
        uint64_t symbol,
        T2Type const *arguments,
        size_t arity
);

T2Type
t2_type_value(
        T2Universe *universe,
        T2Type instance,
        T2Type constructor
);

T2Type
t2_type_value_instance(T2Universe const *universe, T2Type value);

T2Type
t2_type_value_constructor(T2Universe const *universe, T2Type value);

T2Type
t2_function(
        T2Universe *universe,
        T2Type const *parameters,
        size_t parameter_count,
        T2Type result
);

size_t
t2_callable_parameter_count(T2Universe const *universe, T2Type callable);

bool
t2_callable_parameter(
        T2Universe const *universe,
        T2Type callable,
        size_t index,
        T2ParameterSpec *parameter
);

T2Type
t2_callable_result(T2Universe const *universe, T2Type callable);

T2Type
t2_callable_yield(T2Universe const *universe, T2Type callable);

T2Type
t2_callable_send(T2Universe const *universe, T2Type callable);

bool
t2_callable_is_effectful(T2Universe const *universe, T2Type callable);

T2Type
t2_callable(
        T2Universe *universe,
        T2ParameterSpec const *parameters,
        size_t parameter_count,
        T2Type result,
        T2Type yield,
        T2Type send
);

T2Type
t2_effectful_callable(
        T2Universe *universe,
        T2ParameterSpec const *parameters,
        size_t parameter_count,
        T2Type result,
        T2Type yield,
        T2Type send
);

T2Type
t2_tuple(T2Universe *universe, T2Type const *items, size_t count);

T2Type
t2_multi(T2Universe *universe, T2Type const *items, size_t count);

T2Type
t2_multi_item(T2Universe const *universe, T2Type type, size_t index);

T2Type
t2_record(
        T2Universe *universe,
        T2FieldSpec const *fields,
        size_t field_count,
        T2Type row_tail,
        T2RecordExactness exactness
);

T2Type
t2_row(
        T2Universe *universe,
        T2FieldSpec const *fields,
        size_t field_count,
        T2Type tail
);

T2Type
t2_record_field_type(
        T2Universe const *universe,
        T2Type record,
        char const *name,
        T2Presence *presence,
        T2FieldCapability *capability
);

size_t
t2_record_field_count(T2Universe const *universe, T2Type record);

bool
t2_record_field(
        T2Universe const *universe,
        T2Type record,
        size_t index,
        T2FieldSpec *field
);

T2Type
t2_record_row_tail(T2Universe const *universe, T2Type record);

bool
t2_record_exactness(
        T2Universe const *universe,
        T2Type record,
        T2RecordExactness *exactness
);

T2Type
t2_pack(
        T2Universe *universe,
        T2Type const *prefix,
        size_t prefix_count,
        T2Type tail
);

T2Type
t2_pack_expansion(T2Universe *universe, T2Type element);

T2Type
t2_pack_fold_union(T2Universe *universe, T2Type pack);

T2Type
t2_pack_fold_intersection(T2Universe *universe, T2Type pack);

T2Type
t2_variadic_tuple(
        T2Universe *universe,
        T2Type const *prefix,
        size_t prefix_count,
        T2Type tail
);

T2Type
t2_recursive_variable(T2Universe *universe, uint32_t binder);

T2Type
t2_recursive(T2Universe *universe, uint32_t binder, T2Type body);

bool
t2_recursive_is_guarded(T2Universe const *universe, T2Type type);

T2Type
t2_recursive_unfold(T2Universe const *universe, T2Type type);

T2Type
t2_union(T2Universe *universe, T2Type const *arms, size_t count);

T2Type
t2_intersection(T2Universe *universe, T2Type const *arms, size_t count);

T2Type
t2_overload(T2Universe *universe, T2Type const *candidates, size_t count);

T2Type
t2_join(T2Universe *universe, T2Type left, T2Type right);

T2Type
t2_meet(T2Universe *universe, T2Type left, T2Type right);

T2Relation
t2_subtype(T2Universe const *universe, T2Type subtype, T2Type supertype);

T2Relation
t2_consistent(T2Universe const *universe, T2Type left, T2Type right);

T2Scheme *
t2_scheme_new(
        T2Universe *universe,
        T2Quantifier const *quantifiers,
        size_t quantifier_count,
        T2Type body,
        T2Predicate const *predicates,
        size_t predicate_count
);

void
t2_scheme_free(T2Scheme *scheme);

size_t
t2_scheme_quantifier_count(T2Scheme const *scheme);

bool
t2_scheme_quantifier(
        T2Scheme const *scheme,
        size_t index,
        T2Quantifier *quantifier
);

T2Type
t2_scheme_body(T2Scheme const *scheme);

size_t
t2_scheme_predicate_count(T2Scheme const *scheme);

bool
t2_scheme_predicate(
        T2Scheme const *scheme,
        size_t index,
        T2Predicate *predicate
);

T2Type
t2_scheme_instantiate(
        T2Scheme const *scheme,
        T2Solver *solver,
        uint32_t level,
        char const *provenance
);

T2Type
t2_scheme_apply(
        T2Scheme const *scheme,
        T2Solver *solver,
        T2Type const *arguments,
        size_t argument_count,
        char const *provenance
);

T2Scheme *
t2_solver_generalize(
        T2Solver *solver,
        T2Type type,
        T2Type const *environment,
        size_t environment_count,
        uint32_t binding_level,
        bool expansive
);

T2Scheme *
t2_solver_generalize_scoped(
        T2Solver *solver,
        T2Type type,
        T2Type const *environment,
        size_t environment_count,
        uint32_t binding_level,
        bool expansive,
        T2SolverMark scope
);

T2TypeKind
t2_type_kind(T2Universe const *universe, T2Type type);

T2VariableKind
t2_type_variable_kind(T2Universe const *universe, T2Type type);

size_t
t2_type_arity(T2Universe const *universe, T2Type type);

T2Type
t2_type_child(T2Universe const *universe, T2Type type, size_t index);

uint64_t
t2_type_payload(T2Universe const *universe, T2Type type);

char const *
t2_type_name(T2Universe const *universe, T2Type type);

uint64_t
t2_type_hash(T2Universe const *universe, T2Type type);

bool
t2_type_same(T2Universe const *universe, T2Type left, T2Type right);

char *
t2_type_string(T2Universe const *universe, T2Type type);

/*
 * A snapshot is an owned, solver-free representation of one immutable term
 * graph.  It is suitable for dormant reflection/JIT adapters and for passing
 * an already materialized computed-type result through a neutral boundary.
 * Nominal symbols must already be declared in the importing universe.
 */
T2TypeSnapshot *
t2_type_snapshot_new(T2Universe const *universe, T2Type type);

void
t2_type_snapshot_free(T2TypeSnapshot *snapshot);

size_t
t2_type_snapshot_node_count(T2TypeSnapshot const *snapshot);

T2Type
t2_type_snapshot_import(
        T2Universe *universe,
        T2TypeSnapshot const *snapshot
);

/* Conservative runtime-shape facts for a future JIT adapter. */
bool
t2_type_runtime_facts(
        T2Universe const *universe,
        T2Type type,
        T2RuntimeFacts *facts
);

T2Solver *
t2_solver_new(T2Universe *universe);

void
t2_solver_set_predicate_resolver(
        T2Solver *solver,
        T2PredicateResolver *resolver,
        void *context
);

void
t2_solver_free(T2Solver *solver);

T2Type
t2_solver_new_meta(
        T2Solver *solver,
        T2VariableKind kind,
        uint32_t level,
        char const *provenance
);

T2Relation
t2_solver_constrain_subtype(
        T2Solver *solver,
        T2Type subtype,
        T2Type supertype,
        char const *provenance
);

T2Relation
t2_solver_constrain_predicate(
        T2Solver *solver,
        T2Predicate const *predicate
);

T2Relation
t2_solver_unify(
        T2Solver *solver,
        T2Type left,
        T2Type right,
        char const *provenance
);

T2Type
t2_solver_lower_bound(T2Solver *solver, T2Type meta);

T2Type
t2_solver_upper_bound(T2Solver *solver, T2Type meta);

T2Type
t2_solver_solution(
        T2Solver *solver,
        T2Type meta,
        T2SolutionPreference preference
);

T2Type
t2_solver_zonk(
        T2Solver *solver,
        T2Type type,
        T2SolutionPreference preference
);

bool
t2_solver_failed(T2Solver const *solver);

char const *
t2_solver_error(T2Solver const *solver);

char *
t2_solver_explain(T2Solver const *solver);

char *
t2_solver_explain_since(T2Solver const *solver, T2SolverMark mark);

size_t
t2_solver_pending_obligations(T2Solver const *solver);

bool
t2_solver_pending_obligation(
        T2Solver const *solver,
        size_t index,
        T2Predicate *predicate
);

size_t
t2_solver_meta_count(T2Solver const *solver);

size_t
t2_solver_edge_count(T2Solver const *solver);

uint64_t
t2_solver_work_steps(T2Solver const *solver);

T2SolverMark
t2_solver_mark(T2Solver *solver);

void
t2_solver_commit(T2Solver *solver, T2SolverMark mark);

bool
t2_solver_cancel_obligations_since(T2Solver *solver, T2SolverMark mark);

void
t2_solver_rollback(T2Solver *solver, T2SolverMark mark);

#endif

/* vim: set sts=8 sw=8 expandtab: */
