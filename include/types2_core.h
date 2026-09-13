#ifndef T2_CORE_H_INCLUDED
#define T2_CORE_H_INCLUDED

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#include "defs.h"

typedef uint32_t T2Type;

enum { T2_TYPE_INVALID = 0 };

typedef struct t2_index_entry {
        uint64_t key;
        uint32_t value;
        bool used;
} T2IndexEntry;

typedef struct t2_index {
        T2IndexEntry *entries;
        size_t count;
        size_t capacity;
} T2Index;

bool
t2_index_find(T2Index const *index, uint64_t key, uint32_t *value);

bool
t2_index_put(T2Index *index, uint64_t key, uint32_t value);

void
t2_index_clear(T2Index *index);

void
t2_index_free(T2Index *index);

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
        T2_TYPE_SCHEME,
        T2_TYPE_PREDICATE,
        T2_TYPE_BINDER,
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
        T2_CONTRAVARIANT,
        T2_BIVARIANT
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

typedef enum t2_cause_kind {
        T2_CAUSE_LOWER,
        T2_CAUSE_UPPER,
        T2_CAUSE_EDGE,
        T2_CAUSE_EQUALITY,
        T2_CAUSE_PREDICATE,
        T2_CAUSE_FAILURE
} T2CauseKind;

typedef struct t2_cause_info {
        T2CauseKind kind;
        T2Type left;
        T2Type right;
        char const *message;
        char const *provenance;
} T2CauseInfo;

typedef enum t2_relation {
        T2_RELATION_NO,
        T2_RELATION_YES,
        T2_RELATION_DEFERRED,
        T2_RELATION_COMPLEXITY
} T2Relation;

typedef enum t2_solution_preference {
        T2_PREFER_LOWER_BOUND,
        T2_PREFER_UPPER_BOUND,
        T2_PREFER_KNOWN_VALUE,
        T2_PREFER_SOLUTION_ONLY
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
t2_universe_report(T2Universe const *universe, FILE *out);

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
t2_literal_string_n(T2Universe *universe, char const *value, usize length);

T2Type
t2_integer_range(
        T2Universe *universe,
        T2Type lower,
        T2Type upper,
        bool upper_inclusive
);

bool
t2_integer_range_bounds(
        T2Universe const *universe,
        T2Type range,
        T2Type *lower,
        T2Type *upper,
        bool *upper_inclusive
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
t2_nominal_declared(T2Universe const *universe, uint64_t symbol, size_t *arity);

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

bool
t2_definitely_disjoint(T2Universe const *universe, T2Type left, T2Type right);

bool
t2_solver_meta_solved(T2Solver *solver, T2Type meta);

void
t2_solver_retire_metas_since(T2Solver *solver, T2SolverMark mark);

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

bool
t2_scheme_has_metas(T2Scheme const *scheme);

bool
t2_solver_zonk_scheme(T2Solver *solver, T2Scheme *scheme);

size_t
t2_scheme_predicate_count(T2Scheme const *scheme);

bool
t2_scheme_predicate(
        T2Scheme const *scheme,
        size_t index,
        T2Predicate *predicate
);

bool
t2_scheme_name_quantifier(T2Scheme *scheme, size_t index, char const *name);

char const *
t2_scheme_quantifier_name(T2Scheme const *scheme, size_t index);

T2Type
t2_scheme_type(T2Universe *universe, T2Scheme const *scheme);

T2Scheme *
t2_type_scheme(T2Universe *universe, T2Type type);

T2Scheme *
t2_scheme_simplify(T2Scheme *scheme);

T2Type
t2_type_scheme_body(T2Universe const *universe, T2Type type);

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

T2Type
t2_scheme_apply_relaxed(
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

bool
t2_type_has_metas(T2Universe const *universe, T2Type type);

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

void
t2_string_free(char *text);

typedef enum t2_token_kind {
        T2_TOKEN_PUNCTUATION,
        T2_TOKEN_STRUCTURE,
        T2_TOKEN_FUNCTION,
        T2_TOKEN_BRACKET,
        T2_TOKEN_OPERATOR,
        T2_TOKEN_KEYWORD,
        T2_TOKEN_PRIMITIVE,
        T2_TOKEN_NOMINAL,
        T2_TOKEN_VARIABLE,
        T2_TOKEN_META,
        T2_TOKEN_LITERAL,
        T2_TOKEN_FIELD,
        T2_TOKEN_PARAMETER,
        T2_TOKEN_KIND_COUNT
} T2TokenKind;

typedef struct t2_names T2Names;

typedef struct t2_print_options {
        unsigned width;
        unsigned indent;
        unsigned column;
        unsigned hang;
        bool raw;
        char const *const *styles;
        T2Names *names;
} T2PrintOptions;

T2Names *
t2_names_new(void);

void
t2_names_free(T2Names *names);

bool
t2_names_assign(
        T2Universe const *universe,
        T2Names *names,
        T2Type variable,
        char const *name
);

char *
t2_type_render(
        T2Universe const *universe,
        T2Type type,
        T2PrintOptions const *options
);

char *
t2_scheme_render(
        T2Universe const *universe,
        T2Scheme const *scheme,
        T2PrintOptions const *options
);

char *
t2_predicate_render(
        T2Universe const *universe,
        T2Predicate const *predicate,
        T2PrintOptions const *options
);

T2Type
t2_type_substitute(
        T2Universe *universe,
        T2Type type,
        uint32_t const *ids,
        T2Type const *replacements,
        size_t count
);

/*
 * Wire format for persisting types across runs.  A writer accumulates a
 * table of type nodes in dependency order and hands out indices; a reader
 * rebuilds the table in a universe, remapping nominal symbols and recursive
 * binders through the caller.  Metas are recreated through the reader's
 * meta hook; unresolved computed terms keep their identity.
 */
bool
t2_bytes_u8(byte_vector *bytes, uint8_t value);

bool
t2_bytes_u32(byte_vector *bytes, uint32_t value);

bool
t2_bytes_u64(byte_vector *bytes, uint64_t value);

bool
t2_bytes_string(byte_vector *bytes, char const *text);

bool
t2_bytes_append(byte_vector *bytes, void const *data, size_t size);


bool
t2_read_u8(unsigned char const *data, size_t size, size_t *position, uint8_t *value);

bool
t2_read_u32(unsigned char const *data, size_t size, size_t *position, uint32_t *value);

bool
t2_read_u64(unsigned char const *data, size_t size, size_t *position, uint64_t *value);

bool
t2_read_string(
        unsigned char const *data,
        size_t size,
        size_t *position,
        char **text
);

typedef struct t2_symbol_remap {
        uint64_t (*out)(void *context, uint64_t symbol);
        uint64_t (*in)(void *context, uint64_t token);
        void *context;
} T2SymbolRemap;

typedef struct t2_type_writer T2TypeWriter;

T2TypeWriter *
t2_type_writer_new(T2Universe *universe, T2SymbolRemap remap);

bool
t2_type_writer_add(T2TypeWriter *writer, T2Type type, uint32_t *index);

size_t
t2_type_writer_count(T2TypeWriter const *writer);

bool
t2_type_writer_encode(T2TypeWriter const *writer, byte_vector *out);

void
t2_type_writer_free(T2TypeWriter *writer);

typedef struct t2_type_reader T2TypeReader;

typedef struct t2_read_hooks {
        uint32_t floor;
        uint32_t (*reserve)(void *context, uint32_t count);
        T2Type (*meta)(void *context, T2VariableKind kind);
        void *context;
} T2ReadHooks;

T2TypeReader *
t2_type_reader_new(
        T2Universe *universe,
        T2SymbolRemap remap,
        T2ReadHooks hooks,
        unsigned char const *data,
        size_t size,
        size_t *position
);

T2Type
t2_type_reader_type(T2TypeReader const *reader, uint32_t index);

uint32_t
t2_type_reader_variable_limit(T2TypeReader const *reader);

void
t2_type_reader_free(T2TypeReader *reader);

bool
t2_scheme_encode(T2Scheme const *scheme, T2TypeWriter *writer, byte_vector *out);

T2Scheme *
t2_scheme_decode(
        T2TypeReader *reader,
        unsigned char const *data,
        size_t size,
        size_t *position
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

char const *
t2_solver_meta_provenance(T2Solver const *solver, T2Type type);

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
t2_solver_resolve_packs(T2Solver *solver, T2Type type);

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
t2_solver_cause_count(T2Solver const *solver);

bool
t2_solver_cause(T2Solver *solver, size_t index, T2CauseInfo *info);

bool
t2_solver_failure(T2Solver *solver, T2CauseInfo *info);

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
