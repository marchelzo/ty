#include <inttypes.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "types2_core.h"

typedef struct t2_node {
        uint64_t hash;
        uint64_t payload;
        char *text;
        uint32_t arity;
        T2TypeKind kind;
        T2VariableKind variable_kind;
        T2Type children[];
} T2Node;

typedef struct t2_nominal_info {
        uint64_t symbol;
        char *name;
        size_t arity;
        T2Variance *variance;
        T2Type *supertypes;
        size_t supertype_count;
        size_t supertype_capacity;
        bool instantiated;
} T2NominalInfo;

typedef struct t2_applied_nominal {
        T2Type instance;
        T2Type *supertypes;
        size_t supertype_count;
} T2AppliedNominal;

typedef struct t2_recursive_info {
        uint32_t binder;
        T2Type type;
} T2RecursiveInfo;

typedef struct t2_computed_result {
        T2Type computed;
        T2Type result;
} T2ComputedResult;

typedef struct t2_type_snapshot_node {
        uint64_t payload;
        char *text;
        uint32_t *children;
        uint32_t arity;
        T2TypeKind kind;
        T2VariableKind variable_kind;
} T2TypeSnapshotNode;

struct t2_type_snapshot {
        T2TypeSnapshotNode *nodes;
        size_t node_count;
        size_t node_capacity;
        uint32_t root;
};

struct t2_universe {
        T2Node **nodes;
        size_t node_count;
        size_t node_capacity;

        T2Type *table;
        size_t table_count;
        size_t table_capacity;

        T2Type primitives[T2_TYPE_KIND_COUNT];

        T2NominalInfo *nominals;
        size_t nominal_count;
        size_t nominal_capacity;

        T2AppliedNominal *applied_nominals;
        size_t applied_nominal_count;
        size_t applied_nominal_capacity;

        T2RecursiveInfo *recursive;
        size_t recursive_count;
        size_t recursive_capacity;

        T2ComputedResult *computed_results;
        size_t computed_result_count;
        size_t computed_result_capacity;

        uint32_t next_solver_id;
        uint32_t next_recursive_id;
        bool failed;
};

typedef struct t2_watch_vector {
        uint64_t *items;
        size_t count;
        size_t capacity;
} T2WatchVector;

typedef struct t2_meta {
        uint32_t parent;
        uint32_t level;
        uint8_t rank;
        T2VariableKind variable_kind;
        T2Type lower;
        T2Type upper;
        T2Type solution;
        char *provenance;
        T2WatchVector watchers;
        bool checking_bounds;
} T2Meta;

typedef struct t2_edge {
        uint32_t subtype;
        uint32_t supertype;
        char const *provenance;
        uint64_t self_retry_epoch;
} T2Edge;

typedef struct t2_obligation {
        T2Predicate predicate;
        char *name;
        char *provenance;
        uint64_t self_retry_epoch;
        bool active;
} T2Obligation;

typedef enum t2_cause_kind {
        T2_CAUSE_LOWER,
        T2_CAUSE_UPPER,
        T2_CAUSE_EDGE,
        T2_CAUSE_EQUALITY,
        T2_CAUSE_PREDICATE
} T2CauseKind;

typedef struct t2_cause {
        T2CauseKind kind;
        T2Type left;
        T2Type right;
        char *provenance;
} T2Cause;

typedef enum t2_undo_kind {
        T2_UNDO_PARENT,
        T2_UNDO_RANK,
        T2_UNDO_VARIABLE_KIND,
        T2_UNDO_LOWER,
        T2_UNDO_UPPER,
        T2_UNDO_SOLUTION,
        T2_UNDO_WATCH_COUNT,
        T2_UNDO_OBLIGATION_ACTIVE
} T2UndoKind;

typedef struct t2_undo {
        T2UndoKind kind;
        uint32_t index;
        uint64_t old;
} T2Undo;

struct t2_solver {
        T2Universe *universe;
        uint32_t id;

        T2Meta *metas;
        size_t meta_count;
        size_t meta_capacity;

        T2Edge *edges;
        size_t edge_count;
        size_t edge_capacity;

        T2Obligation *obligations;
        size_t obligation_count;
        size_t obligation_capacity;

        T2PredicateResolver *predicate_resolver;
        void *predicate_context;

        uint64_t *work;
        size_t work_count;
        size_t work_capacity;
        size_t work_index;
        uint64_t work_steps;
        uint64_t active_work;
        uint64_t drain_epoch;
        bool draining_work;
        bool processing_work;
        bool rerun_active_work;

        T2Undo *undo;
        size_t undo_count;
        size_t undo_capacity;
        unsigned transaction_depth;

        T2Cause *causes;
        size_t cause_count;
        size_t cause_capacity;

        bool failed;
        char error[512];
};

struct t2_scheme {
        T2Universe *universe;
        T2Quantifier *quantifiers;
        size_t quantifier_count;
        T2Type body;
        T2Predicate *predicates;
        size_t predicate_count;
};

typedef struct t2_type_vector {
        T2Type *items;
        size_t count;
        size_t capacity;
} T2TypeVector;

typedef struct t2_string_buffer {
        char *items;
        size_t count;
        size_t capacity;
        bool failed;
} T2StringBuffer;

static T2Type rebuild_type(
        T2Universe *universe,
        T2Node const *node,
        T2Type const *children
);

enum { T2_RELATION_DEPTH_LIMIT = 256 };

static uint64_t const T2_WATCH_OBLIGATION = UINT64_C(1) << 63;

enum {
        T2_FIELD_PRESENCE_MASK = 0x3,
        T2_FIELD_WRITABLE_BIT = 0x4,
        T2_PARAMETER_KIND_MASK = 0x7,
        T2_PARAMETER_REQUIRED = 0x8,
        T2_RANGE_HAS_LOWER = 0x1,
        T2_RANGE_HAS_UPPER = 0x2,
        T2_RANGE_UPPER_INCLUSIVE = 0x4
};

static uint64_t
mix64(uint64_t value)
{
        value ^= value >> 30;
        value *= UINT64_C(0xbf58476d1ce4e5b9);
        value ^= value >> 27;
        value *= UINT64_C(0x94d049bb133111eb);
        value ^= value >> 31;
        return value;
}

static uint64_t
hash_combine(uint64_t seed, uint64_t value)
{
        return seed ^ (value + UINT64_C(0x9e3779b97f4a7c15) + (seed << 6) + (seed >> 2));
}

static uint64_t
hash_string(char const *text)
{
        uint64_t hash = UINT64_C(1469598103934665603);

        if (text == NULL) {
                return hash;
        }

        for (unsigned char const *p = (unsigned char const *)text; *p != '\0'; ++p) {
                hash ^= *p;
                hash *= UINT64_C(1099511628211);
        }

        return hash;
}

static char *
copy_string(char const *text)
{
        if (text == NULL) {
                return NULL;
        }

        size_t length = strlen(text) + 1;
        char *copy = malloc(length);
        if (copy != NULL) {
                memcpy(copy, text, length);
        }
        return copy;
}

static bool
reserve_array(void **items, size_t *capacity, size_t needed, size_t item_size)
{
        if (*capacity >= needed) {
                return true;
        }

        size_t next = *capacity == 0 ? 8 : *capacity;
        while (next < needed) {
                if (next > SIZE_MAX / 2) {
                        return false;
                }
                next *= 2;
        }

        if (next > SIZE_MAX / item_size) {
                return false;
        }

        void *resized = realloc(*items, next * item_size);
        if (resized == NULL) {
                return false;
        }

        *items = resized;
        *capacity = next;
        return true;
}

static T2Node const *
get_node(T2Universe const *universe, T2Type type)
{
        if (universe == NULL || type == T2_TYPE_INVALID || type > universe->node_count) {
                return NULL;
        }
        return universe->nodes[type - 1];
}

static bool
same_candidate(
        T2Node const *node,
        T2TypeKind kind,
        T2VariableKind variable_kind,
        uint64_t payload,
        char const *text,
        T2Type const *children,
        size_t arity
)
{
        if (
                node->kind != kind
             || node->variable_kind != variable_kind
             || node->payload != payload
             || node->arity != arity
        ) {
                return false;
        }

        if ((node->text == NULL) != (text == NULL)) {
                return false;
        }
        if (node->text != NULL && strcmp(node->text, text) != 0) {
                return false;
        }

        return arity == 0
            || memcmp(node->children, children, arity * sizeof *children) == 0;
}

static bool
resize_intern_table(T2Universe *universe, size_t capacity)
{
        T2Type *table = calloc(capacity, sizeof *table);
        if (table == NULL) {
                universe->failed = true;
                return false;
        }

        for (size_t i = 0; i < universe->node_count; ++i) {
                T2Type type = (T2Type)(i + 1);
                T2Node const *node = universe->nodes[i];
                size_t slot = (size_t)node->hash & (capacity - 1);
                while (table[slot] != T2_TYPE_INVALID) {
                        slot = (slot + 1) & (capacity - 1);
                }
                table[slot] = type;
        }

        free(universe->table);
        universe->table = table;
        universe->table_capacity = capacity;
        universe->table_count = universe->node_count;
        return true;
}

static T2Type
intern_type(
        T2Universe *universe,
        T2TypeKind kind,
        T2VariableKind variable_kind,
        uint64_t payload,
        char const *text,
        T2Type const *children,
        size_t arity
)
{
        if (
                universe == NULL
             || universe->failed
             || kind >= T2_TYPE_KIND_COUNT
             || arity > UINT32_MAX
             || (arity != 0 && children == NULL)
             || universe->node_count >= UINT32_MAX
        ) {
                return T2_TYPE_INVALID;
        }

        uint64_t hash = mix64((uint64_t)kind + 1);
        hash = hash_combine(hash, variable_kind);
        hash = hash_combine(hash, payload);
        hash = hash_combine(hash, hash_string(text));
        hash = hash_combine(hash, arity);
        for (size_t i = 0; i < arity; ++i) {
                T2Node const *child = get_node(universe, children[i]);
                if (child == NULL) {
                        return T2_TYPE_INVALID;
                }
                hash = hash_combine(hash, child->hash);
        }
        hash = mix64(hash);

        if (
                universe->table_capacity == 0
             || (universe->table_count + 1) * 4 >= universe->table_capacity * 3
        ) {
                size_t capacity = universe->table_capacity == 0
                                ? 64
                                : universe->table_capacity * 2;
                if (!resize_intern_table(universe, capacity)) {
                        return T2_TYPE_INVALID;
                }
        }

        size_t slot = (size_t)hash & (universe->table_capacity - 1);
        while (universe->table[slot] != T2_TYPE_INVALID) {
                T2Type type = universe->table[slot];
                T2Node const *node = get_node(universe, type);
                if (
                        node->hash == hash
                     && same_candidate(
                             node,
                             kind,
                             variable_kind,
                             payload,
                             text,
                             children,
                             arity
                     )
                ) {
                        return type;
                }
                slot = (slot + 1) & (universe->table_capacity - 1);
        }

        if (
                !reserve_array(
                        (void **)&universe->nodes,
                        &universe->node_capacity,
                        universe->node_count + 1,
                        sizeof *universe->nodes
                )
        ) {
                universe->failed = true;
                return T2_TYPE_INVALID;
        }

        if (arity > (SIZE_MAX - sizeof (T2Node)) / sizeof (T2Type)) {
                universe->failed = true;
                return T2_TYPE_INVALID;
        }

        T2Node *node = malloc(sizeof *node + arity * sizeof *children);
        if (node == NULL) {
                universe->failed = true;
                return T2_TYPE_INVALID;
        }

        char *owned_text = copy_string(text);
        if (text != NULL && owned_text == NULL) {
                free(node);
                universe->failed = true;
                return T2_TYPE_INVALID;
        }

        *node = (T2Node) {
                .hash = hash,
                .payload = payload,
                .text = owned_text,
                .arity = (uint32_t)arity,
                .kind = kind,
                .variable_kind = variable_kind
        };
        if (arity != 0) {
                memcpy(node->children, children, arity * sizeof *children);
        }

        T2Type type = (T2Type)(universe->node_count + 1);
        universe->nodes[universe->node_count++] = node;
        universe->table[slot] = type;
        universe->table_count += 1;
        return type;
}

T2Universe *
t2_universe_new(void)
{
        T2Universe *universe = calloc(1, sizeof *universe);
        if (universe != NULL) {
                universe->next_solver_id = 1;
                universe->next_recursive_id = 1;
        }
        return universe;
}

void
t2_universe_free(T2Universe *universe)
{
        if (universe == NULL) {
                return;
        }

        for (size_t i = 0; i < universe->node_count; ++i) {
                free(universe->nodes[i]->text);
                free(universe->nodes[i]);
        }
        for (size_t i = 0; i < universe->nominal_count; ++i) {
                free(universe->nominals[i].name);
                free(universe->nominals[i].variance);
                free(universe->nominals[i].supertypes);
        }
        for (size_t i = 0; i < universe->applied_nominal_count; ++i) {
                free(universe->applied_nominals[i].supertypes);
        }

        free(universe->nodes);
        free(universe->table);
        free(universe->nominals);
        free(universe->applied_nominals);
        free(universe->recursive);
        free(universe->computed_results);
        free(universe);
}

bool
t2_universe_ok(T2Universe const *universe)
{
        return universe != NULL && !universe->failed;
}

size_t
t2_universe_type_count(T2Universe const *universe)
{
        return universe == NULL ? 0 : universe->node_count;
}

uint32_t
t2_universe_fresh_recursive_binder(T2Universe *universe)
{
        if (universe == NULL || universe->next_recursive_id == 0) return 0;
        return universe->next_recursive_id++;
}

T2Type
t2_primitive(T2Universe *universe, T2TypeKind kind)
{
        bool primitive = kind >= T2_TYPE_NEVER && kind <= T2_TYPE_STRING;
        primitive = primitive
                 || kind == T2_TYPE_ROW_EMPTY
                 || kind == T2_TYPE_ROW_ANY
                 || kind == T2_TYPE_PACK_EMPTY
                 || kind == T2_TYPE_PACK_ANY;
        if (universe == NULL || !primitive) {
                return T2_TYPE_INVALID;
        }

        if (universe->primitives[kind] == T2_TYPE_INVALID) {
                universe->primitives[kind] = intern_type(
                        universe,
                        kind,
                        T2_VARIABLE_FLEXIBLE,
                        0,
                        NULL,
                        NULL,
                        0
                );
        }

        return universe->primitives[kind];
}

T2Type
t2_literal_bool(T2Universe *universe, bool value)
{
        return intern_type(
                universe,
                T2_TYPE_LITERAL_BOOL,
                T2_VARIABLE_FLEXIBLE,
                value,
                NULL,
                NULL,
                0
        );
}

T2Type
t2_literal_int(T2Universe *universe, int64_t value)
{
        return intern_type(
                universe,
                T2_TYPE_LITERAL_INT,
                T2_VARIABLE_FLEXIBLE,
                (uint64_t)value,
                NULL,
                NULL,
                0
        );
}

T2Type
t2_literal_string(T2Universe *universe, char const *value)
{
        if (value == NULL) {
                return T2_TYPE_INVALID;
        }
        return intern_type(
                universe,
                T2_TYPE_LITERAL_STRING,
                T2_VARIABLE_FLEXIBLE,
                0,
                value,
                NULL,
                0
        );
}

T2Type
t2_integer_range(
        T2Universe *universe,
        T2Type lower,
        T2Type upper,
        bool upper_inclusive
)
{
        if (universe == NULL || (lower == T2_TYPE_INVALID && upper == T2_TYPE_INVALID)) {
                return T2_TYPE_INVALID;
        }

        T2Type bounds[2];
        size_t count = 0;
        uint64_t payload = 0;
        if (lower != T2_TYPE_INVALID) {
                if (get_node(universe, lower) == NULL) return T2_TYPE_INVALID;
                payload |= T2_RANGE_HAS_LOWER;
                bounds[count++] = lower;
        }
        if (upper != T2_TYPE_INVALID) {
                if (get_node(universe, upper) == NULL) return T2_TYPE_INVALID;
                payload |= T2_RANGE_HAS_UPPER;
                bounds[count++] = upper;
        }
        if (upper_inclusive) payload |= T2_RANGE_UPPER_INCLUSIVE;
        if (lower != T2_TYPE_INVALID && upper != T2_TYPE_INVALID) {
                T2Node const *low = get_node(universe, lower);
                T2Node const *high = get_node(universe, upper);
                if (
                        low->kind == T2_TYPE_LITERAL_INT
                     && high->kind == T2_TYPE_LITERAL_INT
                ) {
                        int64_t lo = (int64_t)low->payload;
                        int64_t hi = (int64_t)high->payload;
                        if (upper_inclusive ? lo > hi : lo >= hi) {
                                return t2_primitive(universe, T2_TYPE_NEVER);
                        }
                }
        }
        return intern_type(
                universe,
                T2_TYPE_INT_RANGE,
                T2_VARIABLE_FLEXIBLE,
                payload,
                NULL,
                bounds,
                count
        );
}

T2Type
t2_refinement(T2Universe *universe, T2Type base, T2Type argument)
{
        if (
                universe == NULL
             || get_node(universe, base) == NULL
             || get_node(universe, argument) == NULL
        ) return T2_TYPE_INVALID;
        return intern_type(
                universe,
                T2_TYPE_REFINEMENT,
                T2_VARIABLE_FLEXIBLE,
                0,
                NULL,
                (T2Type[]) { base, argument },
                2
        );
}

T2Type
t2_computed_type(
        T2Universe *universe,
        uint64_t identity,
        char const *name,
        T2Type const *arguments,
        size_t argument_count
)
{
        if (
                universe == NULL
             || identity == 0
             || name == NULL
             || (argument_count != 0 && arguments == NULL)
        ) return T2_TYPE_INVALID;
        return intern_type(
                universe,
                T2_TYPE_COMPUTED,
                T2_VARIABLE_FLEXIBLE,
                identity,
                name,
                arguments,
                argument_count
        );
}

static T2ComputedResult const *
find_computed_result(T2Universe const *universe, T2Type computed)
{
        if (universe == NULL) return NULL;
        for (size_t i = 0; i < universe->computed_result_count; ++i) {
                if (universe->computed_results[i].computed == computed) {
                        return &universe->computed_results[i];
                }
        }
        return NULL;
}

T2Type
t2_computed_type_result(T2Universe const *universe, T2Type computed)
{
        T2Node const *node = get_node(universe, computed);
        if (node == NULL || node->kind != T2_TYPE_COMPUTED) {
                return T2_TYPE_INVALID;
        }
        T2ComputedResult const *entry = find_computed_result(universe, computed);
        return entry == NULL ? T2_TYPE_INVALID : entry->result;
}

T2Type
t2_type_resolve_computed(T2Universe const *universe, T2Type type)
{
        if (get_node(universe, type) == NULL) return T2_TYPE_INVALID;
        size_t remaining = universe->computed_result_count + 1;
        while (remaining-- != 0) {
                T2Node const *node = get_node(universe, type);
                if (node == NULL || node->kind != T2_TYPE_COMPUTED) return type;
                T2ComputedResult const *entry = find_computed_result(universe, type);
                if (entry == NULL) return type;
                type = entry->result;
        }
        return T2_TYPE_INVALID;
}

static bool
computed_result_reaches(
        T2Universe const *universe,
        T2Type source,
        T2Type target,
        bool *visiting
)
{
        if (source == target) return true;
        if (source == T2_TYPE_INVALID || source > universe->node_count) return true;
        size_t index = (size_t)source - 1;
        if (visiting[index]) return false;
        visiting[index] = true;

        T2Node const *node = get_node(universe, source);
        bool reaches = node == NULL || node->kind == T2_TYPE_META;
        if (!reaches && node->kind == T2_TYPE_COMPUTED) {
                T2ComputedResult const *entry = find_computed_result(universe, source);
                reaches = entry != NULL && computed_result_reaches(
                        universe,
                        entry->result,
                        target,
                        visiting
                );
        }
        for (size_t i = 0; !reaches && i < node->arity; ++i) {
                reaches = computed_result_reaches(
                        universe,
                        node->children[i],
                        target,
                        visiting
                );
        }
        visiting[index] = false;
        return reaches;
}

bool
t2_computed_type_set_result(
        T2Universe *universe,
        T2Type computed,
        T2Type result
)
{
        T2Node const *promise = get_node(universe, computed);
        T2Node const *value = get_node(universe, result);
        if (
                universe == NULL
             || promise == NULL
             || promise->kind != T2_TYPE_COMPUTED
             || value == NULL
        ) return false;

        T2ComputedResult const *existing = find_computed_result(universe, computed);
        if (existing != NULL) return existing->result == result;

        bool *visiting = calloc(universe->node_count, sizeof *visiting);
        if (visiting == NULL) {
                universe->failed = true;
                return false;
        }
        bool cyclic_or_solver_local = computed_result_reaches(
                universe,
                result,
                computed,
                visiting
        );
        free(visiting);
        if (cyclic_or_solver_local) return false;

        if (!reserve_array(
                (void **)&universe->computed_results,
                &universe->computed_result_capacity,
                universe->computed_result_count + 1,
                sizeof *universe->computed_results
        )) {
                universe->failed = true;
                return false;
        }
        universe->computed_results[universe->computed_result_count++] =
                (T2ComputedResult) { .computed = computed, .result = result };
        return true;
}

T2Type
t2_variable(T2Universe *universe, T2VariableKind kind, uint32_t id)
{
        return intern_type(
                universe,
                T2_TYPE_VARIABLE,
                kind,
                id,
                NULL,
                NULL,
                0
        );
}

static T2NominalInfo const *
find_nominal(T2Universe const *universe, uint64_t symbol)
{
        if (universe == NULL) {
                return NULL;
        }
        for (size_t i = 0; i < universe->nominal_count; ++i) {
                if (universe->nominals[i].symbol == symbol) {
                        return &universe->nominals[i];
                }
        }
        return NULL;
}

static T2NominalInfo *
find_nominal_mutable(T2Universe *universe, uint64_t symbol)
{
        return (T2NominalInfo *)find_nominal(universe, symbol);
}

bool
t2_declare_nominal(
        T2Universe *universe,
        uint64_t symbol,
        char const *name,
        size_t arity,
        T2Variance const *variance
)
{
        if (universe == NULL || universe->failed || name == NULL) {
                return false;
        }

        T2NominalInfo const *existing = find_nominal(universe, symbol);
        if (existing != NULL) {
                if (existing->arity != arity || strcmp(existing->name, name) != 0) {
                        return false;
                }
                for (size_t i = 0; i < arity; ++i) {
                        T2Variance wanted = variance == NULL ? T2_INVARIANT : variance[i];
                        if (existing->variance[i] != wanted) {
                                return false;
                        }
                }
                return true;
        }

        if (
                !reserve_array(
                        (void **)&universe->nominals,
                        &universe->nominal_capacity,
                        universe->nominal_count + 1,
                        sizeof *universe->nominals
                )
        ) {
                universe->failed = true;
                return false;
        }

        char *owned_name = copy_string(name);
        T2Variance *owned_variance = arity == 0
                                   ? NULL
                                   : malloc(arity * sizeof *owned_variance);
        if (owned_name == NULL || (arity != 0 && owned_variance == NULL)) {
                free(owned_name);
                free(owned_variance);
                universe->failed = true;
                return false;
        }

        for (size_t i = 0; i < arity; ++i) {
                owned_variance[i] = variance == NULL ? T2_INVARIANT : variance[i];
        }

        universe->nominals[universe->nominal_count++] = (T2NominalInfo) {
                .symbol = symbol,
                .name = owned_name,
                .arity = arity,
                .variance = owned_variance
        };
        return true;
}

T2Type
t2_nominal_type_parameter(T2Universe *universe, uint32_t index)
{
        if (index == UINT32_MAX) return T2_TYPE_INVALID;
        return t2_variable(universe, T2_VARIABLE_QUANTIFIED, index + 1);
}

static bool
nominal_reaches(
        T2Universe const *universe,
        uint64_t from,
        uint64_t wanted,
        unsigned depth
)
{
        if (from == wanted) return true;
        if (depth > T2_RELATION_DEPTH_LIMIT) return true;
        T2NominalInfo const *info = find_nominal(universe, from);
        if (info == NULL) return false;
        for (size_t i = 0; i < info->supertype_count; ++i) {
                T2Node const *supertype = get_node(universe, info->supertypes[i]);
                if (
                        supertype != NULL
                     && supertype->kind == T2_TYPE_NOMINAL
                     && nominal_reaches(
                            universe,
                            supertype->payload,
                            wanted,
                            depth + 1
                        )
                ) return true;
        }
        return false;
}

static bool backfill_nominal_super(
        T2Universe *universe,
        uint64_t symbol,
        T2Type supertype_template
);

static T2AppliedNominal const *find_applied_nominal(
        T2Universe const *universe,
        T2Type instance
);

bool
t2_nominal_add_super(
        T2Universe *universe,
        uint64_t symbol,
        T2Type supertype_template
)
{
        T2NominalInfo *info = find_nominal_mutable(universe, symbol);
        T2Node const *supertype = get_node(universe, supertype_template);
        if (
                info == NULL
             || supertype == NULL
             || supertype->kind != T2_TYPE_NOMINAL
             || find_nominal(universe, supertype->payload) == NULL
             || nominal_reaches(universe, supertype->payload, symbol, 0)
        ) return false;
        for (size_t i = 0; i < info->supertype_count; ++i) {
                if (info->supertypes[i] == supertype_template) return true;
        }
        if (!reserve_array(
                (void **)&info->supertypes,
                &info->supertype_capacity,
                info->supertype_count + 1,
                sizeof *info->supertypes
        )) {
                universe->failed = true;
                return false;
        }
        info->supertypes[info->supertype_count++] = supertype_template;
        return backfill_nominal_super(universe, symbol, supertype_template);
}

static T2Type
nominal_project_x(
        T2Universe const *universe,
        T2Type subtype,
        uint64_t target_symbol,
        unsigned depth
)
{
        if (depth > T2_RELATION_DEPTH_LIMIT) return T2_TYPE_INVALID;
        T2Node const *node = get_node(universe, subtype);
        if (node == NULL || node->kind != T2_TYPE_NOMINAL) return T2_TYPE_INVALID;
        if (node->payload == target_symbol) return subtype;
        T2AppliedNominal const *applied = find_applied_nominal(universe, subtype);
        if (applied == NULL) return T2_TYPE_INVALID;
        for (size_t i = 0; i < applied->supertype_count; ++i) {
                T2Type projected = nominal_project_x(
                        universe,
                        applied->supertypes[i],
                        target_symbol,
                        depth + 1
                );
                if (projected != T2_TYPE_INVALID) return projected;
        }
        return T2_TYPE_INVALID;
}

T2Type
t2_nominal_project(
        T2Universe const *universe,
        T2Type subtype,
        uint64_t target_symbol
)
{
        subtype = t2_type_resolve_computed(universe, subtype);
        return universe == NULL || target_symbol == 0
             ? T2_TYPE_INVALID
             : nominal_project_x(universe, subtype, target_symbol, 0);
}

enum {
        T2_POLARITY_POSITIVE = 1,
        T2_POLARITY_NEGATIVE = 2
};

static unsigned
flip_polarity(unsigned polarity)
{
        unsigned result = 0;
        if ((polarity & T2_POLARITY_POSITIVE) != 0) result |= T2_POLARITY_NEGATIVE;
        if ((polarity & T2_POLARITY_NEGATIVE) != 0) result |= T2_POLARITY_POSITIVE;
        return result;
}

static bool
validate_variance_occurrences(
        T2Universe const *universe,
        T2NominalInfo const *declaration,
        T2Type type,
        unsigned polarity,
        unsigned depth
)
{
        if (depth > T2_RELATION_DEPTH_LIMIT) return false;
        T2Node const *node = get_node(universe, type);
        if (node == NULL) return false;
        if (
                node->kind == T2_TYPE_VARIABLE
             && node->variable_kind == T2_VARIABLE_QUANTIFIED
             && node->payload != 0
             && node->payload <= declaration->arity
        ) {
                T2Variance variance = declaration->variance[node->payload - 1];
                if (variance == T2_COVARIANT) {
                        return (polarity & T2_POLARITY_NEGATIVE) == 0;
                }
                if (variance == T2_CONTRAVARIANT) {
                        return (polarity & T2_POLARITY_POSITIVE) == 0;
                }
                return true;
        }

        if (node->kind == T2_TYPE_NOMINAL) {
                T2NominalInfo const *used = find_nominal(universe, node->payload);
                if (used == NULL || used->arity != node->arity) return false;
                for (size_t i = 0; i < node->arity; ++i) {
                        unsigned child_polarity = polarity;
                        if (used->variance[i] == T2_CONTRAVARIANT) {
                                child_polarity = flip_polarity(polarity);
                        } else if (used->variance[i] == T2_INVARIANT) {
                                child_polarity = T2_POLARITY_POSITIVE
                                               | T2_POLARITY_NEGATIVE;
                        }
                        if (!validate_variance_occurrences(
                                universe,
                                declaration,
                                node->children[i],
                                child_polarity,
                                depth + 1
                        )) return false;
                }
                return true;
        }

        if (node->kind == T2_TYPE_FUNCTION) {
                size_t count = (size_t)node->payload;
                if (node->arity != count + 3) return false;
                for (size_t i = 0; i < count; ++i) {
                        T2Node const *parameter = get_node(universe, node->children[i]);
                        if (
                                parameter == NULL
                             || !validate_variance_occurrences(
                                    universe,
                                    declaration,
                                    parameter->children[0],
                                    flip_polarity(polarity),
                                    depth + 1
                                )
                        ) return false;
                }
                return validate_variance_occurrences(
                        universe,
                        declaration,
                        node->children[count],
                        polarity,
                        depth + 1
                ) && validate_variance_occurrences(
                        universe,
                        declaration,
                        node->children[count + 1],
                        polarity,
                        depth + 1
                ) && validate_variance_occurrences(
                        universe,
                        declaration,
                        node->children[count + 2],
                        flip_polarity(polarity),
                        depth + 1
                );
        }

        if (node->kind == T2_TYPE_RECORD || node->kind == T2_TYPE_ROW) {
                for (size_t i = 0; i + 1 < node->arity; ++i) {
                        T2Node const *field = get_node(universe, node->children[i]);
                        unsigned child_polarity = (
                                field->payload & T2_FIELD_WRITABLE_BIT
                        ) != 0 ? T2_POLARITY_POSITIVE | T2_POLARITY_NEGATIVE : polarity;
                        if (!validate_variance_occurrences(
                                universe,
                                declaration,
                                field->children[0],
                                child_polarity,
                                depth + 1
                        )) return false;
                }
                return true;
        }

        if (node->kind == T2_TYPE_REFINEMENT) {
                return node->arity == 2
                    && validate_variance_occurrences(
                            universe,
                            declaration,
                            node->children[0],
                            polarity,
                            depth + 1
                       )
                    && validate_variance_occurrences(
                            universe,
                            declaration,
                            node->children[1],
                            T2_POLARITY_POSITIVE | T2_POLARITY_NEGATIVE,
                            depth + 1
                       );
        }

        if (node->kind == T2_TYPE_COMPUTED) {
                for (size_t i = 0; i < node->arity; ++i) {
                        if (!validate_variance_occurrences(
                                universe,
                                declaration,
                                node->children[i],
                                T2_POLARITY_POSITIVE | T2_POLARITY_NEGATIVE,
                                depth + 1
                        )) return false;
                }
                return true;
        }

        for (size_t i = 0; i < node->arity; ++i) {
                if (!validate_variance_occurrences(
                        universe,
                        declaration,
                        node->children[i],
                        polarity,
                        depth + 1
                )) return false;
        }
        return true;
}

bool
t2_nominal_validate_variance(
        T2Universe const *universe,
        uint64_t symbol,
        T2Type public_contract
)
{
        T2NominalInfo const *declaration = find_nominal(universe, symbol);
        return declaration != NULL
            && validate_variance_occurrences(
                    universe,
                    declaration,
                    public_contract,
                    T2_POLARITY_POSITIVE,
                    0
            );
}

typedef struct t2_nominal_substitution_entry {
        T2Type source;
        T2Type result;
} T2NominalSubstitutionEntry;

typedef struct t2_nominal_substitution {
        T2Universe *universe;
        T2Type const *arguments;
        size_t arity;
        T2NominalSubstitutionEntry *entries;
        size_t count;
        size_t capacity;
} T2NominalSubstitution;

static T2Type
substitute_nominal_template(T2NominalSubstitution *substitution, T2Type source)
{
        T2Node const *node = get_node(substitution->universe, source);
        if (node == NULL) return T2_TYPE_INVALID;
        if (
                node->kind == T2_TYPE_VARIABLE
             && node->variable_kind == T2_VARIABLE_QUANTIFIED
             && node->payload != 0
             && node->payload <= substitution->arity
        ) return substitution->arguments[node->payload - 1];

        for (size_t i = 0; i < substitution->count; ++i) {
                if (substitution->entries[i].source == source) {
                        return substitution->entries[i].result;
                }
        }
        if (node->arity == 0) return source;

        T2Type *children = malloc(node->arity * sizeof *children);
        if (children == NULL) {
                substitution->universe->failed = true;
                return T2_TYPE_INVALID;
        }
        bool changed = false;
        for (size_t i = 0; i < node->arity; ++i) {
                children[i] = substitute_nominal_template(
                        substitution,
                        node->children[i]
                );
                if (children[i] == T2_TYPE_INVALID) {
                        free(children);
                        return T2_TYPE_INVALID;
                }
                changed |= children[i] != node->children[i];
        }

        T2Type result = changed
                      ? rebuild_type(substitution->universe, node, children)
                      : source;
        free(children);
        if (result == T2_TYPE_INVALID) return result;
        if (!reserve_array(
                (void **)&substitution->entries,
                &substitution->capacity,
                substitution->count + 1,
                sizeof *substitution->entries
        )) {
                substitution->universe->failed = true;
                return T2_TYPE_INVALID;
        }
        substitution->entries[substitution->count++] = (T2NominalSubstitutionEntry) {
                .source = source,
                .result = result
        };
        return result;
}

static bool
backfill_nominal_super(
        T2Universe *universe,
        uint64_t symbol,
        T2Type supertype_template
)
{
        for (size_t i = 0; i < universe->applied_nominal_count; ++i) {
                T2AppliedNominal *applied = &universe->applied_nominals[i];
                T2Node const *instance = get_node(universe, applied->instance);
                if (
                        instance == NULL
                     || instance->kind != T2_TYPE_NOMINAL
                     || instance->payload != symbol
                ) continue;
                T2NominalSubstitution substitution = {
                        .universe = universe,
                        .arguments = instance->children,
                        .arity = instance->arity
                };
                T2Type supertype = substitute_nominal_template(
                        &substitution,
                        supertype_template
                );
                free(substitution.entries);
                if (supertype == T2_TYPE_INVALID) return false;
                applied = &universe->applied_nominals[i];
                T2Type *supertypes = realloc(
                        applied->supertypes,
                        (applied->supertype_count + 1) * sizeof *supertypes
                );
                if (supertypes == NULL) {
                        universe->failed = true;
                        return false;
                }
                applied->supertypes = supertypes;
                applied->supertypes[applied->supertype_count++] = supertype;
        }
        return true;
}

static T2AppliedNominal const *
find_applied_nominal(T2Universe const *universe, T2Type instance)
{
        for (size_t i = 0; i < universe->applied_nominal_count; ++i) {
                if (universe->applied_nominals[i].instance == instance) {
                        return &universe->applied_nominals[i];
                }
        }
        return NULL;
}

T2Type
t2_nominal(
        T2Universe *universe,
        uint64_t symbol,
        T2Type const *arguments,
        size_t arity
)
{
        T2NominalInfo *info = find_nominal_mutable(universe, symbol);
        if (info == NULL || info->arity != arity) {
                return T2_TYPE_INVALID;
        }
        T2Type instance = intern_type(
                universe,
                T2_TYPE_NOMINAL,
                T2_VARIABLE_FLEXIBLE,
                symbol,
                NULL,
                arguments,
                arity
        );
        if (instance == T2_TYPE_INVALID || find_applied_nominal(universe, instance) != NULL) {
                return instance;
        }

        if (!reserve_array(
                (void **)&universe->applied_nominals,
                &universe->applied_nominal_capacity,
                universe->applied_nominal_count + 1,
                sizeof *universe->applied_nominals
        )) {
                universe->failed = true;
                return T2_TYPE_INVALID;
        }
        size_t applied_index = universe->applied_nominal_count++;
        universe->applied_nominals[applied_index] = (T2AppliedNominal) {
                .instance = instance
        };
        info->instantiated = true;

        if (info->supertype_count != 0) {
                T2Type *supertypes = malloc(
                        info->supertype_count * sizeof *supertypes
                );
                if (supertypes == NULL) {
                        universe->failed = true;
                        return T2_TYPE_INVALID;
                }
                T2NominalSubstitution substitution = {
                        .universe = universe,
                        .arguments = arguments,
                        .arity = arity
                };
                for (size_t i = 0; i < info->supertype_count; ++i) {
                        supertypes[i] = substitute_nominal_template(
                                &substitution,
                                info->supertypes[i]
                        );
                        if (supertypes[i] == T2_TYPE_INVALID) {
                                free(substitution.entries);
                                free(supertypes);
                                return T2_TYPE_INVALID;
                        }
                }
                free(substitution.entries);
                universe->applied_nominals[applied_index].supertypes = supertypes;
                universe->applied_nominals[applied_index].supertype_count = info->supertype_count;
        }
        return instance;
}

T2Type
t2_type_value(
        T2Universe *universe,
        T2Type instance,
        T2Type constructor
)
{
        if (instance == T2_TYPE_INVALID || constructor == T2_TYPE_INVALID) {
                return T2_TYPE_INVALID;
        }
        return intern_type(
                universe,
                T2_TYPE_TYPE_VALUE,
                T2_VARIABLE_FLEXIBLE,
                0,
                NULL,
                (T2Type[]) { instance, constructor },
                2
        );
}

T2Type
t2_type_value_instance(T2Universe const *universe, T2Type value)
{
        T2Node const *node = get_node(universe, value);
        return node == NULL
            || node->kind != T2_TYPE_TYPE_VALUE
            || node->arity != 2
             ? T2_TYPE_INVALID
             : node->children[0];
}

T2Type
t2_type_value_constructor(T2Universe const *universe, T2Type value)
{
        T2Node const *node = get_node(universe, value);
        return node == NULL
            || node->kind != T2_TYPE_TYPE_VALUE
            || node->arity != 2
             ? T2_TYPE_INVALID
             : node->children[1];
}

T2Type
t2_function(
        T2Universe *universe,
        T2Type const *parameters,
        size_t parameter_count,
        T2Type result
)
{
        if (
                universe == NULL
             || result == T2_TYPE_INVALID
             || (parameter_count != 0 && parameters == NULL)
             || parameter_count > SIZE_MAX / sizeof (T2ParameterSpec)
        ) {
                return T2_TYPE_INVALID;
        }

        T2ParameterSpec *specs = parameter_count == 0
                               ? NULL
                               : malloc(parameter_count * sizeof *specs);
        if (parameter_count != 0 && specs == NULL) {
                universe->failed = true;
                return T2_TYPE_INVALID;
        }
        for (size_t i = 0; i < parameter_count; ++i) {
                specs[i] = (T2ParameterSpec) {
                        .type = parameters[i],
                        .kind = T2_PARAMETER_POSITIONAL_ONLY,
                        .required = true
                };
        }
        T2Type type = t2_callable(
                universe,
                specs,
                parameter_count,
                result,
                t2_primitive(universe, T2_TYPE_NEVER),
                t2_primitive(universe, T2_TYPE_NIL)
        );
        free(specs);
        return type;
}

static bool
parameter_shape_valid(T2ParameterSpec const *parameters, size_t count)
{
        bool saw_keyword_only = false;
        bool saw_positional_rest = false;
        bool saw_keyword_rest = false;
        bool saw_pack = false;

        for (size_t i = 0; i < count; ++i) {
                T2ParameterSpec const *parameter = &parameters[i];
                if (
                        parameter->type == T2_TYPE_INVALID
                     || parameter->kind > T2_PARAMETER_PACK
                     || (
                                parameter->kind != T2_PARAMETER_POSITIONAL_ONLY
                             && parameter->name == NULL
                        )
                     || (
                                parameter->kind == T2_PARAMETER_POSITIONAL_REST
                             && parameter->required
                        )
                     || (
                                parameter->kind == T2_PARAMETER_KEYWORD_REST
                             && parameter->required
                        )
                     || (parameter->kind == T2_PARAMETER_PACK && parameter->required)
                ) return false;

                switch (parameter->kind) {
                case T2_PARAMETER_POSITIONAL_ONLY:
                case T2_PARAMETER_POSITIONAL_OR_KEYWORD:
                        if (
                                saw_keyword_only
                             || saw_positional_rest
                             || saw_keyword_rest
                             || saw_pack
                        ) return false;
                        break;
                case T2_PARAMETER_KEYWORD_ONLY:
                        if (saw_keyword_rest) return false;
                        saw_keyword_only = true;
                        break;
                case T2_PARAMETER_POSITIONAL_REST:
                        if (saw_positional_rest || saw_keyword_rest || saw_pack) return false;
                        saw_positional_rest = true;
                        saw_keyword_only = true;
                        break;
                case T2_PARAMETER_KEYWORD_REST:
                        if (saw_keyword_rest) return false;
                        saw_keyword_rest = true;
                        break;
                case T2_PARAMETER_PACK:
                        if (saw_positional_rest || saw_keyword_rest || saw_pack) {
                                return false;
                        }
                        saw_pack = true;
                        saw_keyword_only = true;
                        break;
                }

                if (parameter->name != NULL) {
                        for (size_t j = 0; j < i; ++j) {
                                if (
                                        parameters[j].name != NULL
                                     && strcmp(parameters[j].name, parameter->name) == 0
                                ) return false;
                        }
                }
        }
        return true;
}

static T2Type
callable_type(
        T2Universe *universe,
        T2ParameterSpec const *parameters,
        size_t parameter_count,
        T2Type result,
        T2Type yield,
        T2Type send,
        bool effectful
)
{
        if (
                universe == NULL
             || result == T2_TYPE_INVALID
             || yield == T2_TYPE_INVALID
             || send == T2_TYPE_INVALID
             || (parameter_count != 0 && parameters == NULL)
             || !parameter_shape_valid(parameters, parameter_count)
             || parameter_count > SIZE_MAX - 3
        ) return T2_TYPE_INVALID;

        T2Type *parts = malloc((parameter_count + 3) * sizeof *parts);
        if (parts == NULL) {
                universe->failed = true;
                return T2_TYPE_INVALID;
        }

        for (size_t i = 0; i < parameter_count; ++i) {
                uint64_t payload = (uint64_t)parameters[i].kind;
                if (parameters[i].required) payload |= T2_PARAMETER_REQUIRED;
                parts[i] = intern_type(
                        universe,
                        T2_TYPE_PARAMETER,
                        T2_VARIABLE_FLEXIBLE,
                        payload,
                        parameters[i].name,
                        &parameters[i].type,
                        1
                );
                if (parts[i] == T2_TYPE_INVALID) {
                        free(parts);
                        return T2_TYPE_INVALID;
                }
        }
        parts[parameter_count] = result;
        parts[parameter_count + 1] = yield;
        parts[parameter_count + 2] = send;

        T2Type type = intern_type(
                universe,
                T2_TYPE_FUNCTION,
                effectful ? T2_VARIABLE_RIGID : T2_VARIABLE_FLEXIBLE,
                parameter_count,
                NULL,
                parts,
                parameter_count + 3
        );
        free(parts);
        return type;
}

T2Type
t2_callable(
        T2Universe *universe,
        T2ParameterSpec const *parameters,
        size_t parameter_count,
        T2Type result,
        T2Type yield,
        T2Type send
)
{
        return callable_type(
                universe,
                parameters,
                parameter_count,
                result,
                yield,
                send,
                false
        );
}

T2Type
t2_effectful_callable(
        T2Universe *universe,
        T2ParameterSpec const *parameters,
        size_t parameter_count,
        T2Type result,
        T2Type yield,
        T2Type send
)
{
        return callable_type(
                universe,
                parameters,
                parameter_count,
                result,
                yield,
                send,
                true
        );
}

size_t
t2_callable_parameter_count(T2Universe const *universe, T2Type callable)
{
        T2Node const *node = get_node(universe, callable);
        return node == NULL || node->kind != T2_TYPE_FUNCTION
             ? 0
             : (size_t)node->payload;
}

bool
t2_callable_parameter(
        T2Universe const *universe,
        T2Type callable,
        size_t index,
        T2ParameterSpec *parameter
)
{
        T2Node const *node = get_node(universe, callable);
        if (
                node == NULL
             || node->kind != T2_TYPE_FUNCTION
             || index >= (size_t)node->payload
             || parameter == NULL
        ) return false;
        T2Node const *part = get_node(universe, node->children[index]);
        if (part == NULL || part->kind != T2_TYPE_PARAMETER) return false;
        *parameter = (T2ParameterSpec) {
                .name = part->text,
                .type = part->children[0],
                .kind = (T2ParameterKind)(part->payload & T2_PARAMETER_KIND_MASK),
                .required = (part->payload & T2_PARAMETER_REQUIRED) != 0
        };
        return true;
}

static T2Type
callable_output(T2Universe const *universe, T2Type callable, size_t offset)
{
        T2Node const *node = get_node(universe, callable);
        if (node == NULL || node->kind != T2_TYPE_FUNCTION) return T2_TYPE_INVALID;
        size_t count = (size_t)node->payload;
        return node->arity == count + 3
             ? node->children[count + offset]
             : T2_TYPE_INVALID;
}

T2Type
t2_callable_result(T2Universe const *universe, T2Type callable)
{
        return callable_output(universe, callable, 0);
}

T2Type
t2_callable_yield(T2Universe const *universe, T2Type callable)
{
        return callable_output(universe, callable, 1);
}

T2Type
t2_callable_send(T2Universe const *universe, T2Type callable)
{
        return callable_output(universe, callable, 2);
}

bool
t2_callable_is_effectful(T2Universe const *universe, T2Type callable)
{
        T2Node const *node = get_node(universe, callable);
        return node != NULL
            && node->kind == T2_TYPE_FUNCTION
            && node->variable_kind == T2_VARIABLE_RIGID;
}

T2Type
t2_tuple(T2Universe *universe, T2Type const *items, size_t count)
{
        return intern_type(
                universe,
                T2_TYPE_TUPLE,
                T2_VARIABLE_FLEXIBLE,
                0,
                NULL,
                items,
                count
        );
}

static bool
row_tail_valid(T2Universe const *universe, T2Type tail)
{
        T2Node const *node = get_node(universe, tail);
        if (node == NULL) return false;
        if (
                node->kind == T2_TYPE_ROW_EMPTY
             || node->kind == T2_TYPE_ROW_ANY
             || node->kind == T2_TYPE_ROW
             || (node->kind == T2_TYPE_META && node->variable_kind == T2_VARIABLE_ROW)
             || (node->kind == T2_TYPE_VARIABLE && node->variable_kind == T2_VARIABLE_ROW)
        ) return true;
        if (node->kind != T2_TYPE_INTERSECTION || node->arity == 0) return false;
        for (size_t i = 0; i < node->arity; ++i) {
                if (!row_tail_valid(universe, node->children[i])) return false;
        }
        return true;
}

T2Type
t2_row(
        T2Universe *universe,
        T2FieldSpec const *fields,
        size_t field_count,
        T2Type tail
)
{
        T2Type record = t2_record(
                universe,
                fields,
                field_count,
                tail,
                T2_RECORD_OPEN
        );
        T2Node const *node = get_node(universe, record);
        if (node == NULL) return T2_TYPE_INVALID;
        return intern_type(
                universe,
                T2_TYPE_ROW,
                T2_VARIABLE_ROW,
                field_count,
                NULL,
                node->children,
                node->arity
        );
}

T2Type
t2_record(
        T2Universe *universe,
        T2FieldSpec const *fields,
        size_t field_count,
        T2Type row_tail,
        T2RecordExactness exactness
)
{
        if (
                universe == NULL
             || (field_count != 0 && fields == NULL)
             || exactness > T2_RECORD_EXACT
             || field_count > SIZE_MAX - 1
        ) return T2_TYPE_INVALID;

        if (row_tail == T2_TYPE_INVALID) {
                row_tail = t2_primitive(
                        universe,
                        exactness == T2_RECORD_EXACT
                            ? T2_TYPE_ROW_EMPTY
                            : T2_TYPE_ROW_ANY
                );
        }
        if (!row_tail_valid(universe, row_tail)) return T2_TYPE_INVALID;
        if (
                exactness == T2_RECORD_EXACT
             && t2_type_kind(universe, row_tail) != T2_TYPE_ROW_EMPTY
        ) return T2_TYPE_INVALID;

        T2Type *parts = malloc((field_count + 1) * sizeof *parts);
        if (parts == NULL) {
                universe->failed = true;
                return T2_TYPE_INVALID;
        }

        for (size_t i = 0; i < field_count; ++i) {
                if (
                        fields[i].name == NULL
                     || fields[i].type == T2_TYPE_INVALID
                     || fields[i].presence > T2_PRESENCE_UNKNOWN
                     || fields[i].capability > T2_FIELD_WRITABLE
                ) {
                        free(parts);
                        return T2_TYPE_INVALID;
                }
                uint64_t payload = fields[i].presence;
                if (fields[i].capability == T2_FIELD_WRITABLE) {
                        payload |= T2_FIELD_WRITABLE_BIT;
                }
                parts[i] = intern_type(
                        universe,
                        T2_TYPE_FIELD,
                        T2_VARIABLE_FLEXIBLE,
                        payload,
                        fields[i].name,
                        &fields[i].type,
                        1
                );
                if (parts[i] == T2_TYPE_INVALID) {
                        free(parts);
                        return T2_TYPE_INVALID;
                }
        }

        for (size_t i = 1; i < field_count; ++i) {
                T2Type item = parts[i];
                T2Node const *item_node = get_node(universe, item);
                size_t j = i;
                while (j != 0) {
                        T2Node const *previous = get_node(universe, parts[j - 1]);
                        if (strcmp(item_node->text, previous->text) >= 0) break;
                        parts[j] = parts[j - 1];
                        --j;
                }
                parts[j] = item;
        }
        for (size_t i = 1; i < field_count; ++i) {
                T2Node const *left = get_node(universe, parts[i - 1]);
                T2Node const *right = get_node(universe, parts[i]);
                if (strcmp(left->text, right->text) == 0) {
                        free(parts);
                        return T2_TYPE_INVALID;
                }
        }

        parts[field_count] = row_tail;
        T2Type type = intern_type(
                universe,
                T2_TYPE_RECORD,
                T2_VARIABLE_FLEXIBLE,
                (uint64_t)exactness,
                NULL,
                parts,
                field_count + 1
        );
        free(parts);
        return type;
}

static T2Node const *
find_record_field_node(T2Universe const *universe, T2Node const *record, char const *name)
{
        size_t low = 0;
        size_t high = record->arity - 1;
        while (low < high) {
                size_t middle = low + (high - low) / 2;
                T2Node const *field = get_node(universe, record->children[middle]);
                int comparison = strcmp(field->text, name);
                if (comparison < 0) low = middle + 1;
                else high = middle;
        }
        if (low >= record->arity - 1) return NULL;
        T2Node const *field = get_node(universe, record->children[low]);
        return strcmp(field->text, name) == 0 ? field : NULL;
}

static T2Node const *
find_row_field_node(
        T2Universe const *universe,
        T2Type row,
        char const *name,
        unsigned depth
)
{
        if (depth > T2_RELATION_DEPTH_LIMIT) return NULL;
        T2Node const *node = get_node(universe, row);
        if (node == NULL) return NULL;
        if (node->kind == T2_TYPE_INTERSECTION) {
                for (size_t i = 0; i < node->arity; ++i) {
                        T2Node const *field = find_row_field_node(
                                universe,
                                node->children[i],
                                name,
                                depth + 1
                        );
                        if (field != NULL) return field;
                }
                return NULL;
        }
        if (node->kind != T2_TYPE_ROW) return NULL;
        T2Node const *field = find_record_field_node(universe, node, name);
        if (field != NULL) return field;
        return find_row_field_node(
                universe,
                node->children[node->arity - 1],
                name,
                depth + 1
        );
}

static bool
row_tail_has_variable(T2Universe const *universe, T2Type row, unsigned depth)
{
        if (depth > T2_RELATION_DEPTH_LIMIT) return true;
        T2Node const *node = get_node(universe, row);
        if (node == NULL) return false;
        if (
                (node->kind == T2_TYPE_META || node->kind == T2_TYPE_VARIABLE)
             && node->variable_kind == T2_VARIABLE_ROW
        ) return true;
        if (node->kind == T2_TYPE_INTERSECTION) {
                for (size_t i = 0; i < node->arity; ++i) {
                        if (row_tail_has_variable(
                                universe,
                                node->children[i],
                                depth + 1
                        )) return true;
                }
                return false;
        }
        return node->kind == T2_TYPE_ROW
            && row_tail_has_variable(
                    universe,
                    node->children[node->arity - 1],
                    depth + 1
            );
}

T2Type
t2_record_field_type(
        T2Universe const *universe,
        T2Type record,
        char const *name,
        T2Presence *presence,
        T2FieldCapability *capability
)
{
        T2Node const *node = get_node(universe, record);
        if (
                node == NULL
             || (node->kind != T2_TYPE_RECORD && node->kind != T2_TYPE_ROW)
             || name == NULL
        ) {
                return T2_TYPE_INVALID;
        }
        T2Node const *field = find_record_field_node(universe, node, name);
        if (field == NULL) {
                field = find_row_field_node(
                        universe,
                        node->children[node->arity - 1],
                        name,
                        0
                );
        }
        if (field == NULL) return T2_TYPE_INVALID;
        if (presence != NULL) {
                *presence = (T2Presence)(field->payload & T2_FIELD_PRESENCE_MASK);
        }
        if (capability != NULL) {
                *capability = (field->payload & T2_FIELD_WRITABLE_BIT)
                            ? T2_FIELD_WRITABLE
                            : T2_FIELD_READONLY;
        }
        return field->children[0];
}

size_t
t2_record_field_count(T2Universe const *universe, T2Type record)
{
        T2Node const *node = get_node(universe, record);
        if (
                node == NULL
             || (node->kind != T2_TYPE_RECORD && node->kind != T2_TYPE_ROW)
             || node->arity == 0
        ) return 0;
        return node->arity - 1;
}

bool
t2_record_field(
        T2Universe const *universe,
        T2Type record,
        size_t index,
        T2FieldSpec *field
)
{
        T2Node const *node = get_node(universe, record);
        if (
                node == NULL
             || field == NULL
             || (node->kind != T2_TYPE_RECORD && node->kind != T2_TYPE_ROW)
             || node->arity == 0
             || index >= node->arity - 1
        ) return false;
        T2Node const *entry = get_node(universe, node->children[index]);
        if (
                entry == NULL
             || entry->kind != T2_TYPE_FIELD
             || entry->arity != 1
             || entry->text == NULL
        ) return false;
        *field = (T2FieldSpec) {
                .name = entry->text,
                .type = entry->children[0],
                .presence = (T2Presence)(
                        entry->payload & T2_FIELD_PRESENCE_MASK
                ),
                .capability = (entry->payload & T2_FIELD_WRITABLE_BIT)
                            ? T2_FIELD_WRITABLE
                            : T2_FIELD_READONLY
        };
        return true;
}

T2Type
t2_record_row_tail(T2Universe const *universe, T2Type record)
{
        T2Node const *node = get_node(universe, record);
        if (
                node == NULL
             || (node->kind != T2_TYPE_RECORD && node->kind != T2_TYPE_ROW)
             || node->arity == 0
        ) return T2_TYPE_INVALID;
        return node->children[node->arity - 1];
}

bool
t2_record_exactness(
        T2Universe const *universe,
        T2Type record,
        T2RecordExactness *exactness
)
{
        T2Node const *node = get_node(universe, record);
        if (node == NULL || node->kind != T2_TYPE_RECORD || exactness == NULL) {
                return false;
        }
        *exactness = (T2RecordExactness)node->payload;
        return *exactness == T2_RECORD_OPEN || *exactness == T2_RECORD_EXACT;
}

static bool
pack_tail_valid(T2Universe const *universe, T2Type tail)
{
        T2Node const *node = get_node(universe, tail);
        return node != NULL
            && (
	               node->kind == T2_TYPE_PACK_EMPTY
	            || node->kind == T2_TYPE_PACK_ANY
	            || node->kind == T2_TYPE_PACK
	            || node->kind == T2_TYPE_PACK_EXPANSION
	            || (node->kind == T2_TYPE_META && node->variable_kind == T2_VARIABLE_PACK)
                    || (node->kind == T2_TYPE_VARIABLE && node->variable_kind == T2_VARIABLE_PACK)
            );
}

T2Type
t2_pack(
        T2Universe *universe,
        T2Type const *prefix,
        size_t prefix_count,
        T2Type tail
)
{
        if (
                universe == NULL
             || (prefix_count != 0 && prefix == NULL)
             || prefix_count > SIZE_MAX - 1
        ) return T2_TYPE_INVALID;
        if (tail == T2_TYPE_INVALID) {
                tail = t2_primitive(universe, T2_TYPE_PACK_EMPTY);
        }
        if (!pack_tail_valid(universe, tail)) return T2_TYPE_INVALID;

        T2Type *parts = malloc((prefix_count + 1) * sizeof *parts);
        if (parts == NULL) {
                universe->failed = true;
                return T2_TYPE_INVALID;
        }
        if (prefix_count != 0) {
                memcpy(parts, prefix, prefix_count * sizeof *parts);
        }
        parts[prefix_count] = tail;
        T2Type type = intern_type(
                universe,
                T2_TYPE_PACK,
                T2_VARIABLE_FLEXIBLE,
                prefix_count,
                NULL,
                parts,
                prefix_count + 1
        );
        free(parts);
        return type;
}

static bool
type_contains_pack_variable(
        T2Universe const *universe,
        T2Type type,
        unsigned depth
)
{
        if (depth > T2_RELATION_DEPTH_LIMIT) return true;
        T2Node const *node = get_node(universe, type);
        if (node == NULL) return true;
        if (
                (node->kind == T2_TYPE_META || node->kind == T2_TYPE_VARIABLE)
             && node->variable_kind == T2_VARIABLE_PACK
        ) return true;
        for (size_t i = 0; i < node->arity; ++i) {
                if (type_contains_pack_variable(universe, node->children[i], depth + 1)) {
                        return true;
                }
        }
        return false;
}

T2Type
t2_pack_expansion(T2Universe *universe, T2Type element)
{
        T2Node const *node = get_node(universe, element);
        if (node == NULL) return T2_TYPE_INVALID;
        if (pack_tail_valid(universe, element)) return element;
        return intern_type(
                universe,
                T2_TYPE_PACK_EXPANSION,
                T2_VARIABLE_PACK,
                0,
                NULL,
                &element,
                1
        );
}

static T2Type
pack_fold(T2Universe *universe, T2Type pack, bool intersection)
{
        T2Node const *node = get_node(universe, pack);
        if (node == NULL || !pack_tail_valid(universe, pack)) {
                return T2_TYPE_INVALID;
        }
        if (node->kind == T2_TYPE_PACK_EMPTY) {
                return t2_primitive(
                        universe,
                        intersection ? T2_TYPE_ANY : T2_TYPE_NEVER
                );
        }
        if (node->kind == T2_TYPE_PACK_ANY) {
                return t2_primitive(universe, T2_TYPE_UNKNOWN);
        }
        if (
                node->kind == T2_TYPE_PACK_EXPANSION
             && !type_contains_pack_variable(universe, node->children[0], 0)
        ) return node->children[0];
        if (node->kind == T2_TYPE_PACK) {
                size_t count = (size_t)node->payload;
                T2Type result = pack_fold(
                        universe,
                        node->children[count],
                        intersection
                );
                if (result == T2_TYPE_INVALID) return result;
                for (size_t i = 0; i < count; ++i) {
                        result = intersection
                               ? t2_intersection(
                                       universe,
                                       (T2Type[]) { result, node->children[i] },
                                       2
                                 )
                               : t2_union(
                                       universe,
                                       (T2Type[]) { result, node->children[i] },
                                       2
                                 );
                        if (result == T2_TYPE_INVALID) return result;
                }
                return result;
        }
        return intern_type(
                universe,
                intersection
                    ? T2_TYPE_PACK_FOLD_INTERSECTION
                    : T2_TYPE_PACK_FOLD_UNION,
                T2_VARIABLE_FLEXIBLE,
                0,
                NULL,
                &pack,
                1
        );
}

T2Type
t2_pack_fold_union(T2Universe *universe, T2Type pack)
{
        return pack_fold(universe, pack, false);
}

T2Type
t2_pack_fold_intersection(T2Universe *universe, T2Type pack)
{
        return pack_fold(universe, pack, true);
}

T2Type
t2_variadic_tuple(
        T2Universe *universe,
        T2Type const *prefix,
        size_t prefix_count,
        T2Type tail
)
{
        if (
                universe == NULL
             || (prefix_count != 0 && prefix == NULL)
             || prefix_count > SIZE_MAX - 1
             || !pack_tail_valid(universe, tail)
        ) return T2_TYPE_INVALID;

        T2Node const *tail_node = get_node(universe, tail);
        if (tail_node->kind == T2_TYPE_PACK_EMPTY) {
                return t2_tuple(universe, prefix, prefix_count);
        }
        if (tail_node->kind == T2_TYPE_PACK) {
                size_t extra = (size_t)tail_node->payload;
                if (prefix_count > SIZE_MAX - extra) return T2_TYPE_INVALID;
                T2Type *combined = malloc(
                        (prefix_count + extra) * sizeof *combined
                );
                if (prefix_count + extra != 0 && combined == NULL) {
                        universe->failed = true;
                        return T2_TYPE_INVALID;
                }
                if (prefix_count != 0) {
                        memcpy(combined, prefix, prefix_count * sizeof *combined);
                }
                if (extra != 0) {
                        memcpy(
                                combined + prefix_count,
                                tail_node->children,
                                extra * sizeof *combined
                        );
                }
                T2Type result = t2_variadic_tuple(
                        universe,
                        combined,
                        prefix_count + extra,
                        tail_node->children[extra]
                );
                free(combined);
                return result;
        }

        T2Type *parts = malloc((prefix_count + 1) * sizeof *parts);
        if (parts == NULL) {
                universe->failed = true;
                return T2_TYPE_INVALID;
        }
        if (prefix_count != 0) {
                memcpy(parts, prefix, prefix_count * sizeof *parts);
        }
        parts[prefix_count] = tail;
        T2Type result = intern_type(
                universe,
                T2_TYPE_VARIADIC_TUPLE,
                T2_VARIABLE_FLEXIBLE,
                prefix_count,
                NULL,
                parts,
                prefix_count + 1
        );
        free(parts);
        return result;
}

static T2Type
rebuild_type(
        T2Universe *universe,
        T2Node const *node,
        T2Type const *children
)
{
        switch (node->kind) {
        case T2_TYPE_NOMINAL:
                return t2_nominal(
                        universe,
                        node->payload,
                        children,
                        node->arity
                );
        case T2_TYPE_INT_RANGE:
        {
                bool has_lower = (node->payload & T2_RANGE_HAS_LOWER) != 0;
                bool has_upper = (node->payload & T2_RANGE_HAS_UPPER) != 0;
                return t2_integer_range(
                        universe,
                        has_lower ? children[0] : T2_TYPE_INVALID,
                        has_upper ? children[has_lower] : T2_TYPE_INVALID,
                        (node->payload & T2_RANGE_UPPER_INCLUSIVE) != 0
                );
        }
        case T2_TYPE_PACK:
                return t2_pack(
                        universe,
                        children,
                        (size_t)node->payload,
                        children[node->payload]
                );
        case T2_TYPE_PACK_EXPANSION:
                return t2_pack_expansion(universe, children[0]);
        case T2_TYPE_PACK_FOLD_UNION:
                return t2_pack_fold_union(universe, children[0]);
        case T2_TYPE_PACK_FOLD_INTERSECTION:
                return t2_pack_fold_intersection(universe, children[0]);
        case T2_TYPE_VARIADIC_TUPLE:
                return t2_variadic_tuple(
                        universe,
                        children,
                        (size_t)node->payload,
                        children[node->payload]
                );
        default:
                return intern_type(
                        universe,
                        node->kind,
                        node->variable_kind,
                        node->payload,
                        node->text,
                        children,
                        node->arity
                );
        }
}

T2Type
t2_recursive_variable(T2Universe *universe, uint32_t binder)
{
        if (binder == 0) return T2_TYPE_INVALID;
        return intern_type(
                universe,
                T2_TYPE_RECURSIVE_VARIABLE,
                T2_VARIABLE_RIGID,
                binder,
                NULL,
                NULL,
                0
        );
}

static bool
guarded_occurrences(
        T2Universe const *universe,
        T2Type type,
        uint32_t binder,
        bool guarded,
        unsigned depth
)
{
        if (depth > T2_RELATION_DEPTH_LIMIT) return false;
        T2Node const *node = get_node(universe, type);
        if (node == NULL) return false;
        if (node->kind == T2_TYPE_RECURSIVE_VARIABLE) {
                return node->payload != binder || guarded;
        }

        bool contractive = guarded
                        || node->kind == T2_TYPE_NOMINAL
                        || node->kind == T2_TYPE_FUNCTION
                        || node->kind == T2_TYPE_TUPLE
                        || node->kind == T2_TYPE_VARIADIC_TUPLE
                        || node->kind == T2_TYPE_RECORD
                        || node->kind == T2_TYPE_PACK
                        || node->kind == T2_TYPE_PACK_EXPANSION;
        if (
                node->kind == T2_TYPE_UNION
             || node->kind == T2_TYPE_INTERSECTION
             || node->kind == T2_TYPE_RECURSIVE
        ) contractive = guarded;

        for (size_t i = 0; i < node->arity; ++i) {
                if (!guarded_occurrences(
                        universe,
                        node->children[i],
                        binder,
                        contractive,
                        depth + 1
                )) return false;
        }
        return true;
}

static bool
contains_recursive_binder(
        T2Universe const *universe,
        T2Type type,
        uint32_t binder,
        unsigned depth
)
{
        if (depth > T2_RELATION_DEPTH_LIMIT) return true;
        T2Node const *node = get_node(universe, type);
        if (node == NULL) return true;
        if (node->kind == T2_TYPE_RECURSIVE_VARIABLE) {
                return node->payload == binder;
        }
        for (size_t i = 0; i < node->arity; ++i) {
                if (contains_recursive_binder(
                        universe,
                        node->children[i],
                        binder,
                        depth + 1
                )) return true;
        }
        return false;
}

T2Type
t2_recursive(T2Universe *universe, uint32_t binder, T2Type body)
{
        if (
                universe == NULL
             || binder == 0
             || get_node(universe, body) == NULL
        ) return T2_TYPE_INVALID;

        /* A vacuous mu binder is exactly its body.  Keeping the wrapper makes
         * every ordinary alias look recursive to expression inference and
         * defeats canonical hashing/display. */
        if (!contains_recursive_binder(universe, body, binder, 0)) return body;
        if (!guarded_occurrences(universe, body, binder, false, 0)) {
                return T2_TYPE_INVALID;
        }

        if (binder >= universe->next_recursive_id) {
                universe->next_recursive_id = binder == UINT32_MAX ? 0 : binder + 1;
        }

        for (size_t i = 0; i < universe->recursive_count; ++i) {
                if (universe->recursive[i].binder != binder) continue;
                T2Node const *existing = get_node(universe, universe->recursive[i].type);
                if (existing != NULL && existing->children[0] == body) {
                        return universe->recursive[i].type;
                }
                return T2_TYPE_INVALID;
        }

        T2Type type = intern_type(
                universe,
                T2_TYPE_RECURSIVE,
                T2_VARIABLE_RIGID,
                binder,
                NULL,
                &body,
                1
        );
        if (type == T2_TYPE_INVALID) return type;
        if (!reserve_array(
                (void **)&universe->recursive,
                &universe->recursive_capacity,
                universe->recursive_count + 1,
                sizeof *universe->recursive
        )) {
                universe->failed = true;
                return T2_TYPE_INVALID;
        }
        universe->recursive[universe->recursive_count++] = (T2RecursiveInfo) {
                .binder = binder,
                .type = type
        };
        return type;
}

bool
t2_recursive_is_guarded(T2Universe const *universe, T2Type type)
{
        T2Node const *node = get_node(universe, type);
        return node != NULL
            && node->kind == T2_TYPE_RECURSIVE
            && guarded_occurrences(
                    universe,
                    node->children[0],
                    (uint32_t)node->payload,
                    false,
                    0
            );
}

static int
compare_types(T2Universe const *universe, T2Type left, T2Type right, unsigned depth)
{
        if (left == right) {
                return 0;
        }
        if (depth > T2_RELATION_DEPTH_LIMIT) {
                return left < right ? -1 : 1;
        }

        T2Node const *a = get_node(universe, left);
        T2Node const *b = get_node(universe, right);
        if (a == NULL || b == NULL) {
                return left < right ? -1 : 1;
        }
        if (a->kind != b->kind) return a->kind < b->kind ? -1 : 1;
        if (a->variable_kind != b->variable_kind) {
                return a->variable_kind < b->variable_kind ? -1 : 1;
        }
        if (a->payload != b->payload) return a->payload < b->payload ? -1 : 1;
        if ((a->text == NULL) != (b->text == NULL)) return a->text == NULL ? -1 : 1;
        if (a->text != NULL) {
                int comparison = strcmp(a->text, b->text);
                if (comparison != 0) return comparison;
        }
        if (a->arity != b->arity) return a->arity < b->arity ? -1 : 1;
        for (size_t i = 0; i < a->arity; ++i) {
                int comparison = compare_types(
                        universe,
                        a->children[i],
                        b->children[i],
                        depth + 1
                );
                if (comparison != 0) return comparison;
        }
        return left < right ? -1 : 1;
}

static bool
push_type(T2TypeVector *types, T2Type type)
{
        if (
                !reserve_array(
                        (void **)&types->items,
                        &types->capacity,
                        types->count + 1,
                        sizeof *types->items
                )
        ) {
                return false;
        }
        types->items[types->count++] = type;
        return true;
}

static bool
collect_set_arms(
        T2Universe const *universe,
        T2TypeKind kind,
        T2Type type,
        T2TypeVector *arms
)
{
        T2Node const *node = get_node(universe, type);
        if (node == NULL) {
                return false;
        }
        if (node->kind != kind) {
                return push_type(arms, type);
        }
        for (size_t i = 0; i < node->arity; ++i) {
                if (!collect_set_arms(universe, kind, node->children[i], arms)) {
                        return false;
                }
        }
        return true;
}

typedef enum t2_pair_state {
        T2_PAIR_IN_PROGRESS,
        T2_PAIR_COMPLETE
} T2PairState;

typedef struct t2_relation_pair {
        T2Type subtype;
        T2Type supertype;
        unsigned progress;
        T2PairState state;
        T2Relation result;
} T2RelationPair;

typedef struct t2_relation_context {
        T2Universe const *universe;
        T2RelationPair *pairs;
        size_t pair_count;
        size_t pair_capacity;
        size_t steps;
        size_t step_limit;
        bool failed;
} T2RelationContext;

static T2Relation subtype_relation(
        T2RelationContext *context,
        T2Type subtype,
        T2Type supertype,
        unsigned progress
);

static T2Relation combine_all(T2Relation aggregate, T2Relation next);
static T2Relation combine_any(T2Relation aggregate, T2Relation next);

static T2TypeKind
literal_base(T2TypeKind kind)
{
        switch (kind) {
        case T2_TYPE_LITERAL_BOOL:
                return T2_TYPE_BOOL;
        case T2_TYPE_LITERAL_INT:
                return T2_TYPE_INT;
        case T2_TYPE_LITERAL_STRING:
                return T2_TYPE_STRING;
        case T2_TYPE_INT_RANGE:
                return T2_TYPE_INT;
        case T2_TYPE_VARIADIC_TUPLE:
                return T2_TYPE_TUPLE;
        default:
                return kind;
        }
}

static T2Node const *
range_bound(
        T2Universe const *universe,
        T2Node const *range,
        bool lower
)
{
        uint64_t flag = lower ? T2_RANGE_HAS_LOWER : T2_RANGE_HAS_UPPER;
        if (range == NULL || (range->payload & flag) == 0) return NULL;
        size_t index = !lower && (range->payload & T2_RANGE_HAS_LOWER) != 0;
        return get_node(universe, range->children[index]);
}

static T2Relation
literal_in_range(
        T2Universe const *universe,
        T2Node const *literal,
        T2Node const *range
)
{
        if (literal == NULL || literal->kind != T2_TYPE_LITERAL_INT) {
                return T2_RELATION_NO;
        }
        int64_t value = (int64_t)literal->payload;
        T2Node const *lower = range_bound(universe, range, true);
        T2Node const *upper = range_bound(universe, range, false);
        if (lower != NULL) {
                if (
                        lower->kind == T2_TYPE_META
                     || lower->kind == T2_TYPE_VARIABLE
                ) return T2_RELATION_DEFERRED;
                if (
                        lower->kind != T2_TYPE_LITERAL_INT
                     || value < (int64_t)lower->payload
                ) return T2_RELATION_NO;
        }
        if (upper != NULL) {
                if (
                        upper->kind == T2_TYPE_META
                     || upper->kind == T2_TYPE_VARIABLE
                ) return T2_RELATION_DEFERRED;
                if (upper->kind != T2_TYPE_LITERAL_INT) return T2_RELATION_NO;
                int64_t high = (int64_t)upper->payload;
                bool inclusive = (range->payload & T2_RANGE_UPPER_INCLUSIVE) != 0;
                if (inclusive ? value > high : value >= high) return T2_RELATION_NO;
        }
        return T2_RELATION_YES;
}

static T2Relation
range_subtype_range(
        T2Universe const *universe,
        T2Node const *actual,
        T2Node const *expected
)
{
        T2Node const *actual_lower = range_bound(universe, actual, true);
        T2Node const *expected_lower = range_bound(universe, expected, true);
        if (expected_lower != NULL) {
                if (actual_lower == NULL) return T2_RELATION_NO;
                if (
                        actual_lower->kind == T2_TYPE_META
                     || actual_lower->kind == T2_TYPE_VARIABLE
                     || expected_lower->kind == T2_TYPE_META
                     || expected_lower->kind == T2_TYPE_VARIABLE
                ) return T2_RELATION_DEFERRED;
                if (
                        actual_lower->kind != T2_TYPE_LITERAL_INT
                     || expected_lower->kind != T2_TYPE_LITERAL_INT
                     || (int64_t)actual_lower->payload
                            < (int64_t)expected_lower->payload
                ) return T2_RELATION_NO;
        }

        T2Node const *actual_upper = range_bound(universe, actual, false);
        T2Node const *expected_upper = range_bound(universe, expected, false);
        if (expected_upper != NULL) {
                if (actual_upper == NULL) return T2_RELATION_NO;
                if (
                        actual_upper->kind == T2_TYPE_META
                     || actual_upper->kind == T2_TYPE_VARIABLE
                     || expected_upper->kind == T2_TYPE_META
                     || expected_upper->kind == T2_TYPE_VARIABLE
                ) return T2_RELATION_DEFERRED;
                if (
                        actual_upper->kind != T2_TYPE_LITERAL_INT
                     || expected_upper->kind != T2_TYPE_LITERAL_INT
                ) return T2_RELATION_NO;
                int64_t actual_high = (int64_t)actual_upper->payload;
                int64_t expected_high = (int64_t)expected_upper->payload;
                if (actual_high > expected_high) return T2_RELATION_NO;
                if (
                        actual_high == expected_high
                     && (actual->payload & T2_RANGE_UPPER_INCLUSIVE) != 0
                     && (expected->payload & T2_RANGE_UPPER_INCLUSIVE) == 0
                ) return T2_RELATION_NO;
        }
        return T2_RELATION_YES;
}

static bool
object_value_kind(T2TypeKind kind)
{
        switch (literal_base(kind)) {
        case T2_TYPE_BOOL:
        case T2_TYPE_INT:
        case T2_TYPE_FLOAT:
        case T2_TYPE_STRING:
        case T2_TYPE_INT_RANGE:
        case T2_TYPE_NOMINAL:
        case T2_TYPE_TYPE_VALUE:
        case T2_TYPE_REFINEMENT:
        case T2_TYPE_FUNCTION:
        case T2_TYPE_TUPLE:
        case T2_TYPE_VARIADIC_TUPLE:
        case T2_TYPE_RECORD:
        case T2_TYPE_PACK:
        case T2_TYPE_RECURSIVE:
        case T2_TYPE_OVERLOAD:
                return true;
        default:
                return false;
        }
}

static T2Type
recursive_definition(T2Universe const *universe, uint32_t binder)
{
        for (size_t i = 0; i < universe->recursive_count; ++i) {
                if (universe->recursive[i].binder == binder) {
                        return universe->recursive[i].type;
                }
        }
        return T2_TYPE_INVALID;
}

static T2Type
unfold_recursive_head(T2Universe const *universe, T2Type type, bool *changed)
{
        T2Node const *node = get_node(universe, type);
        *changed = false;
        if (node == NULL) return T2_TYPE_INVALID;
        if (node->kind == T2_TYPE_RECURSIVE) {
                *changed = true;
                return node->children[0];
        }
        if (node->kind == T2_TYPE_RECURSIVE_VARIABLE) {
                T2Type definition = recursive_definition(universe, (uint32_t)node->payload);
                T2Node const *recursive = get_node(universe, definition);
                if (recursive == NULL || recursive->kind != T2_TYPE_RECURSIVE) {
                        return T2_TYPE_INVALID;
                }
                *changed = true;
                return recursive->children[0];
        }
        return type;
}

static T2Relation
compare_field_types(
        T2RelationContext *context,
        T2Node const *actual,
        T2Node const *expected,
        unsigned progress
)
{
        T2Presence actual_presence = actual == NULL
                                   ? T2_PRESENCE_ABSENT
                                   : (T2Presence)(actual->payload & T2_FIELD_PRESENCE_MASK);
        T2Presence expected_presence = (T2Presence)(
                expected->payload & T2_FIELD_PRESENCE_MASK
        );

        if (expected_presence == T2_PRESENCE_REQUIRED) {
                if (actual_presence != T2_PRESENCE_REQUIRED) return T2_RELATION_NO;
        } else if (expected_presence == T2_PRESENCE_ABSENT) {
                return actual_presence == T2_PRESENCE_ABSENT
                     ? T2_RELATION_YES
                     : T2_RELATION_NO;
        } else if (expected_presence == T2_PRESENCE_OPTIONAL) {
                if (actual_presence == T2_PRESENCE_ABSENT) return T2_RELATION_YES;
                if (actual_presence == T2_PRESENCE_UNKNOWN) return T2_RELATION_NO;
        } else if (actual_presence == T2_PRESENCE_ABSENT) {
                return T2_RELATION_YES;
        }

        if (actual == NULL) return T2_RELATION_NO;
        bool expected_writable = (expected->payload & T2_FIELD_WRITABLE_BIT) != 0;
        bool actual_writable = (actual->payload & T2_FIELD_WRITABLE_BIT) != 0;
        if (expected_writable && !actual_writable) return T2_RELATION_NO;

        T2Relation read = subtype_relation(
                context,
                actual->children[0],
                expected->children[0],
                progress + 1
        );
        if (!expected_writable) return read;
        return combine_all(
                read,
                subtype_relation(
                        context,
                        expected->children[0],
                        actual->children[0],
                        progress + 1
                )
        );
}

static T2Relation
record_subtype(
        T2RelationContext *context,
        T2Node const *actual,
        T2Node const *expected,
        unsigned progress
)
{
        T2Node const *actual_tail = get_node(
                context->universe,
                actual->children[actual->arity - 1]
        );
        T2Node const *expected_tail = get_node(
                context->universe,
                expected->children[expected->arity - 1]
        );
        if (actual_tail == NULL || expected_tail == NULL) return T2_RELATION_NO;

        T2Relation relation = T2_RELATION_YES;
        for (size_t i = 0; i + 1 < expected->arity; ++i) {
                T2Node const *wanted = get_node(context->universe, expected->children[i]);
                T2Node const *have = find_record_field_node(
                        context->universe,
                        actual,
                        wanted->text
                );
                if (have == NULL) {
                        have = find_row_field_node(
                                context->universe,
                                actual->children[actual->arity - 1],
                                wanted->text,
                                0
                        );
                }
                if (have == NULL && actual_tail->kind != T2_TYPE_ROW_EMPTY) {
                        if (row_tail_has_variable(
                                context->universe,
                                actual->children[actual->arity - 1],
                                0
                        )) {
                                relation = combine_all(relation, T2_RELATION_DEFERRED);
                                continue;
                        }
                        T2Presence wanted_presence = (T2Presence)(
                                wanted->payload & T2_FIELD_PRESENCE_MASK
                        );
                        if (
                                wanted_presence == T2_PRESENCE_REQUIRED
                             || wanted_presence == T2_PRESENCE_ABSENT
                        ) return T2_RELATION_NO;
                }
                relation = combine_all(
                        relation,
                        compare_field_types(context, have, wanted, progress)
                );
                if (relation == T2_RELATION_NO) return relation;
        }

        if ((T2RecordExactness)expected->payload == T2_RECORD_EXACT) {
                if (
                        actual_tail->kind != T2_TYPE_ROW_EMPTY
                     || (T2RecordExactness)actual->payload != T2_RECORD_EXACT
                ) return T2_RELATION_NO;
                for (size_t i = 0; i + 1 < actual->arity; ++i) {
                        T2Node const *field = get_node(context->universe, actual->children[i]);
                        T2Node const *wanted = find_record_field_node(
                                context->universe,
                                expected,
                                field->text
                        );
                        if (
                                wanted == NULL
                             && (field->payload & T2_FIELD_PRESENCE_MASK)
                                    != T2_PRESENCE_ABSENT
                        ) return T2_RELATION_NO;
                }
        }

        if (
                expected_tail->kind == T2_TYPE_META
             || expected_tail->kind == T2_TYPE_VARIABLE
             || actual_tail->kind == T2_TYPE_META
             || actual_tail->kind == T2_TYPE_VARIABLE
        ) return combine_all(relation, T2_RELATION_DEFERRED);
        return relation;
}

static T2Relation
row_subtype(
        T2RelationContext *context,
        T2Node const *actual,
        T2Node const *expected,
        unsigned progress
)
{
        T2Node const *actual_tail = get_node(
                context->universe,
                actual->children[actual->arity - 1]
        );
        T2Node const *expected_tail = get_node(
                context->universe,
                expected->children[expected->arity - 1]
        );
        if (actual_tail == NULL || expected_tail == NULL) return T2_RELATION_NO;

        T2Relation relation = T2_RELATION_YES;
        for (size_t i = 0; i + 1 < expected->arity; ++i) {
                T2Node const *wanted = get_node(context->universe, expected->children[i]);
                T2Node const *have = find_record_field_node(
                        context->universe,
                        actual,
                        wanted->text
                );
                if (have == NULL) {
                        have = find_row_field_node(
                                context->universe,
                                actual->children[actual->arity - 1],
                                wanted->text,
                                0
                        );
                }
                if (have == NULL) {
                        if (row_tail_has_variable(
                                context->universe,
                                actual->children[actual->arity - 1],
                                0
                        )) {
                                relation = combine_all(relation, T2_RELATION_DEFERRED);
                                continue;
                        }
                        T2Presence presence = (T2Presence)(
                                wanted->payload & T2_FIELD_PRESENCE_MASK
                        );
                        if (
                                presence == T2_PRESENCE_REQUIRED
                             || presence == T2_PRESENCE_ABSENT
                        ) return T2_RELATION_NO;
                }
                relation = combine_all(
                        relation,
                        compare_field_types(context, have, wanted, progress)
                );
                if (relation == T2_RELATION_NO) return relation;
        }

        if (expected_tail->kind == T2_TYPE_ROW_EMPTY) {
                for (size_t i = 0; i + 1 < actual->arity; ++i) {
                        T2Node const *field = get_node(context->universe, actual->children[i]);
                        if (
                                find_record_field_node(
                                        context->universe,
                                        expected,
                                        field->text
                                ) == NULL
                             && (field->payload & T2_FIELD_PRESENCE_MASK)
                                    != T2_PRESENCE_ABSENT
                        ) return T2_RELATION_NO;
                }
        }
        return combine_all(
                relation,
                subtype_relation(
                        context,
                        actual->children[actual->arity - 1],
                        expected->children[expected->arity - 1],
                        progress + 1
                )
        );
}

static bool
parameter_accepts_position(T2Node const *parameter)
{
        T2ParameterKind kind = (T2ParameterKind)(
                parameter->payload & T2_PARAMETER_KIND_MASK
        );
        return kind == T2_PARAMETER_POSITIONAL_ONLY
            || kind == T2_PARAMETER_POSITIONAL_OR_KEYWORD;
}

static bool
parameter_accepts_keyword(T2Node const *parameter)
{
        T2ParameterKind kind = (T2ParameterKind)(
                parameter->payload & T2_PARAMETER_KIND_MASK
        );
        return kind == T2_PARAMETER_POSITIONAL_OR_KEYWORD
            || kind == T2_PARAMETER_KEYWORD_ONLY;
}

static T2Node const *
function_positional_parameter(
        T2Universe const *universe,
        T2Node const *function,
        size_t position
)
{
        size_t seen = 0;
        size_t count = (size_t)function->payload;
        for (size_t i = 0; i < count; ++i) {
                T2Node const *parameter = get_node(universe, function->children[i]);
                if (!parameter_accepts_position(parameter)) continue;
                if (seen++ == position) return parameter;
        }
        return NULL;
}

static T2Node const *
function_parameter_kind(
        T2Universe const *universe,
        T2Node const *function,
        T2ParameterKind wanted
)
{
        size_t count = (size_t)function->payload;
        for (size_t i = 0; i < count; ++i) {
                T2Node const *parameter = get_node(universe, function->children[i]);
                T2ParameterKind kind = (T2ParameterKind)(
                        parameter->payload & T2_PARAMETER_KIND_MASK
                );
                if (kind == wanted) return parameter;
        }
        return NULL;
}

static T2Node const *
function_keyword_parameter(
        T2Universe const *universe,
        T2Node const *function,
        char const *name
)
{
        size_t count = (size_t)function->payload;
        for (size_t i = 0; i < count; ++i) {
                T2Node const *parameter = get_node(universe, function->children[i]);
                if (
                        parameter_accepts_keyword(parameter)
                     && parameter->text != NULL
                     && strcmp(parameter->text, name) == 0
                ) return parameter;
        }
        return NULL;
}

static T2Relation
contravariant_parameter(
        T2RelationContext *context,
        T2Node const *actual,
        T2Node const *expected,
        unsigned progress
)
{
        if (actual == NULL || expected == NULL) return T2_RELATION_NO;
        return subtype_relation(
                context,
                expected->children[0],
                actual->children[0],
                progress + 1
        );
}

static T2Relation
function_subtype(
        T2RelationContext *context,
        T2Node const *actual,
        T2Node const *expected,
        unsigned progress
)
{
        size_t actual_count = (size_t)actual->payload;
        size_t expected_count = (size_t)expected->payload;
        if (actual->arity != actual_count + 3 || expected->arity != expected_count + 3) {
                return T2_RELATION_NO;
        }

        T2Node const *actual_rest = function_parameter_kind(
                context->universe,
                actual,
                T2_PARAMETER_POSITIONAL_REST
        );
        T2Node const *expected_rest = function_parameter_kind(
                context->universe,
                expected,
                T2_PARAMETER_POSITIONAL_REST
        );
        T2Node const *actual_pack = function_parameter_kind(
                context->universe,
                actual,
                T2_PARAMETER_PACK
        );
        T2Node const *expected_pack = function_parameter_kind(
                context->universe,
                expected,
                T2_PARAMETER_PACK
        );
        T2Node const *actual_kwrest = function_parameter_kind(
                context->universe,
                actual,
                T2_PARAMETER_KEYWORD_REST
        );
        T2Node const *expected_kwrest = function_parameter_kind(
                context->universe,
                expected,
                T2_PARAMETER_KEYWORD_REST
        );

        T2Relation relation = T2_RELATION_YES;
        size_t expected_positions = 0;
        for (size_t i = 0; i < expected_count; ++i) {
                T2Node const *parameter = get_node(context->universe, expected->children[i]);
                if (parameter_accepts_position(parameter)) expected_positions += 1;
        }
        for (size_t i = 0; i < expected_positions; ++i) {
                T2Node const *wanted = function_positional_parameter(
                        context->universe,
                        expected,
                        i
                );
                T2Node const *have = function_positional_parameter(
                        context->universe,
                        actual,
                        i
                );
                if (have == NULL) have = actual_rest == NULL ? actual_pack : actual_rest;
                relation = combine_all(
                        relation,
                        contravariant_parameter(context, have, wanted, progress)
                );
                if (relation == T2_RELATION_NO) return relation;
        }
        if (expected_rest != NULL || expected_pack != NULL) {
                T2Node const *wanted = expected_rest == NULL ? expected_pack : expected_rest;
                T2Node const *have = actual_rest == NULL ? actual_pack : actual_rest;
                relation = combine_all(
                        relation,
                        contravariant_parameter(context, have, wanted, progress)
                );
                if (relation == T2_RELATION_NO) return relation;
        }

        for (size_t i = 0; i < expected_count; ++i) {
                T2Node const *wanted = get_node(context->universe, expected->children[i]);
                if (!parameter_accepts_keyword(wanted)) continue;
                T2Node const *have = function_keyword_parameter(
                        context->universe,
                        actual,
                        wanted->text
                );
                if (have == NULL) have = actual_kwrest;
                relation = combine_all(
                        relation,
                        contravariant_parameter(context, have, wanted, progress)
                );
                if (relation == T2_RELATION_NO) return relation;
        }
        if (expected_kwrest != NULL) {
                relation = combine_all(
                        relation,
                        contravariant_parameter(context, actual_kwrest, expected_kwrest, progress)
                );
                if (relation == T2_RELATION_NO) return relation;
        }

        for (size_t i = 0; i < actual_count; ++i) {
                T2Node const *required = get_node(context->universe, actual->children[i]);
                if ((required->payload & T2_PARAMETER_REQUIRED) == 0) continue;
                T2ParameterKind kind = (T2ParameterKind)(
                        required->payload & T2_PARAMETER_KIND_MASK
                );
                T2Node const *guaranteed = NULL;
                if (
                        kind == T2_PARAMETER_POSITIONAL_ONLY
                     || kind == T2_PARAMETER_POSITIONAL_OR_KEYWORD
                ) {
                        size_t position = 0;
                        for (size_t j = 0; j < i; ++j) {
                                T2Node const *prior = get_node(
                                        context->universe,
                                        actual->children[j]
                                );
                                position += parameter_accepts_position(prior);
                        }
                        guaranteed = function_positional_parameter(
                                context->universe,
                                expected,
                                position
                        );
                        if (
                                kind == T2_PARAMETER_POSITIONAL_OR_KEYWORD
                             && (
                                        guaranteed == NULL
                                     || (guaranteed->payload & T2_PARAMETER_REQUIRED) == 0
                                )
                        ) guaranteed = function_keyword_parameter(
                                context->universe,
                                expected,
                                required->text
                        );
                } else if (kind == T2_PARAMETER_KEYWORD_ONLY) {
                        guaranteed = function_keyword_parameter(
                                context->universe,
                                expected,
                                required->text
                        );
                }
                if (
                        guaranteed == NULL
                     || (guaranteed->payload & T2_PARAMETER_REQUIRED) == 0
                ) return T2_RELATION_NO;
        }

        relation = combine_all(
                relation,
                subtype_relation(
                        context,
                        actual->children[actual_count],
                        expected->children[expected_count],
                        progress + 1
                )
        );
        relation = combine_all(
                relation,
                subtype_relation(
                        context,
                        actual->children[actual_count + 1],
                        expected->children[expected_count + 1],
                        progress + 1
                )
        );
        return combine_all(
                relation,
                subtype_relation(
                        context,
                        expected->children[expected_count + 2],
                        actual->children[actual_count + 2],
                        progress + 1
                )
        );
}

static T2Relation
pack_subtype(
        T2RelationContext *context,
        T2Node const *actual,
        T2Node const *expected,
        unsigned progress
)
{
        if (expected->kind == T2_TYPE_PACK_ANY) return T2_RELATION_YES;
        if (actual->kind == T2_TYPE_PACK_ANY) return T2_RELATION_NO;
        if (actual->kind == T2_TYPE_PACK_EMPTY) {
                return expected->kind == T2_TYPE_PACK_EMPTY
                    || expected->kind == T2_TYPE_PACK_EXPANSION
                     ? T2_RELATION_YES
                     : T2_RELATION_NO;
        }
        if (expected->kind == T2_TYPE_PACK_EMPTY) return T2_RELATION_NO;
        if (expected->kind == T2_TYPE_PACK_EXPANSION) {
                if (actual->kind == T2_TYPE_PACK_EXPANSION) {
                        return subtype_relation(
                                context,
                                actual->children[0],
                                expected->children[0],
                                progress + 1
                        );
                }
                if (actual->kind == T2_TYPE_PACK) {
                        T2Relation relation = T2_RELATION_YES;
                        size_t count = (size_t)actual->payload;
                        for (size_t i = 0; i < count; ++i) {
                                relation = combine_all(
                                        relation,
                                        subtype_relation(
                                                context,
                                                actual->children[i],
                                                expected->children[0],
                                                progress + 1
                                        )
                                );
                                if (relation == T2_RELATION_NO) return relation;
                        }
                        return combine_all(
                                relation,
                                pack_subtype(
                                        context,
                                        get_node(
                                                context->universe,
                                                actual->children[count]
                                        ),
                                        expected,
                                        progress + 1
                                )
                        );
                }
        }
        if (actual->kind == T2_TYPE_PACK_EXPANSION) {
                if (
                        expected->kind == T2_TYPE_META
                     || expected->kind == T2_TYPE_VARIABLE
                ) return T2_RELATION_DEFERRED;
                return T2_RELATION_NO;
        }
        if (actual->kind != T2_TYPE_PACK || expected->kind != T2_TYPE_PACK) {
                if (
                        actual->kind == T2_TYPE_META
                     || expected->kind == T2_TYPE_META
                     || actual->kind == T2_TYPE_VARIABLE
                     || expected->kind == T2_TYPE_VARIABLE
                ) return T2_RELATION_DEFERRED;
                return T2_RELATION_NO;
        }
        if (actual->payload != expected->payload) return T2_RELATION_NO;
        T2Relation relation = T2_RELATION_YES;
        for (size_t i = 0; i < actual->arity; ++i) {
                relation = combine_all(
                        relation,
                        subtype_relation(
                                context,
                                actual->children[i],
                                expected->children[i],
                                progress + 1
                        )
                );
        }
        return relation;
}

static T2Relation
tuple_remainder_subtype(
        T2RelationContext *context,
        T2Node const *tuple,
        size_t offset,
        T2Node const *expected,
        unsigned progress
)
{
        size_t remaining = tuple->arity - offset;
        if (expected->kind == T2_TYPE_PACK_ANY) return T2_RELATION_YES;
        if (expected->kind == T2_TYPE_PACK_EMPTY) {
                return remaining == 0 ? T2_RELATION_YES : T2_RELATION_NO;
        }
        if (expected->kind == T2_TYPE_PACK_EXPANSION) {
                T2Relation relation = T2_RELATION_YES;
                for (size_t i = offset; i < tuple->arity; ++i) {
                        relation = combine_all(
                                relation,
                                subtype_relation(
                                        context,
                                        tuple->children[i],
                                        expected->children[0],
                                        progress + 1
                                )
                        );
                }
                return relation;
        }
        if (
                expected->kind == T2_TYPE_META
             || expected->kind == T2_TYPE_VARIABLE
        ) return T2_RELATION_DEFERRED;
        if (expected->kind != T2_TYPE_PACK) return T2_RELATION_NO;

        size_t prefix = (size_t)expected->payload;
        if (remaining < prefix) return T2_RELATION_NO;
        T2Relation relation = T2_RELATION_YES;
        for (size_t i = 0; i < prefix; ++i) {
                relation = combine_all(
                        relation,
                        subtype_relation(
                                context,
                                tuple->children[offset + i],
                                expected->children[i],
                                progress + 1
                        )
                );
        }
        return combine_all(
                relation,
                tuple_remainder_subtype(
                        context,
                        tuple,
                        offset + prefix,
                        get_node(context->universe, expected->children[prefix]),
                        progress + 1
                )
        );
}

static T2Relation
tuple_subtype_variadic(
        T2RelationContext *context,
        T2Node const *actual,
        T2Node const *expected,
        unsigned progress
)
{
        size_t prefix = (size_t)expected->payload;
        if (actual->arity < prefix) return T2_RELATION_NO;
        T2Relation relation = T2_RELATION_YES;
        for (size_t i = 0; i < prefix; ++i) {
                relation = combine_all(
                        relation,
                        subtype_relation(
                                context,
                                actual->children[i],
                                expected->children[i],
                                progress + 1
                        )
                );
        }
        return combine_all(
                relation,
                tuple_remainder_subtype(
                        context,
                        actual,
                        prefix,
                        get_node(context->universe, expected->children[prefix]),
                        progress + 1
                )
        );
}

static T2Relation
subtype_compute(
        T2RelationContext *context,
        T2Type subtype,
        T2Type supertype,
        unsigned progress
)
{
        T2Universe const *universe = context->universe;
        T2Node const *a = get_node(universe, subtype);
        T2Node const *b = get_node(universe, supertype);
        if (a == NULL || b == NULL) return T2_RELATION_NO;

        if (a->kind == T2_TYPE_ERROR || b->kind == T2_TYPE_ERROR) return T2_RELATION_YES;
        if (a->kind == T2_TYPE_NEVER) return T2_RELATION_YES;
        if (b->kind == T2_TYPE_ANY || b->kind == T2_TYPE_UNKNOWN) return T2_RELATION_YES;
        if (a->kind == T2_TYPE_UNKNOWN) return T2_RELATION_NO;
        if (a->kind == T2_TYPE_DYNAMIC) {
                return b->kind == T2_TYPE_DYNAMIC ? T2_RELATION_YES : T2_RELATION_NO;
        }
        if (b->kind == T2_TYPE_OBJECT && object_value_kind(a->kind)) {
                return T2_RELATION_YES;
        }

        if (a->kind == T2_TYPE_UNION) {
                T2Relation relation = T2_RELATION_YES;
                for (size_t i = 0; i < a->arity; ++i) {
                        relation = combine_all(
                                relation,
                                subtype_relation(context, a->children[i], supertype, progress)
                        );
                        if (relation == T2_RELATION_NO) break;
                }
                return relation;
        }
        if (b->kind == T2_TYPE_UNION) {
                T2Relation relation = T2_RELATION_NO;
                for (size_t i = 0; i < b->arity; ++i) {
                        relation = combine_any(
                                relation,
                                subtype_relation(context, subtype, b->children[i], progress)
                        );
                        if (relation == T2_RELATION_YES) break;
                }
                return relation;
        }
        if (b->kind == T2_TYPE_INTERSECTION) {
                T2Relation relation = T2_RELATION_YES;
                for (size_t i = 0; i < b->arity; ++i) {
                        relation = combine_all(
                                relation,
                                subtype_relation(context, subtype, b->children[i], progress)
                        );
                        if (relation == T2_RELATION_NO) break;
                }
                return relation;
        }
        if (b->kind == T2_TYPE_OVERLOAD) {
                T2Relation relation = T2_RELATION_YES;
                for (size_t i = 0; i < b->arity; ++i) {
                        relation = combine_all(
                                relation,
                                subtype_relation(context, subtype, b->children[i], progress)
                        );
                }
                return relation;
        }
        if (a->kind == T2_TYPE_INTERSECTION) {
                T2Relation relation = T2_RELATION_NO;
                for (size_t i = 0; i < a->arity; ++i) {
                        relation = combine_any(
                                relation,
                                subtype_relation(context, a->children[i], supertype, progress)
                        );
                        if (relation == T2_RELATION_YES) break;
                }
                return relation;
        }
        if (a->kind == T2_TYPE_OVERLOAD) {
                T2Relation relation = T2_RELATION_NO;
                for (size_t i = 0; i < a->arity; ++i) {
                        relation = combine_any(
                                relation,
                                subtype_relation(context, a->children[i], supertype, progress)
                        );
                        if (relation == T2_RELATION_YES) break;
                }
                return relation;
        }

        /* Set structure must be considered before treating variables as
         * opaque.  This proves tautologies such as T <: T | nil while still
         * retaining genuinely undecidable relations such as nil <: T. */
        if (a->kind == T2_TYPE_META || b->kind == T2_TYPE_META) {
                return T2_RELATION_DEFERRED;
        }
        if (a->kind == T2_TYPE_VARIABLE || b->kind == T2_TYPE_VARIABLE) {
                /* Quantified and rigid variables are intentionally opaque here.
                 * Distinct variables are not interchangeable, but a relation
                 * involving one may be a scheme predicate that can only be
                 * decided after instantiation. */
                return T2_RELATION_DEFERRED;
        }

        /* A native computed type is an immutable, memoizable promise.  Until
         * the single-evaluation broker supplies its result, no strict subtype
         * fact beyond canonical identity is justified. */
        if (a->kind == T2_TYPE_COMPUTED || b->kind == T2_TYPE_COMPUTED) {
                return T2_RELATION_DEFERRED;
        }

        if (a->kind == T2_TYPE_REFINEMENT) {
                if (a->arity != 2) return T2_RELATION_NO;
                if (b->kind == T2_TYPE_REFINEMENT) {
                        if (b->arity != 2) return T2_RELATION_NO;
                        return combine_all(
                                subtype_relation(
                                        context,
                                        a->children[0],
                                        b->children[0],
                                        progress + 1
                                ),
                                subtype_relation(
                                        context,
                                        a->children[1],
                                        b->children[1],
                                        progress + 1
                                )
                        );
                }
                return subtype_relation(
                        context,
                        a->children[0],
                        supertype,
                        progress + 1
                );
        }
        if (b->kind == T2_TYPE_REFINEMENT) return T2_RELATION_NO;

        if (a->kind == T2_TYPE_LITERAL_BOOL && b->kind == T2_TYPE_BOOL) {
                return T2_RELATION_YES;
        }
        if (a->kind == T2_TYPE_LITERAL_INT && b->kind == T2_TYPE_INT) {
                return T2_RELATION_YES;
        }
        if (a->kind == T2_TYPE_LITERAL_INT && b->kind == T2_TYPE_INT_RANGE) {
                return literal_in_range(universe, a, b);
        }
        if (a->kind == T2_TYPE_INT_RANGE && b->kind == T2_TYPE_INT) {
                return T2_RELATION_YES;
        }
        if (a->kind == T2_TYPE_INT_RANGE && b->kind == T2_TYPE_INT_RANGE) {
                return range_subtype_range(universe, a, b);
        }
        if (a->kind == T2_TYPE_LITERAL_STRING && b->kind == T2_TYPE_STRING) {
                return T2_RELATION_YES;
        }

        if (
                a->kind == b->kind
             && (
                        a->kind == T2_TYPE_PACK_FOLD_UNION
                     || a->kind == T2_TYPE_PACK_FOLD_INTERSECTION
                )
        ) return subtype_relation(
                context,
                a->children[0],
                b->children[0],
                progress + 1
        );

        if (a->kind == T2_TYPE_NOMINAL && b->kind == T2_TYPE_NOMINAL) {
                if (a->payload != b->payload || a->arity != b->arity) {
                        T2AppliedNominal const *applied = find_applied_nominal(
                                universe,
                                subtype
                        );
                        if (applied == NULL) return T2_RELATION_NO;
                        T2Relation inherited = T2_RELATION_NO;
                        for (size_t i = 0; i < applied->supertype_count; ++i) {
                                inherited = combine_any(
                                        inherited,
                                        subtype_relation(
                                                context,
                                                applied->supertypes[i],
                                                supertype,
                                                progress + 1
                                        )
                                );
                                if (inherited == T2_RELATION_YES) break;
                        }
                        return inherited;
                }
                T2NominalInfo const *info = find_nominal(universe, a->payload);
                T2Relation relation = T2_RELATION_YES;
                for (size_t i = 0; i < a->arity; ++i) {
                        T2Variance variance = info == NULL ? T2_INVARIANT : info->variance[i];
                        T2Relation item;
                        if (variance == T2_COVARIANT) {
                                item = subtype_relation(
                                        context,
                                        a->children[i],
                                        b->children[i],
                                        progress + 1
                                );
                        } else if (variance == T2_CONTRAVARIANT) {
                                item = subtype_relation(
                                        context,
                                        b->children[i],
                                        a->children[i],
                                        progress + 1
                                );
                        } else {
                                item = combine_all(
                                        subtype_relation(
                                                context,
                                                a->children[i],
                                                b->children[i],
                                                progress + 1
                                        ),
                                        subtype_relation(
                                                context,
                                                b->children[i],
                                                a->children[i],
                                                progress + 1
                                        )
                                );
                        }
                        relation = combine_all(relation, item);
                }
                return relation;
        }
        if (
                a->kind == T2_TYPE_TYPE_VALUE
             && b->kind == T2_TYPE_TYPE_VALUE
        ) {
                return combine_all(
                        subtype_relation(
                                context,
                                a->children[0],
                                b->children[0],
                                progress + 1
                        ),
                        subtype_relation(
                                context,
                                a->children[1],
                                b->children[1],
                                progress + 1
                        )
                );
        }

        if (a->kind == T2_TYPE_TUPLE && b->kind == T2_TYPE_TUPLE) {
                if (a->arity != b->arity) return T2_RELATION_NO;
                T2Relation relation = T2_RELATION_YES;
                for (size_t i = 0; i < a->arity; ++i) {
                        relation = combine_all(
                                relation,
                                subtype_relation(
                                        context,
                                        a->children[i],
                                        b->children[i],
                                        progress + 1
                                )
                        );
                }
                return relation;
        }
        if (a->kind == T2_TYPE_TUPLE && b->kind == T2_TYPE_VARIADIC_TUPLE) {
                return tuple_subtype_variadic(context, a, b, progress);
        }
        if (
                a->kind == T2_TYPE_VARIADIC_TUPLE
             && b->kind == T2_TYPE_VARIADIC_TUPLE
        ) {
                size_t actual_prefix = (size_t)a->payload;
                size_t expected_prefix = (size_t)b->payload;
                if (actual_prefix != expected_prefix) return T2_RELATION_NO;
                T2Relation relation = T2_RELATION_YES;
                for (size_t i = 0; i < actual_prefix; ++i) {
                        relation = combine_all(
                                relation,
                                subtype_relation(
                                        context,
                                        a->children[i],
                                        b->children[i],
                                        progress + 1
                                )
                        );
                }
                return combine_all(
                        relation,
                        subtype_relation(
                                context,
                                a->children[actual_prefix],
                                b->children[expected_prefix],
                                progress + 1
                        )
                );
        }
        if (a->kind == T2_TYPE_RECORD && b->kind == T2_TYPE_RECORD) {
                return record_subtype(context, a, b, progress);
        }
        if (a->kind == T2_TYPE_ROW && b->kind == T2_TYPE_ROW) {
                return row_subtype(context, a, b, progress);
        }
        if (a->kind == T2_TYPE_FUNCTION && b->kind == T2_TYPE_FUNCTION) {
                return function_subtype(context, a, b, progress);
        }
        if (
                a->kind == T2_TYPE_PACK
             || a->kind == T2_TYPE_PACK_EMPTY
             || a->kind == T2_TYPE_PACK_ANY
             || a->kind == T2_TYPE_PACK_EXPANSION
             || b->kind == T2_TYPE_PACK
             || b->kind == T2_TYPE_PACK_EMPTY
             || b->kind == T2_TYPE_PACK_ANY
             || b->kind == T2_TYPE_PACK_EXPANSION
        ) return pack_subtype(context, a, b, progress);
        if (
                a->kind == T2_TYPE_ROW
             || a->kind == T2_TYPE_ROW_EMPTY
             || a->kind == T2_TYPE_ROW_ANY
        ) {
                return b->kind == T2_TYPE_ROW_ANY || a->kind == b->kind
                     ? T2_RELATION_YES
                     : T2_RELATION_NO;
        }
        return T2_RELATION_NO;
}

static T2Relation
subtype_relation(
        T2RelationContext *context,
        T2Type subtype,
        T2Type supertype,
        unsigned progress
)
{
        subtype = t2_type_resolve_computed(context->universe, subtype);
        supertype = t2_type_resolve_computed(context->universe, supertype);
        if (subtype == T2_TYPE_INVALID || supertype == T2_TYPE_INVALID) {
                return T2_RELATION_COMPLEXITY;
        }
        if (subtype == supertype && subtype != T2_TYPE_INVALID) return T2_RELATION_YES;
        if (++context->steps > context->step_limit) return T2_RELATION_COMPLEXITY;

        for (;;) {
                bool changed = false;
                T2Type unfolded = unfold_recursive_head(context->universe, subtype, &changed);
                if (unfolded == T2_TYPE_INVALID) return T2_RELATION_NO;
                subtype = unfolded;
                if (!changed) break;
                if (++context->steps > context->step_limit) return T2_RELATION_COMPLEXITY;
        }
        for (;;) {
                bool changed = false;
                T2Type unfolded = unfold_recursive_head(context->universe, supertype, &changed);
                if (unfolded == T2_TYPE_INVALID) return T2_RELATION_NO;
                supertype = unfolded;
                if (!changed) break;
                if (++context->steps > context->step_limit) return T2_RELATION_COMPLEXITY;
        }
        if (subtype == supertype) return T2_RELATION_YES;

        for (size_t i = 0; i < context->pair_count; ++i) {
                T2RelationPair const *pair = &context->pairs[i];
                if (pair->subtype != subtype || pair->supertype != supertype) continue;
                if (pair->state == T2_PAIR_COMPLETE) return pair->result;
                return progress > pair->progress
                     ? T2_RELATION_YES
                     : T2_RELATION_COMPLEXITY;
        }

        if (!reserve_array(
                (void **)&context->pairs,
                &context->pair_capacity,
                context->pair_count + 1,
                sizeof *context->pairs
        )) {
                context->failed = true;
                return T2_RELATION_COMPLEXITY;
        }
        size_t pair_index = context->pair_count++;
        context->pairs[pair_index] = (T2RelationPair) {
                .subtype = subtype,
                .supertype = supertype,
                .progress = progress,
                .state = T2_PAIR_IN_PROGRESS,
                .result = T2_RELATION_COMPLEXITY
        };
        T2Relation result = subtype_compute(context, subtype, supertype, progress);
        context->pairs[pair_index].state = T2_PAIR_COMPLETE;
        context->pairs[pair_index].result = result;
        return result;
}

T2Relation
t2_subtype(T2Universe const *universe, T2Type subtype, T2Type supertype)
{
        T2RelationContext context = {
                .universe = universe,
                .step_limit = 1000000
        };
        T2Relation relation = subtype_relation(&context, subtype, supertype, 0);
        free(context.pairs);
        return context.failed ? T2_RELATION_COMPLEXITY : relation;
}

static T2Relation
combine_all(T2Relation aggregate, T2Relation next)
{
        if (aggregate == T2_RELATION_NO || next == T2_RELATION_NO) {
                return T2_RELATION_NO;
        }
        if (aggregate == T2_RELATION_COMPLEXITY || next == T2_RELATION_COMPLEXITY) {
                return T2_RELATION_COMPLEXITY;
        }
        if (aggregate == T2_RELATION_DEFERRED || next == T2_RELATION_DEFERRED) {
                return T2_RELATION_DEFERRED;
        }
        return T2_RELATION_YES;
}

static T2Relation
combine_any(T2Relation aggregate, T2Relation next)
{
        if (aggregate == T2_RELATION_YES || next == T2_RELATION_YES) {
                return T2_RELATION_YES;
        }
        if (aggregate == T2_RELATION_DEFERRED || next == T2_RELATION_DEFERRED) {
                return T2_RELATION_DEFERRED;
        }
        if (aggregate == T2_RELATION_COMPLEXITY || next == T2_RELATION_COMPLEXITY) {
                return T2_RELATION_COMPLEXITY;
        }
        return T2_RELATION_NO;
}

#if 0
static T2Relation
subtype_x(
        T2Universe const *universe,
        T2Type subtype,
        T2Type supertype,
        unsigned depth
)
{
        if (subtype == supertype && subtype != T2_TYPE_INVALID) {
                return T2_RELATION_YES;
        }
        if (depth > T2_RELATION_DEPTH_LIMIT) {
                return T2_RELATION_COMPLEXITY;
        }

        T2Node const *a = get_node(universe, subtype);
        T2Node const *b = get_node(universe, supertype);
        if (a == NULL || b == NULL) {
                return T2_RELATION_NO;
        }

        if (a->kind == T2_TYPE_ERROR || b->kind == T2_TYPE_ERROR) {
                return T2_RELATION_YES;
        }
        if (a->kind == T2_TYPE_NEVER) {
                return T2_RELATION_YES;
        }
        if (b->kind == T2_TYPE_ANY || b->kind == T2_TYPE_UNKNOWN) {
                return T2_RELATION_YES;
        }
        if (a->kind == T2_TYPE_UNKNOWN) {
                return T2_RELATION_NO;
        }
        if (a->kind == T2_TYPE_DYNAMIC) {
                return b->kind == T2_TYPE_DYNAMIC ? T2_RELATION_YES : T2_RELATION_NO;
        }
        if (a->kind == T2_TYPE_META || b->kind == T2_TYPE_META) {
                return T2_RELATION_DEFERRED;
        }
        if (a->kind == T2_TYPE_VARIABLE || b->kind == T2_TYPE_VARIABLE) {
                return T2_RELATION_NO;
        }

        if (b->kind == T2_TYPE_OBJECT && object_value_kind(a->kind)) {
                return T2_RELATION_YES;
        }

        if (a->kind == T2_TYPE_UNION) {
                T2Relation relation = T2_RELATION_YES;
                for (size_t i = 0; i < a->arity; ++i) {
                        relation = combine_all(
                                relation,
                                subtype_x(universe, a->children[i], supertype, depth + 1)
                        );
                        if (relation == T2_RELATION_NO) break;
                }
                return relation;
        }
        if (b->kind == T2_TYPE_UNION) {
                T2Relation relation = T2_RELATION_NO;
                for (size_t i = 0; i < b->arity; ++i) {
                        relation = combine_any(
                                relation,
                                subtype_x(universe, subtype, b->children[i], depth + 1)
                        );
                        if (relation == T2_RELATION_YES) break;
                }
                return relation;
        }
        if (b->kind == T2_TYPE_INTERSECTION) {
                T2Relation relation = T2_RELATION_YES;
                for (size_t i = 0; i < b->arity; ++i) {
                        relation = combine_all(
                                relation,
                                subtype_x(universe, subtype, b->children[i], depth + 1)
                        );
                        if (relation == T2_RELATION_NO) break;
                }
                return relation;
        }
        if (a->kind == T2_TYPE_INTERSECTION) {
                T2Relation relation = T2_RELATION_NO;
                for (size_t i = 0; i < a->arity; ++i) {
                        relation = combine_any(
                                relation,
                                subtype_x(universe, a->children[i], supertype, depth + 1)
                        );
                        if (relation == T2_RELATION_YES) break;
                }
                return relation;
        }

        if (
                a->kind == T2_TYPE_LITERAL_BOOL
             && b->kind == T2_TYPE_BOOL
        ) return T2_RELATION_YES;
        if (
                a->kind == T2_TYPE_LITERAL_INT
             && b->kind == T2_TYPE_INT
        ) return T2_RELATION_YES;
        if (
                a->kind == T2_TYPE_LITERAL_STRING
             && b->kind == T2_TYPE_STRING
        ) return T2_RELATION_YES;

        if (a->kind == T2_TYPE_NOMINAL && b->kind == T2_TYPE_NOMINAL) {
                if (a->payload != b->payload || a->arity != b->arity) {
                        return T2_RELATION_NO;
                }
                T2NominalInfo const *info = find_nominal(universe, a->payload);
                T2Relation relation = T2_RELATION_YES;
                for (size_t i = 0; i < a->arity; ++i) {
                        T2Variance variance = info == NULL
                                            ? T2_INVARIANT
                                            : info->variance[i];
                        T2Relation item;
                        if (variance == T2_COVARIANT) {
                                item = subtype_x(
                                        universe,
                                        a->children[i],
                                        b->children[i],
                                        depth + 1
                                );
                        } else if (variance == T2_CONTRAVARIANT) {
                                item = subtype_x(
                                        universe,
                                        b->children[i],
                                        a->children[i],
                                        depth + 1
                                );
                        } else {
                                item = a->children[i] == b->children[i]
                                     ? T2_RELATION_YES
                                     : T2_RELATION_NO;
                        }
                        relation = combine_all(relation, item);
                }
                return relation;
        }

        if (a->kind == T2_TYPE_TUPLE && b->kind == T2_TYPE_TUPLE) {
                if (a->arity != b->arity) return T2_RELATION_NO;
                T2Relation relation = T2_RELATION_YES;
                for (size_t i = 0; i < a->arity; ++i) {
                        relation = combine_all(
                                relation,
                                subtype_x(
                                        universe,
                                        a->children[i],
                                        b->children[i],
                                        depth + 1
                                )
                        );
                }
                return relation;
        }

        if (a->kind == T2_TYPE_FUNCTION && b->kind == T2_TYPE_FUNCTION) {
                if (a->arity != b->arity) return T2_RELATION_NO;
                T2Relation relation = T2_RELATION_YES;
                size_t parameter_count = a->arity - 1;
                for (size_t i = 0; i < parameter_count; ++i) {
                        relation = combine_all(
                                relation,
                                subtype_x(
                                        universe,
                                        b->children[i],
                                        a->children[i],
                                        depth + 1
                                )
                        );
                }
                return combine_all(
                        relation,
                        subtype_x(
                                universe,
                                a->children[parameter_count],
                                b->children[parameter_count],
                                depth + 1
                        )
                );
        }

        return T2_RELATION_NO;
}

T2Relation
t2_subtype(T2Universe const *universe, T2Type subtype, T2Type supertype)
{
        return subtype_x(universe, subtype, supertype, 0);
}
#endif

static bool
definitely_disjoint(T2Universe const *universe, T2Type left, T2Type right)
{
        left = t2_type_resolve_computed(universe, left);
        right = t2_type_resolve_computed(universe, right);
        T2Node const *a = get_node(universe, left);
        T2Node const *b = get_node(universe, right);
        if (a == NULL || b == NULL) return false;

        if (a->kind == T2_TYPE_NEVER || b->kind == T2_TYPE_NEVER) return true;
        if (
                a->kind == T2_TYPE_ANY
             || a->kind == T2_TYPE_UNKNOWN
             || a->kind == T2_TYPE_DYNAMIC
             || a->kind == T2_TYPE_ERROR
             || b->kind == T2_TYPE_ANY
             || b->kind == T2_TYPE_UNKNOWN
             || b->kind == T2_TYPE_DYNAMIC
             || b->kind == T2_TYPE_ERROR
        ) return false;

        if (a->kind == T2_TYPE_COMPUTED || b->kind == T2_TYPE_COMPUTED) {
                return false;
        }
        if (a->kind == T2_TYPE_REFINEMENT && a->arity == 2) {
                if (b->kind == T2_TYPE_REFINEMENT && b->arity == 2) {
                        return definitely_disjoint(
                                universe,
                                a->children[0],
                                b->children[0]
                        ) || (
                                a->children[0] == b->children[0]
                             && definitely_disjoint(
                                    universe,
                                    a->children[1],
                                    b->children[1]
                                )
                        );
                }
                return definitely_disjoint(universe, a->children[0], right);
        }
        if (b->kind == T2_TYPE_REFINEMENT && b->arity == 2) {
                return definitely_disjoint(universe, left, b->children[0]);
        }

        if (
                a->kind == T2_TYPE_LITERAL_INT
             && b->kind == T2_TYPE_LITERAL_INT
        ) return a->payload != b->payload;
        if (
                a->kind == T2_TYPE_LITERAL_BOOL
             && b->kind == T2_TYPE_LITERAL_BOOL
        ) return a->payload != b->payload;
        if (
                a->kind == T2_TYPE_LITERAL_STRING
             && b->kind == T2_TYPE_LITERAL_STRING
        ) return strcmp(a->text, b->text) != 0;
        if (a->kind == T2_TYPE_LITERAL_INT && b->kind == T2_TYPE_INT_RANGE) {
                return literal_in_range(universe, a, b) == T2_RELATION_NO;
        }
        if (a->kind == T2_TYPE_INT_RANGE && b->kind == T2_TYPE_LITERAL_INT) {
                return literal_in_range(universe, b, a) == T2_RELATION_NO;
        }
        if (a->kind == T2_TYPE_INT_RANGE && b->kind == T2_TYPE_INT_RANGE) {
                T2Node const *a_upper = range_bound(universe, a, false);
                T2Node const *b_lower = range_bound(universe, b, true);
                if (
                        a_upper != NULL
                     && b_lower != NULL
                     && a_upper->kind == T2_TYPE_LITERAL_INT
                     && b_lower->kind == T2_TYPE_LITERAL_INT
                ) {
                        int64_t high = (int64_t)a_upper->payload;
                        int64_t low = (int64_t)b_lower->payload;
                        if ((a->payload & T2_RANGE_UPPER_INCLUSIVE) != 0
                                ? high < low
                                : high <= low) return true;
                }
                T2Node const *b_upper = range_bound(universe, b, false);
                T2Node const *a_lower = range_bound(universe, a, true);
                if (
                        b_upper != NULL
                     && a_lower != NULL
                     && b_upper->kind == T2_TYPE_LITERAL_INT
                     && a_lower->kind == T2_TYPE_LITERAL_INT
                ) {
                        int64_t high = (int64_t)b_upper->payload;
                        int64_t low = (int64_t)a_lower->payload;
                        if ((b->payload & T2_RANGE_UPPER_INCLUSIVE) != 0
                                ? high < low
                                : high <= low) return true;
                }
        }

        T2TypeKind ak = literal_base(a->kind);
        T2TypeKind bk = literal_base(b->kind);
        bool a_atomic = ak == T2_TYPE_NIL
                     || ak == T2_TYPE_BOOL
                     || ak == T2_TYPE_INT
                     || ak == T2_TYPE_FLOAT
                     || ak == T2_TYPE_STRING
                     || ak == T2_TYPE_FUNCTION
                     || ak == T2_TYPE_TUPLE;
        bool b_atomic = bk == T2_TYPE_NIL
                     || bk == T2_TYPE_BOOL
                     || bk == T2_TYPE_INT
                     || bk == T2_TYPE_FLOAT
                     || bk == T2_TYPE_STRING
                     || bk == T2_TYPE_FUNCTION
                     || bk == T2_TYPE_TUPLE;

        if (ak == T2_TYPE_NOMINAL && b_atomic) return true;
        if (bk == T2_TYPE_NOMINAL && a_atomic) return true;
        return a_atomic && b_atomic && ak != bk;
}

static bool
meet_presence(T2Presence left, T2Presence right, T2Presence *result)
{
        if (left == T2_PRESENCE_UNKNOWN) {
                *result = right;
                return true;
        }
        if (right == T2_PRESENCE_UNKNOWN) {
                *result = left;
                return true;
        }
        if (left == right) {
                *result = left;
                return true;
        }
        if (
                (left == T2_PRESENCE_REQUIRED && right == T2_PRESENCE_ABSENT)
             || (right == T2_PRESENCE_REQUIRED && left == T2_PRESENCE_ABSENT)
        ) return false;
        if (left == T2_PRESENCE_REQUIRED || right == T2_PRESENCE_REQUIRED) {
                *result = T2_PRESENCE_REQUIRED;
                return true;
        }
        if (left == T2_PRESENCE_ABSENT || right == T2_PRESENCE_ABSENT) {
                *result = T2_PRESENCE_ABSENT;
                return true;
        }
        *result = T2_PRESENCE_OPTIONAL;
        return true;
}

static T2Type
record_meet(T2Universe *universe, T2Type left, T2Type right)
{
        T2Node const *a = get_node(universe, left);
        T2Node const *b = get_node(universe, right);
        if (
                a == NULL
             || b == NULL
             || a->kind != T2_TYPE_RECORD
             || b->kind != T2_TYPE_RECORD
        ) return T2_TYPE_INVALID;

        size_t a_count = a->arity - 1;
        size_t b_count = b->arity - 1;
        T2FieldSpec *fields = calloc(a_count + b_count, sizeof *fields);
        if (a_count + b_count != 0 && fields == NULL) {
                universe->failed = true;
                return T2_TYPE_INVALID;
        }
        size_t ai = 0;
        size_t bi = 0;
        size_t count = 0;
        bool a_exact = (T2RecordExactness)a->payload == T2_RECORD_EXACT;
        bool b_exact = (T2RecordExactness)b->payload == T2_RECORD_EXACT;
        T2Type never = t2_primitive(universe, T2_TYPE_NEVER);

        while (ai < a_count || bi < b_count) {
                T2Node const *af = ai < a_count
                                 ? get_node(universe, a->children[ai])
                                 : NULL;
                T2Node const *bf = bi < b_count
                                 ? get_node(universe, b->children[bi])
                                 : NULL;
                int comparison = af == NULL ? 1 : bf == NULL ? -1 : strcmp(af->text, bf->text);
                T2Node const *primary = comparison <= 0 ? af : bf;
                T2Node const *other = comparison == 0 ? bf : NULL;
                bool other_exact = comparison < 0 ? b_exact : comparison > 0 ? a_exact : false;

                T2Presence primary_presence = (T2Presence)(
                        primary->payload & T2_FIELD_PRESENCE_MASK
                );
                T2Presence other_presence = other == NULL
                                          ? (other_exact
                                                ? T2_PRESENCE_ABSENT
                                                : T2_PRESENCE_UNKNOWN)
                                          : (T2Presence)(
                                                other->payload & T2_FIELD_PRESENCE_MASK
                                            );
                T2Presence presence;
                if (!meet_presence(primary_presence, other_presence, &presence)) {
                        free(fields);
                        return never;
                }

                bool primary_writable = (primary->payload & T2_FIELD_WRITABLE_BIT) != 0;
                bool other_writable = other != NULL
                                   && (other->payload & T2_FIELD_WRITABLE_BIT) != 0;
                T2Type field_type = primary->children[0];
                if (other != NULL && presence != T2_PRESENCE_ABSENT) {
                        if (primary_writable && other_writable) {
                                if (
                                        t2_subtype(universe, field_type, other->children[0])
                                            != T2_RELATION_YES
                                     || t2_subtype(universe, other->children[0], field_type)
                                            != T2_RELATION_YES
                                ) {
                                        free(fields);
                                        return never;
                                }
                        } else if (primary_writable || other_writable) {
                                T2Type writable = primary_writable
                                                ? field_type
                                                : other->children[0];
                                T2Type readonly = primary_writable
                                                ? other->children[0]
                                                : field_type;
                                if (t2_subtype(universe, writable, readonly) != T2_RELATION_YES) {
                                        free(fields);
                                        return never;
                                }
                                field_type = writable;
                        } else {
                                field_type = t2_meet(
                                        universe,
                                        field_type,
                                        other->children[0]
                                );
                                if (field_type == never) {
                                        if (presence == T2_PRESENCE_REQUIRED) {
                                                free(fields);
                                                return never;
                                        }
                                        presence = T2_PRESENCE_ABSENT;
                                }
                        }
                }

                fields[count++] = (T2FieldSpec) {
                        .name = primary->text,
                        .type = field_type,
                        .presence = presence,
                        .capability = primary_writable || other_writable
                                    ? T2_FIELD_WRITABLE
                                    : T2_FIELD_READONLY
                };
                if (comparison <= 0) ai += 1;
                if (comparison >= 0) bi += 1;
        }

        T2RecordExactness exactness = a_exact || b_exact
                                    ? T2_RECORD_EXACT
                                    : T2_RECORD_OPEN;
        T2Type tail = T2_TYPE_INVALID;
        if (exactness == T2_RECORD_OPEN) {
                T2Type a_tail = a->children[a_count];
                T2Type b_tail = b->children[b_count];
                T2Node const *an = get_node(universe, a_tail);
                T2Node const *bn = get_node(universe, b_tail);
                if (a_tail == b_tail) tail = a_tail;
                else if (an->kind == T2_TYPE_ROW_ANY) tail = b_tail;
                else if (bn->kind == T2_TYPE_ROW_ANY) tail = a_tail;
                else tail = t2_intersection(
                        universe,
                        (T2Type[]){ a_tail, b_tail },
                        2
                );
        }
        T2Type result = t2_record(universe, fields, count, tail, exactness);
        free(fields);
        return result;
}

static T2Type
make_set(
        T2Universe *universe,
        T2TypeKind kind,
        T2Type const *types,
        size_t count
)
{
        T2TypeVector arms = {0};
        bool saw_any = false;
        bool saw_unknown = false;
        bool saw_dynamic = false;

        for (size_t i = 0; i < count; ++i) {
                T2Node const *node = get_node(universe, types[i]);
                if (node == NULL) {
                        free(arms.items);
                        return T2_TYPE_INVALID;
                }

                if (node->kind == T2_TYPE_ERROR) {
                        free(arms.items);
                        return t2_primitive(universe, T2_TYPE_ERROR);
                }

                if (kind == T2_TYPE_UNION) {
                        if (node->kind == T2_TYPE_NEVER) continue;
                        if (node->kind == T2_TYPE_UNKNOWN) saw_unknown = true;
                        if (node->kind == T2_TYPE_ANY) saw_any = true;
                        if (node->kind == T2_TYPE_DYNAMIC) {
                                saw_dynamic = true;
                                continue;
                        }
                } else {
                        if (node->kind == T2_TYPE_NEVER) {
                                free(arms.items);
                                return t2_primitive(universe, T2_TYPE_NEVER);
                        }
                        if (node->kind == T2_TYPE_UNKNOWN) {
                                saw_unknown = true;
                                continue;
                        }
                        if (node->kind == T2_TYPE_ANY) {
                                saw_any = true;
                                continue;
                        }
                        if (node->kind == T2_TYPE_DYNAMIC) {
                                saw_dynamic = true;
                                continue;
                        }
                }

                if (!collect_set_arms(universe, kind, types[i], &arms)) {
                        universe->failed = true;
                        goto Fail;
                }
        }

        if (kind == T2_TYPE_UNION && saw_unknown) {
                free(arms.items);
                return t2_primitive(universe, T2_TYPE_UNKNOWN);
        }
        if (kind == T2_TYPE_UNION && saw_any) {
                free(arms.items);
                return t2_primitive(universe, T2_TYPE_ANY);
        }
        if (kind == T2_TYPE_UNION && saw_dynamic) {
                free(arms.items);
                return t2_primitive(universe, T2_TYPE_DYNAMIC);
        }

        for (size_t i = 1; i < arms.count; ++i) {
                T2Type item = arms.items[i];
                size_t j = i;
                while (
                        j != 0
                     && compare_types(universe, item, arms.items[j - 1], 0) < 0
                ) {
                        arms.items[j] = arms.items[j - 1];
                        --j;
                }
                arms.items[j] = item;
        }

        size_t unique = 0;
        for (size_t i = 0; i < arms.count; ++i) {
                if (unique == 0 || arms.items[i] != arms.items[unique - 1]) {
                        arms.items[unique++] = arms.items[i];
                }
        }
        arms.count = unique;

        bool *removed = arms.count == 0 ? NULL : calloc(arms.count, sizeof *removed);
        if (arms.count != 0 && removed == NULL) {
                universe->failed = true;
                goto Fail;
        }

        for (size_t i = 0; i < arms.count; ++i) {
                if (removed[i]) continue;
                for (size_t j = i + 1; j < arms.count; ++j) {
                        if (removed[j]) continue;

                        if (
                                kind == T2_TYPE_INTERSECTION
                             && definitely_disjoint(universe, arms.items[i], arms.items[j])
                        ) {
                                free(removed);
                                free(arms.items);
                                return t2_primitive(universe, T2_TYPE_NEVER);
                        }

                        T2Relation ij = t2_subtype(universe, arms.items[i], arms.items[j]);
                        T2Relation ji = t2_subtype(universe, arms.items[j], arms.items[i]);
                        if (kind == T2_TYPE_UNION) {
                                if (ij == T2_RELATION_YES) removed[i] = true;
                                else if (ji == T2_RELATION_YES) removed[j] = true;
                        } else {
                                if (ij == T2_RELATION_YES) removed[j] = true;
                                else if (ji == T2_RELATION_YES) removed[i] = true;
                        }
                        if (removed[i]) break;
                }
        }

        size_t kept = 0;
        for (size_t i = 0; i < arms.count; ++i) {
                if (!removed[i]) arms.items[kept++] = arms.items[i];
        }
        free(removed);
        arms.count = kept;

        if (arms.count == 0) {
                free(arms.items);
                if (kind == T2_TYPE_UNION) {
                        return t2_primitive(universe, T2_TYPE_NEVER);
                }
                return t2_primitive(
                        universe,
                        saw_dynamic ? T2_TYPE_DYNAMIC
                                    : saw_unknown ? T2_TYPE_UNKNOWN : T2_TYPE_ANY
                );
        }
        if (arms.count == 1) {
                T2Type only = arms.items[0];
                free(arms.items);
                return only;
        }

        T2Type result = intern_type(
                universe,
                kind,
                T2_VARIABLE_FLEXIBLE,
                0,
                NULL,
                arms.items,
                arms.count
        );
        free(arms.items);
        return result;

Fail:
        free(arms.items);
        return T2_TYPE_INVALID;
}

T2Type
t2_union(T2Universe *universe, T2Type const *arms, size_t count)
{
        return make_set(universe, T2_TYPE_UNION, arms, count);
}

T2Type
t2_intersection(T2Universe *universe, T2Type const *arms, size_t count)
{
        if (count != 0) {
                bool all_records = true;
                for (size_t i = 0; i < count; ++i) {
                        all_records &= t2_type_kind(universe, arms[i]) == T2_TYPE_RECORD;
                }
                if (all_records) {
                        T2Type result = arms[0];
                        for (size_t i = 1; i < count; ++i) {
                                result = record_meet(universe, result, arms[i]);
                                if (
                                        result == T2_TYPE_INVALID
                                     || t2_type_kind(universe, result) == T2_TYPE_NEVER
                                ) break;
                        }
                        return result;
                }
        }
        return make_set(universe, T2_TYPE_INTERSECTION, arms, count);
}

static bool
append_overload_candidates(
        T2Universe *universe,
        T2TypeVector *flat,
        T2Type candidate
)
{
        T2Node const *node = get_node(universe, candidate);
        if (node == NULL) return false;
        if (node->kind != T2_TYPE_OVERLOAD) return push_type(flat, candidate);
        for (size_t i = 0; i < node->arity; ++i) {
                if (!append_overload_candidates(universe, flat, node->children[i])) {
                        return false;
                }
        }
        return true;
}

T2Type
t2_overload(T2Universe *universe, T2Type const *candidates, size_t count)
{
        if (count == 0) return t2_primitive(universe, T2_TYPE_NEVER);
        if (candidates == NULL) return T2_TYPE_INVALID;
        T2TypeVector flat = {0};
        for (size_t i = 0; i < count; ++i) {
                if (get_node(universe, candidates[i]) == NULL) {
                        free(flat.items);
                        return T2_TYPE_INVALID;
                }
                if (!append_overload_candidates(universe, &flat, candidates[i])) {
                        free(flat.items);
                        universe->failed = true;
                        return T2_TYPE_INVALID;
                }
        }
        if (flat.count == 1) {
                T2Type result = flat.items[0];
                free(flat.items);
                return result;
        }
        T2Type result = intern_type(
                universe,
                T2_TYPE_OVERLOAD,
                T2_VARIABLE_FLEXIBLE,
                flat.count,
                NULL,
                flat.items,
                flat.count
        );
        free(flat.items);
        return result;
}

T2Type
t2_join(T2Universe *universe, T2Type left, T2Type right)
{
        left = t2_type_resolve_computed(universe, left);
        right = t2_type_resolve_computed(universe, right);
        if (left == T2_TYPE_INVALID || right == T2_TYPE_INVALID) {
                return T2_TYPE_INVALID;
        }
        if (left == right) return left;
        T2TypeKind lk = t2_type_kind(universe, left);
        T2TypeKind rk = t2_type_kind(universe, right);
        if (lk == T2_TYPE_ERROR || rk == T2_TYPE_ERROR) {
                return t2_primitive(universe, T2_TYPE_ERROR);
        }
        if (lk == T2_TYPE_UNKNOWN || rk == T2_TYPE_UNKNOWN) {
                return t2_primitive(universe, T2_TYPE_UNKNOWN);
        }
        T2Relation lr = t2_subtype(universe, left, right);
        if (lr == T2_RELATION_YES) return right;
        T2Relation rl = t2_subtype(universe, right, left);
        if (rl == T2_RELATION_YES) return left;
        T2Type arms[] = { left, right };
        return t2_union(universe, arms, 2);
}

static T2Type
meet_x(T2Universe *universe, T2Type left, T2Type right, unsigned depth)
{
        left = t2_type_resolve_computed(universe, left);
        right = t2_type_resolve_computed(universe, right);
        if (left == T2_TYPE_INVALID || right == T2_TYPE_INVALID) {
                return T2_TYPE_INVALID;
        }
        if (left == right) return left;
        if (depth > T2_RELATION_DEPTH_LIMIT) {
                T2Type arms[] = { left, right };
                return t2_intersection(universe, arms, 2);
        }

        T2Node const *a = get_node(universe, left);
        T2Node const *b = get_node(universe, right);
        if (a == NULL || b == NULL) return T2_TYPE_INVALID;

        if (a->kind == T2_TYPE_ERROR || b->kind == T2_TYPE_ERROR) {
                return t2_primitive(universe, T2_TYPE_ERROR);
        }

        if (a->kind == T2_TYPE_RECORD && b->kind == T2_TYPE_RECORD) {
                return record_meet(universe, left, right);
        }

        if (
                (a->kind == T2_TYPE_UNKNOWN && b->kind == T2_TYPE_ANY)
             || (a->kind == T2_TYPE_ANY && b->kind == T2_TYPE_UNKNOWN)
        ) {
                return t2_primitive(universe, T2_TYPE_UNKNOWN);
        }

        T2Relation lr = t2_subtype(universe, left, right);
        if (lr == T2_RELATION_YES) return left;
        T2Relation rl = t2_subtype(universe, right, left);
        if (rl == T2_RELATION_YES) return right;

        if (a->kind == T2_TYPE_UNION || b->kind == T2_TYPE_UNION) {
                T2Node const *u = a->kind == T2_TYPE_UNION ? a : b;
                T2Type other = a->kind == T2_TYPE_UNION ? right : left;
                T2TypeVector results = {0};
                T2Type never = t2_primitive(universe, T2_TYPE_NEVER);

                for (size_t i = 0; i < u->arity; ++i) {
                        T2Type item = meet_x(universe, u->children[i], other, depth + 1);
                        if (item == T2_TYPE_INVALID) {
                                free(results.items);
                                return item;
                        }
                        if (item != never && !push_type(&results, item)) {
                                free(results.items);
                                universe->failed = true;
                                return T2_TYPE_INVALID;
                        }
                }

                T2Type result = t2_union(universe, results.items, results.count);
                free(results.items);
                return result;
        }
        if (definitely_disjoint(universe, left, right)) {
                return t2_primitive(universe, T2_TYPE_NEVER);
        }

        T2Type arms[] = { left, right };
        return t2_intersection(universe, arms, 2);
}

T2Type
t2_meet(T2Universe *universe, T2Type left, T2Type right)
{
        return meet_x(universe, left, right, 0);
}

T2Relation
t2_consistent(T2Universe const *universe, T2Type left, T2Type right)
{
        left = t2_type_resolve_computed(universe, left);
        right = t2_type_resolve_computed(universe, right);
        T2Node const *a = get_node(universe, left);
        T2Node const *b = get_node(universe, right);
        if (a == NULL || b == NULL) return T2_RELATION_NO;

        if (
                a->kind == T2_TYPE_DYNAMIC
             || b->kind == T2_TYPE_DYNAMIC
             || a->kind == T2_TYPE_UNKNOWN
             || b->kind == T2_TYPE_UNKNOWN
             || a->kind == T2_TYPE_ERROR
             || b->kind == T2_TYPE_ERROR
        ) return T2_RELATION_YES;

        T2Relation ab = t2_subtype(universe, left, right);
        if (ab == T2_RELATION_YES) return ab;
        T2Relation ba = t2_subtype(universe, right, left);
        if (ba == T2_RELATION_YES) return ba;
        if (ab == T2_RELATION_COMPLEXITY || ba == T2_RELATION_COMPLEXITY) {
                return T2_RELATION_COMPLEXITY;
        }
        if (ab == T2_RELATION_DEFERRED || ba == T2_RELATION_DEFERRED) {
                return T2_RELATION_DEFERRED;
        }
        return definitely_disjoint(universe, left, right)
             ? T2_RELATION_NO
             : T2_RELATION_YES;
}

T2TypeKind
t2_type_kind(T2Universe const *universe, T2Type type)
{
        T2Node const *node = get_node(universe, type);
        return node == NULL ? T2_TYPE_KIND_COUNT : (T2TypeKind)node->kind;
}

T2VariableKind
t2_type_variable_kind(T2Universe const *universe, T2Type type)
{
        T2Node const *node = get_node(universe, type);
        return node == NULL ? T2_VARIABLE_FLEXIBLE : node->variable_kind;
}

size_t
t2_type_arity(T2Universe const *universe, T2Type type)
{
        T2Node const *node = get_node(universe, type);
        return node == NULL ? 0 : node->arity;
}

T2Type
t2_type_child(T2Universe const *universe, T2Type type, size_t index)
{
        T2Node const *node = get_node(universe, type);
        return node == NULL || index >= node->arity
             ? T2_TYPE_INVALID
             : node->children[index];
}

uint64_t
t2_type_payload(T2Universe const *universe, T2Type type)
{
        T2Node const *node = get_node(universe, type);
        return node == NULL ? 0 : node->payload;
}

char const *
t2_type_name(T2Universe const *universe, T2Type type)
{
        T2Node const *node = get_node(universe, type);
        return node == NULL ? NULL : node->text;
}

uint64_t
t2_type_hash(T2Universe const *universe, T2Type type)
{
        T2Node const *node = get_node(universe, type);
        return node == NULL ? 0 : node->hash;
}

bool
t2_type_same(T2Universe const *universe, T2Type left, T2Type right)
{
        return universe != NULL && left != T2_TYPE_INVALID && left == right;
}

static bool
buffer_reserve(T2StringBuffer *buffer, size_t extra)
{
        if (buffer->failed || extra > SIZE_MAX - buffer->count - 1) {
                buffer->failed = true;
                return false;
        }
        size_t needed = buffer->count + extra + 1;
        if (
                !reserve_array(
                        (void **)&buffer->items,
                        &buffer->capacity,
                        needed,
                        sizeof *buffer->items
                )
        ) {
                buffer->failed = true;
                return false;
        }
        return true;
}

static void
buffer_text(T2StringBuffer *buffer, char const *text)
{
        size_t length = strlen(text);
        if (!buffer_reserve(buffer, length)) return;
        memcpy(buffer->items + buffer->count, text, length);
        buffer->count += length;
        buffer->items[buffer->count] = '\0';
}

static void
buffer_format(T2StringBuffer *buffer, char const *format, ...)
{
        va_list ap;
        va_start(ap, format);
        va_list copy;
        va_copy(copy, ap);
        int length = vsnprintf(NULL, 0, format, copy);
        va_end(copy);
        if (length < 0 || !buffer_reserve(buffer, (size_t)length)) {
                va_end(ap);
                return;
        }
        vsnprintf(buffer->items + buffer->count, (size_t)length + 1, format, ap);
        va_end(ap);
        buffer->count += (size_t)length;
}

static char const *
primitive_name(T2TypeKind kind)
{
        static char const *const names[T2_TYPE_KIND_COUNT] = {
                [T2_TYPE_NEVER] = "Never",
                [T2_TYPE_UNKNOWN] = "Unknown",
                [T2_TYPE_DYNAMIC] = "Dynamic",
                [T2_TYPE_ANY] = "Any",
                [T2_TYPE_OBJECT] = "Object",
                [T2_TYPE_ERROR] = "Error",
                [T2_TYPE_NIL] = "nil",
                [T2_TYPE_BOOL] = "Bool",
                [T2_TYPE_INT] = "Int",
                [T2_TYPE_FLOAT] = "Float",
                [T2_TYPE_STRING] = "String",
                [T2_TYPE_ROW_EMPTY] = "{}",
                [T2_TYPE_ROW_ANY] = "{...}",
                [T2_TYPE_PACK_EMPTY] = "[]",
                [T2_TYPE_PACK_ANY] = "[...]"
        };
        return kind < T2_TYPE_KIND_COUNT ? names[kind] : NULL;
}

static char const *
variable_prefix(T2VariableKind kind)
{
        switch (kind) {
        case T2_VARIABLE_FLEXIBLE: return "m";
        case T2_VARIABLE_RIGID: return "r";
        case T2_VARIABLE_QUANTIFIED: return "q";
        case T2_VARIABLE_WEAK: return "w";
        case T2_VARIABLE_ROW: return "row";
        case T2_VARIABLE_PACK: return "pack";
        }
        return "v";
}

static void
show_type(T2Universe const *universe, T2Type type, T2StringBuffer *buffer)
{
        T2Node const *node = get_node(universe, type);
        if (node == NULL) {
                buffer_text(buffer, "<invalid>");
                return;
        }

        char const *primitive = primitive_name(node->kind);
        if (primitive != NULL) {
                buffer_text(buffer, primitive);
                return;
        }

        switch (node->kind) {
        case T2_TYPE_LITERAL_BOOL:
                buffer_text(buffer, node->payload ? "true" : "false");
                break;
        case T2_TYPE_LITERAL_INT:
                buffer_format(buffer, "%" PRId64, (int64_t)node->payload);
                break;
        case T2_TYPE_LITERAL_STRING:
                buffer_text(buffer, "'");
                buffer_text(buffer, node->text);
                buffer_text(buffer, "'");
                break;
        case T2_TYPE_INT_RANGE:
        {
                T2Node const *lower = range_bound(universe, node, true);
                T2Node const *upper = range_bound(universe, node, false);
                if (lower != NULL) {
                        size_t index = 0;
                        show_type(universe, node->children[index], buffer);
                }
                buffer_text(
                        buffer,
                        (node->payload & T2_RANGE_UPPER_INCLUSIVE) != 0
                            ? "..."
                            : ".."
                );
                if (upper != NULL) {
                        size_t index = (node->payload & T2_RANGE_HAS_LOWER) != 0;
                        show_type(universe, node->children[index], buffer);
                }
                break;
        }
        case T2_TYPE_REFINEMENT:
                show_type(universe, node->children[0], buffer);
                buffer_text(buffer, "[");
                show_type(universe, node->children[1], buffer);
                buffer_text(buffer, "]");
                break;
        case T2_TYPE_COMPUTED:
                buffer_text(buffer, "computed ");
                buffer_text(buffer, node->text);
                buffer_text(buffer, "(");
                for (size_t i = 0; i < node->arity; ++i) {
                        if (i != 0) buffer_text(buffer, ", ");
                        show_type(universe, node->children[i], buffer);
                }
                buffer_text(buffer, ")");
                break;
        case T2_TYPE_VARIABLE:
                buffer_format(
                        buffer,
                        "$%s%" PRIu64,
                        variable_prefix(node->variable_kind),
                        node->payload
                );
                break;
        case T2_TYPE_META:
                buffer_format(
                        buffer,
                        "$%s%" PRIu32,
                        variable_prefix(node->variable_kind),
                        (uint32_t)node->payload
                );
                break;
        case T2_TYPE_NOMINAL:
        {
                T2NominalInfo const *info = find_nominal(universe, node->payload);
                if (info == NULL) buffer_format(buffer, "Nominal#%" PRIu64, node->payload);
                else buffer_text(buffer, info->name);
                if (node->arity != 0) {
                        buffer_text(buffer, "[");
                        for (size_t i = 0; i < node->arity; ++i) {
                                if (i != 0) buffer_text(buffer, ", ");
                                show_type(universe, node->children[i], buffer);
                        }
                        buffer_text(buffer, "]");
                }
                break;
        }
        case T2_TYPE_TYPE_VALUE:
                buffer_text(buffer, "type[");
                show_type(universe, node->children[0], buffer);
                buffer_text(buffer, "]");
                break;
        case T2_TYPE_TUPLE:
                buffer_text(buffer, "(");
                for (size_t i = 0; i < node->arity; ++i) {
                        if (i != 0) buffer_text(buffer, ", ");
                        show_type(universe, node->children[i], buffer);
                }
                if (node->arity == 1) buffer_text(buffer, ",");
                buffer_text(buffer, ")");
                break;
        case T2_TYPE_VARIADIC_TUPLE:
        {
                size_t prefix = (size_t)node->payload;
                buffer_text(buffer, "(");
                for (size_t i = 0; i < prefix; ++i) {
                        if (i != 0) buffer_text(buffer, ", ");
                        show_type(universe, node->children[i], buffer);
                }
                if (prefix != 0) buffer_text(buffer, ", ");
                show_type(universe, node->children[prefix], buffer);
                buffer_text(buffer, ")");
                break;
        }
        case T2_TYPE_RECORD:
                buffer_text(buffer, "{");
                for (size_t i = 0; i + 1 < node->arity; ++i) {
                        T2Node const *field = get_node(universe, node->children[i]);
                        if (i != 0) buffer_text(buffer, ", ");
                        if ((field->payload & T2_FIELD_WRITABLE_BIT) != 0) {
                                buffer_text(buffer, "var ");
                        }
                        buffer_text(buffer, field->text);
                        switch ((T2Presence)(field->payload & T2_FIELD_PRESENCE_MASK)) {
                        case T2_PRESENCE_OPTIONAL: buffer_text(buffer, "?"); break;
                        case T2_PRESENCE_ABSENT: buffer_text(buffer, "!"); break;
                        case T2_PRESENCE_UNKNOWN: buffer_text(buffer, "~"); break;
                        case T2_PRESENCE_REQUIRED: break;
                        }
                        buffer_text(buffer, ": ");
                        show_type(universe, field->children[0], buffer);
                }
                if (node->arity != 0) {
                        T2Node const *tail = get_node(
                                universe,
                                node->children[node->arity - 1]
                        );
                        if (tail->kind != T2_TYPE_ROW_EMPTY) {
                                if (node->arity > 1) buffer_text(buffer, ", ");
                                buffer_text(buffer, ".. ");
                                show_type(universe, node->children[node->arity - 1], buffer);
                        }
                }
                buffer_text(buffer, "}");
                break;
        case T2_TYPE_ROW:
                buffer_text(buffer, "row{");
                for (size_t i = 0; i + 1 < node->arity; ++i) {
                        T2Node const *field = get_node(universe, node->children[i]);
                        if (i != 0) buffer_text(buffer, ", ");
                        buffer_text(buffer, field->text);
                        buffer_text(buffer, ": ");
                        show_type(universe, field->children[0], buffer);
                }
                if (node->arity != 0) {
                        T2Node const *tail = get_node(
                                universe,
                                node->children[node->arity - 1]
                        );
                        if (tail->kind != T2_TYPE_ROW_EMPTY) {
                                if (node->arity > 1) buffer_text(buffer, ", ");
                                buffer_text(buffer, ".. ");
                                show_type(universe, node->children[node->arity - 1], buffer);
                        }
                }
                buffer_text(buffer, "}");
                break;
        case T2_TYPE_FUNCTION:
        {
                size_t parameter_count = (size_t)node->payload;
                buffer_text(buffer, "(");
                for (size_t i = 0; i < parameter_count; ++i) {
                        T2Node const *parameter = get_node(universe, node->children[i]);
                        if (i != 0) buffer_text(buffer, ", ");
                        T2ParameterKind kind = (T2ParameterKind)(
                                parameter->payload & T2_PARAMETER_KIND_MASK
                        );
                        if (kind == T2_PARAMETER_POSITIONAL_REST) buffer_text(buffer, "*");
                        if (kind == T2_PARAMETER_KEYWORD_REST) buffer_text(buffer, "**");
                        if (kind == T2_PARAMETER_PACK) buffer_text(buffer, "...");
                        if (parameter->text != NULL) {
                                buffer_text(buffer, parameter->text);
                                buffer_text(buffer, ": ");
                        }
                        show_type(universe, parameter->children[0], buffer);
                        if ((parameter->payload & T2_PARAMETER_REQUIRED) == 0) {
                                buffer_text(buffer, " = ?");
                        }
                }
                buffer_text(buffer, ") -> ");
                show_type(universe, node->children[parameter_count], buffer);
                T2Node const *yield = get_node(
                        universe,
                        node->children[parameter_count + 1]
                );
                T2Node const *send = get_node(
                        universe,
                        node->children[parameter_count + 2]
                );
                if (
                        yield->kind != T2_TYPE_NEVER
                     || send->kind != T2_TYPE_NIL
                ) {
                        buffer_text(buffer, " yields ");
                        show_type(universe, node->children[parameter_count + 1], buffer);
                        buffer_text(buffer, " sends ");
                        show_type(universe, node->children[parameter_count + 2], buffer);
                }
                break;
        }
        case T2_TYPE_FIELD:
        case T2_TYPE_PARAMETER:
                if (node->text != NULL) {
                        buffer_text(buffer, node->text);
                        buffer_text(buffer, ": ");
                }
                show_type(universe, node->children[0], buffer);
                break;
        case T2_TYPE_PACK:
                buffer_text(buffer, "pack[");
                for (size_t i = 0; i < (size_t)node->payload; ++i) {
                        if (i != 0) buffer_text(buffer, ", ");
                        show_type(universe, node->children[i], buffer);
                }
                if (node->arity != 0) {
                        T2Node const *tail = get_node(
                                universe,
                                node->children[node->arity - 1]
                        );
                        if (tail->kind != T2_TYPE_PACK_EMPTY) {
                                if (node->payload != 0) buffer_text(buffer, ", ");
                                buffer_text(buffer, ".. ");
                                show_type(universe, node->children[node->arity - 1], buffer);
                        }
                }
                buffer_text(buffer, "]");
                break;
        case T2_TYPE_PACK_EXPANSION:
                buffer_text(buffer, "...");
                show_type(universe, node->children[0], buffer);
                break;
        case T2_TYPE_PACK_FOLD_UNION:
        case T2_TYPE_PACK_FOLD_INTERSECTION:
                buffer_text(buffer, "...(");
                show_type(universe, node->children[0], buffer);
                buffer_text(
                        buffer,
                        node->kind == T2_TYPE_PACK_FOLD_UNION ? " |)" : " &)"
                );
                break;
        case T2_TYPE_RECURSIVE:
                buffer_format(buffer, "mu%" PRIu64 ". ", node->payload);
                show_type(universe, node->children[0], buffer);
                break;
        case T2_TYPE_RECURSIVE_VARIABLE:
                buffer_format(buffer, "@%" PRIu64, node->payload);
                break;
        case T2_TYPE_UNION:
        case T2_TYPE_INTERSECTION:
        {
                char const *separator = node->kind == T2_TYPE_UNION ? " | " : " & ";
                for (size_t i = 0; i < node->arity; ++i) {
                        if (i != 0) buffer_text(buffer, separator);
                        show_type(universe, node->children[i], buffer);
                }
                break;
        }
        case T2_TYPE_OVERLOAD:
                buffer_text(buffer, "overload{");
                for (size_t i = 0; i < node->arity; ++i) {
                        if (i != 0) buffer_text(buffer, "; ");
                        show_type(universe, node->children[i], buffer);
                }
                buffer_text(buffer, "}");
                break;
        default:
                buffer_text(buffer, "<unsupported>");
        }
}

char *
t2_type_string(T2Universe const *universe, T2Type type)
{
        T2StringBuffer buffer = {0};
        show_type(universe, type, &buffer);
        if (buffer.failed) {
                free(buffer.items);
                return NULL;
        }
        if (buffer.items == NULL) {
                buffer.items = copy_string("");
        }
        return buffer.items;
}

typedef struct t2_snapshot_build {
        T2Universe const *universe;
        T2TypeSnapshot *snapshot;
        uint32_t *indices;
        unsigned char *state;
        bool failed;
} T2SnapshotBuild;

static bool
snapshot_visit(T2SnapshotBuild *build, T2Type type, uint32_t *result)
{
        if (
                build->failed
             || type == T2_TYPE_INVALID
             || type > build->universe->node_count
        ) return false;
        size_t source_index = (size_t)type - 1;
        if (build->indices[source_index] != UINT32_MAX) {
                *result = build->indices[source_index];
                return true;
        }
        if (build->state[source_index] != 0) {
                build->failed = true;
                return false;
        }

        T2Node const *source = get_node(build->universe, type);
        if (source == NULL || source->kind == T2_TYPE_META) {
                build->failed = true;
                return false;
        }
        build->state[source_index] = 1;
        uint32_t *children = source->arity == 0
                           ? NULL
                           : malloc(source->arity * sizeof *children);
        if (source->arity != 0 && children == NULL) {
                build->failed = true;
                return false;
        }
        for (size_t i = 0; i < source->arity; ++i) {
                if (!snapshot_visit(build, source->children[i], &children[i])) {
                        free(children);
                        return false;
                }
        }

        if (
                build->snapshot->node_count >= UINT32_MAX
             || !reserve_array(
                    (void **)&build->snapshot->nodes,
                    &build->snapshot->node_capacity,
                    build->snapshot->node_count + 1,
                    sizeof *build->snapshot->nodes
                )
        ) {
                free(children);
                build->failed = true;
                return false;
        }
        char *text = copy_string(source->text);
        if (source->text != NULL && text == NULL) {
                free(children);
                build->failed = true;
                return false;
        }
        uint32_t snapshot_index = (uint32_t)build->snapshot->node_count;
        build->snapshot->nodes[build->snapshot->node_count++] =
                (T2TypeSnapshotNode) {
                        .payload = source->payload,
                        .text = text,
                        .children = children,
                        .arity = source->arity,
                        .kind = source->kind,
                        .variable_kind = source->variable_kind
                };
        build->indices[source_index] = snapshot_index;
        build->state[source_index] = 2;
        *result = snapshot_index;
        return true;
}

T2TypeSnapshot *
t2_type_snapshot_new(T2Universe const *universe, T2Type type)
{
        if (get_node(universe, type) == NULL) return NULL;
        T2TypeSnapshot *snapshot = calloc(1, sizeof *snapshot);
        uint32_t *indices = malloc(universe->node_count * sizeof *indices);
        unsigned char *state = calloc(universe->node_count, sizeof *state);
        if (snapshot == NULL || indices == NULL || state == NULL) {
                free(snapshot);
                free(indices);
                free(state);
                return NULL;
        }
        for (size_t i = 0; i < universe->node_count; ++i) {
                indices[i] = UINT32_MAX;
        }
        T2SnapshotBuild build = {
                .universe = universe,
                .snapshot = snapshot,
                .indices = indices,
                .state = state
        };
        bool ok = snapshot_visit(&build, type, &snapshot->root);
        free(indices);
        free(state);
        if (!ok || build.failed) {
                t2_type_snapshot_free(snapshot);
                return NULL;
        }
        return snapshot;
}

void
t2_type_snapshot_free(T2TypeSnapshot *snapshot)
{
        if (snapshot == NULL) return;
        for (size_t i = 0; i < snapshot->node_count; ++i) {
                free(snapshot->nodes[i].text);
                free(snapshot->nodes[i].children);
        }
        free(snapshot->nodes);
        free(snapshot);
}

size_t
t2_type_snapshot_node_count(T2TypeSnapshot const *snapshot)
{
        return snapshot == NULL ? 0 : snapshot->node_count;
}

T2Type
t2_type_snapshot_import(
        T2Universe *universe,
        T2TypeSnapshot const *snapshot
)
{
        if (
                universe == NULL
             || snapshot == NULL
             || snapshot->node_count == 0
             || snapshot->root >= snapshot->node_count
        ) return T2_TYPE_INVALID;

        T2Type *types = malloc(snapshot->node_count * sizeof *types);
        if (types == NULL) {
                universe->failed = true;
                return T2_TYPE_INVALID;
        }
        T2Type result = T2_TYPE_INVALID;
        for (size_t i = 0; i < snapshot->node_count; ++i) {
                T2TypeSnapshotNode const *source = &snapshot->nodes[i];
                if (source->kind >= T2_TYPE_KIND_COUNT || source->kind == T2_TYPE_META) {
                        goto Done;
                }
                T2Node *node = malloc(
                        sizeof *node + (size_t)source->arity * sizeof *node->children
                );
                if (node == NULL) {
                        universe->failed = true;
                        goto Done;
                }
                *node = (T2Node) {
                        .payload = source->payload,
                        .text = source->text,
                        .arity = source->arity,
                        .kind = source->kind,
                        .variable_kind = source->variable_kind
                };
                bool valid = true;
                for (size_t j = 0; j < source->arity; ++j) {
                        if (source->children[j] >= i) {
                                valid = false;
                                break;
                        }
                        node->children[j] = types[source->children[j]];
                }
                if (!valid) {
                        free(node);
                        goto Done;
                }
                if (source->kind == T2_TYPE_RECURSIVE_VARIABLE) {
                        types[i] = t2_recursive_variable(
                                universe,
                                (uint32_t)source->payload
                        );
                } else if (source->kind == T2_TYPE_RECURSIVE) {
                        types[i] = source->arity == 1
                                 ? t2_recursive(
                                         universe,
                                         (uint32_t)source->payload,
                                         node->children[0]
                                   )
                                 : T2_TYPE_INVALID;
                } else {
                        types[i] = rebuild_type(universe, node, node->children);
                }
                free(node);
                if (types[i] == T2_TYPE_INVALID) goto Done;
        }
        result = types[snapshot->root];

Done:
        free(types);
        return result;
}

static T2RuntimeFacts
unknown_runtime_facts(void)
{
        return (T2RuntimeFacts) { .kind = T2_RUNTIME_UNKNOWN };
}

static bool
same_runtime_shape(T2RuntimeFacts left, T2RuntimeFacts right)
{
        return left.exact
            && right.exact
            && left.kind == right.kind
            && (
                       left.kind != T2_RUNTIME_NOMINAL
                    || left.nominal_symbol == right.nominal_symbol
               );
}

static T2RuntimeFacts runtime_facts_x(
        T2Universe const *universe,
        T2Type type,
        unsigned depth
);

static T2RuntimeFacts
union_runtime_facts(
        T2Universe const *universe,
        T2Node const *node,
        unsigned depth
)
{
        T2RuntimeFacts result = {
                .kind = T2_RUNTIME_NEVER,
                .exact = true
        };
        bool have_value = false;
        bool nullable = false;
        for (size_t i = 0; i < node->arity; ++i) {
                T2RuntimeFacts arm = runtime_facts_x(
                        universe,
                        node->children[i],
                        depth + 1
                );
                if (arm.kind == T2_RUNTIME_NEVER && arm.exact) continue;
                if (arm.kind == T2_RUNTIME_NIL && arm.exact) {
                        nullable = true;
                        continue;
                }
                nullable |= arm.nullable;
                if (!have_value) {
                        result = arm;
                        have_value = true;
                } else if (!same_runtime_shape(result, arm)) {
                        return unknown_runtime_facts();
                }
        }
        if (!have_value) {
                return nullable
                     ? (T2RuntimeFacts) {
                               .kind = T2_RUNTIME_NIL,
                               .exact = true
                       }
                     : result;
        }
        result.nullable |= nullable;
        return result;
}

static T2RuntimeFacts
intersection_runtime_facts(
        T2Universe const *universe,
        T2Node const *node,
        unsigned depth
)
{
        T2RuntimeFacts result = unknown_runtime_facts();
        for (size_t i = 0; i < node->arity; ++i) {
                T2RuntimeFacts arm = runtime_facts_x(
                        universe,
                        node->children[i],
                        depth + 1
                );
                if (arm.kind == T2_RUNTIME_NEVER && arm.exact) return arm;
                if (!arm.exact) continue;
                if (!result.exact) result = arm;
                else if (!same_runtime_shape(result, arm)) {
                        return unknown_runtime_facts();
                } else {
                        result.nullable &= arm.nullable;
                }
        }
        return result;
}

static T2RuntimeFacts
runtime_facts_x(T2Universe const *universe, T2Type type, unsigned depth)
{
        if (depth > T2_RELATION_DEPTH_LIMIT) return unknown_runtime_facts();
        type = t2_type_resolve_computed(universe, type);
        T2Node const *node = get_node(universe, type);
        if (node == NULL) return unknown_runtime_facts();

        T2RuntimeFacts exact = { .exact = true };
        switch (literal_base(node->kind)) {
        case T2_TYPE_NEVER: exact.kind = T2_RUNTIME_NEVER; return exact;
        case T2_TYPE_NIL: exact.kind = T2_RUNTIME_NIL; return exact;
        case T2_TYPE_BOOL: exact.kind = T2_RUNTIME_BOOL; return exact;
        case T2_TYPE_INT: exact.kind = T2_RUNTIME_INT; return exact;
        case T2_TYPE_FLOAT: exact.kind = T2_RUNTIME_FLOAT; return exact;
        case T2_TYPE_STRING: exact.kind = T2_RUNTIME_STRING; return exact;
        case T2_TYPE_FUNCTION:
        case T2_TYPE_OVERLOAD:
                exact.kind = T2_RUNTIME_FUNCTION;
                return exact;
        case T2_TYPE_TUPLE:
        case T2_TYPE_VARIADIC_TUPLE:
                exact.kind = T2_RUNTIME_TUPLE;
                return exact;
        case T2_TYPE_RECORD:
                exact.kind = T2_RUNTIME_RECORD;
                return exact;
        case T2_TYPE_NOMINAL:
                exact.kind = T2_RUNTIME_NOMINAL;
                exact.nominal_symbol = node->payload;
                return exact;
        case T2_TYPE_TYPE_VALUE:
                exact.kind = T2_RUNTIME_TYPE_VALUE;
                return exact;
        case T2_TYPE_REFINEMENT:
                return node->arity == 2
                     ? runtime_facts_x(universe, node->children[0], depth + 1)
                     : unknown_runtime_facts();
        case T2_TYPE_RECURSIVE:
                return node->arity == 1
                     ? runtime_facts_x(universe, node->children[0], depth + 1)
                     : unknown_runtime_facts();
        case T2_TYPE_UNION:
                return union_runtime_facts(universe, node, depth);
        case T2_TYPE_INTERSECTION:
                return intersection_runtime_facts(universe, node, depth);
        default:
                return unknown_runtime_facts();
        }
}

bool
t2_type_runtime_facts(
        T2Universe const *universe,
        T2Type type,
        T2RuntimeFacts *facts
)
{
        if (facts == NULL || get_node(universe, type) == NULL) return false;
        *facts = runtime_facts_x(universe, type, 0);
        return true;
}

static bool
solver_reserve(
        T2Solver *solver,
        void **items,
        size_t *capacity,
        size_t needed,
        size_t item_size
)
{
        if (reserve_array(items, capacity, needed, item_size)) {
                return true;
        }
        solver->failed = true;
        snprintf(solver->error, sizeof solver->error, "types2 solver ran out of memory");
        return false;
}

static bool
push_undo(T2Solver *solver, T2Undo undo)
{
        if (solver->transaction_depth == 0) return true;
        if (
                !solver_reserve(
                        solver,
                        (void **)&solver->undo,
                        &solver->undo_capacity,
                        solver->undo_count + 1,
                        sizeof *solver->undo
                )
        ) return false;
        solver->undo[solver->undo_count++] = undo;
        return true;
}

static uint32_t
meta_from_type(T2Solver const *solver, T2Type type)
{
        T2Node const *node = get_node(solver->universe, type);
        if (node == NULL || node->kind != T2_TYPE_META) return 0;
        uint32_t solver_id = (uint32_t)(node->payload >> 32);
        uint32_t meta = (uint32_t)node->payload;
        if (solver_id != solver->id || meta == 0 || meta > solver->meta_count) return 0;
        return meta;
}

static T2Type
meta_type(T2Solver *solver, uint32_t meta)
{
        uint64_t payload = ((uint64_t)solver->id << 32) | meta;
        return intern_type(
                solver->universe,
                T2_TYPE_META,
                solver->metas[meta - 1].variable_kind,
                payload,
                NULL,
                NULL,
                0
        );
}

static uint32_t
find_root(T2Solver *solver, uint32_t meta)
{
        T2Meta *node = &solver->metas[meta - 1];
        if (node->parent == meta) return meta;
        uint32_t root = find_root(solver, node->parent);
        if (node->parent != root) {
                if (!push_undo(solver, (T2Undo) {
                        .kind = T2_UNDO_PARENT,
                        .index = meta,
                        .old = node->parent
                })) return root;
                node->parent = root;
        }
        return root;
}

static T2Type
resolve_sort_solution(T2Solver *solver, T2Type type)
{
        uint32_t meta = meta_from_type(solver, type);
        if (meta == 0) return type;
        meta = find_root(solver, meta);
        T2Meta const *node = &solver->metas[meta - 1];
        return node->solution == T2_TYPE_INVALID ? meta_type(solver, meta) : node->solution;
}

static T2Type
resolve_pack_solutions(T2Solver *solver, T2Type type, unsigned depth)
{
        if (depth > T2_RELATION_DEPTH_LIMIT) return type;
        uint32_t meta = meta_from_type(solver, type);
        if (meta != 0) {
                meta = find_root(solver, meta);
                T2Meta const *node = &solver->metas[meta - 1];
                if (
                        node->variable_kind != T2_VARIABLE_PACK
                     || node->solution == T2_TYPE_INVALID
                ) return meta_type(solver, meta);
                return resolve_pack_solutions(
                        solver,
                        node->solution,
                        depth + 1
                );
        }

        T2Node const *node = get_node(solver->universe, type);
        if (node == NULL || node->arity == 0) return type;
        T2Type *children = malloc(node->arity * sizeof *children);
        if (children == NULL) {
                solver->failed = true;
                snprintf(
                        solver->error,
                        sizeof solver->error,
                        "types2 solver ran out of memory"
                );
                return T2_TYPE_INVALID;
        }
        bool changed = false;
        for (size_t i = 0; i < node->arity; ++i) {
                children[i] = resolve_pack_solutions(
                        solver,
                        node->children[i],
                        depth + 1
                );
                changed |= children[i] != node->children[i];
        }
        T2Type result = changed
                      ? rebuild_type(solver->universe, node, children)
                      : type;
        free(children);
        return result;
}

static bool
type_contains_solved_pack_meta(T2Solver *solver, T2Type type, unsigned depth)
{
        if (depth > T2_RELATION_DEPTH_LIMIT) return false;
        uint32_t meta = meta_from_type(solver, type);
        if (meta != 0) {
                meta = find_root(solver, meta);
                T2Meta const *node = &solver->metas[meta - 1];
                return node->variable_kind == T2_VARIABLE_PACK
                    && node->solution != T2_TYPE_INVALID;
        }
        T2Node const *node = get_node(solver->universe, type);
        if (node == NULL) return false;
        for (size_t i = 0; i < node->arity; ++i) {
                if (type_contains_solved_pack_meta(
                        solver,
                        node->children[i],
                        depth + 1
                )) return true;
        }
        return false;
}

static bool
type_contains_meta(T2Solver *solver, T2Type type, uint32_t wanted, unsigned depth)
{
        if (depth > T2_RELATION_DEPTH_LIMIT) return true;
        uint32_t meta = meta_from_type(solver, type);
        if (meta != 0) {
                meta = find_root(solver, meta);
                if (meta == wanted) return true;
                T2Type solution = solver->metas[meta - 1].solution;
                return solution != T2_TYPE_INVALID
                    && type_contains_meta(solver, solution, wanted, depth + 1);
        }
        T2Node const *node = get_node(solver->universe, type);
        if (node == NULL) return false;
        for (size_t i = 0; i < node->arity; ++i) {
                if (type_contains_meta(solver, node->children[i], wanted, depth + 1)) {
                        return true;
                }
        }
        return false;
}

static bool
push_watch(T2Solver *solver, uint32_t meta, uint64_t watch)
{
        T2Meta *node = &solver->metas[meta - 1];
        if (
                !solver_reserve(
                        solver,
                        (void **)&node->watchers.items,
                        &node->watchers.capacity,
                        node->watchers.count + 1,
                        sizeof *node->watchers.items
                )
        ) return false;
        if (!push_undo(solver, (T2Undo) {
                .kind = T2_UNDO_WATCH_COUNT,
                .index = meta,
                .old = node->watchers.count
        })) return false;
        node->watchers.items[node->watchers.count++] = watch;
        return true;
}

static bool
enqueue(T2Solver *solver, uint64_t work)
{
        if (
                solver->draining_work
             && solver->processing_work
             && solver->active_work == work
        ) {
                solver->rerun_active_work = true;
                return true;
        }
        for (size_t i = solver->work_index; i < solver->work_count; ++i) {
                if (solver->work[i] == work) return true;
        }
        if (
                !solver_reserve(
                        solver,
                        (void **)&solver->work,
                        &solver->work_capacity,
                        solver->work_count + 1,
                        sizeof *solver->work
                )
        ) return false;
        solver->work[solver->work_count++] = work;
        return true;
}

static void
wake_meta(T2Solver *solver, uint32_t meta)
{
        T2Meta const *node = &solver->metas[meta - 1];
        for (size_t i = 0; i < node->watchers.count; ++i) {
                if (!enqueue(solver, node->watchers.items[i])) return;
        }
}

static void
set_solver_error(
        T2Solver *solver,
        char const *message,
        T2Type left,
        T2Type right,
        char const *provenance
)
{
        if (solver->failed) return;
        solver->failed = true;
        char *left_string = t2_type_string(solver->universe, left);
        char *right_string = t2_type_string(solver->universe, right);
        snprintf(
                solver->error,
                sizeof solver->error,
                "%s: %s is not a subtype of %s%s%s",
                message,
                left_string == NULL ? "<type>" : left_string,
                right_string == NULL ? "<type>" : right_string,
                provenance == NULL ? "" : " at ",
                provenance == NULL ? "" : provenance
        );
        free(left_string);
        free(right_string);
}

static char const *
record_cause(
        T2Solver *solver,
        T2CauseKind kind,
        T2Type left,
        T2Type right,
        char const *provenance
)
{
        if (!solver_reserve(
                solver,
                (void **)&solver->causes,
                &solver->cause_capacity,
                solver->cause_count + 1,
                sizeof *solver->causes
        )) return NULL;

        char *owned = copy_string(provenance);
        if (provenance != NULL && owned == NULL) {
                solver->failed = true;
                snprintf(solver->error, sizeof solver->error, "types2 solver ran out of memory");
                return NULL;
        }
        solver->causes[solver->cause_count++] = (T2Cause) {
                .kind = kind,
                .left = left,
                .right = right,
                .provenance = owned
        };
        return owned;
}

T2Solver *
t2_solver_new(T2Universe *universe)
{
        if (universe == NULL || universe->failed || universe->next_solver_id == 0) {
                return NULL;
        }
        T2Solver *solver = calloc(1, sizeof *solver);
        if (solver == NULL) return NULL;
        solver->universe = universe;
        solver->id = universe->next_solver_id++;
        return solver;
}

void
t2_solver_set_predicate_resolver(
        T2Solver *solver,
        T2PredicateResolver *resolver,
        void *context
)
{
        if (solver == NULL) return;
        solver->predicate_resolver = resolver;
        solver->predicate_context = context;
}

void
t2_solver_free(T2Solver *solver)
{
        if (solver == NULL) return;
        for (size_t i = 0; i < solver->meta_count; ++i) {
                free(solver->metas[i].watchers.items);
                free(solver->metas[i].provenance);
        }
        for (size_t i = 0; i < solver->cause_count; ++i) {
                free(solver->causes[i].provenance);
        }
        for (size_t i = 0; i < solver->obligation_count; ++i) {
                free(solver->obligations[i].name);
                free(solver->obligations[i].provenance);
        }
        free(solver->metas);
        free(solver->edges);
        free(solver->obligations);
        free(solver->work);
        free(solver->undo);
        free(solver->causes);
        free(solver);
}

T2Type
t2_solver_new_meta(
        T2Solver *solver,
        T2VariableKind kind,
        uint32_t level,
        char const *provenance
)
{
        if (solver == NULL || solver->failed) return T2_TYPE_INVALID;
        if (kind == T2_VARIABLE_RIGID || kind == T2_VARIABLE_QUANTIFIED) {
                return T2_TYPE_INVALID;
        }
        if (
                !solver_reserve(
                        solver,
                        (void **)&solver->metas,
                        &solver->meta_capacity,
                        solver->meta_count + 1,
                        sizeof *solver->metas
                )
        ) return T2_TYPE_INVALID;

        uint32_t id = (uint32_t)(solver->meta_count + 1);
        char *owned_provenance = copy_string(provenance);
        if (provenance != NULL && owned_provenance == NULL) {
                solver->failed = true;
                snprintf(solver->error, sizeof solver->error, "types2 solver ran out of memory");
                return T2_TYPE_INVALID;
        }
        solver->metas[solver->meta_count++] = (T2Meta) {
                .parent = id,
                .level = level,
                .variable_kind = kind,
                .lower = t2_primitive(solver->universe, T2_TYPE_NEVER),
                .upper = t2_primitive(solver->universe, T2_TYPE_ANY),
                .provenance = owned_provenance
        };
        if (!t2_universe_ok(solver->universe)) {
                solver->failed = true;
                snprintf(solver->error, sizeof solver->error, "types2 type allocation failed");
                return T2_TYPE_INVALID;
        }
        return meta_type(solver, id);
}

static T2Relation constrain_internal(
        T2Solver *solver,
        T2Type subtype,
        T2Type supertype,
        char const *provenance,
        bool retain_deferred
);

static T2Relation
check_bounds(T2Solver *solver, uint32_t meta, char const *provenance)
{
        meta = find_root(solver, meta);
        T2Meta const *node = &solver->metas[meta - 1];
        if (node->checking_bounds) {
                return t2_subtype(solver->universe, node->lower, node->upper);
        }
        T2Type lower = node->lower;
        T2Type upper = node->upper;
        solver->metas[meta - 1].checking_bounds = true;
        /* Maintaining LB <: UB is itself a constraint-solving operation.
         * A pure subtype probe can establish compatibility, but it cannot
         * propagate relationships between nested metas (notably a forward
         * function declaration's result and the later definition's result).
         * Do not retain a second top-level obligation here: nested metas and
         * edges already carry the dependencies that can make progress. */
        T2Relation relation = constrain_internal(
                solver,
                lower,
                upper,
                provenance,
                false
        );
        solver->metas[meta - 1].checking_bounds = false;
        if (relation == T2_RELATION_NO) {
                set_solver_error(
                        solver,
                        "inconsistent bounds",
                        lower,
                        upper,
                        provenance
                );
        } else if (relation == T2_RELATION_COMPLEXITY) {
                set_solver_error(
                        solver,
                        "subtype comparison exceeded its complexity limit",
                        lower,
                        upper,
                        provenance
                );
        }
        return relation;
}

static bool
direct_union_without_meta(
        T2Solver *solver,
        T2Type type,
        uint32_t wanted,
        T2Type *remainder
)
{
        T2Node const *node = get_node(solver->universe, type);
        if (node == NULL || node->kind != T2_TYPE_UNION) return false;

        T2Type *arms = malloc(node->arity * sizeof *arms);
        if (arms == NULL) {
                solver->failed = true;
                snprintf(solver->error, sizeof solver->error, "types2 solver ran out of memory");
                return false;
        }
        size_t count = 0;
        bool removed = false;
        wanted = find_root(solver, wanted);
        for (size_t i = 0; i < node->arity; ++i) {
                uint32_t child = meta_from_type(solver, node->children[i]);
                if (child != 0 && find_root(solver, child) == wanted) {
                        removed = true;
                        continue;
                }
                arms[count++] = node->children[i];
        }
        if (removed) {
                *remainder = count == 0
                           ? t2_primitive(solver->universe, T2_TYPE_NEVER)
                           : t2_union(solver->universe, arms, count);
        }
        free(arms);
        return removed;
}

static T2Relation
update_lower(T2Solver *solver, uint32_t meta, T2Type lower, char const *provenance)
{
        meta = find_root(solver, meta);
        T2Meta *node = &solver->metas[meta - 1];
        T2Type remainder = T2_TYPE_INVALID;
        if (direct_union_without_meta(solver, lower, meta, &remainder)) {
                if (remainder == T2_TYPE_INVALID || solver->failed) {
                        return T2_RELATION_COMPLEXITY;
                }
                return update_lower(solver, meta, remainder, provenance);
        }
        if (type_contains_meta(solver, lower, meta, 0)) {
                set_solver_error(
                        solver,
                        "occurs check failed",
                        lower,
                        meta_type(solver, meta),
                        provenance
                );
                return T2_RELATION_NO;
        }
        T2Type joined = t2_join(solver->universe, node->lower, lower);
        if (joined == T2_TYPE_INVALID) return T2_RELATION_COMPLEXITY;
        if (joined == node->lower) return check_bounds(solver, meta, provenance);
        if (!push_undo(solver, (T2Undo) {
                .kind = T2_UNDO_LOWER,
                .index = meta,
                .old = node->lower
        })) return T2_RELATION_COMPLEXITY;
        node->lower = joined;
        T2Relation relation = check_bounds(solver, meta, provenance);
        if (relation != T2_RELATION_NO && relation != T2_RELATION_COMPLEXITY) {
                wake_meta(solver, meta);
        }
        return relation;
}

static T2Relation
update_upper(T2Solver *solver, uint32_t meta, T2Type upper, char const *provenance)
{
        meta = find_root(solver, meta);
        T2Meta *node = &solver->metas[meta - 1];
        T2Type remainder = T2_TYPE_INVALID;
        if (direct_union_without_meta(solver, upper, meta, &remainder)) {
                return solver->failed
                     ? T2_RELATION_COMPLEXITY
                     : check_bounds(solver, meta, provenance);
        }
        if (type_contains_meta(solver, upper, meta, 0)) {
                set_solver_error(
                        solver,
                        "occurs check failed",
                        meta_type(solver, meta),
                        upper,
                        provenance
                );
                return T2_RELATION_NO;
        }
        T2Type met = t2_meet(solver->universe, node->upper, upper);
        if (met == T2_TYPE_INVALID) return T2_RELATION_COMPLEXITY;
        if (met == node->upper) return check_bounds(solver, meta, provenance);
        if (!push_undo(solver, (T2Undo) {
                .kind = T2_UNDO_UPPER,
                .index = meta,
                .old = node->upper
        })) return T2_RELATION_COMPLEXITY;
        node->upper = met;
        T2Relation relation = check_bounds(solver, meta, provenance);
        if (relation != T2_RELATION_NO && relation != T2_RELATION_COMPLEXITY) {
                wake_meta(solver, meta);
        }
        return relation;
}

static T2VariableKind
term_sort(T2Universe const *universe, T2Type type)
{
        T2Node const *node = get_node(universe, type);
        if (node == NULL) return T2_VARIABLE_FLEXIBLE;
        if (
                node->kind == T2_TYPE_ROW
             || node->kind == T2_TYPE_ROW_EMPTY
             || node->kind == T2_TYPE_ROW_ANY
        ) return T2_VARIABLE_ROW;
        if (
                node->kind == T2_TYPE_PACK
             || node->kind == T2_TYPE_PACK_EMPTY
             || node->kind == T2_TYPE_PACK_ANY
             || node->kind == T2_TYPE_PACK_EXPANSION
        ) return T2_VARIABLE_PACK;
        if (
                (node->kind == T2_TYPE_META || node->kind == T2_TYPE_VARIABLE)
             && (node->variable_kind == T2_VARIABLE_ROW
                    || node->variable_kind == T2_VARIABLE_PACK)
        ) return node->variable_kind;
        if (node->kind == T2_TYPE_INTERSECTION && node->arity != 0) {
                T2VariableKind sort = term_sort(universe, node->children[0]);
                if (sort != T2_VARIABLE_ROW && sort != T2_VARIABLE_PACK) {
                        return T2_VARIABLE_FLEXIBLE;
                }
                for (size_t i = 1; i < node->arity; ++i) {
                        if (term_sort(universe, node->children[i]) != sort) {
                                return T2_VARIABLE_FLEXIBLE;
                        }
                }
                return sort;
        }
        return T2_VARIABLE_FLEXIBLE;
}

static T2Relation merge_meta_roots(
        T2Solver *solver,
        uint32_t left,
        uint32_t right,
        char const *provenance
);

static T2Relation
bind_sort_meta(
        T2Solver *solver,
        uint32_t meta,
        T2Type value,
        char const *provenance
)
{
        meta = find_root(solver, meta);
        T2Meta *node = &solver->metas[meta - 1];
        T2VariableKind sort = node->variable_kind;
        if (sort != T2_VARIABLE_ROW && sort != T2_VARIABLE_PACK) {
                return T2_RELATION_NO;
        }

        uint32_t other = meta_from_type(solver, value);
        if (other != 0) {
                other = find_root(solver, other);
                if (other == meta) return T2_RELATION_YES;
                if (solver->metas[other - 1].variable_kind != sort) {
                        set_solver_error(
                                solver,
                                "cannot equate different variable kinds",
                                meta_type(solver, meta),
                                meta_type(solver, other),
                                provenance
                        );
                        return T2_RELATION_NO;
                }
                return merge_meta_roots(solver, meta, other, provenance);
        }

        if (term_sort(solver->universe, value) != sort) {
                set_solver_error(
                        solver,
                        "kind-specific variable received the wrong term sort",
                        meta_type(solver, meta),
                        value,
                        provenance
                );
                return T2_RELATION_NO;
        }
        if (node->solution != T2_TYPE_INVALID) {
                return t2_solver_unify(solver, node->solution, value, provenance);
        }
        if (type_contains_meta(solver, value, meta, 0)) {
                set_solver_error(
                        solver,
                        "occurs check failed",
                        meta_type(solver, meta),
                        value,
                        provenance
                );
                return T2_RELATION_NO;
        }
        if (!push_undo(solver, (T2Undo) {
                .kind = T2_UNDO_SOLUTION,
                .index = meta,
                .old = node->solution
        })) return T2_RELATION_COMPLEXITY;
        node->solution = value;
        wake_meta(solver, meta);
        return T2_RELATION_YES;
}

static bool
collect_meta_roots(T2Solver *solver, T2Type type, uint32_t **roots, size_t *count, size_t *capacity)
{
        uint32_t meta = meta_from_type(solver, type);
        if (meta != 0) {
                meta = find_root(solver, meta);
                for (size_t i = 0; i < *count; ++i) {
                        if ((*roots)[i] == meta) return true;
                }
                if (!solver_reserve(
                        solver,
                        (void **)roots,
                        capacity,
                        *count + 1,
                        sizeof **roots
                )) return false;
                (*roots)[(*count)++] = meta;
                return true;
        }

        T2Node const *node = get_node(solver->universe, type);
        if (node == NULL) return false;
        for (size_t i = 0; i < node->arity; ++i) {
                if (!collect_meta_roots(solver, node->children[i], roots, count, capacity)) {
                        return false;
                }
        }
        return true;
}

static T2Relation
retain_predicate(
        T2Solver *solver,
        T2Predicate const *predicate
)
{
        if (!solver_reserve(
                solver,
                (void **)&solver->obligations,
                &solver->obligation_capacity,
                solver->obligation_count + 1,
                sizeof *solver->obligations
        )) return T2_RELATION_COMPLEXITY;

        char *name = copy_string(predicate->name);
        char *provenance = copy_string(predicate->provenance);
        if (
                (predicate->name != NULL && name == NULL)
             || (predicate->provenance != NULL && provenance == NULL)
        ) {
                free(name);
                free(provenance);
                solver->failed = true;
                snprintf(
                        solver->error,
                        sizeof solver->error,
                        "types2 solver ran out of memory"
                );
                return T2_RELATION_COMPLEXITY;
        }

        size_t index = solver->obligation_count++;
        solver->obligations[index] = (T2Obligation) {
                .predicate = *predicate,
                .name = name,
                .provenance = provenance,
                .active = true
        };
        solver->obligations[index].predicate.name = name;
        solver->obligations[index].predicate.provenance = provenance;

        uint32_t *roots = NULL;
        size_t count = 0;
        size_t capacity = 0;
        bool ok = collect_meta_roots(
                solver,
                predicate->subtype,
                &roots,
                &count,
                &capacity
        ) && collect_meta_roots(
                solver,
                predicate->supertype,
                &roots,
                &count,
                &capacity
        );
        if (ok && predicate->operand != T2_TYPE_INVALID) {
                ok = collect_meta_roots(
                        solver,
                        predicate->operand,
                        &roots,
                        &count,
                        &capacity
                );
        }
        for (size_t i = 0; ok && i < count; ++i) {
                ok = push_watch(solver, roots[i], T2_WATCH_OBLIGATION | index);
        }
        free(roots);

        return ok ? T2_RELATION_DEFERRED : T2_RELATION_COMPLEXITY;
}

static T2Relation
retain_obligation(
        T2Solver *solver,
        T2Type subtype,
        T2Type supertype,
        char const *provenance
)
{
        T2Predicate predicate = {
                .kind = T2_PREDICATE_SUBTYPE,
                .subtype = subtype,
                .supertype = supertype,
                .provenance = provenance
        };
        return retain_predicate(solver, &predicate);
}

static T2Relation
add_edge(
        T2Solver *solver,
        uint32_t subtype,
        uint32_t supertype,
        char const *provenance
)
{
        subtype = find_root(solver, subtype);
        supertype = find_root(solver, supertype);
        if (subtype == supertype) return T2_RELATION_YES;

        T2VariableKind sub_kind = solver->metas[subtype - 1].variable_kind;
        T2VariableKind sup_kind = solver->metas[supertype - 1].variable_kind;
        if (
                (sub_kind == T2_VARIABLE_ROW) != (sup_kind == T2_VARIABLE_ROW)
             || (sub_kind == T2_VARIABLE_PACK) != (sup_kind == T2_VARIABLE_PACK)
        ) {
                set_solver_error(
                        solver,
                        "cannot relate different variable kinds",
                        meta_type(solver, subtype),
                        meta_type(solver, supertype),
                        provenance
                );
                return T2_RELATION_NO;
        }

        T2WatchVector const *watches = &solver->metas[subtype - 1].watchers;
        for (size_t i = 0; i < watches->count; ++i) {
                uint64_t watch = watches->items[i];
                if ((watch & T2_WATCH_OBLIGATION) != 0 || watch >= solver->edge_count) {
                        continue;
                }
                T2Edge const *edge = &solver->edges[watch];
                if (
                        find_root(solver, edge->subtype) == subtype
                     && find_root(solver, edge->supertype) == supertype
                ) return T2_RELATION_YES;
        }

        if (!solver_reserve(
                solver,
                (void **)&solver->edges,
                &solver->edge_capacity,
                solver->edge_count + 1,
                sizeof *solver->edges
        )) return T2_RELATION_COMPLEXITY;

        size_t edge_index = solver->edge_count++;
        solver->edges[edge_index] = (T2Edge) {
                .subtype = subtype,
                .supertype = supertype,
                .provenance = provenance
        };

        if (
                !push_watch(solver, subtype, edge_index)
             || !push_watch(solver, supertype, edge_index)
             || !enqueue(solver, edge_index)
        ) return T2_RELATION_COMPLEXITY;

        return T2_RELATION_YES;
}

static T2Relation
constrain_children(
        T2Solver *solver,
        T2Node const *a,
        T2Node const *b,
        char const *provenance,
        bool retain_deferred
)
{
        T2Relation result = T2_RELATION_YES;
        for (size_t i = 0; i < a->arity; ++i) {
                T2Relation item = constrain_internal(
                        solver,
                        a->children[i],
                        b->children[i],
                        provenance,
                        retain_deferred
                );
                result = combine_all(result, item);
                if (solver->failed) return item;
        }
        return result;
}

static T2Relation
constrain_parameter_types(
        T2Solver *solver,
        T2Node const *actual,
        T2Node const *expected,
        char const *provenance,
        bool retain_deferred
)
{
        if (actual == NULL || expected == NULL) return T2_RELATION_NO;
        return constrain_internal(
                solver,
                expected->children[0],
                actual->children[0],
                provenance,
                retain_deferred
        );
}

static T2Relation
constrain_function_types(
        T2Solver *solver,
        T2Type actual_type,
        T2Type expected_type,
        T2Node const *actual,
        T2Node const *expected,
        char const *provenance,
        bool retain_deferred
)
{
        T2Relation shape = t2_subtype(solver->universe, actual_type, expected_type);
        if (shape == T2_RELATION_NO || shape == T2_RELATION_COMPLEXITY) {
                set_solver_error(
                        solver,
                        shape == T2_RELATION_NO
                            ? "incompatible callable protocol"
                            : "callable comparison exceeded its complexity limit",
                        actual_type,
                        expected_type,
                        provenance
                );
                return shape;
        }

        size_t actual_count = (size_t)actual->payload;
        size_t expected_count = (size_t)expected->payload;
        T2Node const *actual_rest = function_parameter_kind(
                solver->universe,
                actual,
                T2_PARAMETER_POSITIONAL_REST
        );
        T2Node const *expected_rest = function_parameter_kind(
                solver->universe,
                expected,
                T2_PARAMETER_POSITIONAL_REST
        );
        T2Node const *actual_pack = function_parameter_kind(
                solver->universe,
                actual,
                T2_PARAMETER_PACK
        );
        T2Node const *expected_pack = function_parameter_kind(
                solver->universe,
                expected,
                T2_PARAMETER_PACK
        );
        T2Node const *actual_kwrest = function_parameter_kind(
                solver->universe,
                actual,
                T2_PARAMETER_KEYWORD_REST
        );
        T2Node const *expected_kwrest = function_parameter_kind(
                solver->universe,
                expected,
                T2_PARAMETER_KEYWORD_REST
        );
        T2Relation result = T2_RELATION_YES;

        size_t expected_positions = 0;
        for (size_t i = 0; i < expected_count; ++i) {
                T2Node const *parameter = get_node(solver->universe, expected->children[i]);
                expected_positions += parameter_accepts_position(parameter);
        }
        for (size_t i = 0; i < expected_positions; ++i) {
                T2Node const *wanted = function_positional_parameter(
                        solver->universe,
                        expected,
                        i
                );
                T2Node const *have = function_positional_parameter(
                        solver->universe,
                        actual,
                        i
                );
                if (have == NULL) have = actual_rest == NULL ? actual_pack : actual_rest;
                result = combine_all(
                        result,
                        constrain_parameter_types(
                                solver,
                                have,
                                wanted,
                                provenance,
                                retain_deferred
                        )
                );
                if (solver->failed) return T2_RELATION_NO;
        }
        if (expected_rest != NULL || expected_pack != NULL) {
                result = combine_all(
                        result,
                        constrain_parameter_types(
                                solver,
                                actual_rest == NULL ? actual_pack : actual_rest,
                                expected_rest == NULL ? expected_pack : expected_rest,
                                provenance,
                                retain_deferred
                        )
                );
                if (solver->failed) return T2_RELATION_NO;
        }
        for (size_t i = 0; i < expected_count; ++i) {
                T2Node const *wanted = get_node(solver->universe, expected->children[i]);
                if (!parameter_accepts_keyword(wanted)) continue;
                T2Node const *have = function_keyword_parameter(
                        solver->universe,
                        actual,
                        wanted->text
                );
                if (have == NULL) have = actual_kwrest;
                result = combine_all(
                        result,
                        constrain_parameter_types(
                                solver,
                                have,
                                wanted,
                                provenance,
                                retain_deferred
                        )
                );
                if (solver->failed) return T2_RELATION_NO;
        }
        if (expected_kwrest != NULL) {
                result = combine_all(
                        result,
                        constrain_parameter_types(
                                solver,
                                actual_kwrest,
                                expected_kwrest,
                                provenance,
                                retain_deferred
                        )
                );
                if (solver->failed) return T2_RELATION_NO;
        }

        result = combine_all(
                result,
                constrain_internal(
                        solver,
                        actual->children[actual_count],
                        expected->children[expected_count],
                        provenance,
                        retain_deferred
                )
        );
        result = combine_all(
                result,
                constrain_internal(
                        solver,
                        actual->children[actual_count + 1],
                        expected->children[expected_count + 1],
                        provenance,
                        retain_deferred
                )
        );
        return combine_all(
                result,
                constrain_internal(
                        solver,
                        expected->children[expected_count + 2],
                        actual->children[actual_count + 2],
                        provenance,
                        retain_deferred
                )
        );
}

static T2Node const *
solver_find_row_field(
        T2Solver *solver,
        T2Type row,
        char const *name,
        unsigned depth
)
{
        if (depth > T2_RELATION_DEPTH_LIMIT) return NULL;
        row = resolve_sort_solution(solver, row);
        T2Node const *node = get_node(solver->universe, row);
        if (node == NULL) return NULL;
        if (node->kind == T2_TYPE_INTERSECTION) {
                for (size_t i = 0; i < node->arity; ++i) {
                        T2Node const *field = solver_find_row_field(
                                solver,
                                node->children[i],
                                name,
                                depth + 1
                        );
                        if (field != NULL) return field;
                }
                return NULL;
        }
        if (node->kind != T2_TYPE_ROW) return NULL;
        T2Node const *field = find_record_field_node(solver->universe, node, name);
        if (field != NULL) return field;
        return solver_find_row_field(
                solver,
                node->children[node->arity - 1],
                name,
                depth + 1
        );
}

static T2Node const *
solver_find_record_field(
        T2Solver *solver,
        T2Node const *record,
        char const *name
)
{
        T2Node const *field = find_record_field_node(solver->universe, record, name);
        if (field != NULL) return field;
        return solver_find_row_field(
                solver,
                record->children[record->arity - 1],
                name,
                0
        );
}

static T2FieldSpec
field_spec_from_node(T2Node const *field)
{
        return (T2FieldSpec) {
                .name = field->text,
                .type = field->children[0],
                .presence = (T2Presence)(field->payload & T2_FIELD_PRESENCE_MASK),
                .capability = (field->payload & T2_FIELD_WRITABLE_BIT)
                            ? T2_FIELD_WRITABLE
                            : T2_FIELD_READONLY
        };
}

static T2Relation
require_field_in_row(
        T2Solver *solver,
        T2Type row,
        T2Node const *expected,
        char const *provenance
)
{
        row = resolve_sort_solution(solver, row);
        uint32_t meta = meta_from_type(solver, row);
        if (meta == 0) return T2_RELATION_DEFERRED;
        meta = find_root(solver, meta);
        uint32_t level = solver->metas[meta - 1].level;
        T2Type field_meta = t2_solver_new_meta(
                solver,
                T2_VARIABLE_FLEXIBLE,
                level,
                provenance
        );
        T2Type remainder = t2_solver_new_meta(
                solver,
                T2_VARIABLE_ROW,
                level,
                provenance
        );
        if (field_meta == T2_TYPE_INVALID || remainder == T2_TYPE_INVALID) {
                return T2_RELATION_COMPLEXITY;
        }
        T2FieldSpec field = field_spec_from_node(expected);
        field.type = field_meta;
        T2Type extension = t2_row(solver->universe, &field, 1, remainder);
        if (extension == T2_TYPE_INVALID) return T2_RELATION_COMPLEXITY;
        return bind_sort_meta(solver, meta, extension, provenance);
}

static T2Relation
constrain_record_types(
        T2Solver *solver,
        T2Type actual_type,
        T2Type expected_type,
        T2Node const *actual,
        T2Node const *expected,
        char const *provenance,
        bool retain_deferred
)
{
        T2Relation shape = t2_subtype(solver->universe, actual_type, expected_type);
        if (shape == T2_RELATION_NO || shape == T2_RELATION_COMPLEXITY) {
                set_solver_error(
                        solver,
                        shape == T2_RELATION_NO
                            ? "incompatible record shape"
                            : "record comparison exceeded its complexity limit",
                        actual_type,
                        expected_type,
                        provenance
                );
                return shape;
        }

        T2Relation result = T2_RELATION_YES;
        for (size_t i = 0; i + 1 < expected->arity; ++i) {
                T2Node const *wanted = get_node(solver->universe, expected->children[i]);
                T2Node const *have = solver_find_record_field(
                        solver,
                        actual,
                        wanted->text
                );
                T2Presence wanted_presence = (T2Presence)(
                        wanted->payload & T2_FIELD_PRESENCE_MASK
                );
                if (have == NULL && wanted_presence == T2_PRESENCE_REQUIRED) {
                        T2Relation required = require_field_in_row(
                                solver,
                                actual->children[actual->arity - 1],
                                wanted,
                                provenance
                        );
                        result = combine_all(result, required);
                        if (solver->failed) return T2_RELATION_NO;
                        have = solver_find_record_field(solver, actual, wanted->text);
                }
                if (have == NULL) continue;

                bool wanted_writable = (wanted->payload & T2_FIELD_WRITABLE_BIT) != 0;
                result = combine_all(
                        result,
                        constrain_internal(
                                solver,
                                have->children[0],
                                wanted->children[0],
                                provenance,
                                retain_deferred
                        )
                );
                if (wanted_writable && !solver->failed) {
                        result = combine_all(
                                result,
                                constrain_internal(
                                        solver,
                                        wanted->children[0],
                                        have->children[0],
                                        provenance,
                                        retain_deferred
                                )
                        );
                }
                if (solver->failed) return T2_RELATION_NO;
        }

        T2Type expected_tail = expected->children[expected->arity - 1];
        T2Node const *expected_tail_node = get_node(solver->universe, expected_tail);
        if (expected_tail_node->kind != T2_TYPE_ROW_ANY) {
                size_t extra_count = 0;
                T2FieldSpec *extras = calloc(actual->arity - 1, sizeof *extras);
                if (actual->arity > 1 && extras == NULL) {
                        solver->failed = true;
                        snprintf(solver->error, sizeof solver->error, "types2 solver ran out of memory");
                        return T2_RELATION_COMPLEXITY;
                }
                for (size_t i = 0; i + 1 < actual->arity; ++i) {
                        T2Node const *field = get_node(solver->universe, actual->children[i]);
                        if (
                                find_record_field_node(
                                        solver->universe,
                                        expected,
                                        field->text
                                ) == NULL
                        ) extras[extra_count++] = field_spec_from_node(field);
                }
                T2Type remainder = t2_row(
                        solver->universe,
                        extras,
                        extra_count,
                        actual->children[actual->arity - 1]
                );
                free(extras);
                if (remainder == T2_TYPE_INVALID) return T2_RELATION_COMPLEXITY;
                result = combine_all(
                        result,
                        constrain_internal(
                                solver,
                                remainder,
                                expected_tail,
                                provenance,
                                retain_deferred
                        )
                );
        }
        return result;
}

static T2Relation
constrain_mapped_pack_expansion(
        T2Solver *solver,
        T2Node const *actual,
        T2Node const *expected,
        char const *provenance,
        bool retain_deferred,
        bool *handled
)
{
        *handled = false;
        if (
                actual->kind != T2_TYPE_PACK
             || expected->kind != T2_TYPE_PACK_EXPANSION
             || expected->arity != 1
        ) return T2_RELATION_DEFERRED;

        T2Node const *pattern = get_node(
                solver->universe,
                expected->children[0]
        );
        if (pattern == NULL || pattern->kind != T2_TYPE_NOMINAL) {
                return T2_RELATION_DEFERRED;
        }

        size_t pack_index = SIZE_MAX;
        uint32_t pack_root = 0;
        for (size_t i = 0; i < pattern->arity; ++i) {
                uint32_t meta = meta_from_type(solver, pattern->children[i]);
                if (meta == 0) continue;
                meta = find_root(solver, meta);
                if (solver->metas[meta - 1].variable_kind != T2_VARIABLE_PACK) {
                        continue;
                }
                if (pack_index != SIZE_MAX && pack_root != meta) {
                        return T2_RELATION_DEFERRED;
                }
                pack_index = i;
                pack_root = meta;
        }
        if (pack_index == SIZE_MAX) return T2_RELATION_DEFERRED;

        size_t count = (size_t)actual->payload;
        if (actual->arity != count + 1) return T2_RELATION_DEFERRED;
        T2Node const *tail = get_node(
                solver->universe,
                actual->children[count]
        );
        if (tail == NULL || tail->kind != T2_TYPE_PACK_EMPTY) {
                return T2_RELATION_DEFERRED;
        }

        *handled = true;
        T2Type *elements = count == 0 ? NULL : malloc(count * sizeof *elements);
        if (count != 0 && elements == NULL) {
                solver->failed = true;
                snprintf(
                        solver->error,
                        sizeof solver->error,
                        "types2 solver ran out of memory"
                );
                return T2_RELATION_COMPLEXITY;
        }

        T2NominalInfo const *info = find_nominal(
                solver->universe,
                pattern->payload
        );
        T2Relation result = T2_RELATION_YES;
        for (size_t i = 0; i < count; ++i) {
                T2Type item = actual->children[i];
                T2Node const *item_node = get_node(solver->universe, item);
                if (
                        item_node != NULL
                     && (
                                item_node->kind == T2_TYPE_DYNAMIC
                             || item_node->kind == T2_TYPE_ERROR
                        )
                ) {
                        elements[i] = item;
                        continue;
                }

                T2Type projected = t2_nominal_project(
                        solver->universe,
                        item,
                        pattern->payload
                );
                T2Node const *projection = get_node(
                        solver->universe,
                        projected
                );
                if (
                        projection == NULL
                     || projection->kind != T2_TYPE_NOMINAL
                     || projection->payload != pattern->payload
                     || projection->arity != pattern->arity
                ) {
                        free(elements);
                        set_solver_error(
                                solver,
                                "pack element does not satisfy the mapped nominal shape",
                                item,
                                expected->children[0],
                                provenance
                        );
                        return T2_RELATION_NO;
                }
                elements[i] = projection->children[pack_index];

                for (size_t j = 0; j < pattern->arity; ++j) {
                        if (j == pack_index) continue;
                        T2Variance variance = info == NULL
                                            ? T2_INVARIANT
                                            : info->variance[j];
                        T2Relation item_relation;
                        if (variance == T2_COVARIANT) {
                                item_relation = constrain_internal(
                                        solver,
                                        projection->children[j],
                                        pattern->children[j],
                                        provenance,
                                        retain_deferred
                                );
                        } else if (variance == T2_CONTRAVARIANT) {
                                item_relation = constrain_internal(
                                        solver,
                                        pattern->children[j],
                                        projection->children[j],
                                        provenance,
                                        retain_deferred
                                );
                        } else {
                                item_relation = t2_solver_unify(
                                        solver,
                                        projection->children[j],
                                        pattern->children[j],
                                        provenance
                                );
                        }
                        result = combine_all(result, item_relation);
                        if (solver->failed) {
                                free(elements);
                                return T2_RELATION_NO;
                        }
                }
        }

        T2Type sequence = t2_pack(
                solver->universe,
                elements,
                count,
                T2_TYPE_INVALID
        );
        free(elements);
        if (sequence == T2_TYPE_INVALID) return T2_RELATION_COMPLEXITY;

        T2Variance variance = info == NULL
                            ? T2_INVARIANT
                            : info->variance[pack_index];
        T2Type variable = meta_type(solver, pack_root);
        T2Relation sequence_relation;
        if (variance == T2_COVARIANT) {
                sequence_relation = constrain_internal(
                        solver,
                        sequence,
                        variable,
                        provenance,
                        retain_deferred
                );
        } else if (variance == T2_CONTRAVARIANT) {
                sequence_relation = constrain_internal(
                        solver,
                        variable,
                        sequence,
                        provenance,
                        retain_deferred
                );
        } else {
                sequence_relation = t2_solver_unify(
                        solver,
                        sequence,
                        variable,
                        provenance
                );
        }
        return combine_all(result, sequence_relation);
}

static T2Relation
constrain_pack_types(
        T2Solver *solver,
        T2Node const *actual,
        T2Node const *expected,
        char const *provenance,
        bool retain_deferred
)
{
        if (expected->kind == T2_TYPE_PACK_ANY) return T2_RELATION_YES;
        if (actual->kind == T2_TYPE_PACK_EMPTY) {
                if (
                        expected->kind == T2_TYPE_PACK_EMPTY
                     || expected->kind == T2_TYPE_PACK_EXPANSION
                ) return T2_RELATION_YES;
                set_solver_error(
                        solver,
                        "pack lengths are incompatible",
                        T2_TYPE_INVALID,
                        T2_TYPE_INVALID,
                        provenance
                );
                return T2_RELATION_NO;
        }
        if (expected->kind == T2_TYPE_PACK_EMPTY) {
                set_solver_error(
                        solver,
                        "pack lengths are incompatible",
                        T2_TYPE_INVALID,
                        T2_TYPE_INVALID,
                        provenance
                );
                return T2_RELATION_NO;
        }
        if (expected->kind == T2_TYPE_PACK_EXPANSION) {
                bool handled = false;
                T2Relation mapped = constrain_mapped_pack_expansion(
                        solver,
                        actual,
                        expected,
                        provenance,
                        retain_deferred,
                        &handled
                );
                if (handled) return mapped;
                if (actual->kind == T2_TYPE_PACK_EXPANSION) {
                        return constrain_internal(
                                solver,
                                actual->children[0],
                                expected->children[0],
                                provenance,
                                retain_deferred
                        );
                }
                if (actual->kind == T2_TYPE_PACK) {
                        T2Relation result = T2_RELATION_YES;
                        size_t count = (size_t)actual->payload;
                        for (size_t i = 0; i < count; ++i) {
                                result = combine_all(
                                        result,
                                        constrain_internal(
                                                solver,
                                                actual->children[i],
                                                expected->children[0],
                                                provenance,
                                                retain_deferred
                                        )
                                );
                                if (solver->failed) return T2_RELATION_NO;
                        }
                        T2Type expansion = t2_pack_expansion(
                                solver->universe,
                                expected->children[0]
                        );
                        return combine_all(
                                result,
                                constrain_internal(
                                        solver,
                                        actual->children[count],
                                        expansion,
                                        provenance,
                                        retain_deferred
                                )
                        );
                }
        }
        if (actual->kind == T2_TYPE_PACK_EXPANSION) {
                set_solver_error(
                        solver,
                        "an unbounded pack cannot satisfy this fixed pack shape",
                        T2_TYPE_INVALID,
                        T2_TYPE_INVALID,
                        provenance
                );
                return T2_RELATION_NO;
        }
        if (actual->kind != T2_TYPE_PACK || expected->kind != T2_TYPE_PACK) {
                if (
                        actual->kind == T2_TYPE_META
                     || expected->kind == T2_TYPE_META
                     || actual->kind == T2_TYPE_VARIABLE
                     || expected->kind == T2_TYPE_VARIABLE
                ) return T2_RELATION_DEFERRED;
                set_solver_error(
                        solver,
                        "pack constraint has a non-pack operand",
                        T2_TYPE_INVALID,
                        T2_TYPE_INVALID,
                        provenance
                );
                return T2_RELATION_NO;
        }

        size_t actual_count = (size_t)actual->payload;
        size_t expected_count = (size_t)expected->payload;
        size_t common = actual_count < expected_count ? actual_count : expected_count;
        T2Relation result = T2_RELATION_YES;
        for (size_t i = 0; i < common; ++i) {
                result = combine_all(
                        result,
                        constrain_internal(
                                solver,
                                actual->children[i],
                                expected->children[i],
                                provenance,
                                retain_deferred
                        )
                );
                if (solver->failed) return T2_RELATION_NO;
        }

        T2Type actual_tail = actual->children[actual_count];
        T2Type expected_tail = expected->children[expected_count];
        if (actual_count > common) {
                actual_tail = t2_pack(
                        solver->universe,
                        actual->children + common,
                        actual_count - common,
                        actual_tail
                );
        }
        if (expected_count > common) {
                expected_tail = t2_pack(
                        solver->universe,
                        expected->children + common,
                        expected_count - common,
                        expected_tail
                );
        }
        return combine_all(
                result,
                constrain_internal(
                        solver,
                        actual_tail,
                        expected_tail,
                        provenance,
                        retain_deferred
                )
        );
}

static bool solver_types_identical(
        T2Solver *solver,
        T2Type left,
        T2Type right,
        unsigned depth
);

static T2Type
resolve_exact_meta_head(T2Solver *solver, T2Type type, unsigned outer_depth)
{
        for (
                unsigned depth = outer_depth;
                depth <= T2_RELATION_DEPTH_LIMIT;
                ++depth
        ) {
                type = t2_type_resolve_computed(solver->universe, type);
                uint32_t meta = meta_from_type(solver, type);
                if (meta == 0) return type;
                meta = find_root(solver, meta);
                T2Meta const *node = &solver->metas[meta - 1];
                T2Type root = meta_type(solver, meta);
                T2Type exact = node->solution;
                if (
                        exact == T2_TYPE_INVALID
                     && solver_types_identical(
                                solver,
                                node->lower,
                                node->upper,
                                depth + 1
                        )
                ) exact = node->lower;
                if (exact == T2_TYPE_INVALID || exact == root) return root;
                type = exact;
        }
        return type;
}

/* Immutable terms that were distinct when a union was interned can become
 * identical after their embedded metavariables are merged.  The universe
 * deliberately does not rewrite such terms, so recognize this narrow form of
 * solver equality when choosing a union arm.  Bounds are used only when they
 * have collapsed to one exact type; selecting a mere lower or upper bound here
 * would make an ambiguous union choice unsound. */
static bool
solver_types_identical(
        T2Solver *solver,
        T2Type left,
        T2Type right,
        unsigned depth
)
{
        if (depth > T2_RELATION_DEPTH_LIMIT) return false;
        left = resolve_exact_meta_head(solver, left, depth);
        right = resolve_exact_meta_head(solver, right, depth);
        if (left == right) return left != T2_TYPE_INVALID;

        if (
                meta_from_type(solver, left) != 0
             || meta_from_type(solver, right) != 0
        ) return false;

        T2Node const *a = get_node(solver->universe, left);
        T2Node const *b = get_node(solver->universe, right);
        if (
                a == NULL
             || b == NULL
             || a->kind != b->kind
             || a->variable_kind != b->variable_kind
             || a->payload != b->payload
             || a->arity != b->arity
             || (a->text == NULL) != (b->text == NULL)
             || (
                        a->text != NULL
                     && strcmp(a->text, b->text) != 0
                )
        ) return false;
        for (size_t i = 0; i < a->arity; ++i) {
                if (!solver_types_identical(
                        solver,
                        a->children[i],
                        b->children[i],
                        depth + 1
                )) return false;
        }
        return true;
}

static T2Relation
constrain_internal(
        T2Solver *solver,
        T2Type subtype,
        T2Type supertype,
        char const *provenance,
        bool retain_deferred
)
{
        if (solver->failed) return T2_RELATION_NO;
        subtype = resolve_sort_solution(solver, subtype);
        supertype = resolve_sort_solution(solver, supertype);
        if (type_contains_solved_pack_meta(solver, subtype, 0)) {
                subtype = resolve_pack_solutions(solver, subtype, 0);
        }
        if (type_contains_solved_pack_meta(solver, supertype, 0)) {
                supertype = resolve_pack_solutions(solver, supertype, 0);
        }
        if (
                subtype == T2_TYPE_INVALID
             || supertype == T2_TYPE_INVALID
             || solver->failed
        ) return T2_RELATION_COMPLEXITY;
        if (
                subtype == supertype
             || solver_types_identical(solver, subtype, supertype, 0)
        ) return T2_RELATION_YES;

        uint32_t a_meta = meta_from_type(solver, subtype);
        uint32_t b_meta = meta_from_type(solver, supertype);
        T2Node const *a_term = get_node(solver->universe, subtype);
        T2Node const *b_term = get_node(solver->universe, supertype);

        /* Set equations such as a <: a | T and a | T <: a are finite
         * constraints, not recursive types.  The former is tautological; the
         * latter contributes only T <: a.  Reduce the direct self arm before
         * the ordinary metavariable occurs check sees the enclosing union. */
        if (a_meta != 0 && b_term != NULL && b_term->kind == T2_TYPE_UNION) {
                for (size_t i = 0; i < b_term->arity; ++i) {
                        if (solver_types_identical(
                                solver,
                                subtype,
                                b_term->children[i],
                                0
                        )) return T2_RELATION_YES;
                }
        }
        if (b_meta != 0 && a_term != NULL && a_term->kind == T2_TYPE_UNION) {
                T2Relation result = T2_RELATION_YES;
                bool removed_self = false;
                for (size_t i = 0; i < a_term->arity; ++i) {
                        if (solver_types_identical(
                                solver,
                                a_term->children[i],
                                supertype,
                                0
                        )) {
                                removed_self = true;
                                continue;
                        }
                        result = combine_all(
                                result,
                                constrain_internal(
                                        solver,
                                        a_term->children[i],
                                        supertype,
                                        provenance,
                                        retain_deferred
                                )
                        );
                        if (solver->failed) return T2_RELATION_NO;
                }
                if (removed_self) return result;
        }
        if (a_meta != 0 && b_meta != 0) {
                return add_edge(solver, a_meta, b_meta, provenance);
        }
        if (a_meta != 0) {
                T2VariableKind kind = solver->metas[find_root(solver, a_meta) - 1].variable_kind;
                if (kind == T2_VARIABLE_ROW || kind == T2_VARIABLE_PACK) {
                        return bind_sort_meta(solver, a_meta, supertype, provenance);
                }
                return update_upper(solver, a_meta, supertype, provenance);
        }
        if (b_meta != 0) {
                T2VariableKind kind = solver->metas[find_root(solver, b_meta) - 1].variable_kind;
                if (kind == T2_VARIABLE_ROW || kind == T2_VARIABLE_PACK) {
                        return bind_sort_meta(solver, b_meta, subtype, provenance);
                }
                return update_lower(solver, b_meta, subtype, provenance);
        }

        T2Node const *a = a_term;
        T2Node const *b = b_term;
        if (a == NULL || b == NULL) {
                set_solver_error(solver, "invalid type constraint", subtype, supertype, provenance);
                return T2_RELATION_NO;
        }

        if (a->kind == T2_TYPE_UNION) {
                T2Relation result = T2_RELATION_YES;
                for (size_t i = 0; i < a->arity; ++i) {
                        result = combine_all(
                                result,
                                constrain_internal(
                                        solver,
                                        a->children[i],
                                        supertype,
                                        provenance,
                                        retain_deferred
                                )
                        );
                        if (solver->failed) return T2_RELATION_NO;
                }
                return result;
        }
        if (b->kind == T2_TYPE_UNION) {
                /* A proof that needs no solver mutation wins immediately.  In
                 * particular, T <: nil | T must not remain ambiguous merely
                 * because nil <: T is deferred. */
                for (size_t i = 0; i < b->arity; ++i) {
                        if (
                                solver_types_identical(
                                        solver,
                                        subtype,
                                        b->children[i],
                                        0
                                )
                             || t2_subtype(
                                solver->universe,
                                subtype,
                                b->children[i]
                                ) == T2_RELATION_YES
                        ) return T2_RELATION_YES;
                }
                size_t applicable = 0;
                size_t selected = 0;
                for (size_t i = 0; i < b->arity; ++i) {
                        T2SolverMark mark = t2_solver_mark(solver);
                        T2Relation trial = constrain_internal(
                                solver,
                                subtype,
                                b->children[i],
                                provenance,
                                false
                        );
                        bool success = !solver->failed && trial != T2_RELATION_NO;
                        t2_solver_rollback(solver, mark);
                        if (success) {
                                selected = i;
                                applicable += 1;
                        }
                }
                if (applicable == 1) {
                        return constrain_internal(
                                solver,
                                subtype,
                                b->children[selected],
                                provenance,
                                retain_deferred
                        );
                }
                if (applicable != 0 && retain_deferred) {
                        return retain_obligation(solver, subtype, supertype, provenance);
                }
                if (applicable != 0) return T2_RELATION_DEFERRED;
                set_solver_error(
                        solver,
                        "no union arm accepts the subtype",
                        subtype,
                        supertype,
                        provenance
                );
                return T2_RELATION_NO;
        }
        if (b->kind == T2_TYPE_INTERSECTION) {
                T2Relation result = T2_RELATION_YES;
                for (size_t i = 0; i < b->arity; ++i) {
                        result = combine_all(
                                result,
                                constrain_internal(
                                        solver,
                                        subtype,
                                        b->children[i],
                                        provenance,
                                        retain_deferred
                                )
                        );
                        if (solver->failed) return T2_RELATION_NO;
                }
                return result;
        }

        if (a->kind == T2_TYPE_TUPLE && b->kind == T2_TYPE_TUPLE && a->arity == b->arity) {
                return constrain_children(solver, a, b, provenance, retain_deferred);
        }

        if (a->kind == T2_TYPE_FUNCTION && b->kind == T2_TYPE_FUNCTION) {
                return constrain_function_types(
                        solver,
                        subtype,
                        supertype,
                        a,
                        b,
                        provenance,
                        retain_deferred
                );
        }

        if (a->kind == T2_TYPE_RECORD && b->kind == T2_TYPE_RECORD) {
                return constrain_record_types(
                        solver,
                        subtype,
                        supertype,
                        a,
                        b,
                        provenance,
                        retain_deferred
                );
        }

        if (
                a->kind == T2_TYPE_PACK
             || a->kind == T2_TYPE_PACK_EMPTY
             || a->kind == T2_TYPE_PACK_ANY
             || a->kind == T2_TYPE_PACK_EXPANSION
             || b->kind == T2_TYPE_PACK
             || b->kind == T2_TYPE_PACK_EMPTY
             || b->kind == T2_TYPE_PACK_ANY
             || b->kind == T2_TYPE_PACK_EXPANSION
        ) return constrain_pack_types(
                solver,
                a,
                b,
                provenance,
                retain_deferred
        );

        if (
                a->kind == T2_TYPE_NOMINAL
             && b->kind == T2_TYPE_NOMINAL
             && a->payload == b->payload
             && a->arity == b->arity
        ) {
                T2NominalInfo const *info = find_nominal(solver->universe, a->payload);
                T2Relation result = T2_RELATION_YES;
                for (size_t i = 0; i < a->arity; ++i) {
                        T2Variance variance = info == NULL
                                            ? T2_INVARIANT
                                            : info->variance[i];
                        T2Relation item;
                        if (variance == T2_COVARIANT) {
                                item = constrain_internal(
                                        solver,
                                        a->children[i],
                                        b->children[i],
                                        provenance,
                                        retain_deferred
                                );
                        } else if (variance == T2_CONTRAVARIANT) {
                                item = constrain_internal(
                                        solver,
                                        b->children[i],
                                        a->children[i],
                                        provenance,
                                        retain_deferred
                                );
                        } else {
                                item = t2_solver_unify(
                                        solver,
                                        a->children[i],
                                        b->children[i],
                                        provenance
                                );
                        }
                        result = combine_all(result, item);
                        if (solver->failed) return T2_RELATION_NO;
                }
                return result;
        }

        if (a->kind == T2_TYPE_NOMINAL && b->kind == T2_TYPE_NOMINAL) {
                T2AppliedNominal const *applied = find_applied_nominal(
                        solver->universe,
                        subtype
                );
                if (applied != NULL) {
                        for (size_t i = 0; i < applied->supertype_count; ++i) {
                                T2SolverMark mark = t2_solver_mark(solver);
                                T2Relation trial = constrain_internal(
                                        solver,
                                        applied->supertypes[i],
                                        supertype,
                                        provenance,
                                        retain_deferred
                                );
                                if (!solver->failed && trial != T2_RELATION_NO) {
                                        t2_solver_commit(solver, mark);
                                        return trial;
                                }
                                t2_solver_rollback(solver, mark);
                        }
                }
        }

        T2Relation relation = t2_subtype(solver->universe, subtype, supertype);
        if (relation == T2_RELATION_NO) {
                set_solver_error(solver, "constraint failed", subtype, supertype, provenance);
                return relation;
        }
        if (relation == T2_RELATION_DEFERRED && retain_deferred) {
                return retain_obligation(solver, subtype, supertype, provenance);
        }
        if (relation == T2_RELATION_COMPLEXITY) {
                set_solver_error(
                        solver,
                        "subtype comparison exceeded its complexity limit",
                        subtype,
                        supertype,
                        provenance
                );
        }
        return relation;
}

static void
drain_work(T2Solver *solver)
{
        if (solver->draining_work) return;
        solver->draining_work = true;
        solver->drain_epoch += 1;
        if (solver->drain_epoch == 0) {
                for (size_t i = 0; i < solver->edge_count; ++i) {
                        solver->edges[i].self_retry_epoch = 0;
                }
                for (size_t i = 0; i < solver->obligation_count; ++i) {
                        solver->obligations[i].self_retry_epoch = 0;
                }
                solver->drain_epoch = 1;
        }
        while (!solver->failed && solver->work_index < solver->work_count) {
                uint64_t work = solver->work[solver->work_index++];
                solver->active_work = work;
                solver->processing_work = true;
                solver->rerun_active_work = false;
                solver->work_steps += 1;
                if ((work & T2_WATCH_OBLIGATION) != 0) {
                        size_t index = (size_t)(work & ~T2_WATCH_OBLIGATION);
                        if (index >= solver->obligation_count) goto WorkDone;
                        T2Obligation *obligation = &solver->obligations[index];
                        if (!obligation->active) goto WorkDone;
                        T2Predicate predicate = obligation->predicate;
                        T2Relation relation;
                        if (predicate.kind == T2_PREDICATE_SUBTYPE) {
                                relation = constrain_internal(
                                        solver,
                                        predicate.subtype,
                                        predicate.supertype,
                                        predicate.provenance,
                                        false
                                );
                        } else if (solver->predicate_resolver != NULL) {
                                relation = solver->predicate_resolver(
                                        solver->predicate_context,
                                        solver,
                                        &predicate
                                );
                        } else {
                                relation = T2_RELATION_DEFERRED;
                        }
                        obligation = &solver->obligations[index];
                        if (relation == T2_RELATION_YES) {
                                if (!push_undo(solver, (T2Undo) {
                                        .kind = T2_UNDO_OBLIGATION_ACTIVE,
                                        .index = (uint32_t)index,
                                        .old = obligation->active
                                })) break;
                                obligation->active = false;
                        } else if (
                                relation == T2_RELATION_NO
                             && !solver->failed
                        ) {
                                set_solver_error(
                                        solver,
                                        "external predicate failed",
                                        predicate.subtype,
                                        predicate.supertype,
                                        predicate.provenance
                                );
                        }
                } else {
                        size_t index = (size_t)work;
                        if (index >= solver->edge_count) goto WorkDone;
                        T2Edge edge = solver->edges[index];
                        uint32_t sub = find_root(solver, edge.subtype);
                        uint32_t sup = find_root(solver, edge.supertype);
                        if (sub == sup) goto WorkDone;
                        T2Meta const *sub_node = &solver->metas[sub - 1];
                        T2Meta const *sup_node = &solver->metas[sup - 1];
                        if (
                                update_lower(
                                        solver,
                                        sup,
                                        sub_node->lower,
                                        edge.provenance
                                ) == T2_RELATION_NO
                        ) break;
                        if (
                                update_upper(
                                        solver,
                                        sub,
                                        sup_node->upper,
                                        edge.provenance
                                ) == T2_RELATION_NO
                        ) break;
                }
WorkDone:
                solver->processing_work = false;
                if (solver->rerun_active_work && !solver->failed) {
                        solver->rerun_active_work = false;
                        uint64_t *epoch;
                        if ((work & T2_WATCH_OBLIGATION) != 0) {
                                size_t index = (size_t)(
                                        work & ~T2_WATCH_OBLIGATION
                                );
                                epoch = index < solver->obligation_count
                                      ? &solver->obligations[index].self_retry_epoch
                                      : NULL;
                        } else {
                                size_t index = (size_t)work;
                                epoch = index < solver->edge_count
                                      ? &solver->edges[index].self_retry_epoch
                                      : NULL;
                        }
                        if (epoch != NULL && *epoch != solver->drain_epoch) {
                                *epoch = solver->drain_epoch;
                                if (!enqueue(solver, work)) break;
                        }
                }
        }
        solver->draining_work = false;
        solver->processing_work = false;
        solver->rerun_active_work = false;
        solver->active_work = 0;

        if (solver->work_index == solver->work_count) {
                solver->work_index = 0;
                solver->work_count = 0;
        }
}

T2Relation
t2_solver_constrain_subtype(
        T2Solver *solver,
        T2Type subtype,
        T2Type supertype,
        char const *provenance
)
{
        if (solver == NULL || solver->failed) return T2_RELATION_NO;
        uint32_t subtype_meta = meta_from_type(solver, subtype);
        uint32_t supertype_meta = meta_from_type(solver, supertype);
        T2CauseKind cause_kind = T2_CAUSE_PREDICATE;
        if (subtype_meta != 0 && supertype_meta != 0) cause_kind = T2_CAUSE_EDGE;
        else if (subtype_meta != 0) cause_kind = T2_CAUSE_UPPER;
        else if (supertype_meta != 0) cause_kind = T2_CAUSE_LOWER;
        provenance = record_cause(
                solver,
                cause_kind,
                subtype,
                supertype,
                provenance
        );
        if (solver->failed) return T2_RELATION_NO;
        T2Relation relation = constrain_internal(
                solver,
                subtype,
                supertype,
                provenance,
                true
        );
        drain_work(solver);
        return solver->failed ? T2_RELATION_NO : relation;
}

T2Relation
t2_solver_constrain_predicate(
        T2Solver *solver,
        T2Predicate const *predicate
)
{
        if (solver == NULL || predicate == NULL || solver->failed) {
                return T2_RELATION_NO;
        }
        if (predicate->kind == T2_PREDICATE_SUBTYPE) {
                return t2_solver_constrain_subtype(
                        solver,
                        predicate->subtype,
                        predicate->supertype,
                        predicate->provenance
                );
        }
        if (
                get_node(solver->universe, predicate->subtype) == NULL
             || get_node(solver->universe, predicate->supertype) == NULL
             || get_node(solver->universe, predicate->operand) == NULL
        ) return T2_RELATION_NO;

        (void)record_cause(
                solver,
                T2_CAUSE_PREDICATE,
                predicate->subtype,
                predicate->supertype,
                predicate->provenance
        );
        if (solver->failed) return T2_RELATION_NO;
        T2Relation relation = solver->predicate_resolver == NULL
                            ? T2_RELATION_DEFERRED
                            : solver->predicate_resolver(
                                    solver->predicate_context,
                                    solver,
                                    predicate
                              );
        if (relation == T2_RELATION_DEFERRED) {
                relation = retain_predicate(solver, predicate);
        } else if (relation == T2_RELATION_NO && !solver->failed) {
                set_solver_error(
                        solver,
                        "external predicate failed",
                        predicate->subtype,
                        predicate->supertype,
                        predicate->provenance
                );
        }
        drain_work(solver);
        return solver->failed ? T2_RELATION_NO : relation;
}

static T2Relation
merge_meta_roots(
        T2Solver *solver,
        uint32_t left,
        uint32_t right,
        char const *provenance
)
{
        left = find_root(solver, left);
        right = find_root(solver, right);
        if (left == right) return T2_RELATION_YES;

        T2Meta *a = &solver->metas[left - 1];
        T2Meta *b = &solver->metas[right - 1];
        if (
                (a->variable_kind == T2_VARIABLE_ROW) != (b->variable_kind == T2_VARIABLE_ROW)
             || (a->variable_kind == T2_VARIABLE_PACK) != (b->variable_kind == T2_VARIABLE_PACK)
        ) {
                set_solver_error(
                        solver,
                        "cannot equate different variable kinds",
                        meta_type(solver, left),
                        meta_type(solver, right),
                        provenance
                );
                return T2_RELATION_NO;
        }

        T2Type solution = a->solution != T2_TYPE_INVALID ? a->solution : b->solution;
        if (
                a->solution != T2_TYPE_INVALID
             && b->solution != T2_TYPE_INVALID
             && a->solution != b->solution
             && t2_solver_unify(
                    solver,
                    a->solution,
                    b->solution,
                    provenance
                ) == T2_RELATION_NO
        ) return T2_RELATION_NO;

        T2Type lower = t2_join(solver->universe, a->lower, b->lower);
        T2Type upper = t2_meet(solver->universe, a->upper, b->upper);
        T2Relation consistent = t2_subtype(solver->universe, lower, upper);
        if (consistent == T2_RELATION_NO || consistent == T2_RELATION_COMPLEXITY) {
                set_solver_error(solver, "equality has inconsistent bounds", lower, upper, provenance);
                return consistent;
        }

        if (a->rank < b->rank) {
                uint32_t temporary = left;
                left = right;
                right = temporary;
                a = &solver->metas[left - 1];
                b = &solver->metas[right - 1];
        }

        if (!push_undo(solver, (T2Undo) {
                .kind = T2_UNDO_PARENT,
                .index = right,
                .old = b->parent
        })) return T2_RELATION_COMPLEXITY;
        b->parent = left;

        if (a->rank == b->rank) {
                if (!push_undo(solver, (T2Undo) {
                        .kind = T2_UNDO_RANK,
                        .index = left,
                        .old = a->rank
                })) return T2_RELATION_COMPLEXITY;
                a->rank += 1;
        }

        if (
                a->variable_kind != T2_VARIABLE_ROW
             && a->variable_kind != T2_VARIABLE_PACK
             && (
                        a->variable_kind == T2_VARIABLE_WEAK
                     || b->variable_kind == T2_VARIABLE_WEAK
                )
             && a->variable_kind != T2_VARIABLE_WEAK
        ) {
                if (!push_undo(solver, (T2Undo) {
                        .kind = T2_UNDO_VARIABLE_KIND,
                        .index = left,
                        .old = a->variable_kind
                })) return T2_RELATION_COMPLEXITY;
                a->variable_kind = T2_VARIABLE_WEAK;
        }

        if (!push_undo(solver, (T2Undo) {
                .kind = T2_UNDO_LOWER,
                .index = left,
                .old = a->lower
        })) return T2_RELATION_COMPLEXITY;
        if (!push_undo(solver, (T2Undo) {
                .kind = T2_UNDO_UPPER,
                .index = left,
                .old = a->upper
        })) return T2_RELATION_COMPLEXITY;
        a->lower = lower;
        a->upper = upper;
        if (!push_undo(solver, (T2Undo) {
                .kind = T2_UNDO_SOLUTION,
                .index = left,
                .old = a->solution
        })) return T2_RELATION_COMPLEXITY;
        a->solution = solution;

        for (size_t i = 0; i < b->watchers.count; ++i) {
                if (!push_watch(solver, left, b->watchers.items[i])) {
                        return T2_RELATION_COMPLEXITY;
                }
        }
        wake_meta(solver, left);
        return T2_RELATION_YES;
}

T2Relation
t2_solver_unify(
        T2Solver *solver,
        T2Type left,
        T2Type right,
        char const *provenance
)
{
        if (solver == NULL || solver->failed) return T2_RELATION_NO;
        if (left == right) return T2_RELATION_YES;

        provenance = record_cause(
                solver,
                T2_CAUSE_EQUALITY,
                left,
                right,
                provenance
        );
        if (solver->failed) return T2_RELATION_NO;

        uint32_t a_meta = meta_from_type(solver, left);
        uint32_t b_meta = meta_from_type(solver, right);
        T2Relation result;

        if (a_meta != 0 && b_meta != 0) {
                result = merge_meta_roots(solver, a_meta, b_meta, provenance);
        } else {
                result = constrain_internal(solver, left, right, provenance, true);
                if (!solver->failed) {
                        result = combine_all(
                                result,
                                constrain_internal(solver, right, left, provenance, true)
                        );
                }
        }

        drain_work(solver);
        return solver->failed ? T2_RELATION_NO : result;
}

T2Type
t2_solver_lower_bound(T2Solver *solver, T2Type meta)
{
        if (solver == NULL) return T2_TYPE_INVALID;
        uint32_t id = meta_from_type(solver, meta);
        if (id == 0) return T2_TYPE_INVALID;
        id = find_root(solver, id);
        return solver->metas[id - 1].lower;
}

T2Type
t2_solver_upper_bound(T2Solver *solver, T2Type meta)
{
        if (solver == NULL) return T2_TYPE_INVALID;
        uint32_t id = meta_from_type(solver, meta);
        if (id == 0) return T2_TYPE_INVALID;
        id = find_root(solver, id);
        return solver->metas[id - 1].upper;
}

T2Type
t2_solver_solution(
        T2Solver *solver,
        T2Type meta,
        T2SolutionPreference preference
)
{
        if (solver == NULL) return T2_TYPE_INVALID;
        uint32_t id = meta_from_type(solver, meta);
        if (id == 0) return T2_TYPE_INVALID;
        id = find_root(solver, id);
        if (solver->metas[id - 1].solution != T2_TYPE_INVALID) {
                return solver->metas[id - 1].solution;
        }
        T2Type lower = t2_solver_lower_bound(solver, meta);
        T2Type upper = t2_solver_upper_bound(solver, meta);
        if (lower == T2_TYPE_INVALID || upper == T2_TYPE_INVALID) {
                return T2_TYPE_INVALID;
        }

        T2Type never = t2_primitive(solver->universe, T2_TYPE_NEVER);
        T2Type any = t2_primitive(solver->universe, T2_TYPE_ANY);

        if (preference == T2_PREFER_UPPER_BOUND) {
                if (upper != any) return upper;
                if (lower != never) return lower;
        } else {
                if (lower != never) return lower;
                if (upper != any) return upper;
        }
        return meta;
}

bool
t2_solver_failed(T2Solver const *solver)
{
        return solver == NULL || solver->failed;
}

char const *
t2_solver_error(T2Solver const *solver)
{
        return solver == NULL ? "invalid types2 solver" : solver->error;
}

static char *
solver_explain_from(T2Solver const *solver, size_t cause_start)
{
        if (solver == NULL) return copy_string("invalid types2 solver");
        if (cause_start > solver->cause_count) cause_start = solver->cause_count;

        T2StringBuffer buffer = {0};
        if (solver->error[0] != '\0') {
                buffer_text(&buffer, solver->error);
                buffer_text(&buffer, "\n");
        }
        for (size_t i = cause_start; i < solver->cause_count; ++i) {
                T2Cause const *cause = &solver->causes[i];
                char const *kind = "predicate";
                switch (cause->kind) {
                case T2_CAUSE_LOWER: kind = "lower bound"; break;
                case T2_CAUSE_UPPER: kind = "upper bound"; break;
                case T2_CAUSE_EDGE: kind = "subtype edge"; break;
                case T2_CAUSE_EQUALITY: kind = "equality"; break;
                case T2_CAUSE_PREDICATE: break;
                }
                char *left = t2_type_string(solver->universe, cause->left);
                char *right = t2_type_string(solver->universe, cause->right);
                buffer_format(
                        &buffer,
                        "%s: %s <: %s",
                        kind,
                        left == NULL ? "<type>" : left,
                        right == NULL ? "<type>" : right
                );
                if (cause->provenance != NULL) {
                        buffer_text(&buffer, " from ");
                        buffer_text(&buffer, cause->provenance);
                }
                buffer_text(&buffer, "\n");
                free(left);
                free(right);
        }
        if (buffer.failed) {
                free(buffer.items);
                return NULL;
        }
        return buffer.items == NULL ? copy_string("") : buffer.items;
}

char *
t2_solver_explain(T2Solver const *solver)
{
        return solver_explain_from(solver, 0);
}

char *
t2_solver_explain_since(T2Solver const *solver, T2SolverMark mark)
{
        return solver_explain_from(solver, mark.cause_count);
}

size_t
t2_solver_pending_obligations(T2Solver const *solver)
{
        if (solver == NULL) return 0;
        size_t count = 0;
        for (size_t i = 0; i < solver->obligation_count; ++i) {
                count += solver->obligations[i].active;
        }
        return count;
}

bool
t2_solver_pending_obligation(
        T2Solver const *solver,
        size_t index,
        T2Predicate *predicate
)
{
        if (solver == NULL || predicate == NULL) return false;
        for (size_t i = 0; i < solver->obligation_count; ++i) {
                T2Obligation const *obligation = &solver->obligations[i];
                if (!obligation->active) continue;
                if (index-- != 0) continue;
                *predicate = obligation->predicate;
                return true;
        }
        return false;
}

size_t
t2_solver_meta_count(T2Solver const *solver)
{
        return solver == NULL ? 0 : solver->meta_count;
}

size_t
t2_solver_edge_count(T2Solver const *solver)
{
        return solver == NULL ? 0 : solver->edge_count;
}

uint64_t
t2_solver_work_steps(T2Solver const *solver)
{
        return solver == NULL ? 0 : solver->work_steps;
}

T2SolverMark
t2_solver_mark(T2Solver *solver)
{
        if (solver == NULL) return (T2SolverMark){0};
        T2SolverMark mark = {
                .undo_count = solver->undo_count,
                .meta_count = solver->meta_count,
                .edge_count = solver->edge_count,
                .obligation_count = solver->obligation_count,
                .work_count = solver->work_count,
                .work_index = solver->work_index,
                .cause_count = solver->cause_count,
                .transaction_depth = solver->transaction_depth,
                .failed = solver->failed
        };
        solver->transaction_depth += 1;
        return mark;
}

void
t2_solver_commit(T2Solver *solver, T2SolverMark mark)
{
        if (solver == NULL || solver->transaction_depth != mark.transaction_depth + 1) {
                return;
        }
        solver->transaction_depth = mark.transaction_depth;
        if (solver->transaction_depth == 0) solver->undo_count = 0;
}

bool
t2_solver_cancel_obligations_since(T2Solver *solver, T2SolverMark mark)
{
        if (
                solver == NULL
             || solver->transaction_depth != mark.transaction_depth + 1
             || mark.obligation_count > solver->obligation_count
        ) return false;

        for (size_t i = mark.obligation_count; i < solver->obligation_count; ++i) {
                T2Obligation *obligation = &solver->obligations[i];
                if (!obligation->active) continue;
                if (!push_undo(solver, (T2Undo) {
                        .kind = T2_UNDO_OBLIGATION_ACTIVE,
                        .index = (uint32_t)i,
                        .old = obligation->active
                })) return false;
                obligation->active = false;
        }
        return true;
}

void
t2_solver_rollback(T2Solver *solver, T2SolverMark mark)
{
        if (solver == NULL || solver->transaction_depth != mark.transaction_depth + 1) {
                return;
        }

        while (solver->undo_count > mark.undo_count) {
                T2Undo undo = solver->undo[--solver->undo_count];
                switch (undo.kind) {
                case T2_UNDO_PARENT:
                        solver->metas[undo.index - 1].parent = (uint32_t)undo.old;
                        break;
                case T2_UNDO_RANK:
                        solver->metas[undo.index - 1].rank = (uint8_t)undo.old;
                        break;
                case T2_UNDO_VARIABLE_KIND:
                        solver->metas[undo.index - 1].variable_kind = (T2VariableKind)undo.old;
                        break;
                case T2_UNDO_LOWER:
                        solver->metas[undo.index - 1].lower = (T2Type)undo.old;
                        break;
                case T2_UNDO_UPPER:
                        solver->metas[undo.index - 1].upper = (T2Type)undo.old;
                        break;
                case T2_UNDO_SOLUTION:
                        solver->metas[undo.index - 1].solution = (T2Type)undo.old;
                        break;
                case T2_UNDO_WATCH_COUNT:
                        solver->metas[undo.index - 1].watchers.count = (size_t)undo.old;
                        break;
                case T2_UNDO_OBLIGATION_ACTIVE:
                        solver->obligations[undo.index].active = undo.old;
                        break;
                }
        }

        for (size_t i = mark.meta_count; i < solver->meta_count; ++i) {
                free(solver->metas[i].watchers.items);
                free(solver->metas[i].provenance);
                memset(&solver->metas[i], 0, sizeof solver->metas[i]);
        }

        for (size_t i = mark.cause_count; i < solver->cause_count; ++i) {
                free(solver->causes[i].provenance);
                memset(&solver->causes[i], 0, sizeof solver->causes[i]);
        }

        for (size_t i = mark.obligation_count; i < solver->obligation_count; ++i) {
                free(solver->obligations[i].name);
                free(solver->obligations[i].provenance);
                memset(&solver->obligations[i], 0, sizeof solver->obligations[i]);
        }

        solver->meta_count = mark.meta_count;
        solver->edge_count = mark.edge_count;
        solver->obligation_count = mark.obligation_count;
        solver->work_count = mark.work_count;
        solver->work_index = mark.work_index;
        solver->cause_count = mark.cause_count;
        solver->transaction_depth = mark.transaction_depth;
        solver->failed = mark.failed;
        if (!solver->failed) solver->error[0] = '\0';
        if (solver->transaction_depth == 0) solver->undo_count = 0;
}

T2Scheme *
t2_scheme_new(
        T2Universe *universe,
        T2Quantifier const *quantifiers,
        size_t quantifier_count,
        T2Type body,
        T2Predicate const *predicates,
        size_t predicate_count
)
{
        if (
                universe == NULL
             || get_node(universe, body) == NULL
             || (quantifier_count != 0 && quantifiers == NULL)
             || (predicate_count != 0 && predicates == NULL)
        ) return NULL;

        for (size_t i = 0; i < quantifier_count; ++i) {
                if (
                        quantifiers[i].kind == T2_VARIABLE_RIGID
                     || quantifiers[i].kind == T2_VARIABLE_WEAK
                ) return NULL;
                for (size_t j = 0; j < i; ++j) {
                        if (quantifiers[j].id == quantifiers[i].id) return NULL;
                }
        }
        for (size_t i = 0; i < predicate_count; ++i) {
                if (
                        get_node(universe, predicates[i].subtype) == NULL
                     || get_node(universe, predicates[i].supertype) == NULL
                     || (
                                predicates[i].kind != T2_PREDICATE_SUBTYPE
                             && get_node(universe, predicates[i].operand) == NULL
                        )
                ) return NULL;
        }

        T2Scheme *scheme = calloc(1, sizeof *scheme);
        if (scheme == NULL) return NULL;
        scheme->universe = universe;
        scheme->body = body;

        if (quantifier_count != 0) {
                scheme->quantifiers = malloc(quantifier_count * sizeof *scheme->quantifiers);
                if (scheme->quantifiers == NULL) goto Fail;
                memcpy(
                        scheme->quantifiers,
                        quantifiers,
                        quantifier_count * sizeof *scheme->quantifiers
                );
                scheme->quantifier_count = quantifier_count;
        }
        if (predicate_count != 0) {
                scheme->predicates = calloc(predicate_count, sizeof *scheme->predicates);
                if (scheme->predicates == NULL) goto Fail;
                scheme->predicate_count = predicate_count;
                for (size_t i = 0; i < predicate_count; ++i) {
                        scheme->predicates[i] = predicates[i];
                        scheme->predicates[i].name = copy_string(
                                predicates[i].name
                        );
                        scheme->predicates[i].provenance = copy_string(
                                predicates[i].provenance
                        );
                        if (
                                (
                                        predicates[i].name != NULL
                                     && scheme->predicates[i].name == NULL
                                )
                             || (
                                        predicates[i].provenance != NULL
                                     && scheme->predicates[i].provenance == NULL
                                )
                        ) goto Fail;
                }
        }
        return scheme;

Fail:
        t2_scheme_free(scheme);
        return NULL;
}

void
t2_scheme_free(T2Scheme *scheme)
{
        if (scheme == NULL) return;
        for (size_t i = 0; i < scheme->predicate_count; ++i) {
                free((char *)scheme->predicates[i].name);
                free((char *)scheme->predicates[i].provenance);
        }
        free(scheme->predicates);
        free(scheme->quantifiers);
        free(scheme);
}

size_t
t2_scheme_quantifier_count(T2Scheme const *scheme)
{
        return scheme == NULL ? 0 : scheme->quantifier_count;
}

bool
t2_scheme_quantifier(
        T2Scheme const *scheme,
        size_t index,
        T2Quantifier *quantifier
)
{
        if (scheme == NULL || quantifier == NULL || index >= scheme->quantifier_count) {
                return false;
        }
        *quantifier = scheme->quantifiers[index];
        return true;
}

T2Type
t2_scheme_body(T2Scheme const *scheme)
{
        return scheme == NULL ? T2_TYPE_INVALID : scheme->body;
}

size_t
t2_scheme_predicate_count(T2Scheme const *scheme)
{
        return scheme == NULL ? 0 : scheme->predicate_count;
}

bool
t2_scheme_predicate(
        T2Scheme const *scheme,
        size_t index,
        T2Predicate *predicate
)
{
        if (scheme == NULL || predicate == NULL || index >= scheme->predicate_count) {
                return false;
        }
        *predicate = scheme->predicates[index];
        return true;
}

typedef struct t2_instantiated_node {
        T2Type source;
        T2Type result;
} T2InstantiatedNode;

typedef struct t2_binder_substitution {
        uint32_t source;
        uint32_t result;
} T2BinderSubstitution;

typedef struct t2_instantiation {
        T2Scheme const *scheme;
        T2Solver *solver;
        T2Type *replacements;
        T2InstantiatedNode *nodes;
        size_t node_count;
        size_t node_capacity;
        T2BinderSubstitution *binders;
        size_t binder_count;
        size_t binder_capacity;
        bool failed;
} T2Instantiation;

static bool
collect_generalization_polarity(
        T2Solver *solver,
        T2Type type,
        unsigned polarity,
        unsigned *polarities,
        unsigned depth
)
{
        if (depth > T2_RELATION_DEPTH_LIMIT) return false;
        uint32_t meta = meta_from_type(solver, type);
        if (meta != 0) {
                meta = find_root(solver, meta);
                T2Meta const *node = &solver->metas[meta - 1];
                if (node->solution != T2_TYPE_INVALID) {
                        return collect_generalization_polarity(
                                solver,
                                node->solution,
                                polarity,
                                polarities,
                                depth + 1
                        );
                }
                polarities[meta - 1] |= polarity;
                return true;
        }

        T2Node const *node = get_node(solver->universe, type);
        if (node == NULL) return false;
        if (node->kind == T2_TYPE_NOMINAL) {
                T2NominalInfo const *nominal = find_nominal(
                        solver->universe,
                        node->payload
                );
                if (nominal == NULL) return false;
                for (size_t i = 0; i < node->arity; ++i) {
                        unsigned child = polarity;
                        if (nominal->variance[i] == T2_CONTRAVARIANT) {
                                child = flip_polarity(polarity);
                        } else if (nominal->variance[i] == T2_INVARIANT) {
                                child = T2_POLARITY_POSITIVE | T2_POLARITY_NEGATIVE;
                        }
                        if (!collect_generalization_polarity(
                                solver,
                                node->children[i],
                                child,
                                polarities,
                                depth + 1
                        )) return false;
                }
                return true;
        }
        if (node->kind == T2_TYPE_FUNCTION) {
                size_t count = (size_t)node->payload;
                for (size_t i = 0; i < count; ++i) {
                        T2Node const *parameter = get_node(
                                solver->universe,
                                node->children[i]
                        );
                        if (!collect_generalization_polarity(
                                solver,
                                parameter->children[0],
                                flip_polarity(polarity),
                                polarities,
                                depth + 1
                        )) return false;
                }
                return collect_generalization_polarity(
                        solver,
                        node->children[count],
                        polarity,
                        polarities,
                        depth + 1
                ) && collect_generalization_polarity(
                        solver,
                        node->children[count + 1],
                        polarity,
                        polarities,
                        depth + 1
                ) && collect_generalization_polarity(
                        solver,
                        node->children[count + 2],
                        flip_polarity(polarity),
                        polarities,
                        depth + 1
                );
        }
        if (node->kind == T2_TYPE_RECORD || node->kind == T2_TYPE_ROW) {
                for (size_t i = 0; i + 1 < node->arity; ++i) {
                        T2Node const *field = get_node(
                                solver->universe,
                                node->children[i]
                        );
                        unsigned child = (field->payload & T2_FIELD_WRITABLE_BIT)
                                       ? T2_POLARITY_POSITIVE | T2_POLARITY_NEGATIVE
                                       : polarity;
                        if (!collect_generalization_polarity(
                                solver,
                                field->children[0],
                                child,
                                polarities,
                                depth + 1
                        )) return false;
                }
                return collect_generalization_polarity(
                        solver,
                        node->children[node->arity - 1],
                        polarity,
                        polarities,
                        depth + 1
                );
        }
        for (size_t i = 0; i < node->arity; ++i) {
                if (!collect_generalization_polarity(
                        solver,
                        node->children[i],
                        polarity,
                        polarities,
                        depth + 1
                )) return false;
        }
        return true;
}

static bool
type_touches_marked_meta(
        T2Solver *solver,
        T2Type type,
        unsigned const *marks,
        unsigned depth
)
{
        if (depth > T2_RELATION_DEPTH_LIMIT) return false;
        uint32_t meta = meta_from_type(solver, type);
        if (meta != 0) {
                meta = find_root(solver, meta);
                T2Meta const *node = &solver->metas[meta - 1];
                if (node->solution != T2_TYPE_INVALID) {
                        return type_touches_marked_meta(
                                solver,
                                node->solution,
                                marks,
                                depth + 1
                        );
                }
                return marks[meta - 1] != 0;
        }
        T2Node const *node = get_node(solver->universe, type);
        if (node == NULL) return false;
        for (size_t i = 0; i < node->arity; ++i) {
                if (type_touches_marked_meta(
                        solver,
                        node->children[i],
                        marks,
                        depth + 1
                )) return true;
        }
        return false;
}

static bool
type_contains_variable(
        T2Solver *solver,
        T2Type type,
        T2VariableKind variable_kind,
        uint32_t variable_id,
        unsigned depth
)
{
        if (depth > T2_RELATION_DEPTH_LIMIT) return false;
        uint32_t meta = meta_from_type(solver, type);
        if (meta != 0) {
                meta = find_root(solver, meta);
                T2Type solution = solver->metas[meta - 1].solution;
                return solution != T2_TYPE_INVALID
                    && type_contains_variable(
                            solver,
                            solution,
                            variable_kind,
                            variable_id,
                            depth + 1
                       );
        }

        T2Node const *node = get_node(solver->universe, type);
        if (node == NULL) return false;
        if (
                node->kind == T2_TYPE_VARIABLE
             && node->variable_kind == variable_kind
             && node->payload == variable_id
        ) return true;
        for (size_t i = 0; i < node->arity; ++i) {
                if (type_contains_variable(
                        solver,
                        node->children[i],
                        variable_kind,
                        variable_id,
                        depth + 1
                )) return true;
        }
        return false;
}

static bool
types_share_variable(
        T2Solver *solver,
        T2Type exported,
        T2Type candidate,
        unsigned depth
)
{
        if (depth > T2_RELATION_DEPTH_LIMIT) return false;
        uint32_t meta = meta_from_type(solver, exported);
        if (meta != 0) {
                meta = find_root(solver, meta);
                T2Type solution = solver->metas[meta - 1].solution;
                return solution != T2_TYPE_INVALID
                    && types_share_variable(
                            solver,
                            solution,
                            candidate,
                            depth + 1
                       );
        }

        T2Node const *node = get_node(solver->universe, exported);
        if (node == NULL) return false;
        if (node->kind == T2_TYPE_VARIABLE) {
                return type_contains_variable(
                        solver,
                        candidate,
                        node->variable_kind,
                        (uint32_t)node->payload,
                        0
                );
        }
        for (size_t i = 0; i < node->arity; ++i) {
                if (types_share_variable(
                        solver,
                        node->children[i],
                        candidate,
                        depth + 1
                )) return true;
        }
        return false;
}

static bool
predicate_shares_exported_variable(
        T2Solver *solver,
        T2Type exported,
        T2Predicate const *predicate
)
{
        return types_share_variable(solver, exported, predicate->subtype, 0)
            || types_share_variable(solver, exported, predicate->supertype, 0)
            || (
                       predicate->operand != T2_TYPE_INVALID
                    && types_share_variable(
                            solver,
                            exported,
                            predicate->operand,
                            0
                       )
               );
}

static bool
close_generalization_constraints(T2Solver *solver, unsigned *polarities)
{
        if (solver->meta_count == 0) return true;
        unsigned *previous = malloc(solver->meta_count * sizeof *previous);
        if (previous == NULL) return false;

        size_t remaining = solver->meta_count * 2 + 1;
        bool changed;
        do {
                memcpy(
                        previous,
                        polarities,
                        solver->meta_count * sizeof *previous
                );
                for (size_t i = 0; i < solver->meta_count; ++i) {
                        uint32_t root = find_root(solver, (uint32_t)i + 1);
                        if (root != i + 1 || polarities[i] == 0) continue;
                        T2Meta const *meta = &solver->metas[i];
                        unsigned polarity = polarities[i];
                        if (!collect_generalization_polarity(
                                solver,
                                meta->lower,
                                polarity,
                                polarities,
                                0
                        ) || !collect_generalization_polarity(
                                solver,
                                meta->upper,
                                polarity,
                                polarities,
                                0
                        )) goto Fail;
                }
                for (size_t i = 0; i < solver->edge_count; ++i) {
                        uint32_t subtype = find_root(solver, solver->edges[i].subtype);
                        uint32_t supertype = find_root(solver, solver->edges[i].supertype);
                        unsigned connected = polarities[subtype - 1]
                                           | polarities[supertype - 1];
                        if (connected == 0) continue;
                        polarities[subtype - 1] |= connected;
                        polarities[supertype - 1] |= connected;
                }
                for (size_t i = 0; i < solver->obligation_count; ++i) {
                        T2Obligation const *obligation = &solver->obligations[i];
                        if (!obligation->active) continue;
                        T2Predicate const *predicate = &obligation->predicate;
                        if (
                                !type_touches_marked_meta(
                                        solver,
                                        predicate->subtype,
                                        polarities,
                                        0
                                )
                             && !type_touches_marked_meta(
                                        solver,
                                        predicate->supertype,
                                        polarities,
                                        0
                                )
                             && (
                                        predicate->operand == T2_TYPE_INVALID
                                     || !type_touches_marked_meta(
                                                solver,
                                                predicate->operand,
                                                polarities,
                                                0
                                        )
                                )
                        ) continue;
                        if (!collect_generalization_polarity(
                                solver,
                                predicate->subtype,
                                T2_POLARITY_POSITIVE | T2_POLARITY_NEGATIVE,
                                polarities,
                                0
                        ) || !collect_generalization_polarity(
                                solver,
                                predicate->supertype,
                                T2_POLARITY_POSITIVE | T2_POLARITY_NEGATIVE,
                                polarities,
                                0
                        )) goto Fail;
                        if (
                                predicate->operand != T2_TYPE_INVALID
                             && !collect_generalization_polarity(
                                        solver,
                                        predicate->operand,
                                        T2_POLARITY_POSITIVE | T2_POLARITY_NEGATIVE,
                                        polarities,
                                        0
                                )
                        ) goto Fail;
                }
                changed = memcmp(
                        previous,
                        polarities,
                        solver->meta_count * sizeof *previous
                ) != 0;
        } while (changed && remaining-- != 0);

        free(previous);
        return !changed;

Fail:
        free(previous);
        return false;
}

static bool
type_touches_replacement(
        T2Solver *solver,
        T2Type type,
        T2Type const *replacements,
        unsigned depth
)
{
        if (depth > T2_RELATION_DEPTH_LIMIT) return false;
        uint32_t meta = meta_from_type(solver, type);
        if (meta != 0) {
                meta = find_root(solver, meta);
                if (replacements[meta - 1] != T2_TYPE_INVALID) return true;
                T2Type solution = solver->metas[meta - 1].solution;
                return solution != T2_TYPE_INVALID
                    && type_touches_replacement(
                            solver,
                            solution,
                            replacements,
                            depth + 1
                       );
        }
        T2Node const *node = get_node(solver->universe, type);
        if (node == NULL) return false;
        for (size_t i = 0; i < node->arity; ++i) {
                if (type_touches_replacement(
                        solver,
                        node->children[i],
                        replacements,
                        depth + 1
                )) return true;
        }
        return false;
}

static bool
type_contains_solver_meta(T2Solver *solver, T2Type type, unsigned depth)
{
        if (depth > T2_RELATION_DEPTH_LIMIT) return true;
        if (meta_from_type(solver, type) != 0) return true;
        T2Node const *node = get_node(solver->universe, type);
        if (node == NULL) return true;
        for (size_t i = 0; i < node->arity; ++i) {
                if (type_contains_solver_meta(
                        solver,
                        node->children[i],
                        depth + 1
                )) return true;
        }
        return false;
}

typedef struct t2_generalization_entry {
        T2Type source;
        T2Type result;
} T2GeneralizationEntry;

typedef struct t2_generalization {
        T2Solver *solver;
        T2Type *replacements;
        T2GeneralizationEntry *entries;
        size_t count;
        size_t capacity;
        T2BinderSubstitution *binders;
        size_t binder_count;
        size_t binder_capacity;
} T2Generalization;

static T2Type generalize_type(T2Generalization *generalization, T2Type source);

static T2Type
generalize_recursive(T2Generalization *generalization, T2Node const *node)
{
        T2Universe *universe = generalization->solver->universe;
        uint32_t binder = t2_universe_fresh_recursive_binder(universe);
        if (binder == 0) return T2_TYPE_INVALID;
        if (!reserve_array(
                (void **)&generalization->binders,
                &generalization->binder_capacity,
                generalization->binder_count + 1,
                sizeof *generalization->binders
        )) return T2_TYPE_INVALID;
        size_t mark = generalization->binder_count;
        generalization->binders[generalization->binder_count++] = (T2BinderSubstitution) {
                .source = (uint32_t)node->payload,
                .result = binder
        };
        T2Type body = generalize_type(generalization, node->children[0]);
        generalization->binder_count = mark;
        return body == T2_TYPE_INVALID
             ? body
             : t2_recursive(universe, binder, body);
}

static T2Type
generalize_type(T2Generalization *generalization, T2Type source)
{
        T2Solver *solver = generalization->solver;
        uint32_t meta = meta_from_type(solver, source);
        if (meta != 0) {
                meta = find_root(solver, meta);
                if (generalization->replacements[meta - 1] != T2_TYPE_INVALID) {
                        return generalization->replacements[meta - 1];
                }
                T2Type solution = solver->metas[meta - 1].solution;
                return solution == T2_TYPE_INVALID
                     ? meta_type(solver, meta)
                     : generalize_type(generalization, solution);
        }

        T2Node const *node = get_node(solver->universe, source);
        if (node == NULL) return T2_TYPE_INVALID;
        if (node->kind == T2_TYPE_RECURSIVE_VARIABLE) {
                for (size_t i = generalization->binder_count; i != 0; --i) {
                        T2BinderSubstitution const *binder = &generalization->binders[i - 1];
                        if (binder->source == node->payload) {
                                return t2_recursive_variable(
                                        solver->universe,
                                        binder->result
                                );
                        }
                }
                return source;
        }
        if (node->kind == T2_TYPE_RECURSIVE) {
                return generalize_recursive(generalization, node);
        }
        for (size_t i = 0; i < generalization->count; ++i) {
                if (generalization->entries[i].source == source) {
                        return generalization->entries[i].result;
                }
        }
        if (node->arity == 0) return source;

        T2Type *children = malloc(node->arity * sizeof *children);
        if (children == NULL) return T2_TYPE_INVALID;
        bool changed = false;
        for (size_t i = 0; i < node->arity; ++i) {
                children[i] = generalize_type(generalization, node->children[i]);
                if (children[i] == T2_TYPE_INVALID) {
                        free(children);
                        return T2_TYPE_INVALID;
                }
                changed |= children[i] != node->children[i];
        }
        T2Type result = changed
                      ? rebuild_type(solver->universe, node, children)
                      : source;
        free(children);
        if (result == T2_TYPE_INVALID) return result;
        if (!reserve_array(
                (void **)&generalization->entries,
                &generalization->capacity,
                generalization->count + 1,
                sizeof *generalization->entries
        )) return T2_TYPE_INVALID;
        generalization->entries[generalization->count++] = (T2GeneralizationEntry) {
                .source = source,
                .result = result
        };
        return result;
}

static T2Scheme *
solver_generalize(
        T2Solver *solver,
        T2Type type,
        T2Type const *environment,
        size_t environment_count,
        uint32_t binding_level,
        bool expansive,
        size_t scoped_obligation_start
)
{
        if (
                solver == NULL
             || solver->failed
             || get_node(solver->universe, type) == NULL
             || (environment_count != 0 && environment == NULL)
        ) return NULL;

        size_t count = solver->meta_count;
        unsigned *polarities = calloc(count, sizeof *polarities);
        bool *environment_free = calloc(count, sizeof *environment_free);
        T2Type *replacements = calloc(count, sizeof *replacements);
        if (
                count != 0
             && (polarities == NULL || environment_free == NULL || replacements == NULL)
        ) goto Fail;
        if (!collect_generalization_polarity(
                solver,
                type,
                T2_POLARITY_POSITIVE,
                polarities,
                0
        )) goto Fail;
        if (scoped_obligation_start != SIZE_MAX) {
                for (
                        size_t i = scoped_obligation_start;
                        i < solver->obligation_count;
                        ++i
                ) {
                        T2Obligation const *obligation = &solver->obligations[i];
                        if (!obligation->active) continue;
                        T2Predicate const *predicate = &obligation->predicate;
                        if (!predicate_shares_exported_variable(
                                solver,
                                type,
                                predicate
                        )) continue;
                        if (!collect_generalization_polarity(
                                solver,
                                predicate->subtype,
                                T2_POLARITY_POSITIVE | T2_POLARITY_NEGATIVE,
                                polarities,
                                0
                        ) || !collect_generalization_polarity(
                                solver,
                                predicate->supertype,
                                T2_POLARITY_POSITIVE | T2_POLARITY_NEGATIVE,
                                polarities,
                                0
                        )) goto Fail;
                        if (
                                predicate->operand != T2_TYPE_INVALID
                             && !collect_generalization_polarity(
                                    solver,
                                    predicate->operand,
                                    T2_POLARITY_POSITIVE | T2_POLARITY_NEGATIVE,
                                    polarities,
                                    0
                                )
                        ) goto Fail;
                }
        }
        if (!close_generalization_constraints(solver, polarities)) goto Fail;

        unsigned *environment_marks = calloc(count, sizeof *environment_marks);
        if (count != 0 && environment_marks == NULL) goto Fail;
        for (size_t i = 0; i < environment_count; ++i) {
                if (!collect_generalization_polarity(
                        solver,
                        environment[i],
                        T2_POLARITY_POSITIVE | T2_POLARITY_NEGATIVE,
                        environment_marks,
                        0
                )) {
                        free(environment_marks);
                        goto Fail;
                }
        }
        if (!close_generalization_constraints(solver, environment_marks)) {
                free(environment_marks);
                goto Fail;
        }
        for (size_t i = 0; i < count; ++i) {
                environment_free[i] = environment_marks[i] == 0;
        }
        free(environment_marks);

        size_t quantifier_count = 0;
        for (size_t i = 0; i < count; ++i) {
                if (find_root(solver, (uint32_t)i + 1) != i + 1) continue;
                T2Meta const *meta = &solver->metas[i];
                if (
                        polarities[i] == 0
                     || !environment_free[i]
                     || meta->level <= binding_level
                     || meta->variable_kind == T2_VARIABLE_WEAK
                     || meta->solution != T2_TYPE_INVALID
                     || (
                                expansive
                             && polarities[i] != T2_POLARITY_POSITIVE
                        )
                ) continue;
                quantifier_count += 1;
        }

        T2Quantifier *quantifiers = quantifier_count == 0
                                  ? NULL
                                  : malloc(quantifier_count * sizeof *quantifiers);
        if (quantifier_count != 0 && quantifiers == NULL) goto Fail;
        size_t qi = 0;
        for (size_t i = 0; i < count; ++i) {
                if (find_root(solver, (uint32_t)i + 1) != i + 1) continue;
                T2Meta const *meta = &solver->metas[i];
                if (
                        polarities[i] == 0
                     || !environment_free[i]
                     || meta->level <= binding_level
                     || meta->variable_kind == T2_VARIABLE_WEAK
                     || meta->solution != T2_TYPE_INVALID
                     || (expansive && polarities[i] != T2_POLARITY_POSITIVE)
                ) continue;
                T2VariableKind variable_kind = meta->variable_kind;
                if (
                        variable_kind != T2_VARIABLE_ROW
                     && variable_kind != T2_VARIABLE_PACK
                ) variable_kind = T2_VARIABLE_QUANTIFIED;
                quantifiers[qi] = (T2Quantifier) {
                        .id = (uint32_t)qi + 1,
                        .kind = variable_kind
                };
                replacements[i] = t2_variable(
                        solver->universe,
                        variable_kind,
                        (uint32_t)qi + 1
                );
                qi += 1;
        }

        T2Generalization generalization = {
                .solver = solver,
                .replacements = replacements
        };
        T2Type body = generalize_type(&generalization, type);
        if (body == T2_TYPE_INVALID) {
                free(quantifiers);
                free(generalization.entries);
                free(generalization.binders);
                goto Fail;
        }

        size_t predicate_capacity = quantifier_count * 2
                                  + solver->edge_count
                                  + solver->obligation_count;
        T2Predicate *predicates = predicate_capacity == 0
                                ? NULL
                                : calloc(predicate_capacity, sizeof *predicates);
        size_t *captured_obligations = solver->obligation_count == 0
                                     ? NULL
                                     : malloc(
                                             solver->obligation_count
                                           * sizeof *captured_obligations
                                       );
        if (predicate_capacity != 0 && predicates == NULL) {
                free(quantifiers);
                free(generalization.entries);
                free(generalization.binders);
                free(captured_obligations);
                goto Fail;
        }
        if (solver->obligation_count != 0 && captured_obligations == NULL) {
                free(predicates);
                free(quantifiers);
                free(generalization.entries);
                free(generalization.binders);
                goto Fail;
        }
        size_t predicate_count = 0;
        size_t captured_count = 0;
        T2Type never = t2_primitive(solver->universe, T2_TYPE_NEVER);
        T2Type any = t2_primitive(solver->universe, T2_TYPE_ANY);
        for (size_t i = 0; i < count; ++i) {
                if (replacements[i] == T2_TYPE_INVALID) continue;
                T2Meta const *meta = &solver->metas[i];
                if (meta->lower != never) {
                        predicates[predicate_count++] = (T2Predicate) {
                                .subtype = generalize_type(&generalization, meta->lower),
                                .supertype = replacements[i],
                                .provenance = meta->provenance
                        };
                }
                if (meta->upper != any) {
                        predicates[predicate_count++] = (T2Predicate) {
                                .subtype = replacements[i],
                                .supertype = generalize_type(&generalization, meta->upper),
                                .provenance = meta->provenance
                        };
                }
        }
        for (size_t i = 0; i < solver->edge_count; ++i) {
                uint32_t sub = find_root(solver, solver->edges[i].subtype);
                uint32_t sup = find_root(solver, solver->edges[i].supertype);
                if (
                        replacements[sub - 1] == T2_TYPE_INVALID
                     && replacements[sup - 1] == T2_TYPE_INVALID
                ) continue;
                predicates[predicate_count++] = (T2Predicate) {
                        .subtype = generalize_type(
                                &generalization,
                                meta_type(solver, sub)
                        ),
                        .supertype = generalize_type(
                                &generalization,
                                meta_type(solver, sup)
                        ),
                        .provenance = solver->edges[i].provenance
                };
        }
        for (size_t i = 0; i < solver->obligation_count; ++i) {
                T2Obligation const *obligation = &solver->obligations[i];
                if (!obligation->active) continue;
                T2Predicate const *predicate = &obligation->predicate;
                bool scoped = i >= scoped_obligation_start;
                bool touches_replacement = type_touches_replacement(
                        solver,
                        predicate->subtype,
                        replacements,
                        0
                ) || type_touches_replacement(
                        solver,
                        predicate->supertype,
                        replacements,
                        0
                ) || (
                           predicate->operand != T2_TYPE_INVALID
                        && type_touches_replacement(
                                solver,
                                predicate->operand,
                                replacements,
                                0
                           )
                );
                if (
                        !touches_replacement
                     && !(
                                scoped
                             && predicate_shares_exported_variable(
                                    solver,
                                    type,
                                    predicate
                                )
                        )
                ) continue;
                T2Type subtype = generalize_type(
                        &generalization,
                        predicate->subtype
                );
                T2Type supertype = generalize_type(
                        &generalization,
                        predicate->supertype
                );
                T2Type operand = predicate->operand == T2_TYPE_INVALID
                               ? T2_TYPE_INVALID
                               : generalize_type(
                                       &generalization,
                                       predicate->operand
                                 );
                if (
                        subtype == T2_TYPE_INVALID
                     || supertype == T2_TYPE_INVALID
                     || (
                                predicate->operand != T2_TYPE_INVALID
                             && operand == T2_TYPE_INVALID
                        )
                     || type_contains_solver_meta(solver, subtype, 0)
                     || type_contains_solver_meta(solver, supertype, 0)
                     || (
                                operand != T2_TYPE_INVALID
                             && type_contains_solver_meta(solver, operand, 0)
                        )
                ) continue;
                predicates[predicate_count] = *predicate;
                predicates[predicate_count].subtype = subtype;
                predicates[predicate_count].supertype = supertype;
                predicates[predicate_count].operand = operand;
                predicate_count += 1;
                captured_obligations[captured_count++] = i;
        }

        bool valid = body != T2_TYPE_INVALID;
        for (size_t i = 0; i < predicate_count; ++i) {
                valid &= predicates[i].subtype != T2_TYPE_INVALID;
                valid &= predicates[i].supertype != T2_TYPE_INVALID;
        }
        T2Scheme *scheme = valid
                         ? t2_scheme_new(
                                 solver->universe,
                                 quantifiers,
                                 quantifier_count,
                                 body,
                                 predicates,
                                 predicate_count
                           )
                         : NULL;
        if (scheme != NULL) {
                for (size_t i = 0; i < captured_count; ++i) {
                        size_t index = captured_obligations[i];
                        T2Obligation *obligation = &solver->obligations[index];
                        if (!obligation->active) continue;
                        if (!push_undo(solver, (T2Undo) {
                                .kind = T2_UNDO_OBLIGATION_ACTIVE,
                                .index = (uint32_t)index,
                                .old = obligation->active
                        })) {
                                t2_scheme_free(scheme);
                                scheme = NULL;
                                break;
                        }
                        obligation->active = false;
                }
        }
        free(captured_obligations);
        free(predicates);
        free(quantifiers);
        free(generalization.entries);
        free(generalization.binders);
        free(polarities);
        free(environment_free);
        free(replacements);
        return scheme;

Fail:
        free(polarities);
        free(environment_free);
        free(replacements);
        return NULL;
}

T2Scheme *
t2_solver_generalize(
        T2Solver *solver,
        T2Type type,
        T2Type const *environment,
        size_t environment_count,
        uint32_t binding_level,
        bool expansive
)
{
        return solver_generalize(
                solver,
                type,
                environment,
                environment_count,
                binding_level,
                expansive,
                SIZE_MAX
        );
}

T2Scheme *
t2_solver_generalize_scoped(
        T2Solver *solver,
        T2Type type,
        T2Type const *environment,
        size_t environment_count,
        uint32_t binding_level,
        bool expansive,
        T2SolverMark scope
)
{
        if (
                solver == NULL
             || scope.obligation_count > solver->obligation_count
             || solver->transaction_depth != scope.transaction_depth + 1
        ) return NULL;
        return solver_generalize(
                solver,
                type,
                environment,
                environment_count,
                binding_level,
                expansive,
                scope.obligation_count
        );
}

static size_t
find_quantifier(T2Scheme const *scheme, T2Node const *variable)
{
        for (size_t i = 0; i < scheme->quantifier_count; ++i) {
                T2Quantifier const *quantifier = &scheme->quantifiers[i];
                if (quantifier->id != variable->payload) continue;
                if (
                        quantifier->kind == T2_VARIABLE_ROW
                     || quantifier->kind == T2_VARIABLE_PACK
                ) {
                        if (quantifier->kind == variable->variable_kind) return i;
                } else if (
                        variable->variable_kind == T2_VARIABLE_QUANTIFIED
                     || variable->variable_kind == T2_VARIABLE_FLEXIBLE
                ) {
                        return i;
                }
        }
        return SIZE_MAX;
}

static T2Type instantiate_type(T2Instantiation *instantiation, T2Type source);

static T2Type
instantiate_recursive(T2Instantiation *instantiation, T2Node const *node)
{
        T2Universe *universe = instantiation->solver->universe;
        uint32_t binder = t2_universe_fresh_recursive_binder(universe);
        if (binder == 0) return T2_TYPE_INVALID;
        if (!reserve_array(
                (void **)&instantiation->binders,
                &instantiation->binder_capacity,
                instantiation->binder_count + 1,
                sizeof *instantiation->binders
        )) return T2_TYPE_INVALID;
        size_t mark = instantiation->binder_count;
        instantiation->binders[instantiation->binder_count++] = (T2BinderSubstitution) {
                .source = (uint32_t)node->payload,
                .result = binder
        };
        T2Type body = instantiate_type(instantiation, node->children[0]);
        instantiation->binder_count = mark;
        if (body == T2_TYPE_INVALID) return body;
        return t2_recursive(universe, binder, body);
}

static T2Type
instantiate_type(T2Instantiation *instantiation, T2Type source)
{
        T2Universe *universe = instantiation->solver->universe;
        T2Node const *node = get_node(universe, source);
        if (node == NULL) return T2_TYPE_INVALID;

        if (node->kind == T2_TYPE_VARIABLE) {
                size_t quantifier = find_quantifier(instantiation->scheme, node);
                if (quantifier != SIZE_MAX) return instantiation->replacements[quantifier];
        }
        if (node->kind == T2_TYPE_RECURSIVE_VARIABLE) {
                for (size_t i = instantiation->binder_count; i != 0; --i) {
                        T2BinderSubstitution const *binder = &instantiation->binders[i - 1];
                        if (binder->source == node->payload) {
                                return t2_recursive_variable(universe, binder->result);
                        }
                }
                return source;
        }
        if (node->kind == T2_TYPE_RECURSIVE) {
                return instantiate_recursive(instantiation, node);
        }

        for (size_t i = 0; i < instantiation->node_count; ++i) {
                if (instantiation->nodes[i].source == source) {
                        return instantiation->nodes[i].result;
                }
        }
        if (node->arity == 0) return source;

        T2Type *children = malloc(node->arity * sizeof *children);
        if (children == NULL) return T2_TYPE_INVALID;
        bool changed = false;
        for (size_t i = 0; i < node->arity; ++i) {
                children[i] = instantiate_type(instantiation, node->children[i]);
                if (children[i] == T2_TYPE_INVALID) {
                        free(children);
                        return T2_TYPE_INVALID;
                }
                changed |= children[i] != node->children[i];
        }
        T2Type result = changed
                      ? rebuild_type(universe, node, children)
                      : source;
        free(children);
        if (result == T2_TYPE_INVALID) return result;

        if (!reserve_array(
                (void **)&instantiation->nodes,
                &instantiation->node_capacity,
                instantiation->node_count + 1,
                sizeof *instantiation->nodes
        )) return T2_TYPE_INVALID;
        instantiation->nodes[instantiation->node_count++] = (T2InstantiatedNode) {
                .source = source,
                .result = result
        };
        return result;
}

T2Type
t2_scheme_instantiate(
        T2Scheme const *scheme,
        T2Solver *solver,
        uint32_t level,
        char const *provenance
)
{
        if (
                scheme == NULL
             || solver == NULL
             || solver->failed
             || solver->universe != scheme->universe
        ) return T2_TYPE_INVALID;

        T2SolverMark mark = t2_solver_mark(solver);
        T2Instantiation instantiation = {
                .scheme = scheme,
                .solver = solver
        };
        if (scheme->quantifier_count != 0) {
                instantiation.replacements = malloc(
                        scheme->quantifier_count * sizeof *instantiation.replacements
                );
                if (instantiation.replacements == NULL) goto Fail;
        }
        for (size_t i = 0; i < scheme->quantifier_count; ++i) {
                T2VariableKind kind = scheme->quantifiers[i].kind;
                if (
                        kind != T2_VARIABLE_ROW
                     && kind != T2_VARIABLE_PACK
                     && kind != T2_VARIABLE_WEAK
                ) kind = T2_VARIABLE_FLEXIBLE;
                instantiation.replacements[i] = t2_solver_new_meta(
                        solver,
                        kind,
                        level,
                        provenance
                );
                if (instantiation.replacements[i] == T2_TYPE_INVALID) goto Fail;
        }

        T2Type body = instantiate_type(&instantiation, scheme->body);
        if (body == T2_TYPE_INVALID) goto Fail;
        for (size_t i = 0; i < scheme->predicate_count; ++i) {
                T2Type subtype = instantiate_type(
                        &instantiation,
                        scheme->predicates[i].subtype
                );
                T2Type supertype = instantiate_type(
                        &instantiation,
                        scheme->predicates[i].supertype
                );
                T2Type operand = scheme->predicates[i].kind == T2_PREDICATE_SUBTYPE
                               ? T2_TYPE_INVALID
                               : instantiate_type(
                                       &instantiation,
                                       scheme->predicates[i].operand
                                 );
                T2Predicate predicate = scheme->predicates[i];
                predicate.subtype = subtype;
                predicate.supertype = supertype;
                predicate.operand = operand;
                if (provenance != NULL) predicate.provenance = provenance;
                if (
                        subtype == T2_TYPE_INVALID
                     || supertype == T2_TYPE_INVALID
                     || (
                                predicate.kind != T2_PREDICATE_SUBTYPE
                             && operand == T2_TYPE_INVALID
                        )
                     || t2_solver_constrain_predicate(
                            solver,
                            &predicate
                        ) == T2_RELATION_NO
                ) goto Fail;
        }

        free(instantiation.replacements);
        free(instantiation.nodes);
        free(instantiation.binders);
        t2_solver_commit(solver, mark);
        return body;

Fail:
        free(instantiation.replacements);
        free(instantiation.nodes);
        free(instantiation.binders);
        t2_solver_rollback(solver, mark);
        return T2_TYPE_INVALID;
}

T2Type
t2_scheme_apply(
        T2Scheme const *scheme,
        T2Solver *solver,
        T2Type const *arguments,
        size_t argument_count,
        char const *provenance
)
{
        if (
                scheme == NULL
             || solver == NULL
             || solver->failed
             || solver->universe != scheme->universe
             || argument_count != scheme->quantifier_count
             || (argument_count != 0 && arguments == NULL)
        ) return T2_TYPE_INVALID;
        for (size_t i = 0; i < argument_count; ++i) {
                if (get_node(solver->universe, arguments[i]) == NULL) {
                        return T2_TYPE_INVALID;
                }
                T2VariableKind kind = scheme->quantifiers[i].kind;
                if (
                        (kind == T2_VARIABLE_ROW || kind == T2_VARIABLE_PACK)
                     && term_sort(solver->universe, arguments[i]) != kind
                ) return T2_TYPE_INVALID;
        }

        T2SolverMark mark = t2_solver_mark(solver);
        T2Instantiation instantiation = {
                .scheme = scheme,
                .solver = solver
        };
        if (argument_count != 0) {
                instantiation.replacements = malloc(
                        argument_count * sizeof *instantiation.replacements
                );
                if (instantiation.replacements == NULL) goto Fail;
                memcpy(
                        instantiation.replacements,
                        arguments,
                        argument_count * sizeof *instantiation.replacements
                );
        }

        T2Type body = instantiate_type(&instantiation, scheme->body);
        if (body == T2_TYPE_INVALID) goto Fail;
        for (size_t i = 0; i < scheme->predicate_count; ++i) {
                T2Type subtype = instantiate_type(
                        &instantiation,
                        scheme->predicates[i].subtype
                );
                T2Type supertype = instantiate_type(
                        &instantiation,
                        scheme->predicates[i].supertype
                );
                T2Type operand = scheme->predicates[i].kind == T2_PREDICATE_SUBTYPE
                               ? T2_TYPE_INVALID
                               : instantiate_type(
                                       &instantiation,
                                       scheme->predicates[i].operand
                                 );
                T2Predicate predicate = scheme->predicates[i];
                predicate.subtype = subtype;
                predicate.supertype = supertype;
                predicate.operand = operand;
                if (provenance != NULL) predicate.provenance = provenance;
                if (
                        subtype == T2_TYPE_INVALID
                     || supertype == T2_TYPE_INVALID
                     || (
                                predicate.kind != T2_PREDICATE_SUBTYPE
                             && operand == T2_TYPE_INVALID
                        )
                     || t2_solver_constrain_predicate(
                            solver,
                            &predicate
                        ) == T2_RELATION_NO
                ) goto Fail;
        }
        free(instantiation.replacements);
        free(instantiation.nodes);
        free(instantiation.binders);
        t2_solver_commit(solver, mark);
        return body;

Fail:
        free(instantiation.replacements);
        free(instantiation.nodes);
        free(instantiation.binders);
        t2_solver_rollback(solver, mark);
        return T2_TYPE_INVALID;
}

typedef struct t2_zonk_entry {
        T2Type source;
        T2Type result;
} T2ZonkEntry;

typedef struct t2_zonk_context {
        T2Solver *solver;
        T2SolutionPreference preference;
        T2ZonkEntry *entries;
        size_t count;
        size_t capacity;
        uint32_t *active_metas;
        size_t active_meta_count;
        size_t active_meta_capacity;
        T2BinderSubstitution *binders;
        size_t binder_count;
        size_t binder_capacity;
        bool failed;
} T2ZonkContext;

static T2Type zonk_type(T2ZonkContext *context, T2Type source);

static T2Type
zonk_recursive(T2ZonkContext *context, T2Node const *node)
{
        T2Universe *universe = context->solver->universe;
        uint32_t binder = t2_universe_fresh_recursive_binder(universe);
        if (binder == 0) return T2_TYPE_INVALID;
        if (!reserve_array(
                (void **)&context->binders,
                &context->binder_capacity,
                context->binder_count + 1,
                sizeof *context->binders
        )) return T2_TYPE_INVALID;
        size_t mark = context->binder_count;
        context->binders[context->binder_count++] = (T2BinderSubstitution) {
                .source = (uint32_t)node->payload,
                .result = binder
        };
        T2Type body = zonk_type(context, node->children[0]);
        context->binder_count = mark;
        return body == T2_TYPE_INVALID
             ? body
             : t2_recursive(universe, binder, body);
}

static T2Type
zonk_type(T2ZonkContext *context, T2Type source)
{
        T2Solver *solver = context->solver;
        uint32_t meta = meta_from_type(solver, source);
        if (meta != 0) {
                meta = find_root(solver, meta);
                T2Type root_type = meta_type(solver, meta);
                for (size_t i = 0; i < context->active_meta_count; ++i) {
                        if (context->active_metas[i] == meta) return root_type;
                }
                T2Type solution = t2_solver_solution(
                        solver,
                        root_type,
                        context->preference
                );
                if (solution == root_type) return root_type;
                if (!reserve_array(
                        (void **)&context->active_metas,
                        &context->active_meta_capacity,
                        context->active_meta_count + 1,
                        sizeof *context->active_metas
                )) {
                        context->failed = true;
                        return T2_TYPE_INVALID;
                }
                context->active_metas[context->active_meta_count++] = meta;
                T2Type result = zonk_type(context, solution);
                context->active_meta_count -= 1;
                return result;
        }

        T2Node const *node = get_node(solver->universe, source);
        if (node == NULL) return T2_TYPE_INVALID;
        if (node->kind == T2_TYPE_RECURSIVE_VARIABLE) {
                for (size_t i = context->binder_count; i != 0; --i) {
                        T2BinderSubstitution const *binder = &context->binders[i - 1];
                        if (binder->source == node->payload) {
                                return t2_recursive_variable(
                                        solver->universe,
                                        binder->result
                                );
                        }
                }
                return source;
        }
        if (node->kind == T2_TYPE_RECURSIVE) return zonk_recursive(context, node);
        for (size_t i = 0; i < context->count; ++i) {
                if (context->entries[i].source == source) return context->entries[i].result;
        }
        if (node->arity == 0) return source;

        T2Type *children = malloc(node->arity * sizeof *children);
        if (children == NULL) return T2_TYPE_INVALID;
        bool changed = false;
        for (size_t i = 0; i < node->arity; ++i) {
                children[i] = zonk_type(context, node->children[i]);
                if (children[i] == T2_TYPE_INVALID) {
                        free(children);
                        return T2_TYPE_INVALID;
                }
                changed |= children[i] != node->children[i];
        }
        T2Type result = changed
                      ? rebuild_type(solver->universe, node, children)
                      : source;
        free(children);
        if (result == T2_TYPE_INVALID) return result;
        if (!reserve_array(
                (void **)&context->entries,
                &context->capacity,
                context->count + 1,
                sizeof *context->entries
        )) return T2_TYPE_INVALID;
        context->entries[context->count++] = (T2ZonkEntry) {
                .source = source,
                .result = result
        };
        return result;
}

T2Type
t2_solver_zonk(
        T2Solver *solver,
        T2Type type,
        T2SolutionPreference preference
)
{
        if (solver == NULL || solver->failed) return T2_TYPE_INVALID;
        T2ZonkContext context = {
                .solver = solver,
                .preference = preference
        };
        T2Type result = zonk_type(&context, type);
        free(context.entries);
        free(context.active_metas);
        free(context.binders);
        return result;
}

/* vim: set sts=8 sw=8 expandtab: */
