#include <limits.h>
#include <inttypes.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include <xxhash.h>

#include "defs.h"
#include "xd.h"
#include "types2_core.h"

typedef struct t2_node {
        u64            hash;
        u64            payload;
        char          *text;
        u32            arity;
        T2TypeKind     kind;
        T2VariableKind variable_kind;
        uint8_t        flags;
        T2Type         children[];
} T2Node;

enum {
        T2_NODE_META               = 1,
        T2_NODE_VARIABLE           = 2,
        T2_NODE_RECURSIVE_VARIABLE = 4,
        T2_NODE_GRADUAL            = 8
};

static uint8_t
node_flags_for(T2TypeKind kind)
{
        switch (kind) {
        case T2_TYPE_DYNAMIC:
        case T2_TYPE_ANY:
        case T2_TYPE_UNKNOWN:            return T2_NODE_GRADUAL;
        case T2_TYPE_META:               return T2_NODE_META;
        case T2_TYPE_VARIABLE:           return T2_NODE_VARIABLE;
        case T2_TYPE_RECURSIVE_VARIABLE: return T2_NODE_RECURSIVE_VARIABLE;
        default:                         return 0;
        }
}

typedef struct t2_nominal_info {
        u64         symbol;
        char       *name;
        usize       arity;
        T2Variance *variance;
        vec(T2Type) supertypes;
        bool        instantiated;
        bool        interface;
} T2NominalInfo;

typedef struct t2_applied_nominal {
        T2Type      instance;
        vec(T2Type) supertypes;
} T2AppliedNominal;

typedef struct t2_recursive_info {
        u32    binder;
        T2Type type;
} T2RecursiveInfo;

typedef struct t2_computed_result {
        T2Type computed;
        T2Type result;
} T2ComputedResult;

struct t2_universe {
        vec(T2Node *) nodes;

        T2Type *table;
        usize   table_count;
        usize   table_capacity;

        T2Type primitives[T2_TYPE_KIND_COUNT];
        T2Type primitive_nominals[T2_TYPE_KIND_COUNT];

        vec(T2NominalInfo)    nominals;
        vec(T2AppliedNominal) applied_nominals;
        vec(T2RecursiveInfo)  recursive;
        vec(T2ComputedResult) computed_results;

        T2Index nominal_index;
        T2Index applied_index;
        T2Index relation_memo;

        u32  next_solver_id;
        u32  next_recursive_id;
        bool failed;
};

typedef vec(u64) T2WatchVector;

typedef struct t2_meta {
        u32            parent;
        u32            level;
        uint8_t        rank;
        T2VariableKind variable_kind;
        T2Type         lower;
        T2Type         upper;
        T2Type         solution;
        char          *provenance;
        T2WatchVector  watchers;
        bool           checking_bounds;
        bool           retired;
} T2Meta;

typedef struct t2_edge {
        u32         subtype;
        u32         supertype;
        char const *provenance;
        u64         self_retry_epoch;
} T2Edge;

typedef struct t2_obligation {
        T2Predicate predicate;
        char       *name;
        char       *provenance;
        u64         self_retry_epoch;
        bool        active;
} T2Obligation;

typedef struct t2_cause {
        T2CauseKind kind;
        T2Type      left;
        T2Type      right;
        char       *provenance;
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
        u32        index;
        u64        old;
} T2Undo;

struct t2_solver {
        T2Universe *universe;
        u32         id;

        vec(T2Meta) metas;

        vec(T2Edge) edges;

        vec(T2Obligation) obligations;

        vec(u64) recursive_constraints;

        T2PredicateResolver *predicate_resolver;
        void                *predicate_context;

        vec(u64) work;
        usize    work_index;
        u64      work_steps;
        u64      active_work;
        u64      drain_epoch;
        bool     draining_work;
        bool     processing_work;
        bool     rerun_active_work;

        vec(T2Undo) undo;
        unsigned    transaction_depth;

        vec(T2Cause) causes;

        bool        failed;
        char        error[512];
        char const *failure_message;
        T2Type      failure_left;
        T2Type      failure_right;
        char       *failure_provenance;
};

struct t2_scheme {
        T2Universe   *universe;
        T2Quantifier *quantifiers;
        char        **names;
        usize         quantifier_count;
        T2Type        body;
        T2Predicate  *predicates;
        usize         predicate_count;
};

typedef vec(T2Type) T2TypeVector;

typedef byte_vector T2StringBuffer;

static T2Type
rebuild_type(
        T2Universe   *universe,
        T2Node const *node,
        T2Type const *children
);

enum {
        T2_RELATION_DEPTH_LIMIT = 256
};

static u64 const T2_WATCH_OBLIGATION = UINT64_C(1) << 63;

enum {
        T2_FIELD_PRESENCE_MASK = 0x3,
        T2_FIELD_WRITABLE_BIT  = 0x4,

        T2_PARAMETER_KIND_MASK = 0x7,
        T2_PARAMETER_REQUIRED  = 0x8,

        T2_RANGE_HAS_LOWER       = 0x1,
        T2_RANGE_HAS_UPPER       = 0x2,
        T2_RANGE_UPPER_INCLUSIVE = 0x4
};

static usize
index_slot(T2Index const *index, u64 key)
{
        usize slot = (usize)hash64(key) & (index->capacity - 1);
        while (
                index->entries[slot].used
             && (index->entries[slot].key != key)
        ) {
                slot = (slot + 1) & (index->capacity - 1);
        }

        return slot;
}

bool
t2_index_find(T2Index const *index, u64 key, u32 *value)
{
        if (index->capacity == 0) {
                return false;
        }

        usize slot = index_slot(index, key);
        if (!index->entries[slot].used) {
                return false;
        }

        *value = index->entries[slot].value;

        return true;
}

static bool
index_grow(T2Index *index)
{
        usize capacity = (index->capacity == 0) ? 64 : index->capacity * 2;
        T2IndexEntry *entries = ty_calloc(capacity, sizeof *entries);
        if (entries == NULL) {
                return false;
        }

        T2Index grown = { .entries = entries, .capacity = capacity };
        for (usize i = 0; i < index->capacity; ++i) {
                T2IndexEntry const *entry = &index->entries[i];
                if (!entry->used) {
                        continue;
                }
                grown.entries[index_slot(&grown, entry->key)] = *entry;
                grown.count += 1;
        }

        ty_free(index->entries);
        *index = grown;

        return true;
}

bool
t2_index_put(T2Index *index, u64 key, u32 value)
{
        if (
                ((index->count + 1) * 4 > index->capacity * 3)
             && !index_grow(index)
        ) {
                return false;
        }

        usize slot = index_slot(index, key);
        index->count += !index->entries[slot].used;
        index->entries[slot] = (T2IndexEntry) {
                .key   = key,
                .value = value,
                .used  = true
        };

        return true;
}

void
t2_index_clear(T2Index *index)
{
        if (index->capacity != 0) {
                memset(index->entries, 0, index->capacity * sizeof *index->entries);
        }

        index->count = 0;
}

void
t2_index_free(T2Index *index)
{
        ty_free(index->entries);
        *index = (T2Index) { 0 };
}

static void
forget_relations(T2Universe *universe)
{
        t2_index_clear(&universe->relation_memo);
}

static T2Node const *
get_node(T2Universe const *universe, T2Type type)
{
        if (
                (universe == NULL)
             || (type == T2_TYPE_INVALID)
             || (type > vN(universe->nodes))
        ) {
                return NULL;
        }

        return v__(universe->nodes, type - 1);
}

static usize
text_len(T2TypeKind kind, u64 payload, char const *text)
{
        if (text == NULL) {
                return 0;
        }

        return (kind == T2_TYPE_LITERAL_STRING) ? payload : strlen(text);
}

static bool
same_candidate(
        T2Node const  *node,
        T2TypeKind     kind,
        T2VariableKind variable_kind,
        u64            payload,
        char const    *text,
        T2Type const  *children,
        usize          arity
)
{
        if (
                (node->kind != kind)
             || (node->variable_kind != variable_kind)
             || (node->payload != payload)
             || (node->arity != arity)
        ) {
                return false;
        }

        if ((node->text == NULL) != (text == NULL)) {
                return false;
        }

        if (
                (node->text != NULL)
             && (
                        (kind == T2_TYPE_LITERAL_STRING)
                      ? (memcmp(node->text, text, payload) != 0)
                      : !s_eq(node->text, text)
                )
        ) {
                return false;
        }

        return (arity == 0)
            || (memcmp(node->children, children, arity * sizeof *children) == 0);
}

static bool
resize_intern_table(T2Universe *universe, usize capacity)
{
        T2Type *table = ty_calloc(capacity, sizeof *table);
        if (table == NULL) {
                universe->failed = true;
                return false;
        }

        for (usize i = 0; i < vN(universe->nodes); ++i) {
                T2Type type = (T2Type)(i + 1);
                T2Node const *node = v__(universe->nodes, i);
                usize slot = (usize)node->hash & (capacity - 1);
                while (table[slot] != T2_TYPE_INVALID) {
                        slot = (slot + 1) & (capacity - 1);
                }
                table[slot] = type;
        }

        ty_free(universe->table);
        universe->table = table;
        universe->table_capacity = capacity;
        universe->table_count    = vN(universe->nodes);

        return true;
}

static T2Type
intern_type(
        T2Universe    *universe,
        T2TypeKind     kind,
        T2VariableKind variable_kind,
        u64            payload,
        char const    *text,
        T2Type const  *children,
        usize          arity
)
{
        if (
                (universe == NULL)
             || universe->failed
             || (kind >= T2_TYPE_KIND_COUNT)
             || (arity > UINT32_MAX)
             || ((arity != 0) && (children == NULL))
             || (vN(universe->nodes) >= UINT32_MAX)
        ) {
                return T2_TYPE_INVALID;
        }

        usize length = text_len(kind, payload, text);
        if (length == SIZE_MAX) {
                return T2_TYPE_INVALID;
        }

        u64 hash = hash64((u64)kind + 1);
        hash = HashCombine(hash, variable_kind);
        hash = HashCombine(hash, payload);
        hash = HashCombine(
                hash,
                (text == NULL) ? UINT64_C(146959810393466560) : XXH3_64bits(text, length)
        );
        hash = HashCombine(hash, arity);
        uint8_t flags = node_flags_for(kind);
        for (usize i = 0; i < arity; ++i) {
                T2Node const *child = get_node(universe, children[i]);
                if (child == NULL) {
                        return T2_TYPE_INVALID;
                }
                hash = HashCombine(hash, child->hash);
                flags |= child->flags;
        }

        hash = hash64(hash);
        if (
                (universe->table_capacity == 0)
             || ((universe->table_count + 1) * 4 >= universe->table_capacity * 3)
        ) {
                usize capacity = (universe->table_capacity == 0)
                               ? 64
                               : universe->table_capacity * 2;
                if (!resize_intern_table(universe, capacity)) {
                        return T2_TYPE_INVALID;
                }
        }

        usize slot = (usize)hash & (universe->table_capacity - 1);
        while (universe->table[slot] != T2_TYPE_INVALID) {
                T2Type type = universe->table[slot];
                T2Node const *node = get_node(universe, type);
                if (
                        (node->hash == hash)
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

        if (arity > (SIZE_MAX - sizeof (T2Node)) / sizeof (T2Type)) {
                universe->failed = true;
                return T2_TYPE_INVALID;
        }

        T2Node *node = ty_malloc(sizeof *node + arity * sizeof *children);
        if (node == NULL) {
                universe->failed = true;
                return T2_TYPE_INVALID;
        }

        char *owned_text = (text == NULL) ? NULL : ty_malloc(length + 1);
        if (text != NULL && owned_text == NULL) {
                ty_free(node);
                universe->failed = true;
                return T2_TYPE_INVALID;
        }

        if (owned_text != NULL) {
                memcpy(owned_text, text, length);
                owned_text[length] = '\0';
        }

        *node = (T2Node) {
                .hash    = hash,
                .payload = payload,
                .text    = owned_text,
                .arity   = (u32)arity,
                .kind    = kind,
                .variable_kind = variable_kind,
                .flags         = flags
        };

        if (arity != 0) {
                memcpy(node->children, children, arity * sizeof *children);
        }

        T2Type type = (T2Type)(vN(universe->nodes) + 1);
        xvP(universe->nodes, node);
        universe->table[slot] = type;
        universe->table_count += 1;

        return type;
}

void
t2_universe_report(T2Universe const *universe, FILE *out)
{
        usize kinds[T2_TYPE_KIND_COUNT] = { 0 };
        usize with_metas = 0;
        for (usize i = 0; i < vN(universe->nodes); ++i) {
                T2Node const *node = v__(universe->nodes, i);
                if (node == NULL) {
                        continue;
                }
                kinds[node->kind] += 1;
                with_metas += (node->flags & T2_NODE_META) != 0;
        }

        fprintf(
                out,
                "types2 universe: nodes=%zu containing-metas=%zu metas=%zu nominals=%zu applied=%zu recursive=%zu computed=%zu memo=%zu\n",
                vN(universe->nodes),
                with_metas,
                kinds[T2_TYPE_META],
                vN(universe->nominals),
                vN(universe->applied_nominals),
                vN(universe->recursive),
                vN(universe->computed_results),
                universe->relation_memo.count
        );
        for (usize kind = 0; kind < T2_TYPE_KIND_COUNT; ++kind) {
                if (kinds[kind] != 0) {
                        fprintf(out, "  kind %zu: %zu\n", kind, kinds[kind]);
                }
        }
}

T2Universe *
t2_universe_new(void)
{
        T2Universe *universe = ty_calloc(1, sizeof *universe);
        if (universe != NULL) {
                universe->next_solver_id    = 1;
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

        for (usize i = 0; i < vN(universe->nodes); ++i) {
                ty_free(v__(universe->nodes, i)->text);
                ty_free(v__(universe->nodes, i));
        }

        for (usize i = 0; i < vN(universe->nominals); ++i) {
                ty_free(v__(universe->nominals, i).name);
                ty_free(v__(universe->nominals, i).variance);
                xvF(v__(universe->nominals, i).supertypes);
        }

        for (usize i = 0; i < vN(universe->applied_nominals); ++i) {
                xvF(v__(universe->applied_nominals, i).supertypes);
        }

        xvF(universe->nodes);
        ty_free(universe->table);
        xvF(universe->nominals);
        xvF(universe->applied_nominals);
        xvF(universe->recursive);
        xvF(universe->computed_results);
        t2_index_free(&universe->nominal_index);
        t2_index_free(&universe->applied_index);
        t2_index_free(&universe->relation_memo);
        ty_free(universe);
}

bool
t2_universe_ok(T2Universe const *universe)
{
        return (universe != NULL) && !universe->failed;
}

usize
t2_universe_type_count(T2Universe const *universe)
{
        return (universe == NULL) ? 0 : vN(universe->nodes);
}

u32
t2_universe_fresh_recursive_binder(T2Universe *universe)
{
        if (universe == NULL || universe->next_recursive_id == 0) {
                return 0;
        }

        return universe->next_recursive_id++;
}

T2Type
t2_primitive(T2Universe *universe, T2TypeKind kind)
{
        bool primitive = ((kind >= T2_TYPE_NEVER) && (kind <= T2_TYPE_STRING))
                      || (kind == T2_TYPE_ROW_EMPTY)
                      || (kind == T2_TYPE_ROW_ANY)
                      || (kind == T2_TYPE_PACK_EMPTY)
                      || (kind == T2_TYPE_PACK_ANY);

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
t2_literal_int(T2Universe *universe, i64 value)
{
        return intern_type(
                universe,
                T2_TYPE_LITERAL_INT,
                T2_VARIABLE_FLEXIBLE,
                (u64)value,
                NULL,
                NULL,
                0
        );
}

T2Type
t2_literal_string(T2Universe *universe, char const *value)
{
        return (value == NULL)
             ? T2_TYPE_INVALID
             : t2_literal_string_n(universe, value, strlen(value));
}

T2Type
t2_literal_string_n(T2Universe *universe, char const *value, usize length)
{
        if (value == NULL && length != 0) {
                return T2_TYPE_INVALID;
        }

        return intern_type(
                universe,
                T2_TYPE_LITERAL_STRING,
                T2_VARIABLE_FLEXIBLE,
                length,
                (value == NULL) ? "" : value,
                NULL,
                0
        );
}

T2Type
t2_integer_range(
        T2Universe *universe,
        T2Type      lower,
        T2Type      upper,
        bool        upper_inclusive
)
{
        if (
                (universe == NULL)
             || ((lower == T2_TYPE_INVALID) && (upper == T2_TYPE_INVALID))
        ) {
                return T2_TYPE_INVALID;
        }

        T2Type bounds[2];
        usize count = 0;
        u64 payload = 0;
        if (lower != T2_TYPE_INVALID) {
                if (get_node(universe, lower) == NULL) {
                        return T2_TYPE_INVALID;
                }
                payload |= T2_RANGE_HAS_LOWER;
                bounds[count++] = lower;
        }

        if (upper != T2_TYPE_INVALID) {
                if (get_node(universe, upper) == NULL) {
                        return T2_TYPE_INVALID;
                }
                payload |= T2_RANGE_HAS_UPPER;
                bounds[count++] = upper;
        }

        if (upper_inclusive) {
                payload |= T2_RANGE_UPPER_INCLUSIVE;
        }

        if (lower != T2_TYPE_INVALID && upper != T2_TYPE_INVALID) {
                T2Node const *low  = get_node(universe, lower);
                T2Node const *high = get_node(universe, upper);
                if (
                        (low->kind == T2_TYPE_LITERAL_INT)
                     && (high->kind == T2_TYPE_LITERAL_INT)
                ) {
                        i64 lo = (i64)low->payload;
                        i64 hi = (i64)high->payload;
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

bool
t2_integer_range_bounds(
        T2Universe const *universe,
        T2Type            range,
        T2Type           *lower,
        T2Type           *upper,
        bool             *upper_inclusive
)
{
        T2Node const *node = get_node(universe, range);
        if (node == NULL || node->kind != T2_TYPE_INT_RANGE) {
                return false;
        }

        bool has_lower = ((node->payload & T2_RANGE_HAS_LOWER) != 0);
        bool has_upper = ((node->payload & T2_RANGE_HAS_UPPER) != 0);
        if (lower != NULL) {
                *lower = has_lower ? node->children[0] : T2_TYPE_INVALID;
        }

        if (upper != NULL) {
                *upper = has_upper ? node->children[has_lower] : T2_TYPE_INVALID;
        }

        if (upper_inclusive != NULL) {
                *upper_inclusive = ((node->payload & T2_RANGE_UPPER_INCLUSIVE) != 0);
        }

        return true;
}

T2Type
t2_refinement(T2Universe *universe, T2Type base, T2Type argument)
{
        if (
                (universe == NULL)
             || (get_node(universe, base) == NULL)
             || (get_node(universe, argument) == NULL)
        ) {
                return T2_TYPE_INVALID;
        }

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
        T2Universe   *universe,
        u64           identity,
        char const   *name,
        T2Type const *arguments,
        usize         argument_count
)
{
        if (
                (universe == NULL)
             || (identity == 0)
             || (name == NULL)
             || ((argument_count != 0) && (arguments == NULL))
        ) {
                return T2_TYPE_INVALID;
        }

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
        if (universe == NULL) {
                return NULL;
        }

        for (usize i = 0; i < vN(universe->computed_results); ++i) {
                if (v__(universe->computed_results, i).computed == computed) {
                        return v_(universe->computed_results, i);
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

        return (entry == NULL) ? T2_TYPE_INVALID : entry->result;
}

T2Type
t2_type_resolve_computed(T2Universe const *universe, T2Type type)
{
        T2Node const *head = get_node(universe, type);
        if (head == NULL) {
                return T2_TYPE_INVALID;
        }

        if (head->kind != T2_TYPE_SCHEME && head->kind != T2_TYPE_COMPUTED) {
                return type;
        }

        usize remaining = vN(universe->computed_results) + 1;
        while (remaining-- != 0) {
                type = t2_type_scheme_body(universe, type);
                T2Node const *node = get_node(universe, type);
                if (node == NULL || node->kind != T2_TYPE_COMPUTED) {
                        return type;
                }
                T2ComputedResult const *entry = find_computed_result(universe, type);
                if (entry == NULL) {
                        return type;
                }
                type = entry->result;
        }

        return T2_TYPE_INVALID;
}

static bool
computed_result_reaches(
        T2Universe const *universe,
        T2Type            source,
        T2Type            target,
        bool             *visiting
)
{
        if (source == target) {
                return true;
        }

        if (
                (source == T2_TYPE_INVALID)
             || (source > vN(universe->nodes))
        ) {
                return true;
        }

        usize index = (usize)source - 1;
        if (visiting[index]) {
                return false;
        }

        visiting[index] = true;

        T2Node const *node = get_node(universe, source);
        bool reaches = (node == NULL) || (node->kind == T2_TYPE_META);

        if (!reaches && node->kind == T2_TYPE_COMPUTED) {
                T2ComputedResult const *entry = find_computed_result(universe, source);
                reaches = (entry != NULL)
                       && computed_result_reaches(
                               universe,
                               entry->result,
                               target,
                               visiting
                          )
                ;
        }

        for (usize i = 0; !reaches && i < node->arity; ++i) {
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
        T2Type      computed,
        T2Type      result
)
{
        T2Node const *promise = get_node(universe, computed);
        T2Node const *value   = get_node(universe, result);
        if (
                (universe == NULL)
             || (promise == NULL)
             || (promise->kind != T2_TYPE_COMPUTED)
             || (value == NULL)
        ) {
                return false;
        }

        T2ComputedResult const *existing = find_computed_result(universe, computed);
        if (existing != NULL) {
                return existing->result == result;
        }

        bool *visiting = ty_calloc(vN(universe->nodes), sizeof *visiting);
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
        ty_free(visiting);
        if (cyclic_or_solver_local) {
                return false;
        }

        xvP(universe->computed_results, ((T2ComputedResult) {
                .computed = computed,
                .result   = result
        }));
        forget_relations(universe);

        return true;
}

T2Type
t2_variable(T2Universe *universe, T2VariableKind kind, u32 id)
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
find_nominal(T2Universe const *universe, u64 symbol)
{
        u32 index;
        if (
                (universe == NULL)
             || !t2_index_find(&universe->nominal_index, symbol, &index)
        ) {
                return NULL;
        }

        return v_(universe->nominals, index);
}

static T2NominalInfo *
find_nominal_mutable(T2Universe *universe, u64 symbol)
{
        return (T2NominalInfo *)find_nominal(universe, symbol);
}

bool
t2_declare_nominal(
        T2Universe       *universe,
        u64               symbol,
        char const       *name,
        usize             arity,
        T2Variance const *variance
)
{
        if (universe == NULL || universe->failed || name == NULL) {
                return false;
        }

        forget_relations(universe);
        T2NominalInfo *existing = find_nominal_mutable(universe, symbol);
        if (existing != NULL) {
                if (
                        (existing->arity != arity)
                     || !s_eq(existing->name, name)
                ) {
                        return false;
                }

                for (usize i = 0; i < arity; ++i) {
                        existing->variance[i] = (variance == NULL) ? T2_INVARIANT : variance[i];
                }
                return true;
        }

        char *owned_name = S2N(name);
        T2Variance *owned_variance = (arity == 0)
                                   ? NULL
                                   : ty_malloc(arity * sizeof *owned_variance);
        if (owned_name == NULL || ((arity != 0) && (owned_variance == NULL))) {
                ty_free(owned_name);
                ty_free(owned_variance);
                universe->failed = true;
                return false;
        }

        for (usize i = 0; i < arity; ++i) {
                owned_variance[i] = (variance == NULL) ? T2_INVARIANT : variance[i];
        }

        xvP(universe->nominals, ((T2NominalInfo) {
                .symbol   = symbol,
                .name     = owned_name,
                .arity    = arity,
                .variance = owned_variance
        }));
        if (
                !t2_index_put(
                        &universe->nominal_index,
                        symbol,
                        (u32)(vN(universe->nominals) - 1)
                )
        ) {
                universe->failed = true;
                return false;
        }

        return true;
}

bool
t2_nominal_declared(T2Universe const *universe, u64 symbol, usize *arity)
{
        T2NominalInfo const *info = find_nominal(universe, symbol);
        if (info == NULL) {
                return false;
        }

        if (arity != NULL) {
                *arity = info->arity;
        }

        return true;
}

T2Type
t2_nominal_type_parameter(T2Universe *universe, u32 index)
{
        if (index == UINT32_MAX) {
                return T2_TYPE_INVALID;
        }

        return t2_variable(universe, T2_VARIABLE_QUANTIFIED, index + 1);
}

static T2Type
primitive_nominal(T2Universe const *universe, T2Node const *node);
static T2Type
nominal_project_x(
        T2Universe const *universe,
        T2Type            subtype,
        u64               target_symbol,
        unsigned          depth
);

static bool
nominal_reaches(
        T2Universe const *universe,
        u64               from,
        u64               wanted,
        unsigned          depth
)
{
        if (from == wanted) {
                return true;
        }

        if (depth > T2_RELATION_DEPTH_LIMIT) {
                return true;
        }

        T2NominalInfo const *info = find_nominal(universe, from);
        if (info == NULL) {
                return false;
        }

        for (usize i = 0; i < vN(info->supertypes); ++i) {
                T2Node const *supertype = get_node(universe, v__(info->supertypes, i));
                if (
                        (supertype != NULL)
                     && (supertype->kind == T2_TYPE_NOMINAL)
                     && nominal_reaches(
                             universe,
                             supertype->payload,
                             wanted,
                             depth + 1
                        )
                ) {
                        return true;
                }
        }

        return false;
}

static bool
backfill_nominal_super(
        T2Universe *universe,
        u64         symbol,
        T2Type      supertype_template
);

static T2AppliedNominal const *
find_applied_nominal(
        T2Universe const *universe,
        T2Type            instance
);

bool
t2_nominal_add_super(
        T2Universe *universe,
        u64         symbol,
        T2Type      supertype_template
)
{
        T2NominalInfo *info     = find_nominal_mutable(universe, symbol);
        T2Node const *supertype = get_node(universe, supertype_template);
        if (
                (info == NULL)
             || (supertype == NULL)
             || (supertype->kind != T2_TYPE_NOMINAL)
             || (find_nominal(universe, supertype->payload) == NULL)
             || nominal_reaches(universe, supertype->payload, symbol, 0)
        ) {
                return false;
        }

        for (usize i = 0; i < vN(info->supertypes); ++i) {
                if (v__(info->supertypes, i) == supertype_template) {
                        return true;
                }
        }

        xvP(info->supertypes, supertype_template);
        forget_relations(universe);

        return backfill_nominal_super(universe, symbol, supertype_template);
}

bool
t2_nominal_mark_interface(T2Universe *universe, u64 symbol)
{
        T2NominalInfo *info = (universe == NULL)
                            ? NULL
                            : find_nominal_mutable(universe, symbol);
        if (info == NULL) {
                return false;
        }

        info->interface = true;
        forget_relations(universe);

        return true;
}

static bool
disjoint_nominals(T2Universe const *universe, T2Type left, T2Type right)
{
        T2Node const *a         = get_node(universe, left);
        T2Node const *b         = get_node(universe, right);
        T2NominalInfo const *ai = find_nominal(universe, a->payload);
        T2NominalInfo const *bi = find_nominal(universe, b->payload);

        if (ai == NULL || bi == NULL || ai->interface || bi->interface) {
                return false;
        }

        return (nominal_project_x(universe, left, b->payload, 0) == T2_TYPE_INVALID)
            && (nominal_project_x(universe, right, a->payload, 0) == T2_TYPE_INVALID);
}

bool
t2_primitive_bind_nominal(T2Universe *universe, T2TypeKind kind, T2Type nominal)
{
        T2Node const *node = (universe == NULL) ? NULL : get_node(universe, nominal);
        if (
                (node == NULL)
             || (node->kind != T2_TYPE_NOMINAL)
             || (node->arity != 0)
             || (kind == T2_TYPE_ERROR)
             || (
                        ((kind < T2_TYPE_OBJECT) || (kind > T2_TYPE_STRING))
                     && (kind != T2_TYPE_FUNCTION)
                     && (kind != T2_TYPE_OVERLOAD)
                )
        ) {
                return false;
        }

        universe->primitive_nominals[kind] = nominal;

        return true;
}

static T2Type
nominal_project_x(
        T2Universe const *universe,
        T2Type            subtype,
        u64               target_symbol,
        unsigned          depth
)
{
        if (depth > T2_RELATION_DEPTH_LIMIT) {
                return T2_TYPE_INVALID;
        }

        T2Node const *node = get_node(universe, subtype);
        if (node != NULL && node->kind != T2_TYPE_NOMINAL) {
                subtype = primitive_nominal(universe, node);
                node    = get_node(universe, subtype);
        }

        if (node == NULL || node->kind != T2_TYPE_NOMINAL) {
                return T2_TYPE_INVALID;
        }

        if (node->payload == target_symbol) {
                return subtype;
        }

        T2AppliedNominal const *applied = find_applied_nominal(universe, subtype);
        if (applied == NULL) {
                return T2_TYPE_INVALID;
        }

        for (usize i = 0; i < vN(applied->supertypes); ++i) {
                T2Type projected = nominal_project_x(
                        universe,
                        v__(applied->supertypes, i),
                        target_symbol,
                        depth + 1
                );
                if (projected != T2_TYPE_INVALID) {
                        return projected;
                }
        }

        return T2_TYPE_INVALID;
}

T2Type
t2_nominal_project(
        T2Universe const *universe,
        T2Type            subtype,
        u64               target_symbol
)
{
        subtype = t2_type_resolve_computed(universe, subtype);
        return (universe == NULL) || (target_symbol == 0)
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

        if ((polarity & T2_POLARITY_POSITIVE) != 0) {
                result |= T2_POLARITY_NEGATIVE;
        }

        if ((polarity & T2_POLARITY_NEGATIVE) != 0) {
                result |= T2_POLARITY_POSITIVE;
        }

        return result;
}

static bool
validate_variance_occurrences(
        T2Universe const    *universe,
        T2NominalInfo const *declaration,
        T2Type               type,
        unsigned             polarity,
        unsigned             depth
)
{
        if (depth > T2_RELATION_DEPTH_LIMIT) {
                return false;
        }

        T2Node const *node = get_node(universe, type);
        if (node == NULL) {
                return false;
        }

        if (
                (node->kind == T2_TYPE_VARIABLE)
             && (node->variable_kind == T2_VARIABLE_QUANTIFIED)
             && (node->payload != 0)
             && (node->payload <= declaration->arity)
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
                if (used == NULL || used->arity != node->arity) {
                        return false;
                }
                for (usize i = 0; i < node->arity; ++i) {
                        unsigned child_polarity = polarity;
                        if (used->variance[i] == T2_CONTRAVARIANT) {
                                child_polarity = flip_polarity(polarity);
                        } else if (used->variance[i] == T2_INVARIANT) {
                                child_polarity = T2_POLARITY_POSITIVE
                                               | T2_POLARITY_NEGATIVE;
                        }

                        if (
                                !validate_variance_occurrences(
                                        universe,
                                        declaration,
                                        node->children[i],
                                        child_polarity,
                                        depth + 1
                                )
                        ) {
                                return false;
                        }
                }
                return true;
        }

        if (node->kind == T2_TYPE_FUNCTION) {
                usize count = (usize)node->payload;
                if (node->arity != count + 3) {
                        return false;
                }
                for (usize i = 0; i < count; ++i) {
                        T2Node const *parameter = get_node(universe, node->children[i]);
                        if (
                                (parameter == NULL)
                             || !validate_variance_occurrences(
                                     universe,
                                     declaration,
                                     parameter->children[0],
                                     flip_polarity(polarity),
                                     depth + 1
                                )
                        ) {
                                return false;
                        }
                }

                return (
                        validate_variance_occurrences(
                                universe,
                                declaration,
                                node->children[count],
                                polarity,
                                depth + 1
                        )
                     && validate_variance_occurrences(
                                universe,
                                declaration,
                                node->children[count + 1],
                                polarity,
                                depth + 1
                        )
                     && validate_variance_occurrences(
                                universe,
                                declaration,
                                node->children[count + 2],
                                flip_polarity(polarity),
                                depth + 1
                        )
                );
        }

        if (node->kind == T2_TYPE_RECORD || node->kind == T2_TYPE_ROW) {
                for (usize i = 0; i + 1 < node->arity; ++i) {
                        T2Node const *field = get_node(universe, node->children[i]);
                        unsigned child_polarity = ((
                                                           field->payload & T2_FIELD_WRITABLE_BIT
                                                   ) != 0) ? T2_POLARITY_POSITIVE | T2_POLARITY_NEGATIVE : polarity
                        ;
                        if (
                                !validate_variance_occurrences(
                                        universe,
                                        declaration,
                                        field->children[0],
                                        child_polarity,
                                        depth + 1
                                )
                        ) {
                                return false;
                        }
                }

                return true;
        }

        if (node->kind == T2_TYPE_REFINEMENT) {
                return (
                        (node->arity == 2)
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
                        )
                );
        }

        if (node->kind == T2_TYPE_COMPUTED) {
                for (usize i = 0; i < node->arity; ++i) {
                        if (
                                !validate_variance_occurrences(
                                        universe,
                                        declaration,
                                        node->children[i],
                                        T2_POLARITY_POSITIVE | T2_POLARITY_NEGATIVE,
                                        depth + 1
                                )
                        ) {
                                return false;
                        }
                }

                return true;
        }

        for (usize i = 0; i < node->arity; ++i) {
                if (
                        !validate_variance_occurrences(
                                universe,
                                declaration,
                                node->children[i],
                                polarity,
                                depth + 1
                        )
                ) {
                        return false;
                }
        }

        return true;
}

bool
t2_nominal_validate_variance(
        T2Universe const *universe,
        u64               symbol,
        T2Type            public_contract
)
{
        T2NominalInfo const *declaration = find_nominal(universe, symbol);
        return (declaration != NULL)
            && validate_variance_occurrences(
                    universe,
                    declaration,
                    public_contract,
                    T2_POLARITY_POSITIVE,
                    0
               )
        ;
}

typedef struct t2_nominal_substitution_entry {
        T2Type source;
        T2Type result;
} T2NominalSubstitutionEntry;

typedef struct t2_nominal_substitution {
        T2Universe   *universe;
        T2Type const *arguments;
        usize         arity;
        vec(T2NominalSubstitutionEntry) entries;
} T2NominalSubstitution;

static T2Type
substitute_nominal_template(T2NominalSubstitution *substitution, T2Type source)
{
        T2Node const *node = get_node(substitution->universe, source);
        if (node == NULL) {
                return T2_TYPE_INVALID;
        }

        if (
                (node->kind == T2_TYPE_VARIABLE)
             && (node->variable_kind == T2_VARIABLE_QUANTIFIED)
             && (node->payload != 0)
             && (node->payload <= substitution->arity)
        ) {
                return substitution->arguments[node->payload - 1];
        }

        for (usize i = 0; i < vN(substitution->entries); ++i) {
                if (v__(substitution->entries, i).source == source) {
                        return v__(substitution->entries, i).result;
                }
        }

        if (node->arity == 0) {
                return source;
        }

        T2Type *children = ty_malloc(node->arity * sizeof *children);
        if (children == NULL) {
                substitution->universe->failed = true;
                return T2_TYPE_INVALID;
        }

        bool changed = false;
        for (usize i = 0; i < node->arity; ++i) {
                children[i] = substitute_nominal_template(
                        substitution,
                        node->children[i]
                );
                if (children[i] == T2_TYPE_INVALID) {
                        ty_free(children);
                        return T2_TYPE_INVALID;
                }
                changed |= children[i] != node->children[i];
        }

        T2Type result = changed
                      ? rebuild_type(substitution->universe, node, children)
                      : source;

        ty_free(children);

        if (result == T2_TYPE_INVALID) {
                return result;
        }

        xvP(substitution->entries, ((T2NominalSubstitutionEntry) {
                .source = source,
                .result = result
        }));

        return result;
}

static bool
backfill_nominal_super(
        T2Universe *universe,
        u64         symbol,
        T2Type      supertype_template
)
{
        for (usize i = 0; i < vN(universe->applied_nominals); ++i) {
                T2AppliedNominal *applied = v_(universe->applied_nominals, i);
                T2Node const *instance    = get_node(universe, applied->instance);
                if (
                        (instance == NULL)
                     || (instance->kind != T2_TYPE_NOMINAL)
                     || (instance->payload != symbol)
                ) {
                        continue;
                }
                T2NominalSubstitution substitution = {
                        .universe  = universe,
                        .arguments = instance->children,
                        .arity     = instance->arity
                };
                T2Type supertype = substitute_nominal_template(
                        &substitution,
                        supertype_template
                );
                xvF(substitution.entries);
                if (supertype == T2_TYPE_INVALID) {
                        return false;
                }
                applied = v_(universe->applied_nominals, i);
                T2Type *supertypes = ty_realloc(
                        vv(applied->supertypes),
                        (vN(applied->supertypes) + 1) * sizeof *supertypes
                );
                if (supertypes == NULL) {
                        universe->failed = true;
                        return false;
                }
                vv(applied->supertypes) = supertypes;
                xvP(applied->supertypes, supertype);
        }

        return true;
}

static T2AppliedNominal const *
find_applied_nominal(T2Universe const *universe, T2Type instance)
{
        u32 index;

        if (!t2_index_find(&universe->applied_index, instance, &index)) {
                return NULL;
        }

        return v_(universe->applied_nominals, index);
}

T2Type
t2_nominal(
        T2Universe   *universe,
        u64           symbol,
        T2Type const *arguments,
        usize         arity
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

        if (
                (instance == T2_TYPE_INVALID)
             || (find_applied_nominal(universe, instance) != NULL)
        ) {
                return instance;
        }

        usize applied_index = vN(universe->applied_nominals);
        xvP(universe->applied_nominals, ((T2AppliedNominal) {.instance = instance}));

        if (!t2_index_put(&universe->applied_index, instance, (u32)applied_index)) {
                universe->failed = true;
                return T2_TYPE_INVALID;
        }

        info->instantiated = true;

        if (vN(info->supertypes) != 0) {
                T2Type *supertypes = xtA(T2Type, vN(info->supertypes));
                T2NominalSubstitution substitution = {
                        .universe  = universe,
                        .arguments = arguments,
                        .arity     = arity
                };
                for (usize i = 0; i < vN(info->supertypes); ++i) {
                        supertypes[i] = substitute_nominal_template(
                                &substitution,
                                v__(info->supertypes, i)
                        );
                        if (supertypes[i] == T2_TYPE_INVALID) {
                                xvF(substitution.entries);
                                ty_free(supertypes);
                                return T2_TYPE_INVALID;
                        }
                }
                xvF(substitution.entries);
                vv(v__(universe->applied_nominals, applied_index).supertypes) = supertypes;
                vN(v__(universe->applied_nominals, applied_index).supertypes) = vN(info->supertypes);
        }

        return instance;
}

T2Type
t2_type_value(
        T2Universe *universe,
        T2Type      instance,
        T2Type      constructor
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
                ((T2Type[]) {instance, constructor}),
                2
        );
}

T2Type
t2_type_value_instance(T2Universe const *universe, T2Type value)
{
        T2Node const *node = get_node(universe, value);
        bool invalid = (node == NULL)
                    || (node->kind != T2_TYPE_TYPE_VALUE)
                    || (node->arity != 2)
        ;
        return invalid ? T2_TYPE_INVALID : node->children[0];
}

T2Type
t2_type_value_constructor(T2Universe const *universe, T2Type value)
{
        T2Node const *node = get_node(universe, value);
        bool invalid = (node == NULL)
                    || (node->kind != T2_TYPE_TYPE_VALUE)
                    || (node->arity != 2)
        ;
        return invalid ? T2_TYPE_INVALID : node->children[1];
}

T2Type
t2_function(
        T2Universe   *universe,
        T2Type const *parameters,
        usize         parameter_count,
        T2Type        result
)
{
        if (
                (universe == NULL)
             || (result == T2_TYPE_INVALID)
             || ((parameter_count != 0) && (parameters == NULL))
             || (parameter_count > SIZE_MAX / sizeof (T2ParameterSpec))
        ) {
                return T2_TYPE_INVALID;
        }

        T2ParameterSpec *specs = (parameter_count == 0)
                               ? NULL
                               : ty_malloc(parameter_count * sizeof *specs);

        if (parameter_count != 0 && specs == NULL) {
                universe->failed = true;
                return T2_TYPE_INVALID;
        }

        for (usize i = 0; i < parameter_count; ++i) {
                specs[i] = (T2ParameterSpec) {
                        .type     = parameters[i],
                        .kind     = T2_PARAMETER_POSITIONAL_ONLY,
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
        ty_free(specs);

        return type;
}

static bool
parameter_shape_valid(T2ParameterSpec const *parameters, usize count)
{
        bool saw_keyword_only    = false;
        bool saw_positional_rest = false;
        bool saw_keyword_rest    = false;
        bool saw_pack            = false;

        for (usize i = 0; i < count; ++i) {
                T2ParameterSpec const *parameter = &parameters[i];
                if (
                        (parameter->type == T2_TYPE_INVALID)
                     || (parameter->kind > T2_PARAMETER_PACK)
                     || (
                                (
                                        (parameter->kind == T2_PARAMETER_POSITIONAL_OR_KEYWORD)
                                     || (parameter->kind == T2_PARAMETER_KEYWORD_ONLY)
                                )
                             && (parameter->name == NULL)
                        )
                     || (
                                (parameter->kind == T2_PARAMETER_POSITIONAL_REST)
                             && parameter->required
                        )
                     || (
                                (parameter->kind == T2_PARAMETER_KEYWORD_REST)
                             && parameter->required
                        )
                     || ((parameter->kind == T2_PARAMETER_PACK) && parameter->required)
                ) {
                        return false;
                }
                switch (parameter->kind) {
                case T2_PARAMETER_POSITIONAL_ONLY:
                case T2_PARAMETER_POSITIONAL_OR_KEYWORD:
                        if (
                                saw_keyword_only
                             || saw_positional_rest
                             || saw_keyword_rest
                             || saw_pack
                        ) {
                                return false;
                        }

                        break;
                case T2_PARAMETER_KEYWORD_ONLY:
                        if (saw_keyword_rest) {
                                return false;
                        }
                        saw_keyword_only = true;
                        break;
                case T2_PARAMETER_POSITIONAL_REST:
                        if (saw_positional_rest || saw_keyword_rest || saw_pack) {
                                return false;
                        }
                        saw_positional_rest = true;
                        saw_keyword_only    = true;
                        break;
                case T2_PARAMETER_KEYWORD_REST:
                        if (saw_keyword_rest) {
                                return false;
                        }
                        saw_keyword_rest = true;
                        break;
                case T2_PARAMETER_PACK:
                        if (saw_positional_rest || saw_keyword_rest || saw_pack) {
                                return false;
                        }
                        saw_pack         = true;
                        saw_keyword_only = true;
                        break;
                }
                if (parameter->name != NULL) {
                        for (usize j = 0; j < i; ++j) {
                                if (
                                        (parameters[j].name != NULL)
                                     && s_eq(parameters[j].name, parameter->name)
                                ) {
                                        return false;
                                }
                        }
                }
        }

        return true;
}

static T2Type
callable_type(
        T2Universe            *universe,
        T2ParameterSpec const *parameters,
        usize  parameter_count,
        T2Type result,
        T2Type yield,
        T2Type send,
        bool   effectful
)
{
        if (
                (universe == NULL)
             || (result == T2_TYPE_INVALID)
             || (yield == T2_TYPE_INVALID)
             || (send == T2_TYPE_INVALID)
             || ((parameter_count != 0) && (parameters == NULL))
             || !parameter_shape_valid(parameters, parameter_count)
             || (parameter_count > SIZE_MAX - 3)
        ) {
                return T2_TYPE_INVALID;
        }

        T2Type *parts = ty_malloc((parameter_count + 3) * sizeof *parts);
        if (parts == NULL) {
                universe->failed = true;
                return T2_TYPE_INVALID;
        }

        for (usize i = 0; i < parameter_count; ++i) {
                u64 payload = (u64)parameters[i].kind;
                if (parameters[i].required) {
                        payload |= T2_PARAMETER_REQUIRED;
                }
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
                        ty_free(parts);
                        return T2_TYPE_INVALID;
                }
        }

        parts[parameter_count]     = result;
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
        ty_free(parts);

        return type;
}

T2Type
t2_callable(
        T2Universe            *universe,
        T2ParameterSpec const *parameters,
        usize  parameter_count,
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
        T2Universe            *universe,
        T2ParameterSpec const *parameters,
        usize  parameter_count,
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

usize
t2_callable_parameter_count(T2Universe const *universe, T2Type callable)
{
        T2Node const *node = get_node(universe, callable);
        return (node == NULL) || (node->kind != T2_TYPE_FUNCTION)
             ? 0
             : (usize)node->payload;
}

bool
t2_callable_parameter(
        T2Universe const *universe,
        T2Type            callable,
        usize             index,
        T2ParameterSpec  *parameter
)
{
        T2Node const *node = get_node(universe, callable);
        if (
                (node == NULL)
             || (node->kind != T2_TYPE_FUNCTION)
             || (index >= (usize)node->payload)
             || (parameter == NULL)
        ) {
                return false;
        }

        T2Node const *part = get_node(universe, node->children[index]);
        if (part == NULL || part->kind != T2_TYPE_PARAMETER) {
                return false;
        }

        *parameter = (T2ParameterSpec) {
                .name     = part->text,
                .type     = part->children[0],
                .kind     = (T2ParameterKind)(part->payload & T2_PARAMETER_KIND_MASK),
                .required = ((part->payload & T2_PARAMETER_REQUIRED) != 0)
        };

        return true;
}

static T2Type
callable_output(T2Universe const *universe, T2Type callable, usize offset)
{
        T2Node const *node = get_node(universe, callable);
        if (node == NULL || node->kind != T2_TYPE_FUNCTION) {
                return T2_TYPE_INVALID;
        }

        usize count = (usize)node->payload;

        return (node->arity == count + 3)
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
        return (node != NULL)
            && (node->kind == T2_TYPE_FUNCTION)
            && (node->variable_kind == T2_VARIABLE_RIGID);
}

T2Type
t2_tuple(T2Universe *universe, T2Type const *items, usize count)
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

T2Type
t2_multi(T2Universe *universe, T2Type const *items, usize count)
{
        T2Type nil = t2_primitive(universe, T2_TYPE_NIL);
        if (nil == T2_TYPE_INVALID) {
                return T2_TYPE_INVALID;
        }

        for (usize i = 0; i < count; ++i) {
                if (get_node(universe, items[i]) == NULL) {
                        return T2_TYPE_INVALID;
                }
        }

        while (count != 0 && items[count - 1] == nil) {
                count -= 1;
        }

        if (count == 0) {
                return nil;
        }

        if (count == 1) {
                return items[0];
        }

        return intern_type(
                universe,
                T2_TYPE_MULTI,
                T2_VARIABLE_FLEXIBLE,
                0,
                NULL,
                items,
                count
        );
}

T2Type
t2_multi_item(T2Universe const *universe, T2Type type, usize index)
{
        T2Node const *node = get_node(universe, type);
        if (node == NULL) {
                return T2_TYPE_INVALID;
        }

        if (node->kind != T2_TYPE_MULTI) {
                return (index == 0) ? type : universe->primitives[T2_TYPE_NIL];
        }

        return (index < node->arity)
             ? node->children[index]
             : universe->primitives[T2_TYPE_NIL];
}

static usize
multi_arity(T2Node const *node)
{
        return (node->kind == T2_TYPE_MULTI) ? node->arity : 1;
}

static bool
sentinel_kind(T2TypeKind kind)
{
        return (kind == T2_TYPE_NEVER)
            || (kind == T2_TYPE_UNKNOWN)
            || (kind == T2_TYPE_DYNAMIC)
            || (kind == T2_TYPE_ANY)
            || (kind == T2_TYPE_ERROR);
}

static bool
row_tail_valid(T2Universe const *universe, T2Type tail)
{
        T2Node const *node = get_node(universe, tail);
        if (node == NULL) {
                return false;
        }

        if (
                (node->kind == T2_TYPE_ROW_EMPTY)
             || (node->kind == T2_TYPE_ROW_ANY)
             || (node->kind == T2_TYPE_ROW)
             || (
                        (node->kind == T2_TYPE_META) && (node->variable_kind == T2_VARIABLE_ROW)
                )
             || (
                        (node->kind == T2_TYPE_VARIABLE)
                     && (
                                node->variable_kind == T2_VARIABLE_ROW
                        )
                )
        ) {
                return true;
        }

        if (node->kind != T2_TYPE_INTERSECTION || node->arity == 0) {
                return false;
        }

        for (usize i = 0; i < node->arity; ++i) {
                if (!row_tail_valid(universe, node->children[i])) {
                        return false;
                }
        }

        return true;
}

T2Type
t2_row(
        T2Universe        *universe,
        T2FieldSpec const *fields,
        usize              field_count,
        T2Type             tail
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
        if (node == NULL) {
                return T2_TYPE_INVALID;
        }

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
        T2Universe        *universe,
        T2FieldSpec const *fields,
        usize              field_count,
        T2Type             row_tail,
        T2RecordExactness  exactness
)
{
        if (
                (universe == NULL)
             || ((field_count != 0) && (fields == NULL))
             || (exactness > T2_RECORD_EXACT)
             || (field_count > SIZE_MAX - 1)
        ) {
                return T2_TYPE_INVALID;
        }

        if (row_tail == T2_TYPE_INVALID) {
                row_tail = t2_primitive(
                        universe,
                        (exactness == T2_RECORD_EXACT)
                        ? T2_TYPE_ROW_EMPTY
                        : T2_TYPE_ROW_ANY
                );
        }

        if (!row_tail_valid(universe, row_tail)) {
                return T2_TYPE_INVALID;
        }

        if (
                (exactness == T2_RECORD_EXACT)
             && (t2_type_kind(universe, row_tail) != T2_TYPE_ROW_EMPTY)
        ) {
                return T2_TYPE_INVALID;
        }

        T2Type *parts = ty_malloc((field_count + 1) * sizeof *parts);
        if (parts == NULL) {
                universe->failed = true;
                return T2_TYPE_INVALID;
        }

        for (usize i = 0; i < field_count; ++i) {
                if (
                        (fields[i].name == NULL)
                     || (fields[i].type == T2_TYPE_INVALID)
                     || (fields[i].presence > T2_PRESENCE_UNKNOWN)
                     || (fields[i].capability > T2_FIELD_WRITABLE)
                ) {
                        ty_free(parts);
                        return T2_TYPE_INVALID;
                }
                u64 payload = fields[i].presence;
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
                        ty_free(parts);
                        return T2_TYPE_INVALID;
                }
        }

        for (usize i = 1; i < field_count; ++i) {
                T2Type item = parts[i];
                T2Node const *item_node = get_node(universe, item);
                usize j = i;
                while (j != 0) {
                        T2Node const *previous = get_node(universe, parts[j - 1]);
                        if (strcmp(item_node->text, previous->text) >= 0) {
                                break;
                        }
                        parts[j] = parts[j - 1];
                        --j;
                }

                parts[j] = item;
        }

        for (usize i = 1; i < field_count; ++i) {
                T2Node const *left  = get_node(universe, parts[i - 1]);
                T2Node const *right = get_node(universe, parts[i]);
                if (s_eq(left->text, right->text)) {
                        ty_free(parts);
                        return T2_TYPE_INVALID;
                }
        }

        parts[field_count] = row_tail;

        T2Type type = intern_type(
                universe,
                T2_TYPE_RECORD,
                T2_VARIABLE_FLEXIBLE,
                (u64)exactness,
                NULL,
                parts,
                field_count + 1
        );
        ty_free(parts);

        return type;
}

static T2Node const *
find_record_field_node(
        T2Universe const *universe,
        T2Node const     *record,
        char const       *name
)
{
        usize low  = 0;
        usize high = record->arity - 1;

        while (low < high) {
                usize middle = low + (high - low) / 2;
                T2Node const *field = get_node(universe, record->children[middle]);
                int comparison = strcmp(field->text, name);
                if (comparison < 0) {
                        low = middle + 1;
                } else {
                        high = middle;
                }
        }

        if (low >= record->arity - 1) {
                return NULL;
        }

        T2Node const *field = get_node(universe, record->children[low]);

        return s_eq(field->text, name) ? field : NULL;
}

static T2Node const *
find_row_field_node(
        T2Universe const *universe,
        T2Type            row,
        char const       *name,
        unsigned          depth
)
{
        if (depth > T2_RELATION_DEPTH_LIMIT) {
                return NULL;
        }

        T2Node const *node = get_node(universe, row);
        if (node == NULL) {
                return NULL;
        }

        if (node->kind == T2_TYPE_INTERSECTION) {
                for (usize i = 0; i < node->arity; ++i) {
                        T2Node const *field = find_row_field_node(
                                universe,
                                node->children[i],
                                name,
                                depth + 1
                        );
                        if (field != NULL) {
                                return field;
                        }
                }

                return NULL;
        }

        if (node->kind != T2_TYPE_ROW) {
                return NULL;
        }

        T2Node const *field = find_record_field_node(universe, node, name);
        if (field != NULL) {
                return field;
        }

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
        if (depth > T2_RELATION_DEPTH_LIMIT) {
                return true;
        }

        T2Node const *node = get_node(universe, row);
        if (node == NULL) {
                return false;
        }

        if (
                ((node->kind == T2_TYPE_META) || (node->kind == T2_TYPE_VARIABLE))
             && (node->variable_kind == T2_VARIABLE_ROW)
        ) {
                return true;
        }

        if (node->kind == T2_TYPE_INTERSECTION) {
                for (usize i = 0; i < node->arity; ++i) {
                        if (row_tail_has_variable(
                                universe,
                                node->children[i],
                                depth + 1
                        )) {
                                return true;
                        }
                }

                return false;
        }

        return (node->kind == T2_TYPE_ROW)
            && row_tail_has_variable(
                    universe,
                    node->children[node->arity - 1],
                    depth + 1
               )
        ;
}

T2Type
t2_record_field_type(
        T2Universe const  *universe,
        T2Type             record,
        char const        *name,
        T2Presence        *presence,
        T2FieldCapability *capability
)
{
        T2Node const *node = get_node(universe, record);
        if (
                (node == NULL)
             || ((node->kind != T2_TYPE_RECORD) && (node->kind != T2_TYPE_ROW))
             || (name == NULL)
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

        if (field == NULL) {
                return T2_TYPE_INVALID;
        }

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

usize
t2_record_field_count(T2Universe const *universe, T2Type record)
{
        T2Node const *node = get_node(universe, record);
        if (
                (node == NULL)
             || ((node->kind != T2_TYPE_RECORD) && (node->kind != T2_TYPE_ROW))
             || (node->arity == 0)
        ) {
                return 0;
        }

        return node->arity - 1;
}

bool
t2_record_field(
        T2Universe const *universe,
        T2Type            record,
        usize             index,
        T2FieldSpec      *field
)
{
        T2Node const *node = get_node(universe, record);
        if (
                (node == NULL)
             || (field == NULL)
             || ((node->kind != T2_TYPE_RECORD) && (node->kind != T2_TYPE_ROW))
             || (node->arity == 0)
             || (index >= node->arity - 1)
        ) {
                return false;
        }

        T2Node const *entry = get_node(universe, node->children[index]);
        if (
                (entry == NULL)
             || (entry->kind != T2_TYPE_FIELD)
             || (entry->arity != 1)
             || (entry->text == NULL)
        ) {
                return false;
        }

        *field = (T2FieldSpec) {
                .name       = entry->text,
                .type       = entry->children[0],
                .presence   = (T2Presence)(entry->payload & T2_FIELD_PRESENCE_MASK),
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
                (node == NULL)
             || ((node->kind != T2_TYPE_RECORD) && (node->kind != T2_TYPE_ROW))
             || (node->arity == 0)
        ) {
                return T2_TYPE_INVALID;
        }

        return node->children[node->arity - 1];
}

bool
t2_record_exactness(
        T2Universe const  *universe,
        T2Type             record,
        T2RecordExactness *exactness
)
{
        T2Node const *node = get_node(universe, record);
        if (node == NULL || node->kind != T2_TYPE_RECORD || exactness == NULL) {
                return false;
        }

        *exactness = (T2RecordExactness)node->payload;

        return (*exactness == T2_RECORD_OPEN) || (*exactness == T2_RECORD_EXACT);
}

static bool
pack_tail_valid(T2Universe const *universe, T2Type tail)
{
        T2Node const *node = get_node(universe, tail);
        return (node != NULL)
            && (
                       (node->kind == T2_TYPE_PACK_EMPTY)
                    || (node->kind == T2_TYPE_PACK_ANY)
                    || (node->kind == T2_TYPE_PACK)
                    || (node->kind == T2_TYPE_PACK_EXPANSION)
                    || (
                               (node->kind == T2_TYPE_META)
                            && (node->variable_kind == T2_VARIABLE_PACK)
                       )
                    || (
                               (node->kind == T2_TYPE_VARIABLE)
                            && (node->variable_kind == T2_VARIABLE_PACK)
                       )
               )
        ;
}

T2Type
t2_pack(
        T2Universe   *universe,
        T2Type const *prefix,
        usize         prefix_count,
        T2Type        tail
)
{
        if (
                (universe == NULL)
             || ((prefix_count != 0) && (prefix == NULL))
             || (prefix_count > SIZE_MAX - 1)
        ) {
                return T2_TYPE_INVALID;
        }

        if (tail == T2_TYPE_INVALID) {
                tail = t2_primitive(universe, T2_TYPE_PACK_EMPTY);
        }

        if (!pack_tail_valid(universe, tail)) {
                return T2_TYPE_INVALID;
        }

        T2Type *parts = ty_malloc((prefix_count + 1) * sizeof *parts);
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
        ty_free(parts);

        return type;
}

static bool
type_contains_pack_variable(
        T2Universe const *universe,
        T2Type            type,
        unsigned          depth
)
{
        if (depth > T2_RELATION_DEPTH_LIMIT) {
                return true;
        }

        T2Node const *node = get_node(universe, type);
        if (node == NULL) {
                return true;
        }

        if (
                ((node->kind == T2_TYPE_META) || (node->kind == T2_TYPE_VARIABLE))
             && (node->variable_kind == T2_VARIABLE_PACK)
        ) {
                return true;
        }

        for (usize i = 0; i < node->arity; ++i) {
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
        if (node == NULL) {
                return T2_TYPE_INVALID;
        }

        if (pack_tail_valid(universe, element)) {
                return element;
        }

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
                (node->kind == T2_TYPE_PACK_EXPANSION)
             && !type_contains_pack_variable(universe, node->children[0], 0)
        ) {
                return node->children[0];
        }

        if (node->kind == T2_TYPE_PACK) {
                usize count = (usize)node->payload;
                T2Type result = pack_fold(
                        universe,
                        node->children[count],
                        intersection
                );
                if (result == T2_TYPE_INVALID) {
                        return result;
                }
                for (usize i = 0; i < count; ++i) {
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
                                 )
                        ;
                        if (result == T2_TYPE_INVALID) {
                                return result;
                        }
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
        T2Universe   *universe,
        T2Type const *prefix,
        usize         prefix_count,
        T2Type        tail
)
{
        if (
                (universe == NULL)
             || ((prefix_count != 0) && (prefix == NULL))
             || (prefix_count > SIZE_MAX - 1)
             || !pack_tail_valid(universe, tail)
        ) {
                return T2_TYPE_INVALID;
        }

        T2Node const *tail_node = get_node(universe, tail);
        if (tail_node->kind == T2_TYPE_PACK_EMPTY) {
                return t2_tuple(universe, prefix, prefix_count);
        }

        if (tail_node->kind == T2_TYPE_PACK) {
                usize extra = (usize)tail_node->payload;
                if (prefix_count > SIZE_MAX - extra) {
                        return T2_TYPE_INVALID;
                }
                T2Type *combined = ty_malloc(
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
                ty_free(combined);
                return result;
        }

        T2Type *parts = ty_malloc((prefix_count + 1) * sizeof *parts);
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
        ty_free(parts);

        return result;
}

static T2Type
rebuild_type(
        T2Universe   *universe,
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
                )
                ;
        case T2_TYPE_INT_RANGE:
        {
                bool has_lower = ((node->payload & T2_RANGE_HAS_LOWER) != 0);
                bool has_upper = ((node->payload & T2_RANGE_HAS_UPPER) != 0);
                return t2_integer_range(
                        universe,
                        has_lower ? children[0] : T2_TYPE_INVALID,
                        has_upper ? children[has_lower] : T2_TYPE_INVALID,
                        (node->payload & T2_RANGE_UPPER_INCLUSIVE) != 0
                );
        }
        case T2_TYPE_MULTI:
                return t2_multi(universe, children, node->arity);
        case T2_TYPE_PACK:
                return t2_pack(
                        universe,
                        children,
                        (usize)node->payload,
                        children[node->payload]
                )
                ;
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
                        (usize)node->payload,
                        children[node->payload]
                )
                ;
        case T2_TYPE_UNION:
                return t2_union(universe, children, node->arity);
        case T2_TYPE_INTERSECTION:
                return t2_intersection(universe, children, node->arity);
        default:
                return intern_type(
                        universe,
                        node->kind,
                        node->variable_kind,
                        node->payload,
                        node->text,
                        children,
                        node->arity
                )
                ;
        }
}

T2Type
t2_recursive_variable(T2Universe *universe, u32 binder)
{
        if (binder == 0) {
                return T2_TYPE_INVALID;
        }

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
        T2Type            type,
        u32               binder,
        bool              guarded,
        unsigned          depth
)
{
        if (depth > T2_RELATION_DEPTH_LIMIT) {
                return false;
        }

        T2Node const *node = get_node(universe, type);
        if (node == NULL) {
                return false;
        }

        if (node->kind == T2_TYPE_RECURSIVE_VARIABLE) {
                return (node->payload != binder) || guarded;
        }

        bool contractive = guarded
                        || (node->kind == T2_TYPE_NOMINAL)
                        || (node->kind == T2_TYPE_FUNCTION)
                        || (node->kind == T2_TYPE_TUPLE)
                        || (node->kind == T2_TYPE_VARIADIC_TUPLE)
                        || (node->kind == T2_TYPE_MULTI)
                        || (node->kind == T2_TYPE_RECORD)
                        || (node->kind == T2_TYPE_PACK)
                        || (node->kind == T2_TYPE_PACK_EXPANSION);
        if (
                (node->kind == T2_TYPE_UNION)
             || (node->kind == T2_TYPE_INTERSECTION)
             || (node->kind == T2_TYPE_RECURSIVE)
        ) {
                contractive = guarded;
        }

        for (usize i = 0; i < node->arity; ++i) {
                if (
                        !guarded_occurrences(
                                universe,
                                node->children[i],
                                binder,
                                contractive,
                                depth + 1
                        )
                ) {
                        return false;
                }
        }

        return true;
}

static bool
contains_recursive_binder(
        T2Universe const *universe,
        T2Type            type,
        u32               binder,
        unsigned          depth
)
{
        if (depth > T2_RELATION_DEPTH_LIMIT) {
                return true;
        }

        T2Node const *node = get_node(universe, type);
        if (node == NULL) {
                return true;
        }

        if (node->kind == T2_TYPE_RECURSIVE_VARIABLE) {
                return node->payload == binder;
        }

        for (usize i = 0; i < node->arity; ++i) {
                if (
                        contains_recursive_binder(
                                universe,
                                node->children[i],
                                binder,
                                depth + 1
                        )
                ) {
                        return true;
                }
        }

        return false;
}

T2Type
t2_recursive(T2Universe *universe, u32 binder, T2Type body)
{
        if (
                (universe == NULL)
             || (binder == 0)
             || (get_node(universe, body) == NULL)
        ) {
                return T2_TYPE_INVALID;
        }

        if (!contains_recursive_binder(universe, body, binder, 0)) {
                return body;
        }

        if (!guarded_occurrences(universe, body, binder, false, 0)) {
                return T2_TYPE_INVALID;
        }

        if (binder >= universe->next_recursive_id) {
                universe->next_recursive_id = (binder == UINT32_MAX) ? 0 : binder + 1;
        }

        for (usize i = 0; i < vN(universe->recursive); ++i) {
                if (v__(universe->recursive, i).binder != binder) {
                        continue;
                }
                T2Node const *existing = get_node(
                        universe,
                        v__(universe->recursive, i).type
                );
                if (existing != NULL && existing->children[0] == body) {
                        return v__(universe->recursive, i).type;
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
        if (type == T2_TYPE_INVALID) {
                return type;
        }

        xvP(universe->recursive, ((T2RecursiveInfo) {
                .binder = binder,
                .type   = type
        }));
        forget_relations(universe);

        return type;
}

bool
t2_recursive_is_guarded(T2Universe const *universe, T2Type type)
{
        T2Node const *node = get_node(universe, type);
        return (node != NULL)
            && (node->kind == T2_TYPE_RECURSIVE)
            && guarded_occurrences(
                    universe,
                    node->children[0],
                    (u32)node->payload,
                    false,
                    0
               )
        ;
}

static int
compare_types(
        T2Universe const *universe,
        T2Type            left,
        T2Type            right,
        unsigned          depth
)
{
        if (left == right) {
                return 0;
        }

        if (depth > T2_RELATION_DEPTH_LIMIT) {
                return (left < right) ? -1 : 1;
        }

        T2Node const *a = get_node(universe, left);
        T2Node const *b = get_node(universe, right);
        if (a == NULL || b == NULL) {
                return (left < right) ? -1 : 1;
        }

        if (a->kind != b->kind) {
                return (a->kind < b->kind) ? -1 : 1;
        }

        if (a->variable_kind != b->variable_kind) {
                return (a->variable_kind < b->variable_kind) ? -1 : 1;
        }

        if (a->kind == T2_TYPE_LITERAL_STRING) {
                int comparison = memcmp(a->text, b->text, min(a->payload, b->payload));
                if (comparison != 0) {
                        return comparison;
                }
                return (a->payload > b->payload) - (a->payload < b->payload);
        }

        if (a->payload != b->payload) {
                return (a->payload < b->payload) ? -1 : 1;
        }

        if ((a->text == NULL) != (b->text == NULL)) {
                return (a->text == NULL) ? -1 : 1;
        }

        if (a->text != NULL) {
                int comparison = strcmp(a->text, b->text);
                if (comparison != 0) {
                        return comparison;
                }
        }

        if (a->arity != b->arity) {
                return (a->arity < b->arity) ? -1 : 1;
        }

        for (usize i = 0; i < a->arity; ++i) {
                int comparison = compare_types(
                        universe,
                        a->children[i],
                        b->children[i],
                        depth + 1
                );
                if (comparison != 0) {
                        return comparison;
                }
        }

        return (left < right) ? -1 : 1;
}

static bool
push_type(T2TypeVector *types, T2Type type)
{
        xvP(*types, type);
        return true;
}

static bool
collect_set_arms(
        T2Universe const *universe,
        T2TypeKind        kind,
        T2Type            type,
        T2TypeVector     *arms
)
{
        T2Node const *node = get_node(universe, type);
        if (node == NULL) {
                return false;
        }

        if (node->kind != kind) {
                return push_type(arms, type);
        }

        for (usize i = 0; i < node->arity; ++i) {
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
        T2Type      subtype;
        T2Type      supertype;
        unsigned    progress;
        T2PairState state;
        T2Relation  result;
} T2RelationPair;

typedef struct t2_relation_context {
        T2Universe const   *universe;
        vec(T2RelationPair) pairs;
        usize               steps;
        usize               step_limit;
        bool                gradual;
        bool                failed;
} T2RelationContext;

static T2Relation
subtype_relation(
        T2RelationContext *context,
        T2Type             subtype,
        T2Type             supertype,
        unsigned           progress
);

static T2Relation
combine_all(T2Relation aggregate, T2Relation next);
static T2Relation
combine_any(T2Relation aggregate, T2Relation next);

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

static T2Type
primitive_nominal(T2Universe const *universe, T2Node const *node)
{
        if (node == NULL) {
                return T2_TYPE_INVALID;
        }

        T2TypeKind kind = literal_base(node->kind);

        return (kind < T2_TYPE_KIND_COUNT)
             ? universe->primitive_nominals[kind]
             : T2_TYPE_INVALID;
}

static bool
primitive_conforms(
        T2Universe const *universe,
        T2Node const     *primitive,
        T2Node const     *nominal
)
{
        T2Type bound = primitive_nominal(universe, primitive);
        return (bound != T2_TYPE_INVALID)
            && (
                    nominal_project_x(universe, bound, nominal->payload, 0)
                 != T2_TYPE_INVALID
               )
        ;
}

static T2Node const *
range_bound(
        T2Universe const *universe,
        T2Node const     *range,
        bool              lower
)
{
        u64 flag = lower ? T2_RANGE_HAS_LOWER : T2_RANGE_HAS_UPPER;
        if (range == NULL || (range->payload & flag) == 0) {
                return NULL;
        }

        usize index = !lower && ((range->payload & T2_RANGE_HAS_LOWER) != 0);

        return get_node(universe, range->children[index]);
}

static T2Relation
literal_in_range(
        T2Universe const *universe,
        T2Node const     *literal,
        T2Node const     *range
)
{
        if (literal == NULL || literal->kind != T2_TYPE_LITERAL_INT) {
                return T2_RELATION_NO;
        }

        i64 value = (i64)literal->payload;
        T2Node const *lower = range_bound(universe, range, true);
        T2Node const *upper = range_bound(universe, range, false);
        if (lower != NULL) {
                if (
                        (lower->kind == T2_TYPE_META)
                     || (lower->kind == T2_TYPE_VARIABLE)
                ) {
                        return T2_RELATION_DEFERRED;
                }

                if (
                        (lower->kind != T2_TYPE_LITERAL_INT)
                     || (value < (i64)lower->payload)
                ) {
                        return T2_RELATION_NO;
                }
        }

        if (upper != NULL) {
                if (
                        (upper->kind == T2_TYPE_META)
                     || (upper->kind == T2_TYPE_VARIABLE)
                ) {
                        return T2_RELATION_DEFERRED;
                }

                if (upper->kind != T2_TYPE_LITERAL_INT) {
                        return T2_RELATION_NO;
                }
                i64 high       = (i64)upper->payload;
                bool inclusive = ((range->payload & T2_RANGE_UPPER_INCLUSIVE) != 0);
                if (inclusive ? value > high : value >= high) {
                        return T2_RELATION_NO;
                }
        }

        return T2_RELATION_YES;
}

static T2Relation
range_subtype_range(
        T2Universe const *universe,
        T2Node const     *actual,
        T2Node const     *expected
)
{
        T2Node const *actual_lower   = range_bound(universe, actual, true);
        T2Node const *expected_lower = range_bound(universe, expected, true);
        if (expected_lower != NULL) {
                if (actual_lower == NULL) {
                        return T2_RELATION_NO;
                }
                if (
                        (actual_lower->kind == T2_TYPE_META)
                     || (actual_lower->kind == T2_TYPE_VARIABLE)
                     || (expected_lower->kind == T2_TYPE_META)
                     || (expected_lower->kind == T2_TYPE_VARIABLE)
                ) {
                        return T2_RELATION_DEFERRED;
                }

                if (
                        (actual_lower->kind != T2_TYPE_LITERAL_INT)
                     || (expected_lower->kind != T2_TYPE_LITERAL_INT)
                     || ((i64)actual_lower->payload
                       < (i64)expected_lower->payload)
                ) {
                        return T2_RELATION_NO;
                }
        }

        T2Node const *actual_upper   = range_bound(universe, actual, false);
        T2Node const *expected_upper = range_bound(universe, expected, false);
        if (expected_upper != NULL) {
                if (actual_upper == NULL) {
                        return T2_RELATION_NO;
                }
                if (
                        (actual_upper->kind == T2_TYPE_META)
                     || (actual_upper->kind == T2_TYPE_VARIABLE)
                     || (expected_upper->kind == T2_TYPE_META)
                     || (expected_upper->kind == T2_TYPE_VARIABLE)
                ) {
                        return T2_RELATION_DEFERRED;
                }

                if (
                        (actual_upper->kind != T2_TYPE_LITERAL_INT)
                     || (expected_upper->kind != T2_TYPE_LITERAL_INT)
                ) {
                        return T2_RELATION_NO;
                }

                i64 actual_high   = (i64)actual_upper->payload;
                i64 expected_high = (i64)expected_upper->payload;
                if (actual_high > expected_high) {
                        return T2_RELATION_NO;
                }
                if (
                        (actual_high == expected_high)
                     && ((actual->payload & T2_RANGE_UPPER_INCLUSIVE) != 0)
                     && ((expected->payload & T2_RANGE_UPPER_INCLUSIVE) == 0)
                ) {
                        return T2_RELATION_NO;
                }
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
        case T2_TYPE_SCHEME:
                return true;
        default:
                return false;
        }
}

static T2Type
recursive_definition(T2Universe const *universe, u32 binder)
{
        for (usize i = 0; i < vN(universe->recursive); ++i) {
                if (v__(universe->recursive, i).binder == binder) {
                        return v__(universe->recursive, i).type;
                }
        }

        return T2_TYPE_INVALID;
}

static T2Type
unfold_recursive_head(T2Universe const *universe, T2Type type, bool *changed)
{
        T2Node const *node = get_node(universe, type);
        *changed = false;
        if (node == NULL) {
                return T2_TYPE_INVALID;
        }

        if (node->kind == T2_TYPE_RECURSIVE) {
                *changed = true;
                return node->children[0];
        }

        if (node->kind == T2_TYPE_RECURSIVE_VARIABLE) {
                T2Type definition = recursive_definition(universe, (u32)node->payload);
                T2Node const *recursive = get_node(universe, definition);
                if (recursive == NULL || recursive->kind != T2_TYPE_RECURSIVE) {
                        return T2_TYPE_INVALID;
                }
                *changed = true;
                return recursive->children[0];
        }

        return type;
}

T2Type
t2_recursive_unfold(T2Universe const *universe, T2Type type)
{
        bool changed = false;
        T2Type unfolded = (universe == NULL)
                        ? T2_TYPE_INVALID
                        : unfold_recursive_head(universe, type, &changed);
        return (unfolded == T2_TYPE_INVALID) ? type : unfolded;
}

static T2Relation
compare_field_types(
        T2RelationContext *context,
        T2Node const      *actual,
        T2Node const      *expected,
        unsigned           progress,
        bool               shape_only
)
{
        T2Presence actual_presence = (actual == NULL)
                                   ? T2_PRESENCE_ABSENT
                                   : (T2Presence)(actual->payload & T2_FIELD_PRESENCE_MASK);
        T2Presence expected_presence = (T2Presence)(
                expected->payload & T2_FIELD_PRESENCE_MASK
        );

        if (expected_presence == T2_PRESENCE_REQUIRED) {
                if (actual_presence != T2_PRESENCE_REQUIRED) {
                        return T2_RELATION_NO;
                }
        } else if (expected_presence == T2_PRESENCE_ABSENT) {
                return (actual_presence == T2_PRESENCE_ABSENT)
                     ? T2_RELATION_YES
                     : T2_RELATION_NO;
        } else if (expected_presence == T2_PRESENCE_OPTIONAL) {
                if (actual_presence == T2_PRESENCE_ABSENT) {
                        return T2_RELATION_YES;
                }
                if (actual_presence == T2_PRESENCE_UNKNOWN) {
                        return T2_RELATION_NO;
                }
        } else if (actual_presence == T2_PRESENCE_ABSENT) {
                return T2_RELATION_YES;
        }

        if (actual == NULL) {
                return T2_RELATION_NO;
        }

        bool expected_writable = ((expected->payload & T2_FIELD_WRITABLE_BIT) != 0);
        bool actual_writable   = ((actual->payload & T2_FIELD_WRITABLE_BIT) != 0);
        if (expected_writable && !actual_writable) {
                return T2_RELATION_NO;
        }

        if (shape_only) {
                return T2_RELATION_YES;
        }

        return subtype_relation(
                context,
                actual->children[0],
                expected->children[0],
                progress + 1
        );
}

static T2Relation
record_subtype(
        T2RelationContext *context,
        T2Node const      *actual,
        T2Node const      *expected,
        unsigned           progress,
        bool               shape_only
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
        if (actual_tail == NULL || expected_tail == NULL) {
                return T2_RELATION_NO;
        }

        T2Relation relation = T2_RELATION_YES;
        for (usize i = 0; i + 1 < expected->arity; ++i) {
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
                        if (
                                row_tail_has_variable(
                                        context->universe,
                                        actual->children[actual->arity - 1],
                                        0
                                )
                        ) {
                                relation = combine_all(relation, T2_RELATION_DEFERRED);
                                continue;
                        }

                        T2Presence wanted_presence = (T2Presence)(
                                wanted->payload & T2_FIELD_PRESENCE_MASK
                        );
                        if (
                                (wanted_presence == T2_PRESENCE_REQUIRED)
                             || (wanted_presence == T2_PRESENCE_ABSENT)
                        ) {
                                return T2_RELATION_NO;
                        }
                }

                relation = combine_all(
                        relation,
                        compare_field_types(context, have, wanted, progress, shape_only)
                );
                if (relation == T2_RELATION_NO) {
                        return relation;
                }
        }

        if ((T2RecordExactness)expected->payload == T2_RECORD_EXACT) {
                if (
                        (actual_tail->kind != T2_TYPE_ROW_EMPTY)
                     || ((T2RecordExactness)actual->payload != T2_RECORD_EXACT)
                ) {
                        return T2_RELATION_NO;
                }

                for (usize i = 0; i + 1 < actual->arity; ++i) {
                        T2Node const *field = get_node(context->universe, actual->children[i]);
                        T2Node const *wanted = find_record_field_node(
                                context->universe,
                                expected,
                                field->text
                        );
                        if (
                                (wanted == NULL)
                             && ((field->payload & T2_FIELD_PRESENCE_MASK)
                              != T2_PRESENCE_ABSENT)
                        ) {
                                return T2_RELATION_NO;
                        }
                }
        }

        if (
                (expected_tail->kind == T2_TYPE_META)
             || (expected_tail->kind == T2_TYPE_VARIABLE)
             || (actual_tail->kind == T2_TYPE_META)
             || (actual_tail->kind == T2_TYPE_VARIABLE)
        ) {
                return combine_all(relation, T2_RELATION_DEFERRED);
        }

        return relation;
}

static T2Relation
row_subtype(
        T2RelationContext *context,
        T2Node const      *actual,
        T2Node const      *expected,
        unsigned           progress
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
        if (actual_tail == NULL || expected_tail == NULL) {
                return T2_RELATION_NO;
        }

        T2Relation relation = T2_RELATION_YES;
        for (usize i = 0; i + 1 < expected->arity; ++i) {
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
                        if (
                                row_tail_has_variable(
                                        context->universe,
                                        actual->children[actual->arity - 1],
                                        0
                                )
                        ) {
                                relation = combine_all(relation, T2_RELATION_DEFERRED);
                                continue;
                        }

                        T2Presence presence = (T2Presence)(
                                wanted->payload & T2_FIELD_PRESENCE_MASK
                        );
                        if (
                                (presence == T2_PRESENCE_REQUIRED)
                             || (presence == T2_PRESENCE_ABSENT)
                        ) {
                                return T2_RELATION_NO;
                        }
                }

                relation = combine_all(
                        relation,
                        compare_field_types(context, have, wanted, progress, false)
                );
                if (relation == T2_RELATION_NO) {
                        return relation;
                }
        }

        if (expected_tail->kind == T2_TYPE_ROW_EMPTY) {
                for (usize i = 0; i + 1 < actual->arity; ++i) {
                        T2Node const *field = get_node(context->universe, actual->children[i]);
                        if (
                                (
                                        find_record_field_node(
                                                context->universe,
                                                expected,
                                                field->text
                                        )
                                     == NULL
                                )
                             && ((field->payload & T2_FIELD_PRESENCE_MASK)
                              != T2_PRESENCE_ABSENT)
                        ) {
                                return T2_RELATION_NO;
                        }
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
        return (kind == T2_PARAMETER_POSITIONAL_ONLY)
            || (kind == T2_PARAMETER_POSITIONAL_OR_KEYWORD);
}

static bool
parameter_accepts_keyword(T2Node const *parameter)
{
        T2ParameterKind kind = (T2ParameterKind)(
                parameter->payload & T2_PARAMETER_KIND_MASK
        );
        return (kind == T2_PARAMETER_POSITIONAL_OR_KEYWORD)
            || (kind == T2_PARAMETER_KEYWORD_ONLY);
}

static T2Node const *
function_positional_parameter(
        T2Universe const *universe,
        T2Node const     *function,
        usize             position
)
{
        usize seen  = 0;
        usize count = (usize)function->payload;
        for (usize i = 0; i < count; ++i) {
                T2Node const *parameter = get_node(universe, function->children[i]);
                if (!parameter_accepts_position(parameter)) {
                        continue;
                }
                if (seen++ == position) {
                        return parameter;
                }
        }

        return NULL;
}

static T2Node const *
function_parameter_kind(
        T2Universe const *universe,
        T2Node const     *function,
        T2ParameterKind   wanted
)
{
        usize count = (usize)function->payload;
        for (usize i = 0; i < count; ++i) {
                T2Node const *parameter = get_node(universe, function->children[i]);
                T2ParameterKind kind = (T2ParameterKind)(
                        parameter->payload & T2_PARAMETER_KIND_MASK
                );
                if (kind == wanted) {
                        return parameter;
                }
        }

        return NULL;
}

static T2Node const *
function_keyword_parameter(
        T2Universe const *universe,
        T2Node const     *function,
        char const       *name
)
{
        usize count = (usize)function->payload;
        for (usize i = 0; i < count; ++i) {
                T2Node const *parameter = get_node(universe, function->children[i]);
                if (
                        parameter_accepts_keyword(parameter)
                     && (parameter->text != NULL)
                     && s_eq(parameter->text, name)
                ) {
                        return parameter;
                }
        }

        return NULL;
}

static T2Relation
contravariant_parameter(
        T2RelationContext *context,
        T2Node const      *actual,
        T2Node const      *expected,
        unsigned           progress
)
{
        if (actual == NULL || expected == NULL) {
                return T2_RELATION_NO;
        }

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
        T2Node const      *actual,
        T2Node const      *expected,
        unsigned           progress
)
{
        usize actual_count   = (usize)actual->payload;
        usize expected_count = (usize)expected->payload;
        if (
                (actual->arity != actual_count + 3)
             || (expected->arity != expected_count + 3)
        ) {
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

        T2Relation relation      = T2_RELATION_YES;
        usize expected_positions = 0;
        for (usize i = 0; i < expected_count; ++i) {
                T2Node const *parameter = get_node(
                        context->universe,
                        expected->children[i]
                );
                if (parameter_accepts_position(parameter)) {
                        expected_positions += 1;
                }
        }

        for (usize i = 0; i < expected_positions; ++i) {
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
                if (have == NULL) {
                        have = (actual_rest == NULL) ? actual_pack : actual_rest;
                }
                relation = combine_all(
                        relation,
                        contravariant_parameter(context, have, wanted, progress)
                );
                if (relation == T2_RELATION_NO) {
                        return relation;
                }
        }

        if (expected_rest != NULL || expected_pack != NULL) {
                T2Node const *wanted = (expected_rest == NULL) ? expected_pack : expected_rest;
                T2Node const *have = (actual_rest == NULL) ? actual_pack : actual_rest;
                relation = combine_all(
                        relation,
                        contravariant_parameter(context, have, wanted, progress)
                );
                if (relation == T2_RELATION_NO) {
                        return relation;
                }
        }

        for (usize i = 0; i < expected_count; ++i) {
                T2Node const *wanted = get_node(context->universe, expected->children[i]);
                if (!parameter_accepts_keyword(wanted)) {
                        continue;
                }
                T2Node const *have = function_keyword_parameter(
                        context->universe,
                        actual,
                        wanted->text
                );
                if (have == NULL) {
                        have = actual_kwrest;
                }
                relation = combine_all(
                        relation,
                        contravariant_parameter(context, have, wanted, progress)
                );
                if (relation == T2_RELATION_NO) {
                        return relation;
                }
        }

        if (expected_kwrest != NULL) {
                relation = combine_all(
                        relation,
                        contravariant_parameter(
                                context,
                                actual_kwrest,
                                expected_kwrest,
                                progress
                        )
                );
                if (relation == T2_RELATION_NO) {
                        return relation;
                }
        }

        for (usize i = 0; i < actual_count; ++i) {
                T2Node const *required = get_node(context->universe, actual->children[i]);
                if ((required->payload & T2_PARAMETER_REQUIRED) == 0) {
                        continue;
                }
                T2ParameterKind kind = (T2ParameterKind)(
                        required->payload & T2_PARAMETER_KIND_MASK
                );
                T2Node const *guaranteed = NULL;
                if (
                        (kind == T2_PARAMETER_POSITIONAL_ONLY)
                     || (kind == T2_PARAMETER_POSITIONAL_OR_KEYWORD)
                ) {
                        usize position = 0;
                        for (usize j = 0; j < i; ++j) {
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
                                (kind == T2_PARAMETER_POSITIONAL_OR_KEYWORD)
                             && (
                                        (guaranteed == NULL)
                                     || ((guaranteed->payload & T2_PARAMETER_REQUIRED) == 0)
                                )
                        ) {
                                guaranteed = function_keyword_parameter(
                                        context->universe,
                                        expected,
                                        required->text
                                );
                        }
                } else if (kind == T2_PARAMETER_KEYWORD_ONLY) {
                        guaranteed = function_keyword_parameter(
                                context->universe,
                                expected,
                                required->text
                        );
                }

                if (
                        (guaranteed == NULL)
                     || ((guaranteed->payload & T2_PARAMETER_REQUIRED) == 0)
                ) {
                        return T2_RELATION_NO;
                }
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
        T2Node const *expected_yield = get_node(
                context->universe,
                expected->children[expected_count + 1]
        );
        T2Node const *expected_send = get_node(
                context->universe,
                expected->children[expected_count + 2]
        );
        if (
                (expected_yield->kind == T2_TYPE_NEVER)
             && (expected_send->kind == T2_TYPE_NIL)
        ) {
                return relation;
        }

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
        T2Node const      *actual,
        T2Node const      *expected,
        unsigned           progress
)
{
        if (expected->kind == T2_TYPE_PACK_ANY) {
                return T2_RELATION_YES;
        }

        if (actual->kind == T2_TYPE_PACK_ANY) {
                return T2_RELATION_NO;
        }

        if (actual->kind == T2_TYPE_PACK_EMPTY) {
                return (expected->kind == T2_TYPE_PACK_EMPTY)
                    || (expected->kind == T2_TYPE_PACK_EXPANSION)
                     ? T2_RELATION_YES
                     : T2_RELATION_NO;
        }

        if (expected->kind == T2_TYPE_PACK_EMPTY) {
                return T2_RELATION_NO;
        }

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
                        usize count         = (usize)actual->payload;
                        for (usize i = 0; i < count; ++i) {
                                relation = combine_all(
                                        relation,
                                        subtype_relation(
                                                context,
                                                actual->children[i],
                                                expected->children[0],
                                                progress + 1
                                        )
                                );
                                if (relation == T2_RELATION_NO) {
                                        return relation;
                                }
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
                        (expected->kind == T2_TYPE_META)
                     || (expected->kind == T2_TYPE_VARIABLE)
                ) {
                        return T2_RELATION_DEFERRED;
                }

                return T2_RELATION_NO;
        }

        if (actual->kind != T2_TYPE_PACK || expected->kind != T2_TYPE_PACK) {
                if (
                        (actual->kind == T2_TYPE_META)
                     || (expected->kind == T2_TYPE_META)
                     || (actual->kind == T2_TYPE_VARIABLE)
                     || (expected->kind == T2_TYPE_VARIABLE)
                ) {
                        return T2_RELATION_DEFERRED;
                }

                return T2_RELATION_NO;
        }

        if (actual->payload != expected->payload) {
                return T2_RELATION_NO;
        }

        T2Relation relation = T2_RELATION_YES;
        for (usize i = 0; i < actual->arity; ++i) {
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
        T2Node const      *tuple,
        usize              offset,
        T2Node const      *expected,
        unsigned           progress
)
{
        usize remaining = tuple->arity - offset;
        if (expected->kind == T2_TYPE_PACK_ANY) {
                return T2_RELATION_YES;
        }

        if (expected->kind == T2_TYPE_PACK_EMPTY) {
                return (remaining == 0) ? T2_RELATION_YES : T2_RELATION_NO;
        }

        if (expected->kind == T2_TYPE_PACK_EXPANSION) {
                T2Relation relation = T2_RELATION_YES;
                for (usize i = offset; i < tuple->arity; ++i) {
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
                (expected->kind == T2_TYPE_META)
             || (expected->kind == T2_TYPE_VARIABLE)
        ) {
                return T2_RELATION_DEFERRED;
        }

        if (expected->kind != T2_TYPE_PACK) {
                return T2_RELATION_NO;
        }

        usize prefix = (usize)expected->payload;
        if (remaining < prefix) {
                return T2_RELATION_NO;
        }

        T2Relation relation = T2_RELATION_YES;
        for (usize i = 0; i < prefix; ++i) {
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
        T2Node const      *actual,
        T2Node const      *expected,
        unsigned           progress
)
{
        usize prefix = (usize)expected->payload;
        if (actual->arity < prefix) {
                return T2_RELATION_NO;
        }

        T2Relation relation = T2_RELATION_YES;
        for (usize i = 0; i < prefix; ++i) {
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
        T2Type             subtype,
        T2Type             supertype,
        unsigned           progress
)
{
        T2Universe const *universe = context->universe;
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

        if (
                context->gradual
             && ((a->kind == T2_TYPE_DYNAMIC) || (b->kind == T2_TYPE_DYNAMIC))
        ) {
                return T2_RELATION_YES;
        }

        if (a->kind == T2_TYPE_UNKNOWN) {
                return T2_RELATION_NO;
        }

        if (a->kind == T2_TYPE_DYNAMIC) {
                return (b->kind == T2_TYPE_DYNAMIC) ? T2_RELATION_YES : T2_RELATION_NO;
        }

        if (
                (b->kind == T2_TYPE_OBJECT)
             && object_value_kind(a->kind)
        ) {
                return T2_RELATION_YES;
        }

        if (a->kind == T2_TYPE_UNION) {
                T2Relation relation = T2_RELATION_YES;
                for (usize i = 0; i < a->arity; ++i) {
                        relation = combine_all(
                                relation,
                                subtype_relation(context, a->children[i], supertype, progress)
                        );
                        if (relation == T2_RELATION_NO) {
                                break;
                        }
                }

                return relation;
        }

        if (b->kind == T2_TYPE_UNION) {
                T2Relation relation = T2_RELATION_NO;
                for (usize i = 0; i < b->arity; ++i) {
                        relation = combine_any(
                                relation,
                                subtype_relation(context, subtype, b->children[i], progress)
                        );
                        if (relation == T2_RELATION_YES) {
                                break;
                        }
                }

                return relation;
        }

        if (b->kind == T2_TYPE_INTERSECTION) {
                T2Relation relation = T2_RELATION_YES;
                for (usize i = 0; i < b->arity; ++i) {
                        relation = combine_all(
                                relation,
                                subtype_relation(context, subtype, b->children[i], progress)
                        );
                        if (relation == T2_RELATION_NO) {
                                break;
                        }
                }

                return relation;
        }

        if (b->kind == T2_TYPE_OVERLOAD) {
                T2Relation relation = T2_RELATION_YES;
                for (usize i = 0; i < b->arity; ++i) {
                        relation = combine_all(
                                relation,
                                subtype_relation(context, subtype, b->children[i], progress)
                        );
                }

                return relation;
        }

        if (a->kind == T2_TYPE_INTERSECTION) {
                T2Relation relation = T2_RELATION_NO;
                for (usize i = 0; i < a->arity; ++i) {
                        relation = combine_any(
                                relation,
                                subtype_relation(context, a->children[i], supertype, progress)
                        );
                        if (relation == T2_RELATION_YES) {
                                break;
                        }
                }

                return relation;
        }

        if (a->kind == T2_TYPE_OVERLOAD) {
                T2Relation relation = T2_RELATION_NO;
                for (usize i = 0; i < a->arity; ++i) {
                        relation = combine_any(
                                relation,
                                subtype_relation(context, a->children[i], supertype, progress)
                        );
                        if (relation == T2_RELATION_YES) {
                                break;
                        }
                }

                return relation;
        }

        if (
                (a->kind == T2_TYPE_TYPE_VALUE)
             && (a->arity == 2)
             && (b->kind == T2_TYPE_FUNCTION)
        ) {
                return subtype_relation(context, a->children[1], supertype, progress);
        }

        if (a->kind == T2_TYPE_META || b->kind == T2_TYPE_META) {
                return T2_RELATION_DEFERRED;
        }

        if (a->kind == T2_TYPE_VARIABLE || b->kind == T2_TYPE_VARIABLE) {
                return T2_RELATION_DEFERRED;
        }

        if (a->kind == T2_TYPE_COMPUTED || b->kind == T2_TYPE_COMPUTED) {
                return T2_RELATION_DEFERRED;
        }

        if (a->kind == T2_TYPE_REFINEMENT) {
                if (a->arity != 2) {
                        return T2_RELATION_NO;
                }
                if (b->kind == T2_TYPE_REFINEMENT) {
                        if (b->arity != 2) {
                                return T2_RELATION_NO;
                        }
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

        if (b->kind == T2_TYPE_REFINEMENT) {
                return T2_RELATION_NO;
        }

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
                (a->kind == b->kind)
             && (
                        (a->kind == T2_TYPE_PACK_FOLD_UNION)
                     || (a->kind == T2_TYPE_PACK_FOLD_INTERSECTION)
                )
        ) {
                return subtype_relation(
                        context,
                        a->children[0],
                        b->children[0],
                        progress + 1
                );
        }

        if (b->kind == T2_TYPE_NOMINAL && a->kind != T2_TYPE_NOMINAL) {
                T2Type bound = primitive_nominal(universe, a);
                if (bound != T2_TYPE_INVALID) {
                        return subtype_relation(context, bound, supertype, progress + 1);
                }
        }

        if (a->kind == T2_TYPE_NOMINAL && b->kind == T2_TYPE_NOMINAL) {
                if (a->payload != b->payload || a->arity != b->arity) {
                        T2AppliedNominal const *applied = find_applied_nominal(
                                universe,
                                subtype
                        );
                        if (applied == NULL) {
                                return T2_RELATION_NO;
                        }
                        T2Relation inherited = T2_RELATION_NO;
                        for (usize i = 0; i < vN(applied->supertypes); ++i) {
                                inherited = combine_any(
                                        inherited,
                                        subtype_relation(
                                                context,
                                                v__(applied->supertypes, i),
                                                supertype,
                                                progress + 1
                                        )
                                );
                                if (inherited == T2_RELATION_YES) {
                                        break;
                                }
                        }

                        return inherited;
                }

                T2NominalInfo const *info = find_nominal(universe, a->payload);
                T2Relation relation = T2_RELATION_YES;
                for (usize i = 0; i < a->arity; ++i) {
                        T2Variance variance = (info == NULL) ? T2_INVARIANT : info->variance[i];
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
                        } else if (variance == T2_BIVARIANT) {
                                item = combine_any(
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
                (a->kind == T2_TYPE_TYPE_VALUE)
             && (b->kind == T2_TYPE_TYPE_VALUE)
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

        if (a->kind == T2_TYPE_MULTI || b->kind == T2_TYPE_MULTI) {
                usize count = (multi_arity(a) > multi_arity(b))
                            ? multi_arity(a)
                            : multi_arity(b);
                T2Relation relation = T2_RELATION_YES;
                for (usize i = 0; i < count; ++i) {
                        relation = combine_all(
                                relation,
                                subtype_relation(
                                        context,
                                        t2_multi_item(universe, subtype, i),
                                        t2_multi_item(universe, supertype, i),
                                        progress + 1
                                )
                        );
                        if (relation == T2_RELATION_NO) {
                                break;
                        }
                }

                return relation;
        }

        if (a->kind == T2_TYPE_TUPLE && b->kind == T2_TYPE_TUPLE) {
                if (a->arity != b->arity) {
                        return T2_RELATION_NO;
                }
                T2Relation relation = T2_RELATION_YES;
                for (usize i = 0; i < a->arity; ++i) {
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
                (a->kind == T2_TYPE_VARIADIC_TUPLE)
             && (b->kind == T2_TYPE_VARIADIC_TUPLE)
        ) {
                usize actual_prefix   = (usize)a->payload;
                usize expected_prefix = (usize)b->payload;
                if (actual_prefix != expected_prefix) {
                        return T2_RELATION_NO;
                }
                T2Relation relation = T2_RELATION_YES;
                for (usize i = 0; i < actual_prefix; ++i) {
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
                return record_subtype(context, a, b, progress, false);
        }

        if (a->kind == T2_TYPE_ROW && b->kind == T2_TYPE_ROW) {
                return row_subtype(context, a, b, progress);
        }

        if (a->kind == T2_TYPE_FUNCTION && b->kind == T2_TYPE_FUNCTION) {
                return function_subtype(context, a, b, progress);
        }

        if (
                (a->kind == T2_TYPE_PACK)
             || (a->kind == T2_TYPE_PACK_EMPTY)
             || (a->kind == T2_TYPE_PACK_ANY)
             || (a->kind == T2_TYPE_PACK_EXPANSION)
             || (b->kind == T2_TYPE_PACK)
             || (b->kind == T2_TYPE_PACK_EMPTY)
             || (b->kind == T2_TYPE_PACK_ANY)
             || (b->kind == T2_TYPE_PACK_EXPANSION)
        ) {
                return pack_subtype(context, a, b, progress);
        }

        if (
                (a->kind == T2_TYPE_ROW)
             || (a->kind == T2_TYPE_ROW_EMPTY)
             || (a->kind == T2_TYPE_ROW_ANY)
        ) {
                return (b->kind == T2_TYPE_ROW_ANY) || (a->kind == b->kind)
                     ? T2_RELATION_YES
                     : T2_RELATION_NO;
        }

        return T2_RELATION_NO;
}

static T2Relation
subtype_relation(
        T2RelationContext *context,
        T2Type             subtype,
        T2Type             supertype,
        unsigned           progress
)
{
        subtype   = t2_type_resolve_computed(context->universe, subtype);
        supertype = t2_type_resolve_computed(context->universe, supertype);
        if (subtype == T2_TYPE_INVALID || supertype == T2_TYPE_INVALID) {
                return T2_RELATION_COMPLEXITY;
        }

        if (subtype == supertype && subtype != T2_TYPE_INVALID) {
                return T2_RELATION_YES;
        }

        if (++context->steps > context->step_limit) {
                return T2_RELATION_COMPLEXITY;
        }

        for (;;) {
                bool changed = false;
                T2Type unfolded = unfold_recursive_head(
                        context->universe,
                        subtype,
                        &changed
                );
                if (unfolded == T2_TYPE_INVALID) {
                        return T2_RELATION_NO;
                }
                subtype = unfolded;
                if (!changed) {
                        break;
                }
                if (++context->steps > context->step_limit) {
                        return T2_RELATION_COMPLEXITY;
                }
        }

        for (;;) {
                bool changed = false;
                T2Type unfolded = unfold_recursive_head(
                        context->universe,
                        supertype,
                        &changed
                );
                if (unfolded == T2_TYPE_INVALID) {
                        return T2_RELATION_NO;
                }
                supertype = unfolded;
                if (!changed) {
                        break;
                }
                if (++context->steps > context->step_limit) {
                        return T2_RELATION_COMPLEXITY;
                }
        }

        if (subtype == supertype) {
                return T2_RELATION_YES;
        }

        for (usize i = 0; i < vN(context->pairs); ++i) {
                T2RelationPair const *pair = v_(context->pairs, i);
                if (pair->subtype != subtype || pair->supertype != supertype) {
                        continue;
                }
                if (pair->state == T2_PAIR_COMPLETE) {
                        return pair->result;
                }
                return (progress > pair->progress)
                     ? T2_RELATION_YES
                     : T2_RELATION_COMPLEXITY;
        }

        usize pair_index = vN(context->pairs);
        xvP(context->pairs, ((T2RelationPair) {
                .subtype   = subtype,
                .supertype = supertype,
                .progress  = progress,
                .state     = T2_PAIR_IN_PROGRESS,
                .result    = T2_RELATION_COMPLEXITY
        }));
        T2Relation result = subtype_compute(context, subtype, supertype, progress);
        v__(context->pairs, pair_index).state  = T2_PAIR_COMPLETE;
        v__(context->pairs, pair_index).result = result;

        return result;
}

static void
remember_relation(T2Universe const *universe, u64 key, T2Relation relation)
{
        T2Index *memo = &((T2Universe *)universe)->relation_memo;
        if (memo->count >= ((usize)1 << 20)) {
                t2_index_clear(memo);
        }

        (void)t2_index_put(memo, key, (u32)relation);
}

T2Relation
t2_subtype(T2Universe const *universe, T2Type subtype, T2Type supertype)
{
        u64 key = (u64)subtype << 32 | supertype;
        u32 remembered;
        if (
                (universe != NULL)
             && t2_index_find(&universe->relation_memo, key, &remembered)
        ) {
                return (T2Relation)remembered;
        }

        T2RelationContext context = {
                .universe   = universe,
                .step_limit = 1000000
        };
        T2Relation relation = subtype_relation(&context, subtype, supertype, 0);
        xvF(context.pairs);
        if (context.failed) {
                return T2_RELATION_COMPLEXITY;
        }

        if (
                (universe != NULL)
             && ((relation == T2_RELATION_YES) || (relation == T2_RELATION_NO))
        ) {
                remember_relation(universe, key, relation);
        }

        return relation;
}

T2Relation
t2_gradual_subtype(T2Universe const *universe, T2Type subtype, T2Type supertype)
{
        T2RelationContext context = {
                .universe   = universe,
                .step_limit = 1000000,
                .gradual    = true
        };
        T2Relation relation = subtype_relation(&context, subtype, supertype, 0);
        xvF(context.pairs);

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

static bool
definitely_disjoint(T2Universe const *universe, T2Type left, T2Type right)
{
        left  = t2_type_resolve_computed(universe, left);
        right = t2_type_resolve_computed(universe, right);
        T2Node const *a = get_node(universe, left);
        T2Node const *b = get_node(universe, right);
        if (a == NULL || b == NULL) {
                return false;
        }

        if (a->kind == T2_TYPE_NEVER || b->kind == T2_TYPE_NEVER) {
                return true;
        }

        if (
                (a->kind == T2_TYPE_ANY)
             || (a->kind == T2_TYPE_UNKNOWN)
             || (a->kind == T2_TYPE_DYNAMIC)
             || (a->kind == T2_TYPE_ERROR)
             || (b->kind == T2_TYPE_ANY)
             || (b->kind == T2_TYPE_UNKNOWN)
             || (b->kind == T2_TYPE_DYNAMIC)
             || (b->kind == T2_TYPE_ERROR)
        ) {
                return false;
        }

        if (a->kind == T2_TYPE_COMPUTED || b->kind == T2_TYPE_COMPUTED) {
                return false;
        }

        if (a->kind == T2_TYPE_REFINEMENT && a->arity == 2) {
                if (b->kind == T2_TYPE_REFINEMENT && b->arity == 2) {
                        return (
                                definitely_disjoint(
                                        universe,
                                        a->children[0],
                                        b->children[0]
                                )
                             || (
                                        (a->children[0] == b->children[0])
                                     && definitely_disjoint(
                                                universe,
                                                a->children[1],
                                                b->children[1]
                                        )
                                )
                        );
                }

                return definitely_disjoint(universe, a->children[0], right);
        }

        if (b->kind == T2_TYPE_REFINEMENT && b->arity == 2) {
                return definitely_disjoint(universe, left, b->children[0]);
        }

        if (
                (a->kind == T2_TYPE_LITERAL_INT)
             && (b->kind == T2_TYPE_LITERAL_INT)
        ) {
                return a->payload != b->payload;
        }

        if (
                (a->kind == T2_TYPE_LITERAL_BOOL)
             && (b->kind == T2_TYPE_LITERAL_BOOL)
        ) {
                return a->payload != b->payload;
        }

        if (
                (a->kind == T2_TYPE_LITERAL_STRING)
             && (b->kind == T2_TYPE_LITERAL_STRING)
        ) {
                return (a->payload != b->payload)
                    || (memcmp(a->text, b->text, a->payload) != 0);
        }

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
                        (a_upper != NULL)
                     && (b_lower != NULL)
                     && (a_upper->kind == T2_TYPE_LITERAL_INT)
                     && (b_lower->kind == T2_TYPE_LITERAL_INT)
                ) {
                        i64 high = (i64)a_upper->payload;
                        i64 low  = (i64)b_lower->payload;
                        if (
                                ((a->payload & T2_RANGE_UPPER_INCLUSIVE) != 0)
                                ? high < low
                                : high <= low
                        ) {
                                return true;
                        }
                }

                T2Node const *b_upper = range_bound(universe, b, false);
                T2Node const *a_lower = range_bound(universe, a, true);
                if (
                        (b_upper != NULL)
                     && (a_lower != NULL)
                     && (b_upper->kind == T2_TYPE_LITERAL_INT)
                     && (a_lower->kind == T2_TYPE_LITERAL_INT)
                ) {
                        i64 high = (i64)b_upper->payload;
                        i64 low  = (i64)a_lower->payload;
                        if (
                                ((b->payload & T2_RANGE_UPPER_INCLUSIVE) != 0)
                                ? high < low
                                : high <= low
                        ) {
                                return true;
                        }
                }
        }

        T2TypeKind ak = literal_base(a->kind);
        T2TypeKind bk = literal_base(b->kind);
        bool a_atomic = (ak == T2_TYPE_NIL)
                     || (ak == T2_TYPE_BOOL)
                     || (ak == T2_TYPE_INT)
                     || (ak == T2_TYPE_FLOAT)
                     || (ak == T2_TYPE_STRING)
                     || (ak == T2_TYPE_FUNCTION)
                     || (ak == T2_TYPE_TUPLE);
        bool b_atomic = (bk == T2_TYPE_NIL)
                     || (bk == T2_TYPE_BOOL)
                     || (bk == T2_TYPE_INT)
                     || (bk == T2_TYPE_FLOAT)
                     || (bk == T2_TYPE_STRING)
                     || (bk == T2_TYPE_FUNCTION)
                     || (bk == T2_TYPE_TUPLE);

        if (
                (ak == T2_TYPE_NOMINAL)
             && (bk == T2_TYPE_NOMINAL)
             && (a->payload != b->payload)
        ) {
                return disjoint_nominals(universe, left, right);
        }

        if (ak == T2_TYPE_NOMINAL && b_atomic) {
                return !primitive_conforms(universe, b, a);
        }

        if (bk == T2_TYPE_NOMINAL && a_atomic) {
                return !primitive_conforms(universe, a, b);
        }

        return a_atomic && b_atomic && (ak != bk);
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
                ((left == T2_PRESENCE_REQUIRED) && (right == T2_PRESENCE_ABSENT))
             || ((right == T2_PRESENCE_REQUIRED) && (left == T2_PRESENCE_ABSENT))
        ) {
                return false;
        }

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
                (a == NULL)
             || (b == NULL)
             || (a->kind != T2_TYPE_RECORD)
             || (b->kind != T2_TYPE_RECORD)
        ) {
                return T2_TYPE_INVALID;
        }

        usize a_count = a->arity - 1;
        usize b_count = b->arity - 1;
        T2FieldSpec *fields = ty_calloc(a_count + b_count, sizeof *fields);
        if (a_count + b_count != 0 && fields == NULL) {
                universe->failed = true;
                return T2_TYPE_INVALID;
        }

        usize ai     = 0;
        usize bi     = 0;
        usize count  = 0;
        bool a_exact = ((T2RecordExactness)a->payload == T2_RECORD_EXACT);
        bool b_exact = ((T2RecordExactness)b->payload == T2_RECORD_EXACT);
        T2Type never = t2_primitive(universe, T2_TYPE_NEVER);

        while (ai < a_count || bi < b_count) {
                T2Node const *af = (ai < a_count) ? get_node(universe, a->children[ai]) : NULL;
                T2Node const *bf = (bi < b_count) ? get_node(universe, b->children[bi]) : NULL;

                int comparison = (af == NULL) ?  1
                               : (bf == NULL) ? -1
                               :                 strcmp(af->text, bf->text);

                T2Node const *primary = (comparison <= 0) ? af: bf;
                T2Node const *other   = (comparison == 0) ? bf : NULL;

                bool other_exact = (comparison < 0) ? b_exact
                                 : (comparison > 0) ? a_exact
                                 :                    false;

                T2Presence primary_presence = (primary->payload & T2_FIELD_PRESENCE_MASK);

                T2Presence other_presence = (other == NULL)
                                          ? (other_exact ? T2_PRESENCE_ABSENT : T2_PRESENCE_UNKNOWN)
                                          : (other->payload & T2_FIELD_PRESENCE_MASK);
                T2Presence presence;
                if (!meet_presence(primary_presence, other_presence, &presence)) {
                        ty_free(fields);
                        return never;
                }

                bool primary_writable = ((primary->payload & T2_FIELD_WRITABLE_BIT) != 0);
                bool other_writable = (other != NULL)
                                   && ((other->payload & T2_FIELD_WRITABLE_BIT) != 0);

                T2Type field_type = primary->children[0];

                if (other != NULL && presence != T2_PRESENCE_ABSENT) {
                        if (primary_writable && other_writable) {
                                if (
                                        (t2_subtype(universe, field_type, other->children[0]) != T2_RELATION_YES)
                                     || (t2_subtype(universe, other->children[0], field_type) != T2_RELATION_YES)
                                ) {
                                        ty_free(fields);
                                        return never;
                                }
                        } else if (primary_writable || other_writable) {
                                T2Type writable = primary_writable ? field_type : other->children[0];
                                T2Type readonly = primary_writable ? other->children[0] : field_type;
                                if (t2_subtype(universe, writable, readonly) != T2_RELATION_YES) {
                                        ty_free(fields);
                                        return never;
                                }
                                field_type = writable;
                        } else {
                                field_type = t2_meet(universe, field_type, other->children[0]);
                                if (field_type == never) {
                                        if (presence == T2_PRESENCE_REQUIRED) {
                                                ty_free(fields);
                                                return never;
                                        }
                                        presence = T2_PRESENCE_ABSENT;
                                }
                        }
                }
                fields[count++] = (T2FieldSpec) {
                        .name       = primary->text,
                        .type       = field_type,
                        .presence   = presence,
                        .capability = (primary_writable || other_writable)
                                        ? T2_FIELD_WRITABLE
                                        : T2_FIELD_READONLY
                };
                if (comparison <= 0) {
                        ai += 1;
                }
                if (comparison >= 0) {
                        bi += 1;
                }
        }

        T2Type tail = T2_TYPE_INVALID;
        T2RecordExactness exactness = (a_exact || b_exact) ? T2_RECORD_EXACT : T2_RECORD_OPEN;

        if (exactness == T2_RECORD_OPEN) {
                T2Type a_tail = a->children[a_count];
                T2Type b_tail = b->children[b_count];
                T2Node const *an = get_node(universe, a_tail);
                T2Node const *bn = get_node(universe, b_tail);
                if (a_tail == b_tail) {
                        tail = a_tail;
                } else if (an->kind == T2_TYPE_ROW_ANY) {
                        tail = b_tail;
                } else if (bn->kind == T2_TYPE_ROW_ANY) {
                        tail = a_tail;
                } else {
                        tail = t2_intersection(universe, (T2Type[]) {a_tail, b_tail}, 2);
                }
        }

        T2Type result = t2_record(universe, fields, count, tail, exactness);
        ty_free(fields);

        return result;
}

static T2Type
make_set(
        T2Universe   *universe,
        T2TypeKind    kind,
        T2Type const *types,
        usize         count
)
{
        T2TypeVector arms = { 0 };
        bool saw_any      = false;
        bool saw_unknown  = false;
        bool saw_dynamic  = false;

        for (usize i = 0; i < count; ++i) {
                T2Node const *node = get_node(universe, types[i]);
                if (node == NULL) {
                        xvF(arms);
                        return T2_TYPE_INVALID;
                }
                if (node->kind == T2_TYPE_ERROR) {
                        xvF(arms);
                        return t2_primitive(universe, T2_TYPE_ERROR);
                }
                if (kind == T2_TYPE_UNION) {
                        if (node->kind == T2_TYPE_NEVER) {
                                continue;
                        }
                        if (node->kind == T2_TYPE_UNKNOWN) {
                                saw_unknown = true;
                        }
                        if (node->kind == T2_TYPE_ANY) {
                                saw_any = true;
                        }
                        if (node->kind == T2_TYPE_DYNAMIC) {
                                saw_dynamic = true;
                                continue;
                        }
                } else {
                        if (node->kind == T2_TYPE_NEVER) {
                                xvF(arms);
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
                xvF(arms);
                return t2_primitive(universe, T2_TYPE_UNKNOWN);
        }

        if (kind == T2_TYPE_UNION && saw_any) {
                xvF(arms);
                return t2_primitive(universe, T2_TYPE_ANY);
        }

        if (kind == T2_TYPE_UNION && saw_dynamic) {
                xvF(arms);
                return t2_primitive(universe, T2_TYPE_DYNAMIC);
        }

        for (usize i = 1; i < vN(arms); ++i) {
                T2Type item = v__(arms, i);
                usize j     = i;
                while (
                        (j != 0)
                     && (compare_types(universe, item, v__(arms, j - 1), 0) < 0)
                ) {
                        v__(arms, j) = v__(arms, j - 1);
                        --j;
                }

                v__(arms, j) = item;
        }

        usize unique = 0;
        for (usize i = 0; i < vN(arms); ++i) {
                if (
                        (unique == 0)
                     || (v__(arms, i) != v__(arms, unique - 1))
                ) {
                        v__(arms, unique++) = v__(arms, i);
                }
        }

        vN(arms) = unique;

        bool *removed = (vN(arms) == 0) ? NULL : ty_calloc(vN(arms), sizeof *removed);
        if (vN(arms) != 0 && removed == NULL) {
                universe->failed = true;
                goto Fail;
        }

        for (usize i = 0; i < vN(arms); ++i) {
                if (removed[i]) {
                        continue;
                }
                for (usize j = i + 1; j < vN(arms); ++j) {
                        if (removed[j]) {
                                continue;
                        }
                        if (
                                (kind == T2_TYPE_INTERSECTION)
                             && definitely_disjoint(universe, v__(arms, i), v__(arms, j))
                        ) {
                                ty_free(removed);
                                xvF(arms);
                                return t2_primitive(universe, T2_TYPE_NEVER);
                        }

                        T2Relation ij = t2_subtype(universe, v__(arms, i), v__(arms, j));
                        T2Relation ji = t2_subtype(universe, v__(arms, j), v__(arms, i));
                        if (kind == T2_TYPE_UNION) {
                                if (ij == T2_RELATION_YES) {
                                        removed[i] = true;
                                } else if (ji == T2_RELATION_YES) {
                                        removed[j] = true;
                                }
                        } else {
                                if (ij == T2_RELATION_YES) {
                                        removed[j] = true;
                                } else if (ji == T2_RELATION_YES) {
                                        removed[i] = true;
                                }
                        }

                        if (removed[i]) {
                                break;
                        }
                }
        }

        usize kept = 0;
        for (usize i = 0; i < vN(arms); ++i) {
                if (!removed[i]) {
                        v__(arms, kept++) = v__(arms, i);
                }
        }

        ty_free(removed);
        vN(arms) = kept;

        if (vN(arms) == 0) {
                xvF(arms);
                if (kind == T2_TYPE_UNION) {
                        return t2_primitive(universe, T2_TYPE_NEVER);
                }
                return t2_primitive(
                        universe,
                        saw_dynamic ? T2_TYPE_DYNAMIC
                        : saw_unknown ? T2_TYPE_UNKNOWN : T2_TYPE_ANY
                );
        }

        if (vN(arms) == 1) {
                T2Type only = v__(arms, 0);
                xvF(arms);
                return only;
        }

        T2Type result = intern_type(
                universe,
                kind,
                T2_VARIABLE_FLEXIBLE,
                0,
                NULL,
                vv(arms),
                vN(arms)
        );
        xvF(arms);
        return result;

Fail:
        xvF(arms);

        return T2_TYPE_INVALID;
}

T2Type
t2_union(T2Universe *universe, T2Type const *arms, usize count)
{
        return make_set(universe, T2_TYPE_UNION, arms, count);
}

T2Type
t2_intersection(T2Universe *universe, T2Type const *arms, usize count)
{
        if (count != 0) {
                bool all_records = true;
                for (usize i = 0; i < count; ++i) {
                        all_records &= t2_type_kind(universe, arms[i]) == T2_TYPE_RECORD;
                }
                if (all_records) {
                        T2Type result = arms[0];
                        for (usize i = 1; i < count; ++i) {
                                result = record_meet(universe, result, arms[i]);
                                if (
                                        (result == T2_TYPE_INVALID)
                                     || (t2_type_kind(universe, result) == T2_TYPE_NEVER)
                                ) {
                                        break;
                                }
                        }

                        return result;
                }
        }

        return make_set(universe, T2_TYPE_INTERSECTION, arms, count);
}

static bool
append_overload_candidates(
        T2Universe   *universe,
        T2TypeVector *flat,
        T2Type        candidate
)
{
        T2Node const *node = get_node(universe, candidate);
        if (node == NULL) {
                return false;
        }

        if (node->kind != T2_TYPE_OVERLOAD) {
                return push_type(flat, candidate);
        }

        for (usize i = 0; i < node->arity; ++i) {
                if (!append_overload_candidates(universe, flat, node->children[i])) {
                        return false;
                }
        }

        return true;
}

T2Type
t2_overload(T2Universe *universe, T2Type const *candidates, usize count)
{
        if (count == 0) {
                return t2_primitive(universe, T2_TYPE_NEVER);
        }

        if (candidates == NULL) {
                return T2_TYPE_INVALID;
        }

        T2TypeVector flat = { 0 };
        for (usize i = 0; i < count; ++i) {
                if (get_node(universe, candidates[i]) == NULL) {
                        xvF(flat);
                        return T2_TYPE_INVALID;
                }
                if (!append_overload_candidates(universe, &flat, candidates[i])) {
                        xvF(flat);
                        universe->failed = true;
                        return T2_TYPE_INVALID;
                }
        }

        if (vN(flat) == 1) {
                T2Type result = v__(flat, 0);
                xvF(flat);
                return result;
        }

        T2Type result = intern_type(
                universe,
                T2_TYPE_OVERLOAD,
                T2_VARIABLE_FLEXIBLE,
                vN(flat),
                NULL,
                vv(flat),
                vN(flat)
        );
        xvF(flat);

        return result;
}

static bool
interchangeable(T2Universe const *universe, T2Type left, T2Type right)
{
        T2Node const *a = get_node(universe, left);
        T2Node const *b = get_node(universe, right);
        return (a != NULL)
            && (b != NULL)
            && (((a->flags | b->flags) & T2_NODE_GRADUAL) == 0)
            && (t2_subtype(universe, right, left) == T2_RELATION_YES);
}

T2Type
t2_join(T2Universe *universe, T2Type left, T2Type right)
{
        left  = t2_type_resolve_computed(universe, left);
        right = t2_type_resolve_computed(universe, right);
        if (left == T2_TYPE_INVALID || right == T2_TYPE_INVALID) {
                return T2_TYPE_INVALID;
        }

        if (left == right) {
                return left;
        }

        T2TypeKind lk = t2_type_kind(universe, left);
        T2TypeKind rk = t2_type_kind(universe, right);
        if (lk == T2_TYPE_ERROR || rk == T2_TYPE_ERROR) {
                return t2_primitive(universe, T2_TYPE_ERROR);
        }

        if (lk == T2_TYPE_UNKNOWN || rk == T2_TYPE_UNKNOWN) {
                return t2_primitive(universe, T2_TYPE_UNKNOWN);
        }

        T2Relation lr = t2_subtype(universe, left, right);
        if (lr == T2_RELATION_YES) {
                return interchangeable(universe, left, right) ? left : right;
        }

        T2Relation rl = t2_subtype(universe, right, left);
        if (rl == T2_RELATION_YES) {
                return left;
        }

        T2Type arms[] = { left, right };

        return t2_union(universe, arms, 2);
}

static T2Type
meet_x(T2Universe *universe, T2Type left, T2Type right, unsigned depth)
{
        left  = t2_type_resolve_computed(universe, left);
        right = t2_type_resolve_computed(universe, right);
        if (left == T2_TYPE_INVALID || right == T2_TYPE_INVALID) {
                return T2_TYPE_INVALID;
        }

        if (left == right) {
                return left;
        }

        if (depth > T2_RELATION_DEPTH_LIMIT) {
                T2Type arms[] = { left, right };
                return t2_intersection(universe, arms, 2);
        }

        T2Node const *a = get_node(universe, left);
        T2Node const *b = get_node(universe, right);
        if (a == NULL || b == NULL) {
                return T2_TYPE_INVALID;
        }

        if (a->kind == T2_TYPE_ERROR || b->kind == T2_TYPE_ERROR) {
                return t2_primitive(universe, T2_TYPE_ERROR);
        }

        if (a->kind == T2_TYPE_RECORD && b->kind == T2_TYPE_RECORD) {
                return record_meet(universe, left, right);
        }

        if (
                ((a->kind == T2_TYPE_UNKNOWN) && (b->kind == T2_TYPE_ANY))
             || ((a->kind == T2_TYPE_ANY) && (b->kind == T2_TYPE_UNKNOWN))
        ) {
                return t2_primitive(universe, T2_TYPE_UNKNOWN);
        }

        T2Relation lr = t2_subtype(universe, left, right);
        if (lr == T2_RELATION_YES) {
                return left;
        }

        T2Relation rl = t2_subtype(universe, right, left);
        if (rl == T2_RELATION_YES) {
                return right;
        }

        if (a->kind == T2_TYPE_UNION || b->kind == T2_TYPE_UNION) {
                T2Node const *u = (a->kind == T2_TYPE_UNION) ? a : b;
                T2Type other         = (a->kind == T2_TYPE_UNION) ? right : left;
                T2TypeVector results = { 0 };
                T2Type never         = t2_primitive(universe, T2_TYPE_NEVER);

                for (usize i = 0; i < u->arity; ++i) {
                        T2Type item = meet_x(universe, u->children[i], other, depth + 1);
                        if (item == T2_TYPE_INVALID) {
                                xvF(results);
                                return item;
                        }
                        if (item != never && !push_type(&results, item)) {
                                xvF(results);
                                universe->failed = true;
                                return T2_TYPE_INVALID;
                        }
                }

                T2Type result = t2_union(universe, vv(results), vN(results));
                xvF(results);
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
        left  = t2_type_resolve_computed(universe, left);
        right = t2_type_resolve_computed(universe, right);
        T2Node const *a = get_node(universe, left);
        T2Node const *b = get_node(universe, right);
        if (a == NULL || b == NULL) {
                return T2_RELATION_NO;
        }

        if (
                (a->kind == T2_TYPE_DYNAMIC)
             || (b->kind == T2_TYPE_DYNAMIC)
             || (a->kind == T2_TYPE_UNKNOWN)
             || (b->kind == T2_TYPE_UNKNOWN)
             || (a->kind == T2_TYPE_ERROR)
             || (b->kind == T2_TYPE_ERROR)
        ) {
                return T2_RELATION_YES;
        }

        T2Relation ab = t2_subtype(universe, left, right);
        if (ab == T2_RELATION_YES) {
                return ab;
        }

        T2Relation ba = t2_subtype(universe, right, left);
        if (ba == T2_RELATION_YES) {
                return ba;
        }

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
        return (node == NULL) ? T2_TYPE_KIND_COUNT : (T2TypeKind)node->kind;
}

bool
t2_type_has_metas(T2Universe const *universe, T2Type type)
{
        T2Node const *node = get_node(universe, type);
        return (node != NULL) && ((node->flags & T2_NODE_META) != 0);
}

T2VariableKind
t2_type_variable_kind(T2Universe const *universe, T2Type type)
{
        T2Node const *node = get_node(universe, type);
        return (node == NULL) ? T2_VARIABLE_FLEXIBLE : node->variable_kind;
}

usize
t2_type_arity(T2Universe const *universe, T2Type type)
{
        T2Node const *node = get_node(universe, type);
        return (node == NULL) ? 0 : node->arity;
}

T2Type
t2_type_child(T2Universe const *universe, T2Type type, usize index)
{
        T2Node const *node = get_node(universe, type);
        return (node == NULL) || (index >= node->arity)
             ? T2_TYPE_INVALID
             : node->children[index];
}

u64
t2_type_payload(T2Universe const *universe, T2Type type)
{
        T2Node const *node = get_node(universe, type);
        return (node == NULL) ? 0 : node->payload;
}

char const *
t2_type_name(T2Universe const *universe, T2Type type)
{
        T2Node const *node = get_node(universe, type);
        return (node == NULL) ? NULL : node->text;
}

u64
t2_type_hash(T2Universe const *universe, T2Type type)
{
        T2Node const *node = get_node(universe, type);
        return (node == NULL) ? 0 : node->hash;
}

bool
t2_type_same(T2Universe const *universe, T2Type left, T2Type right)
{
        return (universe != NULL) && (left != T2_TYPE_INVALID) && (left == right);
}

static void
buffer_text(T2StringBuffer *buffer, char const *text)
{
        usize length = strlen(text);
        xvR(*buffer, vN(*buffer) + length + 1);
        xvPn(*buffer, text, length);
        *vZ(*buffer) = '\0';
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
        if (length < 0) {
                va_end(ap);
                return;
        }

        xvR(*buffer, vN(*buffer) + (usize)length + 1);
        vsnprintf(vv(*buffer) + vN(*buffer), (usize)length + 1, format, ap);
        va_end(ap);
        vN(*buffer) += (usize)length;
}

static char const *
primitive_name(T2TypeKind kind)
{
        static char const *const names[T2_TYPE_KIND_COUNT] = {
                [T2_TYPE_NEVER]      = "Never",
                [T2_TYPE_UNKNOWN]    = "Unknown",
                [T2_TYPE_DYNAMIC]    = "Dynamic",
                [T2_TYPE_ANY]        = "Any",
                [T2_TYPE_OBJECT]     = "Object",
                [T2_TYPE_ERROR]      = "Error",
                [T2_TYPE_NIL]        = "nil",
                [T2_TYPE_BOOL]       = "Bool",
                [T2_TYPE_INT]        = "Int",
                [T2_TYPE_FLOAT]      = "Float",
                [T2_TYPE_STRING]     = "String",
                [T2_TYPE_ROW_EMPTY]  = "{}",
                [T2_TYPE_ROW_ANY]    = "{...}",
                [T2_TYPE_PACK_EMPTY] = "[]",
                [T2_TYPE_PACK_ANY]   = "[...]"
        };

        return (kind < T2_TYPE_KIND_COUNT) ? names[kind] : NULL;
}

static char const *
variable_prefix(T2VariableKind kind)
{
        switch (kind) {
        case T2_VARIABLE_FLEXIBLE:   return "m";
        case T2_VARIABLE_RIGID:      return "r";
        case T2_VARIABLE_QUANTIFIED: return "q";
        case T2_VARIABLE_WEAK:       return "w";
        case T2_VARIABLE_ROW:        return "row";
        case T2_VARIABLE_PACK:       return "pack";
        }

        return "v";
}

enum {
        T2_PRINT_DEPTH_LIMIT = 96
};

static T2Predicate
predicate_from_node(T2Node const *node);

typedef struct t2_name_entry {
        u64  id;
        bool meta;
        bool dead;
        char name[24];
} T2NameEntry;

struct t2_names {
        vec(T2NameEntry) entries;
        unsigned         variables;
        unsigned         metas;
};

T2Names *
t2_names_new(void)
{
        return ty_calloc(1, sizeof (T2Names));
}

void
t2_names_free(T2Names *names)
{
        if (names == NULL) {
                return;
        }

        xvF(names->entries);
        ty_free(names);
}

static T2NameEntry *
find_name(T2Names const *names, bool meta, u64 id)
{
        for (usize i = vN(names->entries); i != 0; --i) {
                T2NameEntry *entry = v_(names->entries, i - 1);
                if (!entry->dead && entry->meta == meta && entry->id == id) {
                        return entry;
                }
        }

        return NULL;
}

static void
spell_name(unsigned ordinal, bool meta, char *out, usize size)
{
        unsigned letter = ordinal % 26;
        unsigned round  = ordinal / 26;
        if (round == 0) {
                ty_snprintf(out, size, "%s%c", meta ? "?" : "", 'a' + letter);
        } else {
                ty_snprintf(out, size, "%s%c%u", meta ? "?" : "", 'a' + letter, round);
        }
}

static T2NameEntry *
name_entry(T2Names *names, bool meta, u64 id, char const *chosen)
{
        T2NameEntry *entry = (chosen == NULL) ? find_name(names, meta, id) : NULL;
        if (entry != NULL) {
                return entry;
        }

        xvP(names->entries, ((T2NameEntry) { 0 }));
        entry       = v_(names->entries, vN(names->entries) - 1);
        entry->meta = meta;
        entry->id   = id;
        if (chosen != NULL) {
                ty_snprintf(entry->name, sizeof entry->name, "%s", chosen);
        } else if (meta) {
                spell_name(names->metas++, true, entry->name, sizeof entry->name);
        } else {
                spell_name(names->variables++, false, entry->name, sizeof entry->name);
        }

        return entry;
}

bool
t2_names_assign(
        T2Universe const *universe,
        T2Names          *names,
        T2Type            variable,
        char const       *name
)
{
        T2Node const *node = get_node(universe, variable);
        if (names == NULL || node == NULL || name == NULL) {
                return false;
        }

        if (node->kind != T2_TYPE_VARIABLE && node->kind != T2_TYPE_META) {
                return false;
        }

        return name_entry(names, node->kind == T2_TYPE_META, node->payload, name)
            != NULL;
}

typedef enum t2_doc_kind {
        T2_DOC_TEXT,
        T2_DOC_LINE,
        T2_DOC_SOFTLINE,
        T2_DOC_NEST,
        T2_DOC_GROUP
} T2DocKind;

typedef struct t2_doc {
        u32         next;
        u32         child;
        u32         text;
        u32         length;
        i32         indent;
        T2DocKind   kind;
        T2TokenKind token;
} T2Doc;

typedef struct t2_container {
        u32 doc;
        u32 tail;
} T2Container;

typedef struct t2_printer {
        T2Universe const *universe;
        T2PrintOptions    options;
        T2Names          *names;
        vec(T2Doc)        docs;
        vec(char)         text;
        vec(T2Container)  open;
        bool              failed;
} T2Printer;

static u32
new_doc(T2Printer *printer, T2DocKind kind)
{
        if (printer->failed) {
                return 0;
        }

        u32 index = (u32)vN(printer->docs);
        xvP(printer->docs, ((T2Doc) { .kind = kind }));

        return index;
}

static void
attach(T2Printer *printer, u32 doc)
{
        if (
                printer->failed
             || (doc == 0)
             || (vN(printer->open) == 0)
        ) {
                return;
        }

        T2Container *container = v_(printer->open, vN(printer->open) - 1);
        if (container->tail == 0) {
                v__(printer->docs, container->doc).child = doc;
        } else {
                v__(printer->docs, container->tail).next = doc;
        }

        container->tail = doc;
}

static void
open_container(T2Printer *printer, T2DocKind kind, i32 indent)
{
        u32 doc = new_doc(printer, kind);
        if (printer->failed) {
                return;
        }

        v__(printer->docs, doc).indent = indent;
        attach(printer, doc);
        xvP(printer->open, (T2Container) { .doc = doc });
}

static void
close_container(T2Printer *printer)
{
        if (!printer->failed && vN(printer->open) > 1) {
                vN(printer->open) -= 1;
        }
}

static void
open_group(T2Printer *printer)
{
        open_container(printer, T2_DOC_GROUP, 0);
}

static void
open_nest(T2Printer *printer)
{
        open_container(printer, T2_DOC_NEST, (i32)printer->options.indent);
}

static void
text_n(T2Printer *printer, T2TokenKind token, char const *text, usize length)
{
        u32 doc = new_doc(printer, T2_DOC_TEXT);
        if (printer->failed) {
                return;
        }

        v__(printer->docs, doc).text   = (u32)vN(printer->text);
        v__(printer->docs, doc).length = (u32)length;
        v__(printer->docs, doc).token  = token;
        xvPn(printer->text, text, length);
        attach(printer, doc);
}

static void
text(T2Printer *printer, T2TokenKind token, char const *string)
{
        text_n(printer, token, string, strlen(string));
}

static void
formatted(T2Printer *printer, T2TokenKind token, char const *format, ...)
{
        char buffer[64];
        va_list ap;
        va_start(ap, format);
        vsnprintf(buffer, sizeof buffer, format, ap);
        va_end(ap);
        text(printer, token, buffer);
}

static void
line(T2Printer *printer)
{
        attach(printer, new_doc(printer, T2_DOC_LINE));
}

static void
softline(T2Printer *printer)
{
        attach(printer, new_doc(printer, T2_DOC_SOFTLINE));
}

static void
begin_list(T2Printer *printer, T2TokenKind token, char const *open)
{
        text(printer, token, open);
        open_group(printer);
        open_nest(printer);
        softline(printer);
}

static void
list_separator(T2Printer *printer, usize index)
{
        if (index == 0) {
                return;
        }

        text(printer, T2_TOKEN_PUNCTUATION, ",");
        line(printer);
}

static void
end_list(T2Printer *printer, T2TokenKind token, char const *close)
{
        close_container(printer);
        softline(printer);
        close_container(printer);
        text(printer, token, close);
}

static void
doc_type(T2Printer *printer, T2Type type, unsigned depth);

static void
doc_variable(T2Printer *printer, T2Node const *node)
{
        bool meta         = (node->kind == T2_TYPE_META);
        T2TokenKind token = meta ? T2_TOKEN_META : T2_TOKEN_VARIABLE;
        if (printer->options.raw) {
                formatted(
                        printer,
                        token,
                        "$%s%" PRIu64,
                        variable_prefix(node->variable_kind),
                        node->payload
                );
                return;
        }

        T2NameEntry *entry = name_entry(printer->names, meta, node->payload, NULL);
        if (entry == NULL) {
                printer->failed = true;
                return;
        }

        text(printer, token, entry->name);
}

static void
doc_row_tail(T2Printer *printer, T2Type tail, bool after_fields, unsigned depth)
{
        T2Node const *node = get_node(printer->universe, tail);
        if (node == NULL || node->kind == T2_TYPE_ROW_EMPTY) {
                return;
        }

        if (node->kind == T2_TYPE_ROW_ANY) {
                if (!after_fields) {
                        text(printer, T2_TOKEN_PUNCTUATION, "...");
                }
                return;
        }

        if (after_fields) {
                list_separator(printer, 1);
        }

        text(printer, T2_TOKEN_PUNCTUATION, "..");
        if (node->kind != T2_TYPE_VARIABLE && node->kind != T2_TYPE_META) {
                text(printer, T2_TOKEN_PUNCTUATION, " ");
        }

        doc_type(printer, tail, depth);
}

static void
doc_fields(
        T2Printer    *printer,
        T2Node const *node,
        bool          decorated,
        unsigned      depth
)
{
        for (usize i = 0; i + 1 < node->arity; ++i) {
                T2Node const *field = get_node(printer->universe, node->children[i]);
                list_separator(printer, i);
                if (decorated && (field->payload & T2_FIELD_WRITABLE_BIT) == 0) {
                        text(printer, T2_TOKEN_KEYWORD, "const");
                        text(printer, T2_TOKEN_PUNCTUATION, " ");
                }
                if (decorated) {
                        switch ((T2Presence)(field->payload & T2_FIELD_PRESENCE_MASK)) {
                        case T2_PRESENCE_OPTIONAL:  text(printer, T2_TOKEN_PUNCTUATION, "?"); break;
                        case T2_PRESENCE_ABSENT:    text(printer, T2_TOKEN_PUNCTUATION, "!"); break;
                        case T2_PRESENCE_UNKNOWN:   text(printer, T2_TOKEN_PUNCTUATION, "~"); break;
                        case T2_PRESENCE_REQUIRED:                                            break;
                        }
                }
                text(printer, T2_TOKEN_FIELD, field->text);
                text(printer, T2_TOKEN_PUNCTUATION, ": ");
                doc_type(printer, field->children[0], depth);
        }

        if (node->arity != 0) {
                doc_row_tail(
                        printer,
                        node->children[node->arity - 1],
                        node->arity > 1,
                        depth
                );
        }
}

static void
doc_arguments(T2Printer *printer, T2Node const *node, unsigned depth)
{
        if (node->arity == 0) {
                return;
        }

        begin_list(printer, T2_TOKEN_BRACKET, "[");
        for (usize i = 0; i < node->arity; ++i) {
                list_separator(printer, i);
                doc_type(printer, node->children[i], depth);
        }
        end_list(printer, T2_TOKEN_BRACKET, "]");
}

static bool
needs_parentheses(T2Universe const *universe, T2Type type)
{
        T2Node const *node = get_node(universe, type);
        return (node != NULL) && (node->kind == T2_TYPE_FUNCTION);
}

static void
doc_operand(T2Printer *printer, T2Type type, unsigned depth)
{
        bool wrap = needs_parentheses(printer->universe, type);
        if (wrap) { text(printer, T2_TOKEN_PUNCTUATION, "("); }
        doc_type(printer, type, depth);
        if (wrap) { text(printer, T2_TOKEN_PUNCTUATION, ")"); }
}

static void
doc_arms(
        T2Printer    *printer,
        T2Node const *node,
        char const   *operator,
        unsigned      depth
)
{
        open_group(printer);
        doc_operand(printer, node->children[0], depth);
        open_nest(printer);
        for (usize i = 1; i < node->arity; ++i) {
                line(printer);
                text(printer, T2_TOKEN_OPERATOR, operator);
                text(printer, T2_TOKEN_PUNCTUATION, " ");
                doc_operand(printer, node->children[i], depth);
        }
        close_container(printer);
        close_container(printer);
}

static void
doc_function(T2Printer *printer, T2Node const *node, unsigned depth)
{
        usize parameter_count = (usize)node->payload;
        open_group(printer);
        begin_list(printer, T2_TOKEN_FUNCTION, "(");
        for (usize i = 0; i < parameter_count; ++i) {
                T2Node const *parameter = get_node(printer->universe, node->children[i]);
                list_separator(printer, i);
                T2ParameterKind kind = (parameter->payload & T2_PARAMETER_KIND_MASK);
                bool variadic = (kind == T2_PARAMETER_POSITIONAL_REST)
                             || (kind == T2_PARAMETER_KEYWORD_REST)
                             || (kind == T2_PARAMETER_PACK);
                bool optional = !variadic && ((parameter->payload & T2_PARAMETER_REQUIRED) == 0);
                if (kind == T2_PARAMETER_POSITIONAL_REST) {
                        text(printer, T2_TOKEN_PUNCTUATION, "*");
                }
                if (kind == T2_PARAMETER_KEYWORD_REST) {
                        text(printer, T2_TOKEN_PUNCTUATION, "**");
                }
                if (kind == T2_PARAMETER_PACK) {
                        text(printer, T2_TOKEN_PUNCTUATION, "...");
                }
                if (parameter->text != NULL) {
                        if (optional) {
                                text(printer, T2_TOKEN_PUNCTUATION, "?");
                        }
                        text(printer, T2_TOKEN_PARAMETER, parameter->text);
                        text(printer, T2_TOKEN_PUNCTUATION, ": ");
                        doc_type(printer, parameter->children[0], depth);
                } else {
                        doc_type(printer, parameter->children[0], depth);
                        if (optional) {
                                text(printer, T2_TOKEN_PUNCTUATION, " = ?");
                        }
                }
        }

        end_list(printer, T2_TOKEN_FUNCTION, ")");
        text(printer, T2_TOKEN_PUNCTUATION, " ");
        text(printer, T2_TOKEN_FUNCTION, "->");
        text(printer, T2_TOKEN_PUNCTUATION, " ");
        doc_type(printer, node->children[parameter_count], depth);

        T2Node const *yield = get_node(printer->universe, node->children[parameter_count + 1]);
        T2Node const *send = get_node(printer->universe, node->children[parameter_count + 2]);

        if (yield->kind != T2_TYPE_NEVER || send->kind != T2_TYPE_NIL) {
                open_nest(printer);
                line(printer);
                text(printer, T2_TOKEN_KEYWORD, "yields");
                text(printer, T2_TOKEN_PUNCTUATION, " ");
                doc_type(printer, node->children[parameter_count + 1], depth);
                text(printer, T2_TOKEN_PUNCTUATION, " ");
                text(printer, T2_TOKEN_KEYWORD, "sends");
                text(printer, T2_TOKEN_PUNCTUATION, " ");
                doc_type(printer, node->children[parameter_count + 2], depth);
                close_container(printer);
        }

        close_container(printer);
}

static void
doc_pack(T2Printer *printer, T2Node const *node, unsigned depth)
{
        text(printer, T2_TOKEN_KEYWORD, "pack");
        begin_list(printer, T2_TOKEN_BRACKET, "[");
        for (usize i = 0; i < (usize)node->payload; ++i) {
                list_separator(printer, i);
                doc_type(printer, node->children[i], depth);
        }

        if (node->arity != 0) {
                T2Node const *tail = get_node(
                        printer->universe,
                        node->children[node->arity - 1]
                );
                if (tail->kind != T2_TYPE_PACK_EMPTY) {
                        list_separator(printer, (usize)node->payload);
                        text(printer, T2_TOKEN_PUNCTUATION, ".. ");
                        doc_type(printer, node->children[node->arity - 1], depth);
                }
        }

        end_list(printer, T2_TOKEN_BRACKET, "]");
}

static void
doc_predicate(T2Printer *printer, T2Predicate const *predicate, unsigned depth);

static void
doc_where(
        T2Printer         *printer,
        T2Predicate const *predicates,
        usize              count,
        unsigned           depth
);

static void
doc_scheme_node(T2Printer *printer, T2Node const *node, unsigned depth)
{
        usize quantifier_count = (usize)node->payload;
        usize predicate_count  = node->arity - quantifier_count - 1;
        usize scope = vN(printer->names->entries);
        usize bound = 0;
        for (usize i = 0; i < quantifier_count; ++i) {
                T2Node const *binder = get_node(printer->universe, node->children[i]);
                if (binder->text == NULL || printer->options.raw) {
                        continue;
                }
                if (
                        name_entry(printer->names, false, binder->payload, binder->text) == NULL
                ) {
                        printer->failed = true;
                        return;
                }

                bound += 1;
        }

        T2Predicate *predicates = (predicate_count == 0)
                                ? NULL
                                : ty_malloc(predicate_count * sizeof *predicates);
        if (predicate_count != 0 && predicates == NULL) {
                printer->failed = true;
                return;
        }

        for (usize i = 0; i < predicate_count; ++i) {
                predicates[i] = predicate_from_node(
                        get_node(printer->universe, node->children[quantifier_count + 1 + i])
                );
        }

        open_group(printer);
        doc_type(printer, node->children[quantifier_count], depth);
        doc_where(printer, predicates, predicate_count, depth);
        close_container(printer);
        ty_free(predicates);
        for (usize i = 0; i < bound; ++i) {
                v__(printer->names->entries, scope + i).dead = true;
        }
}

static void
doc_type(T2Printer *printer, T2Type type, unsigned depth)
{
        if (printer->failed) {
                return;
        }

        T2Node const *node = get_node(printer->universe, type);
        if (node == NULL) {
                text(printer, T2_TOKEN_PRIMITIVE, "<invalid>");
                return;
        }

        if (depth > T2_PRINT_DEPTH_LIMIT) {
                text(printer, T2_TOKEN_PUNCTUATION, "...");
                return;
        }

        depth += 1;

        char const *primitive = primitive_name(node->kind);
        if (primitive != NULL) {
                text(printer, T2_TOKEN_PRIMITIVE, primitive);
                return;
        }

        switch (node->kind) {
        case T2_TYPE_LITERAL_BOOL:
                text(printer, T2_TOKEN_LITERAL, node->payload ? "true" : "false");
                break;
        case T2_TYPE_LITERAL_INT:
                formatted(printer, T2_TOKEN_LITERAL, "%" PRId64, (i64)node->payload);
                break;
        case T2_TYPE_LITERAL_STRING:
        {
                T2StringBuffer quoted = { 0 };
                buffer_text(&quoted, "'");
                for (usize i = 0; i < node->payload; ++i) {
                        u8 c = node->text[i];
                        if (c < ' ' || c == '\x7f') {
                                buffer_format(&quoted, "\\x%02x", c);
                        } else if (c == '\\' || c == '\'') {
                                buffer_format(&quoted, "\\%c", c);
                        } else {
                                buffer_format(&quoted, "%c", c);
                        }
                }
                buffer_text(&quoted, "'");
                text(printer, T2_TOKEN_LITERAL, vv(quoted));
                xvF(quoted);
                break;
        }
        case T2_TYPE_INT_RANGE:
        {
                T2Node const *lower = range_bound(printer->universe, node, true);
                T2Node const *upper = range_bound(printer->universe, node, false);
                if (lower != NULL) {
                        doc_type(printer, node->children[0], depth);
                }
                text(
                        printer,
                        T2_TOKEN_PUNCTUATION,
                        ((node->payload & T2_RANGE_UPPER_INCLUSIVE) != 0) ? "..." : ".."
                );
                if (upper != NULL) {
                        usize index = ((node->payload & T2_RANGE_HAS_LOWER) != 0);
                        doc_type(printer, node->children[index], depth);
                }
                break;
        }
        case T2_TYPE_REFINEMENT:
                doc_operand(printer, node->children[0], depth);
                begin_list(printer, T2_TOKEN_BRACKET, "[");
                doc_type(printer, node->children[1], depth);
                end_list(printer, T2_TOKEN_BRACKET, "]");
                break;
        case T2_TYPE_COMPUTED:
                text(printer, T2_TOKEN_KEYWORD, "computed");
                text(printer, T2_TOKEN_PUNCTUATION, " ");
                text(printer, T2_TOKEN_NOMINAL, node->text);
                begin_list(printer, T2_TOKEN_STRUCTURE, "(");
                for (usize i = 0; i < node->arity; ++i) {
                        list_separator(printer, i);
                        doc_type(printer, node->children[i], depth);
                }
                end_list(printer, T2_TOKEN_STRUCTURE, ")");
                break;
        case T2_TYPE_VARIABLE:
        case T2_TYPE_META:
                doc_variable(printer, node);
                break;
        case T2_TYPE_NOMINAL:
        {
                T2NominalInfo const *info = find_nominal(printer->universe, node->payload);
                if (info == NULL) {
                        formatted(printer, T2_TOKEN_NOMINAL, "Nominal#%" PRIu64, node->payload);
                } else {
                        text(printer, T2_TOKEN_NOMINAL, info->name);
                }

                doc_arguments(printer, node, depth);
                break;
        }
        case T2_TYPE_TYPE_VALUE:
                text(printer, T2_TOKEN_KEYWORD, "type");
                begin_list(printer, T2_TOKEN_BRACKET, "[");
                doc_type(printer, node->children[0], depth);
                end_list(printer, T2_TOKEN_BRACKET, "]");
                break;
        case T2_TYPE_TUPLE:
                begin_list(printer, T2_TOKEN_STRUCTURE, "(");
                for (usize i = 0; i < node->arity; ++i) {
                        list_separator(printer, i);
                        doc_type(printer, node->children[i], depth);
                }
                if (node->arity == 1) {
                        text(printer, T2_TOKEN_PUNCTUATION, ",");
                }
                end_list(printer, T2_TOKEN_STRUCTURE, ")");
                break;
        case T2_TYPE_MULTI:
                begin_list(printer, T2_TOKEN_STRUCTURE, "|");
                for (usize i = 0; i < node->arity; ++i) {
                        list_separator(printer, i);
                        doc_type(printer, node->children[i], depth);
                }
                end_list(printer, T2_TOKEN_STRUCTURE, "|");
                break;
        case T2_TYPE_VARIADIC_TUPLE:
        {
                usize prefix = (usize)node->payload;
                begin_list(printer, T2_TOKEN_STRUCTURE, "(");
                for (usize i = 0; i < prefix; ++i) {
                        list_separator(printer, i);
                        doc_type(printer, node->children[i], depth);
                }
                list_separator(printer, prefix);
                doc_type(printer, node->children[prefix], depth);
                end_list(printer, T2_TOKEN_STRUCTURE, ")");
                break;
        }
        case T2_TYPE_RECORD:
                begin_list(printer, T2_TOKEN_STRUCTURE, "{");
                doc_fields(printer, node, true, depth);
                end_list(printer, T2_TOKEN_STRUCTURE, "}");
                break;
        case T2_TYPE_ROW:
                text(printer, T2_TOKEN_KEYWORD, "row");
                begin_list(printer, T2_TOKEN_STRUCTURE, "{");
                doc_fields(printer, node, false, depth);
                end_list(printer, T2_TOKEN_STRUCTURE, "}");
                break;
        case T2_TYPE_FUNCTION:
                doc_function(printer, node, depth);
                break;
        case T2_TYPE_FIELD:
        case T2_TYPE_PARAMETER:
                if (node->text != NULL) {
                        text(
                                printer,
                                (node->kind == T2_TYPE_FIELD) ? T2_TOKEN_FIELD : T2_TOKEN_PARAMETER,
                                node->text
                        );
                        text(printer, T2_TOKEN_PUNCTUATION, ": ");
                }

                doc_type(printer, node->children[0], depth);
                break;
        case T2_TYPE_PACK:
                doc_pack(printer, node, depth);
                break;
        case T2_TYPE_PACK_EXPANSION:
                text(printer, T2_TOKEN_PUNCTUATION, "...");
                doc_operand(printer, node->children[0], depth);
                break;
        case T2_TYPE_PACK_FOLD_UNION:
        case T2_TYPE_PACK_FOLD_INTERSECTION:
                text(printer, T2_TOKEN_PUNCTUATION, "...(");
                doc_type(printer, node->children[0], depth);
                text(printer, T2_TOKEN_PUNCTUATION, " ");
                text(
                        printer,
                        T2_TOKEN_OPERATOR,
                        (node->kind == T2_TYPE_PACK_FOLD_UNION) ? "|" : "&"
                );
                text(printer, T2_TOKEN_PUNCTUATION, ")");
                break;
        case T2_TYPE_RECURSIVE:
                text(printer, T2_TOKEN_KEYWORD, "mu");
                formatted(printer, T2_TOKEN_VARIABLE, "%" PRIu64, node->payload);
                text(printer, T2_TOKEN_PUNCTUATION, ". ");
                doc_type(printer, node->children[0], depth);
                break;
        case T2_TYPE_RECURSIVE_VARIABLE:
                formatted(printer, T2_TOKEN_VARIABLE, "@%" PRIu64, node->payload);
                break;
        case T2_TYPE_UNION:
                doc_arms(printer, node, "|", depth);
                break;
        case T2_TYPE_INTERSECTION:
                doc_arms(printer, node, "&", depth);
                break;
        case T2_TYPE_SCHEME:
                doc_scheme_node(printer, node, depth);
                break;
        case T2_TYPE_PREDICATE:
        {
                T2Predicate predicate = predicate_from_node(node);
                doc_predicate(printer, &predicate, depth);
                break;
        }
        case T2_TYPE_BINDER:
                if (node->text != NULL) {
                        text(printer, T2_TOKEN_VARIABLE, node->text);
                } else {
                        doc_variable(printer, node);
                }

                break;
        case T2_TYPE_OVERLOAD:
                text(printer, T2_TOKEN_KEYWORD, "overload");
                begin_list(printer, T2_TOKEN_STRUCTURE, "{");
                for (usize i = 0; i < node->arity; ++i) {
                        if (i != 0) {
                                text(printer, T2_TOKEN_PUNCTUATION, ";");
                                line(printer);
                        }
                        doc_type(printer, node->children[i], depth);
                }

                end_list(printer, T2_TOKEN_STRUCTURE, "}");
                break;
        default:
                text(printer, T2_TOKEN_PRIMITIVE, "<unsupported>");
        }
}

static bool
unary_predicate(T2Universe const *universe, T2Predicate const *predicate)
{
        T2Node const *operand = get_node(universe, predicate->operand);
        return (operand == NULL) || (operand->kind == T2_TYPE_NEVER);
}

static void
doc_access(T2Printer *printer, T2Predicate const *predicate, unsigned depth)
{
        doc_type(printer, predicate->subtype, depth);
        switch (predicate->kind) {
        case T2_PREDICATE_MEMBER_READ:
        case T2_PREDICATE_MEMBER_WRITE:
                text(printer, T2_TOKEN_PUNCTUATION, ".");
                text(
                        printer,
                        T2_TOKEN_FIELD,
                        (predicate->name == NULL) ? "?" : predicate->name
                );
                break;
        default:
                text(printer, T2_TOKEN_BRACKET, "[");
                doc_type(printer, predicate->operand, depth);
                text(printer, T2_TOKEN_BRACKET, "]");
                break;
        }
}

static void
doc_subtype_operator(T2Printer *printer)
{
        text(printer, T2_TOKEN_PUNCTUATION, " ");
        text(printer, T2_TOKEN_OPERATOR, "<:");
        text(printer, T2_TOKEN_PUNCTUATION, " ");
}

static void
doc_predicate(T2Printer *printer, T2Predicate const *predicate, unsigned depth)
{
        switch (predicate->kind) {
        case T2_PREDICATE_SUBTYPE:
                doc_type(printer, predicate->subtype, depth);
                doc_subtype_operator(printer);
                doc_type(printer, predicate->supertype, depth);
                break;
        case T2_PREDICATE_OPERATOR:
                if (unary_predicate(printer->universe, predicate)) {
                        text(
                                printer,
                                T2_TOKEN_OPERATOR,
                                (predicate->name == NULL) ? "?" : predicate->name
                        );
                        doc_type(printer, predicate->subtype, depth);
                } else {
                        doc_type(printer, predicate->subtype, depth);
                        text(printer, T2_TOKEN_PUNCTUATION, " ");
                        text(
                                printer,
                                T2_TOKEN_OPERATOR,
                                (predicate->name == NULL) ? "?" : predicate->name
                        );
                        text(printer, T2_TOKEN_PUNCTUATION, " ");
                        doc_type(printer, predicate->operand, depth);
                }

                doc_subtype_operator(printer);
                doc_type(printer, predicate->supertype, depth);
                break;
        case T2_PREDICATE_SUBSCRIPT_READ:
        case T2_PREDICATE_MEMBER_READ:
                doc_access(printer, predicate, depth);
                doc_subtype_operator(printer);
                doc_type(printer, predicate->supertype, depth);
                break;
        case T2_PREDICATE_SUBSCRIPT_WRITE:
        case T2_PREDICATE_MEMBER_WRITE:
                doc_type(printer, predicate->supertype, depth);
                doc_subtype_operator(printer);
                doc_access(printer, predicate, depth);
                break;
        case T2_PREDICATE_KEYWORD_SPREAD:
                text(printer, T2_TOKEN_PUNCTUATION, "**");
                doc_type(printer, predicate->subtype, depth);
                doc_subtype_operator(printer);
                doc_type(printer, predicate->supertype, depth);
                break;
        }
}

static void
doc_where(
        T2Printer         *printer,
        T2Predicate const *predicates,
        usize              count,
        unsigned           depth
)
{
        if (count == 0) {
                return;
        }

        open_nest(printer);
        line(printer);
        text(printer, T2_TOKEN_KEYWORD, "where");
        open_group(printer);
        open_nest(printer);
        for (usize i = 0; i < count; ++i) {
                if (i != 0) {
                        text(printer, T2_TOKEN_PUNCTUATION, ",");
                }
                line(printer);
                doc_predicate(printer, &predicates[i], depth);
        }

        close_container(printer);
        close_container(printer);
        close_container(printer);
}

static void
doc_scheme(T2Printer *printer, T2Scheme const *scheme)
{
        open_group(printer);
        doc_type(printer, scheme->body, 0);
        doc_where(printer, scheme->predicates, scheme->predicate_count, 0);
        close_container(printer);
}

typedef struct t2_frame {
        u32  doc;
        i32  indent;
        bool flat;
} T2Frame;

typedef struct t2_frame_stack {
        vec(T2Frame) frames;
        bool         failed;
} T2FrameStack;

static void
push_frame(T2FrameStack *stack, T2Frame frame)
{
        if (frame.doc == 0 || stack->failed) {
                return;
        }

        xvP(stack->frames, frame);
}

static usize
visible_width(char const *text, usize length)
{
        usize width = 0;
        for (usize i = 0; i < length; ++i) {
                width += ((unsigned char)text[i] & 0xC0) != 0x80;
        }

        return width;
}

static bool
fits(
        T2Printer const    *printer,
        long                remaining,
        T2Frame             candidate,
        T2FrameStack const *rest
)
{
        T2FrameStack scratch = { 0 };
        push_frame(&scratch, candidate);
        usize rest_index = vN(rest->frames);
        bool answer      = true;
        for (;;) {
                if (scratch.failed) {
                        answer = false;
                        break;
                }
                if (vN(scratch.frames) == 0) {
                        if (rest_index == 0) {
                                break;
                        }
                        push_frame(&scratch, v__(rest->frames, --rest_index));
                        continue;
                }

                T2Frame frame = v__(scratch.frames, --vN(scratch.frames));
                T2Doc const *doc = v_(printer->docs, frame.doc);
                push_frame(&scratch, (T2Frame) { doc->next, frame.indent, frame.flat });
                switch (doc->kind) {
                case T2_DOC_TEXT:
                        remaining -= (long)visible_width(
                                vv(printer->text) + doc->text,
                                doc->length
                        )
                        ;
                        break;
                case T2_DOC_LINE:
                        if (!frame.flat) {
                                goto Done;
                        }
                        remaining -= 1;
                        break;
                case T2_DOC_SOFTLINE:
                        if (!frame.flat) {
                                goto Done;
                        }
                        break;
                case T2_DOC_NEST:
                case T2_DOC_GROUP:
                        push_frame(&scratch, (T2Frame) { doc->child, frame.indent, frame.flat });
                        break;
                }

                if (remaining < 0) {
                        answer = false;
                        break;
                }
        }

Done:
        xvF(scratch.frames);

        return answer;
}

static void
emit_indent(T2StringBuffer *out, unsigned hang, i32 indent)
{
        buffer_text(out, "\n");
        long spaces = (long)hang + indent;
        for (long i = 0; i < spaces; ++i) {
                buffer_text(out, " ");
        }
}

static void
emit_text(T2Printer const *printer, T2StringBuffer *out, T2Doc const *doc)
{
        char const *style = (printer->options.styles == NULL)
                          ? NULL
                          : printer->options.styles[doc->token];
        if (style != NULL && *style != '\0') {
                buffer_text(out, "\x1b[");
                buffer_text(out, style);
                buffer_text(out, "m");
        }

        xvR(*out, vN(*out) + doc->length + 1);
        xvPn(*out, vv(printer->text) + doc->text, doc->length);
        vv(*out)[vN(*out)] = '\0';
        if (style != NULL && *style != '\0') {
                buffer_text(out, "\x1b[0m");
        }
}

static char *
layout(T2Printer *printer)
{
        if (printer->failed) {
                return NULL;
        }

        T2StringBuffer out = { 0 };
        T2FrameStack stack = { 0 };
        long column = (long)printer->options.column;
        long width = (printer->options.width == 0) ? LONG_MAX : (long)printer->options.width;
        push_frame(
                &stack,
                (T2Frame) { v__(printer->docs, 0).child, 0, printer->options.width == 0 }
        );
        while (vN(stack.frames) != 0 && !stack.failed) {
                T2Frame frame = vv(stack.frames)[--vN(stack.frames)];
                T2Doc const *doc = v_(printer->docs, frame.doc);
                push_frame(&stack, (T2Frame) { doc->next, frame.indent, frame.flat });
                switch (doc->kind) {
                case T2_DOC_TEXT:
                        emit_text(printer, &out, doc);
                        column += (long)visible_width(vv(printer->text) + doc->text, doc->length);
                        break;
                case T2_DOC_LINE:
                        if (frame.flat) {
                                buffer_text(&out, " ");
                                column += 1;
                        } else {
                                emit_indent(&out, printer->options.hang, frame.indent);
                                column = (long)printer->options.hang + frame.indent;
                        }

                        break;
                case T2_DOC_SOFTLINE:
                        if (!frame.flat) {
                                emit_indent(&out, printer->options.hang, frame.indent);
                                column = (long)printer->options.hang + frame.indent;
                        }

                        break;
                case T2_DOC_NEST:
                        push_frame(
                                &stack,
                                (T2Frame) { doc->child, frame.indent + doc->indent, frame.flat }
                        )
                        ;
                        break;
                case T2_DOC_GROUP:
                {
                        T2Frame child = { doc->child, frame.indent, true };
                        if (
                                !frame.flat
                             && !fits(printer, width - column, child, &stack)
                        ) {
                                child.flat = false;
                        }

                        push_frame(&stack, child);
                        break;
                }
                }
        }

        bool failed = stack.failed;
        xvF(stack.frames);
        if (failed) {
                xvF(out);
                return NULL;
        }

        return (vv(out) == NULL) ? S2("") : vv(out);
}

static void
printer_init(
        T2Printer            *printer,
        T2Universe const     *universe,
        T2PrintOptions const *options
)
{
        static T2PrintOptions const defaults = { .indent = 4 };
        *printer = (T2Printer) {
                .universe = universe,
                .options  = (options == NULL) ? defaults : *options
        };
        if (printer->options.indent == 0) {
                printer->options.indent = 4;
        }

        printer->names = (printer->options.names != NULL)
                       ? printer->options.names
                       : t2_names_new();
        if (printer->names == NULL) {
                printer->failed = true;
                return;
        }

        u32 root = new_doc(printer, T2_DOC_NEST);
        if (printer->failed) {
                return;
        }

        xvP(printer->open, (T2Container) { .doc = root });
}

static char *
printer_finish(T2Printer *printer)
{
        char *result = layout(printer);
        if (printer->options.names == NULL) {
                t2_names_free(printer->names);
        }

        xvF(printer->docs);
        xvF(printer->text);
        xvF(printer->open);

        return result;
}

char *
t2_type_render(
        T2Universe const     *universe,
        T2Type                type,
        T2PrintOptions const *options
)
{
        T2Printer printer;
        printer_init(&printer, universe, options);
        doc_type(&printer, type, 0);
        return printer_finish(&printer);
}

char *
t2_scheme_render(
        T2Universe const     *universe,
        T2Scheme const       *scheme,
        T2PrintOptions const *options
)
{
        if (scheme == NULL) {
                return NULL;
        }

        T2Printer printer;
        printer_init(&printer, universe, options);
        doc_scheme(&printer, scheme);

        return printer_finish(&printer);
}

char *
t2_predicate_render(
        T2Universe const     *universe,
        T2Predicate const    *predicate,
        T2PrintOptions const *options
)
{
        if (predicate == NULL) {
                return NULL;
        }

        T2Printer printer;
        printer_init(&printer, universe, options);
        doc_predicate(&printer, predicate, 0);

        return printer_finish(&printer);
}

char *
t2_type_string(T2Universe const *universe, T2Type type)
{
        T2PrintOptions options = { .raw = true, .indent = 4 };
        return t2_type_render(universe, type, &options);
}

void
t2_string_free(char *text)
{
        ty_free(text);
}

typedef struct t2_substitution {
        T2Universe   *universe;
        u32 const    *ids;
        T2Type const *replacements;
        usize         count;
} T2Substitution;

static T2Type
substitute_type(
        T2Substitution const *substitution,
        T2Type                source,
        unsigned              depth
)
{
        T2Node const *node = get_node(substitution->universe, source);
        if (node == NULL || depth > T2_RELATION_DEPTH_LIMIT) {
                return source;
        }

        if (node->kind == T2_TYPE_VARIABLE) {
                for (usize i = 0; i < substitution->count; ++i) {
                        if (node->payload == substitution->ids[i]) {
                                return substitution->replacements[i];
                        }
                }

                return source;
        }

        if (node->arity == 0 || node->kind == T2_TYPE_RECURSIVE) {
                return source;
        }

        T2Type *children = ty_malloc(node->arity * sizeof *children);
        if (children == NULL) {
                return T2_TYPE_INVALID;
        }

        bool changed = false;
        for (usize i = 0; i < node->arity; ++i) {
                children[i] = substitute_type(substitution, node->children[i], depth + 1);
                if (children[i] == T2_TYPE_INVALID) {
                        ty_free(children);
                        return T2_TYPE_INVALID;
                }
                changed |= children[i] != node->children[i];
        }

        T2Type result = changed
                      ? rebuild_type(substitution->universe, node, children)
                      : source;
        ty_free(children);

        return result;
}

T2Type
t2_type_substitute(
        T2Universe   *universe,
        T2Type        type,
        u32 const    *ids,
        T2Type const *replacements,
        usize         count
)
{
        if (
                (universe == NULL)
             || ((count != 0) && ((ids == NULL) || (replacements == NULL)))
        ) {
                return T2_TYPE_INVALID;
        }

        T2Substitution substitution = {
                .universe = universe,
                .ids      = ids,
                .replacements = replacements,
                .count        = count
        };

        return substitute_type(&substitution, type, 0);
}

enum {
        T2_WIRE_NO_TEXT = UINT32_MAX
};

bool
t2_bytes_append(byte_vector *bytes, void const *data, usize size)
{
        xvPn(*bytes, data, size);
        return true;
}

bool
t2_bytes_u8(byte_vector *bytes, uint8_t value)
{
        xvP(*bytes, (char)value);
        return true;
}

bool
t2_bytes_u32(byte_vector *bytes, u32 value)
{
        unsigned char raw[4];
        for (usize i = 0; i < 4; ++i) {
                raw[i] = (unsigned char)(value >> (8 * i));
        }

        return t2_bytes_append(bytes, raw, sizeof raw);
}

bool
t2_bytes_u64(byte_vector *bytes, u64 value)
{
        unsigned char raw[8];
        for (usize i = 0; i < 8; ++i) {
                raw[i] = (unsigned char)(value >> (8 * i));
        }

        return t2_bytes_append(bytes, raw, sizeof raw);
}

static bool
write_text(byte_vector *bytes, char const *text, usize length)
{
        if (text == NULL) {
                return t2_bytes_u32(bytes, T2_WIRE_NO_TEXT);
        }

        if (length >= T2_WIRE_NO_TEXT) {
                return false;
        }

        return t2_bytes_u32(bytes, (u32)length)
            && t2_bytes_append(
                    bytes,
                    text,
                    length
               )
        ;
}

bool
t2_bytes_string(byte_vector *bytes, char const *text)
{
        return write_text(bytes, text, (text == NULL) ? 0 : strlen(text));
}

bool
t2_read_u8(
        unsigned char const *data,
        usize                size,
        usize               *position,
        uint8_t             *value
)
{
        if (*position + 1 > size) {
                return false;
        }

        *value = data[*position];
        *position += 1;

        return true;
}

bool
t2_read_u32(unsigned char const *data, usize size, usize *position, u32 *value)
{
        if (*position + 4 > size) {
                return false;
        }

        u32 result = 0;
        for (usize i = 0; i < 4; ++i) {
                result |= (u32)data[*position + i] << (8 * i);
        }

        *position += 4;
        *value = result;

        return true;
}

bool
t2_read_u64(unsigned char const *data, usize size, usize *position, u64 *value)
{
        if (*position + 8 > size) {
                return false;
        }

        u64 result = 0;
        for (usize i = 0; i < 8; ++i) {
                result |= (u64)data[*position + i] << (8 * i);
        }

        *position += 8;
        *value = result;

        return true;
}

static bool
read_text(
        unsigned char const *data,
        usize                size,
        usize               *position,
        char               **text,
        u32                 *length
)
{
        if (!t2_read_u32(data, size, position, length)) {
                return false;
        }

        if (*length == T2_WIRE_NO_TEXT) {
                *text = NULL;
                return true;
        }

        if (*position > size || *length > size - *position) {
                return false;
        }

        char *copy = ty_malloc((usize)*length + 1);
        if (copy == NULL) {
                return false;
        }

        memcpy(copy, data + *position, *length);
        copy[*length] = '\0';
        *position += *length;
        *text = copy;

        return true;
}

bool
t2_read_string(
        unsigned char const *data,
        usize                size,
        usize               *position,
        char               **text
)
{
        u32 length;
        return read_text(data, size, position, text, &length);
}

struct t2_type_writer {
        T2Universe   *universe;
        T2SymbolRemap remap;
        T2Index       memo;
        byte_vector   table;
        u32           count;
};

T2TypeWriter *
t2_type_writer_new(T2Universe *universe, T2SymbolRemap remap)
{
        if (universe == NULL) {
                return NULL;
        }

        T2TypeWriter *writer = ty_calloc(1, sizeof *writer);
        if (writer == NULL) {
                return NULL;
        }

        writer->universe = universe;
        writer->remap    = remap;

        return writer;
}

static bool
writer_visit(T2TypeWriter *writer, T2Type type, u32 *index)
{
        T2Universe *universe = writer->universe;
        T2Node const *node   = get_node(universe, type);
        if (node != NULL && node->kind == T2_TYPE_COMPUTED) {
                type = t2_type_resolve_computed(universe, type);
                node = get_node(universe, type);
        }

        if (node == NULL) {
                return false;
        }

        u32 known;
        if (t2_index_find(&writer->memo, type, &known)) {
                *index = known;
                return true;
        }

        u64 payload = node->payload;
        if (node->kind == T2_TYPE_NOMINAL) {
                if (writer->remap.out == NULL) {
                        return false;
                }
                payload = writer->remap.out(writer->remap.context, payload);
                if (payload == UINT64_MAX) {
                        return false;
                }
        }

        u32 *children = (node->arity == 0) ? NULL : xtA(u32, node->arity);
        for (usize i = 0; i < node->arity; ++i) {
                if (!writer_visit(writer, node->children[i], &children[i])) {
                        ty_free(children);
                        return false;
                }
        }

        bool ok = t2_bytes_u8(&writer->table, (uint8_t)node->kind)
               && t2_bytes_u8(&writer->table, (uint8_t)node->variable_kind)
               && t2_bytes_u64(&writer->table, payload)
               && write_text(
                       &writer->table,
                       node->text,
                       text_len(node->kind, node->payload, node->text)
                  )
               && t2_bytes_u32(&writer->table, node->arity);

        for (usize i = 0; ok && i < node->arity; ++i) {
                ok = t2_bytes_u32(&writer->table, children[i]);
        }

        ty_free(children);

        if (!ok) {
                return false;
        }

        *index = writer->count;

        if (!t2_index_put(&writer->memo, type, writer->count)) {
                return false;
        }

        writer->count += 1;

        return true;
}

bool
t2_type_writer_add(T2TypeWriter *writer, T2Type type, u32 *index)
{
        if (writer == NULL || index == NULL) {
                return false;
        }

        return writer_visit(writer, type, index);
}

usize
t2_type_writer_count(T2TypeWriter const *writer)
{
        return (writer == NULL) ? 0 : writer->count;
}

bool
t2_type_writer_encode(T2TypeWriter const *writer, byte_vector *out)
{
        if (writer == NULL || out == NULL) {
                return false;
        }

        return t2_bytes_u32(out, writer->count)
            && t2_bytes_append(out, vv(writer->table), vN(writer->table));
}

void
t2_type_writer_free(T2TypeWriter *writer)
{
        if (writer == NULL) {
                return;
        }

        t2_index_free(&writer->memo);
        xvF(writer->table);
        ty_free(writer);
}

struct t2_type_reader {
        T2Universe *universe;
        T2Type     *types;
        u32         count;
        u32         variable_limit;
        u32         variable_floor;
        u32         variable_base;
        bool        rebased;
};

struct wire_record {
        u64     payload;
        char   *text;
        u32     arity;
        u32     first_child;
        uint8_t kind;
        uint8_t variable_kind;
};

static u32
rebase_variable(T2TypeReader const *reader, u32 id)
{
        if (!reader->rebased || id < reader->variable_floor) {
                return id;
        }

        return id - reader->variable_floor + reader->variable_base;
}

static T2Type
reader_build(
        T2Universe    *universe,
        T2SymbolRemap  remap,
        T2ReadHooks    hooks,
        T2Index       *binders,
        T2TypeKind     kind,
        T2VariableKind variable_kind,
        u64            payload,
        char const    *text,
        T2Type const  *children,
        u32            arity
)
{
        switch (kind) {
        case T2_TYPE_META:
                return (hooks.meta == NULL)
                     ? T2_TYPE_INVALID
                     : hooks.meta(hooks.context, variable_kind);
        case T2_TYPE_COMPUTED:
                return t2_computed_type(universe, payload, text, children, arity);
        case T2_TYPE_NOMINAL:
                if (remap.in == NULL) {
                        return T2_TYPE_INVALID;
                }
                payload = remap.in(remap.context, payload);
                if (payload == 0) {
                        return T2_TYPE_INVALID;
                }
                return t2_nominal(universe, payload, children, arity);
        case T2_TYPE_RECURSIVE_VARIABLE:
        case T2_TYPE_RECURSIVE:
        {
                u32 binder;
                if (!t2_index_find(binders, payload, &binder)) {
                        binder = t2_universe_fresh_recursive_binder(universe);
                        if (
                                (binder == 0)
                             || !t2_index_put(binders, payload, binder)
                        ) {
                                return T2_TYPE_INVALID;
                        }
                }

                if (kind == T2_TYPE_RECURSIVE_VARIABLE) {
                        return t2_recursive_variable(universe, binder);
                }
                return (arity == 1)
                     ? t2_recursive(universe, binder, children[0])
                     : T2_TYPE_INVALID;
        }
        default:
                break;
        }

        T2Node *node = ty_malloc(
                sizeof *node + (usize)arity * sizeof *node->children
        );
        if (node == NULL) {
                return T2_TYPE_INVALID;
        }

        *node = (T2Node) {
                .payload = payload,
                .text    = (char *)text,
                .arity   = arity,
                .kind    = kind,
                .variable_kind = variable_kind
        };
        if (arity != 0) {
                memcpy(node->children, children, arity * sizeof *children);
        }

        T2Type type = rebuild_type(universe, node, node->children);
        ty_free(node);

        return type;
}

T2TypeReader *
t2_type_reader_new(
        T2Universe          *universe,
        T2SymbolRemap        remap,
        T2ReadHooks          hooks,
        unsigned char const *data,
        usize                size,
        usize               *position
)
{
        if (universe == NULL || data == NULL || position == NULL) {
                return NULL;
        }

        u32 count;
        if (!t2_read_u32(data, size, position, &count)) {
                return NULL;
        }

        T2TypeReader *reader = ty_calloc(1, sizeof *reader);
        T2Type       *types  = (count == 0) ? NULL : ty_calloc(count, sizeof *types);

        struct wire_record *records = (count == 0)
                                    ? NULL
                                    : ty_calloc(count, sizeof *records);

        if (
                (reader == NULL)
             || ((count != 0) && ((types == NULL) || (records == NULL)))
        ) {
                ty_free(reader);
                ty_free(types);
                ty_free(records);
                return NULL;
        }

        reader->universe       = universe;
        reader->types          = types;
        reader->count          = count;
        reader->variable_floor = hooks.floor;

        u32   *children       = NULL;
        usize  child_capacity = 0;
        u32    child_count    = 0;
        u32    widest         = 0;
        u32    highest        = 0;
        bool   floating       = false;

        bool ok = true;
        for (u32 i = 0; ok && i < count; ++i) {
                struct wire_record *record = &records[i];
                u32 length;
                ok = t2_read_u8(data, size, position, &record->kind)
                  && t2_read_u8(data, size, position, &record->variable_kind)
                  && t2_read_u64(data, size, position, &record->payload)
                  && read_text(data, size, position, &record->text, &length)
                  && t2_read_u32(data, size, position, &record->arity)
                  && (record->kind < T2_TYPE_KIND_COUNT)
                  && (record->arity <= UINT32_MAX - child_count);
                if (ok && record->kind == T2_TYPE_LITERAL_STRING) {
                        ok = (record->text != NULL);
                        record->payload = length;
                }
                if (ok && (child_count + record->arity > child_capacity)) {
                        usize capacity = (child_capacity == 0) ? 64 : child_capacity;
                        while (capacity < child_count + record->arity) {
                                capacity *= 2;
                        }
                        u32 *grown = ty_realloc(children, capacity * sizeof *grown);
                        if (grown == NULL) {
                                ok = false;
                        } else {
                                children       = grown;
                                child_capacity = capacity;
                        }
                }
                record->first_child = child_count;
                for (u32 j = 0; ok && j < record->arity; ++j) {
                        u32 child;
                        ok = t2_read_u32(data, size, position, &child) && (child < i);
                        if (ok) {
                                children[child_count++] = child;
                        }
                }
                if (ok && record->arity > widest) {
                        widest = record->arity;
                }
                if (
                        ok
                     && (record->kind == T2_TYPE_VARIABLE)
                     && (record->payload < UINT32_MAX)
                     && (record->payload >= hooks.floor)
                     && (hooks.reserve != NULL)
                ) {
                        floating = true;
                        if ((u32)record->payload > highest) {
                                highest = (u32)record->payload;
                        }
                }
        }

        if (ok && floating) {
                reader->variable_base = hooks.reserve(
                        hooks.context,
                        highest - hooks.floor + 1
                );
                reader->rebased = (reader->variable_base != 0);
                ok = reader->rebased;
        }

        T2Type *arguments = (widest == 0) ? NULL : xtA(T2Type, widest);
        T2Index binders   = {0};

        ok = ok && ((widest == 0) || (arguments != NULL));

        for (u32 i = 0; ok && i < count; ++i) {
                struct wire_record const *record = &records[i];
                for (u32 j = 0; j < record->arity; ++j) {
                        arguments[j] = types[children[record->first_child + j]];
                }
                u64  payload  = record->payload;
                bool variable = (record->kind == T2_TYPE_VARIABLE)
                             || (record->kind == T2_TYPE_BINDER);
                if (variable && payload < UINT32_MAX) {
                        payload = rebase_variable(reader, (u32)payload);
                        if (payload + 1 > reader->variable_limit) {
                                reader->variable_limit = (u32)payload + 1;
                        }
                }
                types[i] = reader_build(
                        universe,
                        remap,
                        hooks,
                        &binders,
                        (T2TypeKind)record->kind,
                        (T2VariableKind)record->variable_kind,
                        payload,
                        record->text,
                        arguments,
                        record->arity
                );
                ok = (types[i] != T2_TYPE_INVALID);
        }

        for (u32 i = 0; i < count; ++i) {
                ty_free(records[i].text);
        }
        ty_free(records);
        ty_free(children);
        ty_free(arguments);
        t2_index_free(&binders);

        if (!ok) {
                t2_type_reader_free(reader);
                return NULL;
        }

        return reader;
}

T2Type
t2_type_reader_type(T2TypeReader const *reader, u32 index)
{
        if (reader == NULL || index >= reader->count) {
                return T2_TYPE_INVALID;
        }

        return reader->types[index];
}

u32
t2_type_reader_variable_limit(T2TypeReader const *reader)
{
        return (reader == NULL) ? 0 : reader->variable_limit;
}

void
t2_type_reader_free(T2TypeReader *reader)
{
        if (reader == NULL) {
                return;
        }

        ty_free(reader->types);
        ty_free(reader);
}

bool
t2_scheme_encode(T2Scheme const *scheme, T2TypeWriter *writer, byte_vector *out)
{
        if (scheme == NULL || writer == NULL || out == NULL) {
                return false;
        }

        u32 body;
        if (!t2_type_writer_add(writer, scheme->body, &body)) {
                return false;
        }

        if (!t2_bytes_u32(out, (u32)scheme->quantifier_count)) {
                return false;
        }

        for (usize i = 0; i < scheme->quantifier_count; ++i) {
                if (
                        !t2_bytes_u32(out, scheme->quantifiers[i].id)
                     || !t2_bytes_u8(out, (uint8_t)scheme->quantifiers[i].kind)
                     || !t2_bytes_string(out, t2_scheme_quantifier_name(scheme, i))
                ) {
                        return false;
                }
        }

        if (!t2_bytes_u32(out, body)) {
                return false;
        }

        if (!t2_bytes_u32(out, (u32)scheme->predicate_count)) {
                return false;
        }

        for (usize i = 0; i < scheme->predicate_count; ++i) {
                T2Predicate const *predicate = &scheme->predicates[i];
                u32 subtype;
                u32 supertype;
                u32 operand = UINT32_MAX;
                if (
                        !t2_type_writer_add(writer, predicate->subtype, &subtype)
                     || !t2_type_writer_add(writer, predicate->supertype, &supertype)
                ) {
                        return false;
                }

                if (
                        (predicate->operand != T2_TYPE_INVALID)
                     && !t2_type_writer_add(writer, predicate->operand, &operand)
                ) {
                        return false;
                }

                if (
                        !t2_bytes_u8(out, (uint8_t)predicate->kind)
                     || !t2_bytes_u32(out, subtype)
                     || !t2_bytes_u32(out, supertype)
                     || !t2_bytes_u32(out, operand)
                     || !t2_bytes_string(out, predicate->name)
                     || !t2_bytes_string(out, predicate->provenance)
                ) {
                        return false;
                }
        }

        return true;
}

T2Scheme *
t2_scheme_decode(
        T2TypeReader        *reader,
        unsigned char const *data,
        usize                size,
        usize               *position
)
{
        if (reader == NULL || data == NULL || position == NULL) {
                return NULL;
        }

        u32 quantifier_count;
        if (!t2_read_u32(data, size, position, &quantifier_count)) {
                return NULL;
        }

        T2Quantifier *quantifiers = (quantifier_count == 0)
                                  ? NULL
                                  : ty_calloc(quantifier_count, sizeof *quantifiers);
        char **names = (quantifier_count == 0)
                     ? NULL
                     : ty_calloc(quantifier_count, sizeof *names);

        T2Predicate *predicates      = NULL;
        u32          predicate_count = 0;

        T2Scheme *scheme = NULL;

        bool ok = (quantifier_count == 0)
               || (quantifiers != NULL && names != NULL);

        for (u32 i = 0; ok && i < quantifier_count; ++i) {
                uint8_t kind;
                ok = t2_read_u32(data, size, position, &quantifiers[i].id)
                  && t2_read_u8(data, size, position, &kind)
                  && t2_read_string(data, size, position, &names[i]);
                if (ok) {
                        quantifiers[i].id   = rebase_variable(reader, quantifiers[i].id);
                        quantifiers[i].kind = (T2VariableKind)kind;
                }
        }

        u32 body_index = 0;

        ok = ok
          && t2_read_u32(data, size, position, &body_index)
          && t2_read_u32(data, size, position, &predicate_count);

        if (ok && predicate_count != 0) {
                predicates = ty_calloc(predicate_count, sizeof *predicates);
                ok         = (predicates != NULL);
        }

        for (u32 i = 0; ok && i < predicate_count; ++i) {
                uint8_t kind;
                u32 subtype;
                u32 supertype;
                u32 operand;
                char *name       = NULL;
                char *provenance = NULL;
                ok = t2_read_u8(data, size, position, &kind)
                  && t2_read_u32(data, size, position, &subtype)
                  && t2_read_u32(data, size, position, &supertype)
                  && t2_read_u32(data, size, position, &operand)
                  && t2_read_string(data, size, position, &name)
                  && t2_read_string(data, size, position, &provenance);
                if (ok) {
                        predicates[i] = (T2Predicate) {
                                .kind      = (T2PredicateKind)kind,
                                .subtype   = t2_type_reader_type(reader, subtype),
                                .supertype = t2_type_reader_type(reader, supertype),
                                .operand = (operand == UINT32_MAX)
                                         ? T2_TYPE_INVALID
                                         : t2_type_reader_type(reader, operand),
                                .name       = name,
                                .provenance = provenance
                        };
                        ok = (predicates[i].subtype   != T2_TYPE_INVALID)
                          && (predicates[i].supertype != T2_TYPE_INVALID)
                          && (operand == UINT32_MAX || predicates[i].operand != T2_TYPE_INVALID);
                } else {
                        ty_free(name);
                        ty_free(provenance);
                }
        }

        T2Type body = t2_type_reader_type(reader, body_index);

        if (ok && body != T2_TYPE_INVALID) {
                scheme = t2_scheme_new(
                        reader->universe,
                        quantifiers,
                        quantifier_count,
                        body,
                        predicates,
                        predicate_count
                );
                for (u32 i = 0; scheme != NULL && i < quantifier_count; ++i) {
                        if (names[i] != NULL) {
                                t2_scheme_name_quantifier(scheme, i, names[i]);
                        }
                }
        }

        for (u32 i = 0; i < predicate_count; ++i) {
                ty_free((char *)predicates[i].name);
                ty_free((char *)predicates[i].provenance);
        }
        for (u32 i = 0; i < quantifier_count; ++i) {
                ty_free(names[i]);
        }
        ty_free(predicates);
        ty_free(quantifiers);
        ty_free(names);

        return scheme;
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
            && (left.kind == right.kind)
            && (
                       (left.kind != T2_RUNTIME_NOMINAL)
                    || (left.nominal_symbol == right.nominal_symbol)
               )
        ;
}

static T2RuntimeFacts
runtime_facts_x(
        T2Universe const *universe,
        T2Type            type,
        unsigned          depth
);

static T2RuntimeFacts
union_runtime_facts(
        T2Universe const *universe,
        T2Node const     *node,
        unsigned          depth
)
{
        T2RuntimeFacts result = {
                .kind  = T2_RUNTIME_NEVER,
                .exact = true
        };
        bool have_value = false;
        bool nullable   = false;
        for (usize i = 0; i < node->arity; ++i) {
                T2RuntimeFacts arm = runtime_facts_x(
                        universe,
                        node->children[i],
                        depth + 1
                );
                if (arm.kind == T2_RUNTIME_NEVER && arm.exact) {
                        continue;
                }
                if (arm.kind == T2_RUNTIME_NIL && arm.exact) {
                        nullable = true;
                        continue;
                }
                nullable |= arm.nullable;
                if (!have_value) {
                        result     = arm;
                        have_value = true;
                } else if (!same_runtime_shape(result, arm)) {
                        return unknown_runtime_facts();
                }
        }

        if (!have_value) {
                return nullable
                     ? (T2RuntimeFacts) {
                             .kind  = T2_RUNTIME_NIL,
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
        T2Node const     *node,
        unsigned          depth
)
{
        T2RuntimeFacts result = unknown_runtime_facts();
        for (usize i = 0; i < node->arity; ++i) {
                T2RuntimeFacts arm = runtime_facts_x(
                        universe,
                        node->children[i],
                        depth + 1
                );
                if (arm.kind == T2_RUNTIME_NEVER && arm.exact) {
                        return arm;
                }
                if (!arm.exact) {
                        continue;
                }
                if (!result.exact) {
                        result = arm;
                } else if (!same_runtime_shape(result, arm)) {
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
        if (depth > T2_RELATION_DEPTH_LIMIT) {
                return unknown_runtime_facts();
        }

        type = t2_type_resolve_computed(universe, type);
        T2Node const *node = get_node(universe, type);
        if (node == NULL) {
                return unknown_runtime_facts();
        }

        T2RuntimeFacts exact = { .exact = true };
        switch (literal_base(node->kind)) {
        case T2_TYPE_NEVER:  exact.kind = T2_RUNTIME_NEVER; return exact;
        case T2_TYPE_NIL:    exact.kind = T2_RUNTIME_NIL; return exact;
        case T2_TYPE_BOOL:   exact.kind = T2_RUNTIME_BOOL; return exact;
        case T2_TYPE_INT:    exact.kind = T2_RUNTIME_INT; return exact;
        case T2_TYPE_FLOAT:  exact.kind = T2_RUNTIME_FLOAT; return exact;
        case T2_TYPE_STRING: exact.kind = T2_RUNTIME_STRING; return exact;
        case T2_TYPE_FUNCTION:
        case T2_TYPE_OVERLOAD:
                exact.kind = T2_RUNTIME_FUNCTION;
                return exact;
        case T2_TYPE_TUPLE:
        case T2_TYPE_VARIADIC_TUPLE:
                exact.kind = T2_RUNTIME_TUPLE;
                return exact;
        case T2_TYPE_MULTI:
                return runtime_facts_x(universe, node->children[0], depth + 1);
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
                return (node->arity == 2)
                     ? runtime_facts_x(universe, node->children[0], depth + 1)
                     : unknown_runtime_facts();
        case T2_TYPE_RECURSIVE:
                return (node->arity == 1)
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
        T2Type            type,
        T2RuntimeFacts   *facts
)
{
        if (facts == NULL || get_node(universe, type) == NULL) {
                return false;
        }

        *facts = runtime_facts_x(universe, type, 0);

        return true;
}

static bool
push_undo(T2Solver *solver, T2Undo undo)
{
        if (solver->transaction_depth == 0) {
                return true;
        }

        xvP(solver->undo, undo);

        return true;
}

static u32
meta_from_type(T2Solver const *solver, T2Type type)
{
        T2Node const *node = get_node(solver->universe, type);
        if (node == NULL || node->kind != T2_TYPE_META) {
                return 0;
        }

        u32 solver_id = (u32)(node->payload >> 32);
        u32 meta      = (u32)node->payload;
        if (
                (solver_id != solver->id)
             || (meta == 0)
             || (meta > vN(solver->metas))
        ) {
                return 0;
        }

        return meta;
}

static T2Type
meta_type(T2Solver *solver, u32 meta)
{
        u64 payload = ((u64)solver->id << 32) | meta;
        return intern_type(
                solver->universe,
                T2_TYPE_META,
                v__(solver->metas, meta - 1).variable_kind,
                payload,
                NULL,
                NULL,
                0
        );
}

static u32
find_root(T2Solver *solver, u32 meta)
{
        T2Meta *node = v_(solver->metas, meta - 1);
        if (node->parent == meta) {
                return meta;
        }

        u32 root = find_root(solver, node->parent);
        if (node->parent != root) {
                if (
                        !push_undo(
                                solver,
                                (T2Undo) {
                                        .kind  = T2_UNDO_PARENT,
                                        .index = meta,
                                        .old   = node->parent
                                }
                        )
                ) {
                        return root;
                }

                node->parent = root;
        }

        return root;
}

static T2Type
resolve_sort_solution(T2Solver *solver, T2Type type)
{
        u32 meta = meta_from_type(solver, type);
        if (meta == 0) {
                return type;
        }

        meta = find_root(solver, meta);
        T2Meta const *node = v_(solver->metas, meta - 1);

        return (node->solution == T2_TYPE_INVALID) ? meta_type(solver, meta) : node->solution;
}

static T2Type
resolve_pack_solutions(T2Solver *solver, T2Type type, unsigned depth)
{
        if (depth > T2_RELATION_DEPTH_LIMIT) {
                return type;
        }

        u32 meta = meta_from_type(solver, type);
        if (meta != 0) {
                meta = find_root(solver, meta);
                T2Meta const *node = v_(solver->metas, meta - 1);
                if (
                        (node->variable_kind != T2_VARIABLE_PACK)
                     || (node->solution == T2_TYPE_INVALID)
                ) {
                        return meta_type(solver, meta);
                }

                return resolve_pack_solutions(
                        solver,
                        node->solution,
                        depth + 1
                );
        }

        T2Node const *node = get_node(solver->universe, type);
        if (node == NULL || node->arity == 0) {
                return type;
        }

        T2Type *children = ty_malloc(node->arity * sizeof *children);
        if (children == NULL) {
                solver->failed = true;
                ty_snprintf(
                        solver->error,
                        sizeof solver->error,
                        "types2 solver ran out of memory"
                );
                return T2_TYPE_INVALID;
        }

        bool changed = false;
        for (usize i = 0; i < node->arity; ++i) {
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
        ty_free(children);

        return result;
}

static bool
type_contains_solved_pack_meta(T2Solver *solver, T2Type type, unsigned depth)
{
        if (depth > T2_RELATION_DEPTH_LIMIT) {
                return false;
        }

        u32 meta = meta_from_type(solver, type);
        if (meta != 0) {
                meta = find_root(solver, meta);
                T2Meta const *node = v_(solver->metas, meta - 1);
                return (node->variable_kind == T2_VARIABLE_PACK)
                    && (node->solution != T2_TYPE_INVALID);
        }

        T2Node const *node = get_node(solver->universe, type);
        if (node == NULL) {
                return false;
        }

        for (usize i = 0; i < node->arity; ++i) {
                if (type_contains_solved_pack_meta(
                        solver,
                        node->children[i],
                        depth + 1
                )) {
                        return true;
                }
        }

        return false;
}

static bool
type_contains_meta(T2Solver *solver, T2Type type, u32 wanted, unsigned depth)
{
        if (depth > T2_RELATION_DEPTH_LIMIT) {
                return true;
        }

        u32 meta = meta_from_type(solver, type);
        if (meta != 0) {
                meta = find_root(solver, meta);
                if (meta == wanted) {
                        return true;
                }
                T2Type solution = v__(solver->metas, meta - 1).solution;
                return (solution != T2_TYPE_INVALID)
                    && type_contains_meta(solver, solution, wanted, depth + 1);
        }

        T2Node const *node = get_node(solver->universe, type);
        if (node == NULL || (node->flags & T2_NODE_META) == 0) {
                return false;
        }

        for (usize i = 0; i < node->arity; ++i) {
                if (type_contains_meta(solver, node->children[i], wanted, depth + 1)) {
                        return true;
                }
        }

        return false;
}

static bool
push_watch(T2Solver *solver, u32 meta, u64 watch)
{
        T2Meta *node = v_(solver->metas, meta - 1);
        if (
                !push_undo(
                        solver,
                        (T2Undo) {
                                .kind  = T2_UNDO_WATCH_COUNT,
                                .index = meta,
                                .old   = vN(node->watchers)
                        }
                )
        ) {
                return false;
        }

        xvP(node->watchers, watch);

        return true;
}

static bool
enqueue(T2Solver *solver, u64 work)
{
        if (
                solver->draining_work
             && solver->processing_work
             && (solver->active_work == work)
        ) {
                solver->rerun_active_work = true;
                return true;
        }

        for (usize i = solver->work_index; i < vN(solver->work); ++i) {
                if (v__(solver->work, i) == work) {
                        return true;
                }
        }

        xvP(solver->work, work);

        return true;
}

static void
wake_meta(T2Solver *solver, u32 meta)
{
        T2Meta const *node = v_(solver->metas, meta - 1);
        for (usize i = 0; i < vN(node->watchers); ++i) {
                if (!enqueue(solver, v__(node->watchers, i))) {
                        return;
                }
        }
}

static void
clear_solver_failure(T2Solver *solver)
{
        solver->error[0]        = '\0';
        solver->failure_message = NULL;
        solver->failure_left    = T2_TYPE_INVALID;
        solver->failure_right   = T2_TYPE_INVALID;
        ty_free(solver->failure_provenance);
        solver->failure_provenance = NULL;
}

static void
set_solver_error(
        T2Solver   *solver,
        char const *message,
        T2Type      left,
        T2Type      right,
        char const *provenance
)
{
        if (solver->failed) {
                return;
        }

        solver->failed = true;
        solver->failure_message = message;
        solver->failure_left    = left;
        solver->failure_right   = right;
        ty_free(solver->failure_provenance);
        solver->failure_provenance = S2N(provenance);
        char *left_string  = t2_type_string(solver->universe, left);
        char *right_string = t2_type_string(solver->universe, right);
        ty_snprintf(
                solver->error,
                sizeof solver->error,
                "%s: %s is not a subtype of %s%s%s",
                message,
                (left_string == NULL) ? "<type>" : left_string,
                (right_string == NULL) ? "<type>" : right_string,
                (provenance == NULL) ? "" : " at ",
                (provenance == NULL) ? "" : provenance
        );
        ty_free(left_string);
        ty_free(right_string);
}

static char const *
record_cause(
        T2Solver   *solver,
        T2CauseKind kind,
        T2Type      left,
        T2Type      right,
        char const *provenance
)
{
        char *owned = S2N(provenance);
        if (provenance != NULL && owned == NULL) {
                solver->failed = true;
                ty_snprintf(
                        solver->error,
                        sizeof solver->error,
                        "types2 solver ran out of memory"
                );
                return NULL;
        }

        xvP(solver->causes, ((T2Cause) {
                .kind       = kind,
                .left       = left,
                .right      = right,
                .provenance = owned
        }));

        return owned;
}

T2Solver *
t2_solver_new(T2Universe *universe)
{
        if (universe == NULL || universe->failed || universe->next_solver_id == 0) {
                return NULL;
        }

        T2Solver *solver = ty_calloc(1, sizeof *solver);
        if (solver == NULL) {
                return NULL;
        }

        solver->universe = universe;
        solver->id       = universe->next_solver_id++;

        return solver;
}

void
t2_solver_set_predicate_resolver(
        T2Solver            *solver,
        T2PredicateResolver *resolver,
        void                *context
)
{
        if (solver == NULL) {
                return;
        }

        solver->predicate_resolver = resolver;
        solver->predicate_context  = context;
}

void
t2_solver_free(T2Solver *solver)
{
        if (solver == NULL) {
                return;
        }

        for (usize i = 0; i < vN(solver->metas); ++i) {
                xvF(v__(solver->metas, i).watchers);
                ty_free(v__(solver->metas, i).provenance);
        }

        for (usize i = 0; i < vN(solver->causes); ++i) {
                ty_free(v__(solver->causes, i).provenance);
        }

        for (usize i = 0; i < vN(solver->obligations); ++i) {
                ty_free(v__(solver->obligations, i).name);
                ty_free(v__(solver->obligations, i).provenance);
        }

        xvF(solver->metas);
        xvF(solver->edges);
        xvF(solver->obligations);
        xvF(solver->work);
        xvF(solver->recursive_constraints);
        xvF(solver->undo);
        xvF(solver->causes);
        ty_free(solver->failure_provenance);
        ty_free(solver);
}

T2Type
t2_solver_new_meta(
        T2Solver      *solver,
        T2VariableKind kind,
        u32            level,
        char const    *provenance
)
{
        if (solver == NULL || solver->failed) {
                return T2_TYPE_INVALID;
        }

        if (kind == T2_VARIABLE_RIGID || kind == T2_VARIABLE_QUANTIFIED) {
                return T2_TYPE_INVALID;
        }

        u32 id = (u32)(vN(solver->metas) + 1);
        char *owned_provenance = S2N(provenance);
        if (provenance != NULL && owned_provenance == NULL) {
                solver->failed = true;
                ty_snprintf(
                        solver->error,
                        sizeof solver->error,
                        "types2 solver ran out of memory"
                );
                return T2_TYPE_INVALID;
        }

        xvP(solver->metas, ((T2Meta) {
                .parent        = id,
                .level         = level,
                .variable_kind = kind,
                .lower         = t2_primitive(solver->universe, T2_TYPE_NEVER),
                .upper         = t2_primitive(solver->universe, T2_TYPE_ANY),
                .provenance    = owned_provenance
        }));
        if (!t2_universe_ok(solver->universe)) {
                solver->failed = true;
                ty_snprintf(
                        solver->error,
                        sizeof solver->error,
                        "types2 type allocation failed"
                );
                return T2_TYPE_INVALID;
        }

        return meta_type(solver, id);
}

static T2Relation
constrain_internal(
        T2Solver   *solver,
        T2Type      subtype,
        T2Type      supertype,
        char const *provenance,
        bool        retain_deferred
);

static T2Relation
check_bounds(T2Solver *solver, u32 meta, char const *provenance)
{
        meta = find_root(solver, meta);
        T2Meta const *node = v_(solver->metas, meta - 1);
        if (node->checking_bounds) {
                return t2_subtype(solver->universe, node->lower, node->upper);
        }

        T2Type lower = node->lower;
        T2Type upper = node->upper;
        v__(solver->metas, meta - 1).checking_bounds = true;
        T2Relation relation = constrain_internal(
                solver,
                lower,
                upper,
                provenance,
                t2_type_has_metas(solver->universe, lower)
             || t2_type_has_metas(solver->universe, upper)
        );
        v__(solver->metas, meta - 1).checking_bounds = false;
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
        T2Type    type,
        u32       wanted,
        T2Type   *remainder
)
{
        T2Node const *node = get_node(solver->universe, type);
        if (node == NULL || node->kind != T2_TYPE_UNION) {
                return false;
        }

        T2Type *arms = ty_malloc(node->arity * sizeof *arms);
        if (arms == NULL) {
                solver->failed = true;
                ty_snprintf(
                        solver->error,
                        sizeof solver->error,
                        "types2 solver ran out of memory"
                );
                return false;
        }

        usize count  = 0;
        bool removed = false;
        wanted = find_root(solver, wanted);
        for (usize i = 0; i < node->arity; ++i) {
                u32 child = meta_from_type(solver, node->children[i]);
                if (child != 0 && find_root(solver, child) == wanted) {
                        removed = true;
                        continue;
                }
                arms[count++] = node->children[i];
        }

        if (removed) {
                *remainder = (count == 0)
                           ? t2_primitive(solver->universe, T2_TYPE_NEVER)
                           : t2_union(solver->universe, arms, count);
        }

        ty_free(arms);

        return removed;
}

static T2Relation
update_lower(T2Solver *solver, u32 meta, T2Type lower, char const *provenance)
{
        meta         = find_root(solver, meta);
        T2Meta *node = v_(solver->metas, meta - 1);
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
        if (joined == T2_TYPE_INVALID) {
                return T2_RELATION_COMPLEXITY;
        }

        if (joined == node->lower) {
                return check_bounds(solver, meta, provenance);
        }

        if (
                !push_undo(
                        solver,
                        (T2Undo) {
                                .kind  = T2_UNDO_LOWER,
                                .index = meta,
                                .old   = node->lower
                        }
                )
        ) {
                return T2_RELATION_COMPLEXITY;
        }

        node->lower = joined;
        T2Relation relation = check_bounds(solver, meta, provenance);
        if (relation != T2_RELATION_NO && relation != T2_RELATION_COMPLEXITY) {
                wake_meta(solver, meta);
        }

        return relation;
}

static T2Relation
update_upper(T2Solver *solver, u32 meta, T2Type upper, char const *provenance)
{
        meta         = find_root(solver, meta);
        T2Meta *node = v_(solver->metas, meta - 1);
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
        if (met == T2_TYPE_INVALID) {
                return T2_RELATION_COMPLEXITY;
        }

        if (met == node->upper) {
                return check_bounds(solver, meta, provenance);
        }

        if (
                !push_undo(
                        solver,
                        (T2Undo) {
                                .kind  = T2_UNDO_UPPER,
                                .index = meta,
                                .old   = node->upper
                        }
                )
        ) {
                return T2_RELATION_COMPLEXITY;
        }

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
        if (node == NULL) {
                return T2_VARIABLE_FLEXIBLE;
        }

        if (
                (node->kind == T2_TYPE_ROW)
             || (node->kind == T2_TYPE_ROW_EMPTY)
             || (node->kind == T2_TYPE_ROW_ANY)
        ) {
                return T2_VARIABLE_ROW;
        }

        if (
                (node->kind == T2_TYPE_PACK)
             || (node->kind == T2_TYPE_PACK_EMPTY)
             || (node->kind == T2_TYPE_PACK_ANY)
             || (node->kind == T2_TYPE_PACK_EXPANSION)
        ) {
                return T2_VARIABLE_PACK;
        }

        if (
                ((node->kind == T2_TYPE_META) || (node->kind == T2_TYPE_VARIABLE))
             && (
                        (node->variable_kind == T2_VARIABLE_ROW)
                     || (node->variable_kind == T2_VARIABLE_PACK)
                )
        ) {
                return node->variable_kind;
        }

        if (node->kind == T2_TYPE_INTERSECTION && node->arity != 0) {
                T2VariableKind sort = term_sort(universe, node->children[0]);
                if (sort != T2_VARIABLE_ROW && sort != T2_VARIABLE_PACK) {
                        return T2_VARIABLE_FLEXIBLE;
                }
                for (usize i = 1; i < node->arity; ++i) {
                        if (term_sort(universe, node->children[i]) != sort) {
                                return T2_VARIABLE_FLEXIBLE;
                        }
                }

                return sort;
        }

        return T2_VARIABLE_FLEXIBLE;
}

static T2Relation
merge_meta_roots(
        T2Solver   *solver,
        u32         left,
        u32         right,
        char const *provenance
);

static T2Relation
bind_sort_meta(
        T2Solver   *solver,
        u32         meta,
        T2Type      value,
        char const *provenance
)
{
        meta         = find_root(solver, meta);
        T2Meta *node = v_(solver->metas, meta - 1);
        T2VariableKind sort = node->variable_kind;
        if (sort != T2_VARIABLE_ROW && sort != T2_VARIABLE_PACK) {
                return T2_RELATION_NO;
        }

        u32 other = meta_from_type(solver, value);
        if (other != 0) {
                other = find_root(solver, other);
                if (other == meta) {
                        return T2_RELATION_YES;
                }
                if (v__(solver->metas, other - 1).variable_kind != sort) {
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

        if (
                !push_undo(
                        solver,
                        (T2Undo) {
                                .kind  = T2_UNDO_SOLUTION,
                                .index = meta,
                                .old   = node->solution
                        }
                )
        ) {
                return T2_RELATION_COMPLEXITY;
        }

        node->solution = value;
        wake_meta(solver, meta);

        return T2_RELATION_YES;
}

typedef vec(u32) T2MetaList;

static bool
collect_live_meta_roots(
        T2Solver   *solver,
        T2Type      type,
        T2MetaList *roots,
        unsigned    depth
)
{
        if (depth > T2_RELATION_DEPTH_LIMIT) {
                return true;
        }

        u32 meta = meta_from_type(solver, type);
        if (meta != 0) {
                meta = find_root(solver, meta);
                for (usize i = 0; i < vN(*roots); ++i) {
                        if (v__(*roots, i) == meta) {
                                return true;
                        }
                }

                xvP(*roots, meta);
                T2Meta const *node = v_(solver->metas, meta - 1);
                if (node->solution != T2_TYPE_INVALID) {
                        return collect_live_meta_roots(solver, node->solution, roots, depth + 1);
                }
                return collect_live_meta_roots(solver, node->lower, roots, depth + 1)
                    && collect_live_meta_roots(solver, node->upper, roots, depth + 1);
        }

        T2Node const *node = get_node(solver->universe, type);
        if (node == NULL) {
                return false;
        }

        for (usize i = 0; i < node->arity; ++i) {
                if (!collect_live_meta_roots(solver, node->children[i], roots, depth + 1)) {
                        return false;
                }
        }

        return true;
}

static bool
meta_watches(T2Solver const *solver, u32 meta, u64 watch)
{
        T2WatchVector const *watchers = &v__(solver->metas, meta - 1).watchers;
        for (usize i = 0; i < vN(*watchers); ++i) {
                if (v__(*watchers, i) == watch) {
                        return true;
                }
        }

        return false;
}

static bool
watch_obligation(T2Solver *solver, usize index)
{
        T2Predicate const *predicate = &v__(solver->obligations, index).predicate;
        u64 watch        = T2_WATCH_OBLIGATION | index;
        T2MetaList roots = { 0 };
        bool ok = collect_live_meta_roots(solver, predicate->subtype, &roots, 0)
               && collect_live_meta_roots(solver, predicate->supertype, &roots, 0);
        if (ok && predicate->operand != T2_TYPE_INVALID) {
                ok = collect_live_meta_roots(solver, predicate->operand, &roots, 0);
        }

        for (usize i = 0; ok && i < vN(roots); ++i) {
                if (meta_watches(solver, v__(roots, i), watch)) {
                        continue;
                }
                ok = push_watch(solver, v__(roots, i), watch);
        }

        xvF(roots);

        return ok;
}

static T2Relation
retain_predicate(
        T2Solver          *solver,
        T2Predicate const *predicate
)
{
        char *name       = S2N(predicate->name);
        char *provenance = S2N(predicate->provenance);
        if (
                ((predicate->name != NULL) && (name == NULL))
             || ((predicate->provenance != NULL) && (provenance == NULL))
        ) {
                ty_free(name);
                ty_free(provenance);
                solver->failed = true;
                ty_snprintf(
                        solver->error,
                        sizeof solver->error,
                        "types2 solver ran out of memory"
                );
                return T2_RELATION_COMPLEXITY;
        }

        usize index = vN(solver->obligations);
        xvP(solver->obligations, ((T2Obligation) {
                .predicate  = *predicate,
                .name       = name,
                .provenance = provenance,
                .active     = true
        }));
        v__(solver->obligations, index).predicate.name       = name;
        v__(solver->obligations, index).predicate.provenance = provenance;

        return watch_obligation(solver, index)
             ? T2_RELATION_DEFERRED
             : T2_RELATION_COMPLEXITY;
}

static T2Relation
retain_obligation(
        T2Solver   *solver,
        T2Type      subtype,
        T2Type      supertype,
        char const *provenance
)
{
        T2Predicate predicate = {
                .kind       = T2_PREDICATE_SUBTYPE,
                .subtype    = subtype,
                .supertype  = supertype,
                .provenance = provenance
        };

        return retain_predicate(solver, &predicate);
}

static T2Relation
add_edge(
        T2Solver   *solver,
        u32         subtype,
        u32         supertype,
        char const *provenance
)
{
        subtype   = find_root(solver, subtype);
        supertype = find_root(solver, supertype);
        if (subtype == supertype) {
                return T2_RELATION_YES;
        }

        T2VariableKind sub_kind = v__(solver->metas, subtype - 1).variable_kind;
        T2VariableKind sup_kind = v__(solver->metas, supertype - 1).variable_kind;
        if (
                ((sub_kind == T2_VARIABLE_ROW) != (sup_kind == T2_VARIABLE_ROW))
             || ((sub_kind == T2_VARIABLE_PACK) != (sup_kind == T2_VARIABLE_PACK))
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

        T2WatchVector const *watches = &v__(solver->metas, subtype - 1).watchers;
        for (usize i = 0; i < vN(*watches); ++i) {
                u64 watch = v__(*watches, i);
                if (
                        ((watch & T2_WATCH_OBLIGATION) != 0)
                     || (watch >= vN(solver->edges))
                ) {
                        continue;
                }

                T2Edge const *edge = v_(solver->edges, watch);
                if (
                        (find_root(solver, edge->subtype) == subtype)
                     && (find_root(solver, edge->supertype) == supertype)
                ) {
                        return T2_RELATION_YES;
                }
        }

        usize edge_index = vN(solver->edges);
        xvP(solver->edges, ((T2Edge) {
                .subtype    = subtype,
                .supertype  = supertype,
                .provenance = provenance
        }));

        if (
                !push_watch(solver, subtype, edge_index)
             || !push_watch(solver, supertype, edge_index)
             || !enqueue(solver, edge_index)
        ) {
                return T2_RELATION_COMPLEXITY;
        }

        return T2_RELATION_YES;
}

static T2Relation
constrain_children(
        T2Solver     *solver,
        T2Node const *a,
        T2Node const *b,
        char const   *provenance,
        bool          retain_deferred
)
{
        T2Relation result = T2_RELATION_YES;
        for (usize i = 0; i < a->arity; ++i) {
                T2Relation item = constrain_internal(
                        solver,
                        a->children[i],
                        b->children[i],
                        provenance,
                        retain_deferred
                );
                result = combine_all(result, item);
                if (solver->failed) {
                        return item;
                }
        }

        return result;
}

static T2Type
erase_callable_types(T2Universe *universe, T2Type callable)
{
        usize count = t2_callable_parameter_count(universe, callable);
        T2ParameterSpec *parameters = (count == 0)
                                    ? NULL
                                    : ty_malloc(count * sizeof *parameters);
        if (count != 0 && parameters == NULL) {
                return T2_TYPE_INVALID;
        }

        T2Type dynamic = t2_primitive(universe, T2_TYPE_DYNAMIC);
        for (usize i = 0; i < count; ++i) {
                if (!t2_callable_parameter(universe, callable, i, &parameters[i])) {
                        ty_free(parameters);
                        return T2_TYPE_INVALID;
                }
                parameters[i].type = dynamic;
        }

        T2Type erased = t2_callable(
                universe,
                parameters,
                count,
                dynamic,
                dynamic,
                dynamic
        );
        ty_free(parameters);

        return erased;
}

static T2Relation
callable_shape_relation(T2Universe *universe, T2Type actual, T2Type expected)
{
        T2Type erased_actual   = erase_callable_types(universe, actual);
        T2Type erased_expected = erase_callable_types(universe, expected);
        if (
                (erased_actual == T2_TYPE_INVALID)
             || (erased_expected == T2_TYPE_INVALID)
        ) {
                return T2_RELATION_COMPLEXITY;
        }

        return t2_subtype(universe, erased_actual, erased_expected);
}

static T2Relation
constrain_parameter_types(
        T2Solver     *solver,
        T2Node const *actual,
        T2Node const *expected,
        char const   *provenance,
        bool          retain_deferred
)
{
        if (actual == NULL || expected == NULL) {
                return T2_RELATION_NO;
        }

        return constrain_internal(
                solver,
                expected->children[0],
                actual->children[0],
                provenance,
                retain_deferred
        );
}

static T2Type
replace_type(
        T2Universe *universe,
        T2Type      type,
        T2Type      from,
        T2Type      to,
        unsigned    depth
)
{
        if (type == from) {
                return to;
        }

        T2Node const *node = get_node(universe, type);
        if (
                (node == NULL)
             || (node->arity == 0)
             || (node->kind == T2_TYPE_RECURSIVE)
             || (depth > T2_RELATION_DEPTH_LIMIT)
        ) {
                return type;
        }

        T2Type *children = ty_malloc(node->arity * sizeof *children);
        if (children == NULL) {
                return T2_TYPE_INVALID;
        }

        bool changed = false;
        for (usize i = 0; i < node->arity; ++i) {
                children[i] = replace_type(
                        universe,
                        node->children[i],
                        from,
                        to,
                        depth + 1
                );
                if (children[i] == T2_TYPE_INVALID) {
                        ty_free(children);
                        return T2_TYPE_INVALID;
                }
                changed |= children[i] != node->children[i];
        }

        T2Type result = changed ? rebuild_type(universe, node, children) : type;
        ty_free(children);

        return result;
}

static T2Type
closed_pack_in(T2Universe const *universe, T2Type type, unsigned depth)
{
        T2Node const *node = get_node(universe, type);
        if (node == NULL || depth > T2_RELATION_DEPTH_LIMIT) {
                return T2_TYPE_INVALID;
        }

        if (node->kind == T2_TYPE_PACK) {
                T2Node const *tail = get_node(universe, node->children[node->payload]);
                return (tail != NULL) && (tail->kind == T2_TYPE_PACK_EMPTY)
                     ? type
                     : T2_TYPE_INVALID;
        }

        for (usize i = 0; i < node->arity; ++i) {
                T2Type found = closed_pack_in(universe, node->children[i], depth + 1);
                if (found != T2_TYPE_INVALID) {
                        return found;
                }
        }

        return T2_TYPE_INVALID;
}

static T2Type
expand_pack_parameter(T2Solver *solver, T2Type callable)
{
        T2Universe *universe = solver->universe;
        T2Node const *node   = get_node(universe, callable);
        if (node == NULL || node->kind != T2_TYPE_FUNCTION) {
                return callable;
        }

        usize count = (usize)node->payload;
        T2Node const *parameter = function_parameter_kind(
                universe,
                node,
                T2_PARAMETER_PACK
        );
        if (parameter == NULL) {
                return callable;
        }

        T2Type resolved = resolve_pack_solutions(solver, parameter->children[0], 0);
        T2Node const *resolved_node = get_node(universe, resolved);
        if (resolved_node == NULL) {
                return callable;
        }

        T2Type pattern = T2_TYPE_INVALID;
        T2Type pack    = resolved;
        if (resolved_node->kind == T2_TYPE_PACK_EXPANSION) {
                pattern = resolved_node->children[0];
                pack    = closed_pack_in(universe, pattern, 0);
        } else {
                pack = (closed_pack_in(universe, resolved, 0) == resolved) ? resolved : T2_TYPE_INVALID;
        }

        T2Node const *pack_node = get_node(universe, pack);
        if (pack_node == NULL) {
                return callable;
        }

        usize elements = (usize)pack_node->payload;
        T2ParameterSpec *specs = ty_malloc((count + elements) * sizeof *specs);
        if (specs == NULL) {
                return callable;
        }

        usize expanded = 0;
        for (usize i = 0; i < count; ++i) {
                if (get_node(universe, node->children[i]) != parameter) {
                        (void)t2_callable_parameter(universe, callable, i, &specs[expanded++]);
                        continue;
                }
                for (usize j = 0; j < elements; ++j) {
                        T2Type element = pack_node->children[j];
                        T2Type type = (pattern == T2_TYPE_INVALID)
                                    ? element
                                    : replace_type(universe, pattern, pack, element, 0);
                        if (type == T2_TYPE_INVALID) {
                                ty_free(specs);
                                return callable;
                        }
                        specs[expanded++] = (T2ParameterSpec) {
                                .type     = type,
                                .kind     = T2_PARAMETER_POSITIONAL_ONLY,
                                .required = true
                        };
                }
        }

        T2Type result = callable_type(
                universe,
                specs,
                expanded,
                t2_callable_result(universe, callable),
                t2_callable_yield(universe, callable),
                t2_callable_send(universe, callable),
                t2_callable_is_effectful(universe, callable)
        );
        ty_free(specs);

        return (result == T2_TYPE_INVALID) ? callable : result;
}

static T2Relation
constrain_positional_suffix_pack(
        T2Solver     *solver,
        T2Node const *actual,
        usize         skip,
        T2Type        expected_pack,
        char const   *provenance,
        bool          retain_deferred
)
{
        T2Universe *universe = solver->universe;
        usize count = 0;
        while (function_positional_parameter(universe, actual, skip + count) != NULL) {
                count += 1;
        }

        T2Type *elements = (count == 0) ? NULL : ty_malloc(count * sizeof *elements);
        if (count != 0 && elements == NULL) {
                solver->failed = true;
                return T2_RELATION_COMPLEXITY;
        }

        for (usize i = 0; i < count; ++i) {
                T2Node const *parameter = function_positional_parameter(
                        universe,
                        actual,
                        skip + i
                );
                elements[i] = parameter->children[0];
        }

        T2Type pack = t2_pack(universe, elements, count, T2_TYPE_INVALID);
        ty_free(elements);
        if (pack == T2_TYPE_INVALID) {
                return T2_RELATION_COMPLEXITY;
        }

        return constrain_internal(
                solver,
                pack,
                expected_pack,
                provenance,
                retain_deferred
        );
}

static T2Relation
constrain_function_types(
        T2Solver     *solver,
        T2Type        actual_type,
        T2Type        expected_type,
        T2Node const *actual,
        T2Node const *expected,
        char const   *provenance,
        bool          retain_deferred
)
{
        T2Type expanded_actual   = expand_pack_parameter(solver, actual_type);
        T2Type expanded_expected = expand_pack_parameter(solver, expected_type);
        if (expanded_actual != actual_type || expanded_expected != expected_type) {
                return constrain_function_types(
                        solver,
                        expanded_actual,
                        expanded_expected,
                        get_node(solver->universe, expanded_actual),
                        get_node(solver->universe, expanded_expected),
                        provenance,
                        retain_deferred
                );
        }

        usize actual_count   = (usize)actual->payload;
        usize expected_count = (usize)expected->payload;
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
        bool suffix_pack = (expected_pack != NULL)
                        && (actual_rest == NULL)
                        && (actual_pack == NULL);
        T2Relation shape = suffix_pack
                         ? T2_RELATION_YES
                         : callable_shape_relation(
                                 solver->universe,
                                 actual_type,
                                 expected_type
                           )
        ;
        if (shape == T2_RELATION_NO || shape == T2_RELATION_COMPLEXITY) {
                set_solver_error(
                        solver,
                        (shape == T2_RELATION_NO)
                        ? "incompatible callable protocol"
                        : "callable comparison exceeded its complexity limit",
                        actual_type,
                        expected_type,
                        provenance
                );
                return shape;
        }

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

        usize expected_positions = 0;
        for (usize i = 0; i < expected_count; ++i) {
                T2Node const *parameter = get_node(solver->universe, expected->children[i]);
                expected_positions += parameter_accepts_position(parameter);
        }

        for (usize i = 0; i < expected_positions; ++i) {
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
                if (have == NULL) {
                        have = (actual_rest == NULL) ? actual_pack : actual_rest;
                }
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
                if (solver->failed) {
                        return T2_RELATION_NO;
                }
        }

        if (suffix_pack) {
                result = combine_all(
                        result,
                        constrain_positional_suffix_pack(
                                solver,
                                actual,
                                expected_positions,
                                expected_pack->children[0],
                                provenance,
                                retain_deferred
                        )
                );
                if (solver->failed) {
                        return T2_RELATION_NO;
                }
        } else if (expected_rest != NULL || expected_pack != NULL) {
                result = combine_all(
                        result,
                        constrain_parameter_types(
                                solver,
                                (actual_rest == NULL) ? actual_pack : actual_rest,
                                (expected_rest == NULL) ? expected_pack : expected_rest,
                                provenance,
                                retain_deferred
                        )
                );
                if (solver->failed) {
                        return T2_RELATION_NO;
                }
        }

        for (usize i = 0; i < expected_count; ++i) {
                T2Node const *wanted = get_node(solver->universe, expected->children[i]);
                if (!parameter_accepts_keyword(wanted)) {
                        continue;
                }
                T2Node const *have = function_keyword_parameter(
                        solver->universe,
                        actual,
                        wanted->text
                );
                if (have == NULL) {
                        have = actual_kwrest;
                }
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
                if (solver->failed) {
                        return T2_RELATION_NO;
                }
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
                if (solver->failed) {
                        return T2_RELATION_NO;
                }
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
        T2Node const *expected_yield = get_node(
                solver->universe,
                expected->children[expected_count + 1]
        );
        T2Node const *expected_send = get_node(
                solver->universe,
                expected->children[expected_count + 2]
        );
        if (
                (expected_yield->kind == T2_TYPE_NEVER)
             && (expected_send->kind == T2_TYPE_NIL)
        ) {
                return result;
        }

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
        T2Solver   *solver,
        T2Type      row,
        char const *name,
        unsigned    depth
)
{
        if (depth > T2_RELATION_DEPTH_LIMIT) {
                return NULL;
        }

        row = resolve_sort_solution(solver, row);
        T2Node const *node = get_node(solver->universe, row);
        if (node == NULL) {
                return NULL;
        }

        if (node->kind == T2_TYPE_INTERSECTION) {
                for (usize i = 0; i < node->arity; ++i) {
                        T2Node const *field = solver_find_row_field(
                                solver,
                                node->children[i],
                                name,
                                depth + 1
                        );
                        if (field != NULL) {
                                return field;
                        }
                }

                return NULL;
        }

        if (node->kind != T2_TYPE_ROW) {
                return NULL;
        }

        T2Node const *field = find_record_field_node(solver->universe, node, name);
        if (field != NULL) {
                return field;
        }

        return solver_find_row_field(
                solver,
                node->children[node->arity - 1],
                name,
                depth + 1
        );
}

static T2Node const *
solver_find_record_field(
        T2Solver     *solver,
        T2Node const *record,
        char const   *name
)
{
        T2Node const *field = find_record_field_node(solver->universe, record, name);
        if (field != NULL) {
                return field;
        }

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
                .name     = field->text,
                .type     = field->children[0],
                .presence = (T2Presence)(field->payload & T2_FIELD_PRESENCE_MASK),
                .capability = (field->payload & T2_FIELD_WRITABLE_BIT)
                            ? T2_FIELD_WRITABLE
                            : T2_FIELD_READONLY
        };
}

static T2Relation
require_field_in_row(
        T2Solver     *solver,
        T2Type        row,
        T2Node const *expected,
        char const   *provenance
)
{
        row = resolve_sort_solution(solver, row);
        u32 meta = meta_from_type(solver, row);
        if (meta == 0) {
                return T2_RELATION_DEFERRED;
        }

        meta = find_root(solver, meta);
        u32 level = v__(solver->metas, meta - 1).level;
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
        if (extension == T2_TYPE_INVALID) {
                return T2_RELATION_COMPLEXITY;
        }

        return bind_sort_meta(solver, meta, extension, provenance);
}

static T2Relation
constrain_record_types(
        T2Solver     *solver,
        T2Type        actual_type,
        T2Type        expected_type,
        T2Node const *actual,
        T2Node const *expected,
        char const   *provenance,
        bool          retain_deferred
)
{
        T2RelationContext context = { .universe = solver->universe };
        T2Relation shape = record_subtype(&context, actual, expected, 0, true);
        if (shape == T2_RELATION_NO || shape == T2_RELATION_COMPLEXITY) {
                set_solver_error(
                        solver,
                        (shape == T2_RELATION_NO)
                        ? "incompatible record shape"
                        : "record comparison exceeded its complexity limit",
                        actual_type,
                        expected_type,
                        provenance
                );
                return shape;
        }

        T2Relation result = T2_RELATION_YES;
        for (usize i = 0; i + 1 < expected->arity; ++i) {
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
                        if (solver->failed) {
                                return T2_RELATION_NO;
                        }
                        have = solver_find_record_field(solver, actual, wanted->text);
                }

                if (have == NULL) {
                        continue;
                }
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
                if (solver->failed) {
                        return T2_RELATION_NO;
                }
        }

        T2Type expected_tail = expected->children[expected->arity - 1];
        T2Node const *expected_tail_node = get_node(solver->universe, expected_tail);
        if (expected_tail_node->kind != T2_TYPE_ROW_ANY) {
                usize extra_count = 0;
                T2FieldSpec *extras = ty_calloc(actual->arity - 1, sizeof *extras);
                if (actual->arity > 1 && extras == NULL) {
                        solver->failed = true;
                        ty_snprintf(
                                solver->error,
                                sizeof solver->error,
                                "types2 solver ran out of memory"
                        );
                        return T2_RELATION_COMPLEXITY;
                }

                for (usize i = 0; i + 1 < actual->arity; ++i) {
                        T2Node const *field = get_node(solver->universe, actual->children[i]);
                        if (
                                find_record_field_node(
                                        solver->universe,
                                        expected,
                                        field->text
                                ) == NULL
                        ) {
                                extras[extra_count++] = field_spec_from_node(field);
                        }
                }

                T2Type remainder = t2_row(
                        solver->universe,
                        extras,
                        extra_count,
                        actual->children[actual->arity - 1]
                );
                ty_free(extras);
                if (remainder == T2_TYPE_INVALID) {
                        return T2_RELATION_COMPLEXITY;
                }
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
        T2Solver     *solver,
        T2Node const *actual,
        T2Node const *expected,
        char const   *provenance,
        bool          retain_deferred,
        bool         *handled
)
{
        *handled = false;
        if (
                (actual->kind != T2_TYPE_PACK)
             || (expected->kind != T2_TYPE_PACK_EXPANSION)
             || (expected->arity != 1)
        ) {
                return T2_RELATION_DEFERRED;
        }

        T2Node const *pattern = get_node(
                solver->universe,
                expected->children[0]
        );
        if (pattern == NULL || pattern->kind != T2_TYPE_NOMINAL) {
                return T2_RELATION_DEFERRED;
        }

        usize pack_index = SIZE_MAX;
        u32 pack_root    = 0;
        for (usize i = 0; i < pattern->arity; ++i) {
                u32 meta = meta_from_type(solver, pattern->children[i]);
                if (meta == 0) {
                        continue;
                }
                meta = find_root(solver, meta);
                if (v__(solver->metas, meta - 1).variable_kind != T2_VARIABLE_PACK) {
                        continue;
                }
                if (pack_index != SIZE_MAX && pack_root != meta) {
                        return T2_RELATION_DEFERRED;
                }
                pack_index = i;
                pack_root  = meta;
        }

        if (pack_index == SIZE_MAX) {
                return T2_RELATION_DEFERRED;
        }

        usize count = (usize)actual->payload;
        if (actual->arity != count + 1) {
                return T2_RELATION_DEFERRED;
        }

        T2Node const *tail = get_node(
                solver->universe,
                actual->children[count]
        );
        if (tail == NULL || tail->kind != T2_TYPE_PACK_EMPTY) {
                return T2_RELATION_DEFERRED;
        }

        *handled = true;
        T2Type *elements = (count == 0) ? NULL : ty_malloc(count * sizeof *elements);
        if (count != 0 && elements == NULL) {
                solver->failed = true;
                ty_snprintf(
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
        for (usize i = 0; i < count; ++i) {
                T2Type item = actual->children[i];
                T2Node const *item_node = get_node(solver->universe, item);
                if (
                        (item_node != NULL)
                     && (
                                (item_node->kind == T2_TYPE_DYNAMIC)
                             || (item_node->kind == T2_TYPE_ERROR)
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
                        (projection == NULL)
                     || (projection->kind != T2_TYPE_NOMINAL)
                     || (projection->payload != pattern->payload)
                     || (projection->arity != pattern->arity)
                ) {
                        ty_free(elements);
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

                for (usize j = 0; j < pattern->arity; ++j) {
                        if (j == pack_index) {
                                continue;
                        }
                        T2Variance variance = (info == NULL)
                                            ? T2_INVARIANT
                                            : info->variance[j];
                        T2Relation item_relation;
                        if (variance == T2_COVARIANT || variance == T2_BIVARIANT) {
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
                                ty_free(elements);
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
        ty_free(elements);
        if (sequence == T2_TYPE_INVALID) {
                return T2_RELATION_COMPLEXITY;
        }

        T2Variance variance = (info == NULL)
                            ? T2_INVARIANT
                            : info->variance[pack_index];
        T2Type variable = meta_type(solver, pack_root);
        T2Relation sequence_relation;
        if (variance == T2_COVARIANT || variance == T2_BIVARIANT) {
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
        T2Solver     *solver,
        T2Node const *actual,
        T2Node const *expected,
        char const   *provenance,
        bool          retain_deferred
)
{
        if (expected->kind == T2_TYPE_PACK_ANY) {
                return T2_RELATION_YES;
        }

        if (actual->kind == T2_TYPE_PACK_EMPTY) {
                if (
                        (expected->kind == T2_TYPE_PACK_EMPTY)
                     || (expected->kind == T2_TYPE_PACK_EXPANSION)
                ) {
                        return T2_RELATION_YES;
                }

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
                if (handled) {
                        return mapped;
                }
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
                        usize count       = (usize)actual->payload;
                        for (usize i = 0; i < count; ++i) {
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
                                if (solver->failed) {
                                        return T2_RELATION_NO;
                                }
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
                        (actual->kind == T2_TYPE_META)
                     || (expected->kind == T2_TYPE_META)
                     || (actual->kind == T2_TYPE_VARIABLE)
                     || (expected->kind == T2_TYPE_VARIABLE)
                ) {
                        return T2_RELATION_DEFERRED;
                }

                set_solver_error(
                        solver,
                        "pack constraint has a non-pack operand",
                        T2_TYPE_INVALID,
                        T2_TYPE_INVALID,
                        provenance
                );
                return T2_RELATION_NO;
        }

        usize actual_count = (usize)actual->payload;
        usize expected_count = (usize)expected->payload;
        usize common = (actual_count < expected_count) ? actual_count : expected_count;
        T2Relation result = T2_RELATION_YES;
        for (usize i = 0; i < common; ++i) {
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
                if (solver->failed) {
                        return T2_RELATION_NO;
                }
        }

        T2Type actual_tail   = actual->children[actual_count];
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

static bool
solver_types_identical(
        T2Solver *solver,
        T2Type    left,
        T2Type    right,
        unsigned  depth
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
                u32 meta = meta_from_type(solver, type);
                if (meta == 0) {
                        return type;
                }
                meta = find_root(solver, meta);
                T2Meta const *node = v_(solver->metas, meta - 1);
                T2Type root  = meta_type(solver, meta);
                T2Type exact = node->solution;
                if (
                        (exact == T2_TYPE_INVALID)
                     && solver_types_identical(
                             solver,
                             node->lower,
                             node->upper,
                             depth + 1
                        )
                ) {
                        exact = node->lower;
                }

                if (exact == T2_TYPE_INVALID || exact == root) {
                        return root;
                }
                type = exact;
        }

        return type;
}

static bool
solver_types_identical(
        T2Solver *solver,
        T2Type    left,
        T2Type    right,
        unsigned  depth
)
{
        if (depth > T2_RELATION_DEPTH_LIMIT) {
                return false;
        }

        left  = resolve_exact_meta_head(solver, left, depth);
        right = resolve_exact_meta_head(solver, right, depth);
        if (left == right) {
                return left != T2_TYPE_INVALID;
        }

        if (
                (meta_from_type(solver, left) != 0)
             || (meta_from_type(solver, right) != 0)
        ) {
                return false;
        }

        T2Node const *a = get_node(solver->universe, left);
        T2Node const *b = get_node(solver->universe, right);
        if (
                (a == NULL)
             || (b == NULL)
             || (a->kind != b->kind)
             || (a->variable_kind != b->variable_kind)
             || (a->payload != b->payload)
             || (a->arity != b->arity)
             || ((a->text == NULL) != (b->text == NULL))
             || (
                        (a->text != NULL)
                     && (
                                (a->kind == T2_TYPE_LITERAL_STRING)
                              ? (memcmp(a->text, b->text, a->payload) != 0)
                              : !s_eq(a->text, b->text)
                        )
                )
        ) {
                return false;
        }

        for (usize i = 0; i < a->arity; ++i) {
                if (
                        !solver_types_identical(
                                solver,
                                a->children[i],
                                b->children[i],
                                depth + 1
                        )
                ) {
                        return false;
                }
        }

        return true;
}

static bool
argument_type_is_open(T2Solver *solver, T2Type type, unsigned depth)
{
        if (depth > T2_RELATION_DEPTH_LIMIT || type == T2_TYPE_INVALID) {
                return true;
        }

        u32 meta = meta_from_type(solver, type);
        if (meta != 0) {
                meta = find_root(solver, meta);
                T2Type solution = v__(solver->metas, meta - 1).solution;
                if (solution == T2_TYPE_INVALID) {
                        solution = v__(solver->metas, meta - 1).lower;
                        if (t2_type_kind(solver->universe, solution) == T2_TYPE_NEVER) {
                                return true;
                        }
                }
                return argument_type_is_open(solver, solution, depth + 1);
        }

        T2Node const *node = get_node(solver->universe, type);
        if (node == NULL || node->kind == T2_TYPE_FUNCTION) {
                return false;
        }

        for (usize i = 0; i < node->arity; ++i) {
                if (argument_type_is_open(solver, node->children[i], depth + 1)) {
                        return true;
                }
        }

        return false;
}

static bool
callable_parameters_open(T2Solver *solver, T2Node const *callable)
{
        usize count = (usize)callable->payload;
        for (usize i = 0; i < count && i < callable->arity; ++i) {
                if (argument_type_is_open(solver, callable->children[i], 0)) {
                        return true;
                }
        }

        return false;
}

static bool
arm_lower_bound_admits(T2Solver *solver, T2Type arm, T2Type subtype)
{
        if (meta_from_type(solver, arm) == 0) {
                return false;
        }

        T2Type lower = t2_solver_lower_bound(solver, arm);

        return (lower != T2_TYPE_INVALID)
            && (t2_subtype(solver->universe, subtype, lower) == T2_RELATION_YES);
}

static T2Type
resolve_meta_solution(T2Solver *solver, T2Type type)
{
        for (unsigned depth = 0; depth < 64; ++depth) {
                type = resolve_sort_solution(solver, type);
                u32 meta = meta_from_type(solver, type);
                if (meta == 0) {
                        return type;
                }
                T2Meta const *node = v_(solver->metas, find_root(solver, meta) - 1);
                T2Type solution = node->solution;
                if (solution == T2_TYPE_INVALID && node->lower == node->upper) {
                        solution = node->lower;
                }
                if (solution == T2_TYPE_INVALID) {
                        return type;
                }
                type = solution;
        }

        return type;
}

static T2Relation
constrain_either_way(
        T2Solver   *solver,
        T2Type      left,
        T2Type      right,
        char const *provenance,
        bool        retain_deferred
)
{
        left  = resolve_meta_solution(solver, left);
        right = resolve_meta_solution(solver, right);
        if (
                (meta_from_type(solver, left) != 0)
             || (meta_from_type(solver, right) != 0)
        ) {
                return t2_solver_unify(solver, left, right, provenance);
        }

        T2SolverMark mark = t2_solver_mark(solver);
        T2Relation forward = constrain_internal(
                solver,
                left,
                right,
                provenance,
                retain_deferred
        );
        if (forward != T2_RELATION_NO && !solver->failed) {
                t2_solver_commit(solver, mark);
                return forward;
        }

        t2_solver_rollback(solver, mark);

        return constrain_internal(
                solver,
                right,
                left,
                provenance,
                retain_deferred
        );
}

static bool
structural_actual(T2TypeKind kind)
{
        switch (kind) {
        case T2_TYPE_NOMINAL:
        case T2_TYPE_STRING:
        case T2_TYPE_LITERAL_STRING:
        case T2_TYPE_INT:
        case T2_TYPE_LITERAL_INT:
        case T2_TYPE_FLOAT:
        case T2_TYPE_BOOL:
        case T2_TYPE_LITERAL_BOOL:
        case T2_TYPE_TUPLE:
        case T2_TYPE_FUNCTION:
        case T2_TYPE_OVERLOAD:
                return true;
        default:
                return false;
        }
}

static T2Relation
constrain_internal(
        T2Solver   *solver,
        T2Type      subtype,
        T2Type      supertype,
        char const *provenance,
        bool        retain_deferred
)
{
        if (solver->failed) {
                return T2_RELATION_NO;
        }

        subtype   = resolve_sort_solution(solver, subtype);
        supertype = resolve_sort_solution(solver, supertype);
        if (type_contains_solved_pack_meta(solver, subtype, 0)) {
                subtype = resolve_pack_solutions(solver, subtype, 0);
        }

        if (type_contains_solved_pack_meta(solver, supertype, 0)) {
                supertype = resolve_pack_solutions(solver, supertype, 0);
        }

        if (
                (subtype == T2_TYPE_INVALID)
             || (supertype == T2_TYPE_INVALID)
             || solver->failed
        ) {
                return T2_RELATION_COMPLEXITY;
        }

        if (
                (subtype == supertype)
             || solver_types_identical(solver, subtype, supertype, 0)
        ) {
                return T2_RELATION_YES;
        }

        u32 a_meta = meta_from_type(solver, subtype);
        u32 b_meta = meta_from_type(solver, supertype);
        T2Node const *a_term = get_node(solver->universe, subtype);
        T2Node const *b_term = get_node(solver->universe, supertype);

        if (a_meta != 0 && b_term != NULL && b_term->kind == T2_TYPE_UNION) {
                for (usize i = 0; i < b_term->arity; ++i) {
                        if (solver_types_identical(
                                solver,
                                subtype,
                                b_term->children[i],
                                0
                        )) {
                                return T2_RELATION_YES;
                        }
                }
        }

        if (b_meta != 0 && a_term != NULL && a_term->kind == T2_TYPE_UNION) {
                T2Relation result = T2_RELATION_YES;
                bool removed_self = false;
                for (usize i = 0; i < a_term->arity; ++i) {
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
                        if (solver->failed) {
                                return T2_RELATION_NO;
                        }
                }

                if (removed_self) {
                        return result;
                }
        }

        if (a_meta != 0 && b_meta != 0) {
                T2VariableKind kind = v__(solver->metas, find_root(solver, a_meta) - 1).variable_kind;
                if (kind == T2_VARIABLE_ROW || kind == T2_VARIABLE_PACK) {
                        return bind_sort_meta(solver, a_meta, supertype, provenance);
                }
                return add_edge(solver, a_meta, b_meta, provenance);
        }

        if (a_meta != 0) {
                T2VariableKind kind = v__(solver->metas, find_root(solver, a_meta) - 1).variable_kind;
                if (kind == T2_VARIABLE_ROW || kind == T2_VARIABLE_PACK) {
                        return bind_sort_meta(solver, a_meta, supertype, provenance);
                }
                return update_upper(solver, a_meta, supertype, provenance);
        }

        if (b_meta != 0) {
                T2VariableKind kind = v__(solver->metas, find_root(solver, b_meta) - 1).variable_kind;
                if (kind == T2_VARIABLE_ROW || kind == T2_VARIABLE_PACK) {
                        return bind_sort_meta(solver, b_meta, subtype, provenance);
                }
                return update_lower(solver, b_meta, subtype, provenance);
        }

        T2Node const *a = a_term;
        T2Node const *b = b_term;
        if (a == NULL || b == NULL) {
                set_solver_error(
                        solver,
                        "invalid type constraint",
                        subtype,
                        supertype,
                        provenance
                );
                return T2_RELATION_NO;
        }

        if (a->kind == T2_TYPE_DYNAMIC || b->kind == T2_TYPE_DYNAMIC) {
                return T2_RELATION_YES;
        }

        if (a->kind == T2_TYPE_ANY) {
                return T2_RELATION_YES;
        }

        T2Type unfolded_subtype   = t2_recursive_unfold(solver->universe, subtype);
        T2Type unfolded_supertype = t2_recursive_unfold(solver->universe, supertype);
        if (unfolded_subtype != subtype || unfolded_supertype != supertype) {
                if (t2_subtype(solver->universe, subtype, supertype) == T2_RELATION_YES) {
                        return T2_RELATION_YES;
                }
                u64 pair = (u64)subtype << 32 | supertype;
                for (usize i = 0; i < vN(solver->recursive_constraints); ++i) {
                        if (v__(solver->recursive_constraints, i) == pair) {
                                return T2_RELATION_YES;
                        }
                }
                if (vN(solver->recursive_constraints) >= T2_RELATION_DEPTH_LIMIT) {
                        set_solver_error(
                                solver,
                                "recursive constraint exceeded its complexity limit",
                                subtype,
                                supertype,
                                provenance
                        );
                        return T2_RELATION_COMPLEXITY;
                }
                xvP(solver->recursive_constraints, pair);
                T2Relation result = constrain_internal(
                        solver,
                        unfolded_subtype,
                        unfolded_supertype,
                        provenance,
                        retain_deferred
                );
                vN(solver->recursive_constraints) -= 1;
                return result;
        }

        if (a->kind == T2_TYPE_UNION) {
                T2Relation result = T2_RELATION_YES;
                for (usize i = 0; i < a->arity; ++i) {
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
                        if (solver->failed) {
                                return T2_RELATION_NO;
                        }
                }

                return result;
        }

        if (b->kind == T2_TYPE_UNION) {
                for (usize i = 0; i < b->arity; ++i) {
                        if (
                                solver_types_identical(
                                        solver,
                                        subtype,
                                        b->children[i],
                                        0
                                )
                             || (
                                     t2_subtype(
                                             solver->universe,
                                             subtype,
                                             b->children[i]
                                     )
                                  == T2_RELATION_YES
                                )
                             || arm_lower_bound_admits(
                                     solver,
                                     b->children[i],
                                     subtype
                                )
                        ) {
                                return T2_RELATION_YES;
                        }
                }

                usize applicable = 0;
                usize selected   = 0;
                for (usize i = 0; i < b->arity; ++i) {
                        T2SolverMark mark = t2_solver_mark(solver);
                        T2Relation trial = constrain_internal(
                                solver,
                                subtype,
                                b->children[i],
                                provenance,
                                false
                        );
                        bool success = !solver->failed && (trial != T2_RELATION_NO);
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
                if (applicable != 0) {
                        return T2_RELATION_DEFERRED;
                }
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
                for (usize i = 0; i < b->arity; ++i) {
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
                        if (solver->failed) {
                                return T2_RELATION_NO;
                        }
                }

                return result;
        }

        if (
                ((a->kind == T2_TYPE_MULTI) || (b->kind == T2_TYPE_MULTI))
             && !sentinel_kind(a->kind)
             && !sentinel_kind(b->kind)
        ) {
                usize count = (multi_arity(a) > multi_arity(b))
                            ? multi_arity(a)
                            : multi_arity(b);
                T2Relation result = T2_RELATION_YES;
                for (usize i = 0; i < count; ++i) {
                        result = combine_all(
                                result,
                                constrain_internal(
                                        solver,
                                        t2_multi_item(solver->universe, subtype, i),
                                        t2_multi_item(solver->universe, supertype, i),
                                        provenance,
                                        retain_deferred
                                )
                        );
                        if (solver->failed || result == T2_RELATION_NO) {
                                return T2_RELATION_NO;
                        }
                }

                return result;
        }

        if (
                (a->kind == T2_TYPE_TUPLE)
             && (b->kind == T2_TYPE_TUPLE)
             && (a->arity == b->arity)
        ) {
                return constrain_children(solver, a, b, provenance, retain_deferred);
        }

        if (b->kind == T2_TYPE_OVERLOAD) {
                T2Relation result = T2_RELATION_YES;
                for (usize i = 0; i < b->arity; ++i) {
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
                        if (solver->failed) {
                                return T2_RELATION_NO;
                        }
                }

                return result;
        }

        if (
                (a->kind == T2_TYPE_TYPE_VALUE)
             && (a->arity == 2)
             && (b->kind == T2_TYPE_FUNCTION)
        ) {
                return constrain_internal(
                        solver,
                        a->children[1],
                        supertype,
                        provenance,
                        retain_deferred
                );
        }

        if (a->kind == T2_TYPE_TYPE_VALUE && b->kind == T2_TYPE_TYPE_VALUE) {
                return constrain_children(solver, a, b, provenance, retain_deferred);
        }

        if (a->kind == T2_TYPE_OVERLOAD && b->kind == T2_TYPE_FUNCTION) {
                usize applicable = 0;
                usize selected   = 0;
                for (usize i = 0; i < a->arity; ++i) {
                        T2SolverMark mark = t2_solver_mark(solver);
                        T2Relation trial = constrain_internal(
                                solver,
                                a->children[i],
                                supertype,
                                provenance,
                                false
                        );
                        bool success = !solver->failed && (trial != T2_RELATION_NO);
                        t2_solver_rollback(solver, mark);
                        if (!success) {
                                continue;
                        }
                        if (applicable == 0) {
                                selected = i;
                        }
                        applicable += 1;
                }

                if (applicable == 0) {
                        set_solver_error(
                                solver,
                                "no overload arm satisfies the expected callable",
                                subtype,
                                supertype,
                                provenance
                        );
                        return T2_RELATION_NO;
                }

                if (
                        (applicable == 1)
                     || !callable_parameters_open(solver, b)
                ) {
                        return constrain_internal(
                                solver,
                                a->children[selected],
                                supertype,
                                provenance,
                                retain_deferred
                        );
                }

                if (retain_deferred) {
                        return retain_obligation(solver, subtype, supertype, provenance);
                }
                return T2_RELATION_DEFERRED;
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
                (b->kind == T2_TYPE_RECORD)
             && structural_actual(a->kind)
             && (solver->predicate_resolver != NULL)
        ) {
                T2Predicate predicate = {
                        .kind       = T2_PREDICATE_SUBTYPE,
                        .subtype    = subtype,
                        .supertype  = supertype,
                        .operand    = t2_primitive(solver->universe, T2_TYPE_NEVER),
                        .provenance = provenance
                };
                T2Relation relation = solver->predicate_resolver(
                        solver->predicate_context,
                        solver,
                        &predicate
                );
                if (relation == T2_RELATION_DEFERRED) {
                        return retain_deferred
                             ? retain_obligation(solver, subtype, supertype, provenance)
                             : T2_RELATION_DEFERRED;
                }

                if (relation == T2_RELATION_NO && !solver->failed) {
                        set_solver_error(
                                solver,
                                "the value does not provide the required members",
                                subtype,
                                supertype,
                                provenance
                        );
                }

                return relation;
        }

        if (
                (a->kind == T2_TYPE_PACK)
             || (a->kind == T2_TYPE_PACK_EMPTY)
             || (a->kind == T2_TYPE_PACK_ANY)
             || (a->kind == T2_TYPE_PACK_EXPANSION)
             || (b->kind == T2_TYPE_PACK)
             || (b->kind == T2_TYPE_PACK_EMPTY)
             || (b->kind == T2_TYPE_PACK_ANY)
             || (b->kind == T2_TYPE_PACK_EXPANSION)
        ) {
                return constrain_pack_types(
                        solver,
                        a,
                        b,
                        provenance,
                        retain_deferred
                );
        }

        if (
                (a->kind == T2_TYPE_NOMINAL)
             && (b->kind == T2_TYPE_NOMINAL)
             && (a->payload == b->payload)
             && (a->arity == b->arity)
        ) {
                T2NominalInfo const *info = find_nominal(solver->universe, a->payload);
                T2Relation result = T2_RELATION_YES;
                for (usize i = 0; i < a->arity; ++i) {
                        T2Variance variance = (info == NULL)
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
                        } else if (variance == T2_BIVARIANT) {
                                item = constrain_either_way(
                                        solver,
                                        a->children[i],
                                        b->children[i],
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
                        if (solver->failed) {
                                return T2_RELATION_NO;
                        }
                }

                return result;
        }

        if (b->kind == T2_TYPE_NOMINAL && a->kind != T2_TYPE_NOMINAL) {
                T2Type bound = primitive_nominal(solver->universe, a);
                if (bound != T2_TYPE_INVALID) {
                        return constrain_internal(
                                solver,
                                bound,
                                supertype,
                                provenance,
                                retain_deferred
                        );
                }
        }

        if (a->kind == T2_TYPE_NOMINAL && b->kind == T2_TYPE_NOMINAL) {
                T2AppliedNominal const *applied = find_applied_nominal(
                        solver->universe,
                        subtype
                );
                if (applied != NULL) {
                        for (usize i = 0; i < vN(applied->supertypes); ++i) {
                                T2SolverMark mark = t2_solver_mark(solver);
                                T2Relation trial = constrain_internal(
                                        solver,
                                        v__(applied->supertypes, i),
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
                set_solver_error(
                        solver,
                        "constraint failed",
                        subtype,
                        supertype,
                        provenance
                );
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
        if (solver->draining_work) {
                return;
        }

        solver->draining_work = true;
        solver->drain_epoch += 1;
        if (solver->drain_epoch == 0) {
                for (usize i = 0; i < vN(solver->edges); ++i) {
                        v__(solver->edges, i).self_retry_epoch = 0;
                }
                for (usize i = 0; i < vN(solver->obligations); ++i) {
                        v__(solver->obligations, i).self_retry_epoch = 0;
                }
                solver->drain_epoch = 1;
        }

        while (
                !solver->failed
             && (solver->work_index < vN(solver->work))
        ) {
                u64 work = v__(solver->work, solver->work_index++);
                solver->active_work       = work;
                solver->processing_work   = true;
                solver->rerun_active_work = false;
                solver->work_steps += 1;
                if ((work & T2_WATCH_OBLIGATION) != 0) {
                        usize index = (usize)(work & ~T2_WATCH_OBLIGATION);
                        if (index >= vN(solver->obligations)) {
                                goto WorkDone;
                        }
                        T2Obligation *obligation = v_(solver->obligations, index);
                        if (!obligation->active) {
                                goto WorkDone;
                        }
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

                        obligation = v_(solver->obligations, index);
                        if (relation == T2_RELATION_YES) {
                                if (
                                        !push_undo(
                                                solver,
                                                (T2Undo) {
                                                        .kind  = T2_UNDO_OBLIGATION_ACTIVE,
                                                        .index = (u32)index,
                                                        .old   = obligation->active
                                                }
                                        )
                                ) {
                                        break;
                                }

                                obligation->active = false;
                        } else if (
                                (relation == T2_RELATION_DEFERRED)
                             && !solver->failed
                        ) {
                                if (!watch_obligation(solver, index)) {
                                        break;
                                }
                        } else if (
                                (relation == T2_RELATION_NO)
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
                        usize index = (usize)work;
                        if (index >= vN(solver->edges)) {
                                goto WorkDone;
                        }
                        T2Edge edge = v__(solver->edges, index);
                        u32 sub     = find_root(solver, edge.subtype);
                        u32 sup     = find_root(solver, edge.supertype);
                        if (sub == sup) {
                                goto WorkDone;
                        }
                        T2Meta const *sub_node = v_(solver->metas, sub - 1);
                        T2Meta const *sup_node = v_(solver->metas, sup - 1);
                        if (
                                update_lower(
                                        solver,
                                        sup,
                                        sub_node->lower,
                                        edge.provenance
                                )
                             == T2_RELATION_NO
                        ) {
                                break;
                        }

                        if (
                                update_upper(
                                        solver,
                                        sub,
                                        sup_node->upper,
                                        edge.provenance
                                )
                             == T2_RELATION_NO
                        ) {
                                break;
                        }
                }

WorkDone:
                solver->processing_work = false;
                if (solver->rerun_active_work && !solver->failed) {
                        solver->rerun_active_work = false;
                        u64 *epoch;
                        if ((work & T2_WATCH_OBLIGATION) != 0) {
                                usize index = (usize)(
                                        work & ~T2_WATCH_OBLIGATION
                                );
                                epoch = (index < vN(solver->obligations))
                                      ? &v__(solver->obligations, index).self_retry_epoch
                                      : NULL;
                        } else {
                                usize index = (usize)work;
                                epoch = (index < vN(solver->edges))
                                      ? &v__(solver->edges, index).self_retry_epoch
                                      : NULL;
                        }

                        if (epoch != NULL && *epoch != solver->drain_epoch) {
                                *epoch = solver->drain_epoch;
                                if (!enqueue(solver, work)) {
                                        break;
                                }
                        }
                }
        }

        solver->draining_work     = false;
        solver->processing_work   = false;
        solver->rerun_active_work = false;
        solver->active_work       = 0;

        if (solver->work_index == vN(solver->work)) {
                solver->work_index = 0;
                vN(solver->work)   = 0;
        }
}

char const *
t2_solver_meta_provenance(T2Solver const *solver, T2Type type)
{
        if (solver == NULL) {
                return NULL;
        }

        u32 meta = meta_from_type(solver, type);

        return (meta == 0) ? NULL : v__(solver->metas, meta - 1).provenance;
}

T2Relation
t2_solver_constrain_subtype(
        T2Solver   *solver,
        T2Type      subtype,
        T2Type      supertype,
        char const *provenance
)
{
        if (solver == NULL || solver->failed) {
                return T2_RELATION_NO;
        }

        u32 subtype_meta       = meta_from_type(solver, subtype);
        u32 supertype_meta     = meta_from_type(solver, supertype);
        T2CauseKind cause_kind = T2_CAUSE_PREDICATE;

        if (subtype_meta != 0 && supertype_meta != 0) {
                cause_kind = T2_CAUSE_EDGE;
        } else if (subtype_meta != 0) {
                cause_kind = T2_CAUSE_UPPER;
        } else if (supertype_meta != 0) {
                cause_kind = T2_CAUSE_LOWER;
        }

        provenance = record_cause(
                solver,
                cause_kind,
                subtype,
                supertype,
                provenance
        );
        if (solver->failed) {
                return T2_RELATION_NO;
        }

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
        T2Solver          *solver,
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
                (get_node(solver->universe, predicate->subtype) == NULL)
             || (get_node(solver->universe, predicate->supertype) == NULL)
             || (get_node(solver->universe, predicate->operand) == NULL)
        ) {
                return T2_RELATION_NO;
        }

        (void)record_cause(
                solver,
                T2_CAUSE_PREDICATE,
                predicate->subtype,
                predicate->supertype,
                predicate->provenance
        );

        if (solver->failed) {
                return T2_RELATION_NO;
        }

        T2Relation relation = (solver->predicate_resolver == NULL)
                            ? T2_RELATION_DEFERRED
                            : solver->predicate_resolver(
                                    solver->predicate_context,
                                    solver,
                                    predicate
                              )
        ;

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
        T2Solver   *solver,
        u32         left,
        u32         right,
        char const *provenance
)
{
        left  = find_root(solver, left);
        right = find_root(solver, right);

        if (left == right) {
                return T2_RELATION_YES;
        }

        T2Meta *a = v_(solver->metas, left - 1);
        T2Meta *b = v_(solver->metas, right - 1);
        if (
                (
                        (a->variable_kind == T2_VARIABLE_ROW)
                     != (b->variable_kind == T2_VARIABLE_ROW)
                )
             || (
                     (a->variable_kind == T2_VARIABLE_PACK)
                  != (b->variable_kind == T2_VARIABLE_PACK)
                )
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

        T2Type solution = (a->solution != T2_TYPE_INVALID) ? a->solution : b->solution;
        if (
                (a->solution != T2_TYPE_INVALID)
             && (b->solution != T2_TYPE_INVALID)
             && (a->solution != b->solution)
             && (
                     t2_solver_unify(solver, a->solution, b->solution, provenance)
                  == T2_RELATION_NO
                )
        ) {
                return T2_RELATION_NO;
        }

        T2Type lower = t2_join(solver->universe, a->lower, b->lower);
        T2Type upper = t2_meet(solver->universe, a->upper, b->upper);
        T2Relation consistent = t2_subtype(solver->universe, lower, upper);

        if (consistent == T2_RELATION_NO || consistent == T2_RELATION_COMPLEXITY) {
                set_solver_error(
                        solver,
                        "equality has inconsistent bounds",
                        lower,
                        upper,
                        provenance
                );
                return consistent;
        }

        if (a->rank < b->rank) {
                u32 temporary = left;
                left  = right;
                right = temporary;
                a     = v_(solver->metas, left - 1);
                b     = v_(solver->metas, right - 1);
        }

        if (
                !push_undo(
                        solver,
                        (T2Undo) {
                                .kind  = T2_UNDO_PARENT,
                                .index = right,
                                .old   = b->parent
                        }
                )
        ) {
                return T2_RELATION_COMPLEXITY;
        }

        b->parent = left;

        if (a->rank == b->rank) {
                if (
                        !push_undo(
                                solver,
                                (T2Undo) {
                                        .kind  = T2_UNDO_RANK,
                                        .index = left,
                                        .old   = a->rank
                                }
                        )
                ) {
                        return T2_RELATION_COMPLEXITY;
                }

                a->rank += 1;
        }

        if (
                (a->variable_kind != T2_VARIABLE_ROW)
             && (a->variable_kind != T2_VARIABLE_PACK)
             && (
                        (a->variable_kind == T2_VARIABLE_WEAK)
                     || (b->variable_kind == T2_VARIABLE_WEAK)
                )
             && (a->variable_kind != T2_VARIABLE_WEAK)
        ) {
                if (
                        !push_undo(
                                solver,
                                (T2Undo) {
                                        .kind  = T2_UNDO_VARIABLE_KIND,
                                        .index = left,
                                        .old   = a->variable_kind
                                }
                        )
                ) {
                        return T2_RELATION_COMPLEXITY;
                }

                a->variable_kind = T2_VARIABLE_WEAK;
        }

        if (
                !push_undo(
                        solver,
                        (T2Undo) {
                                .kind  = T2_UNDO_LOWER,
                                .index = left,
                                .old   = a->lower
                        }
                )
        ) {
                return T2_RELATION_COMPLEXITY;
        }

        if (
                !push_undo(
                        solver,
                        (T2Undo) {
                                .kind  = T2_UNDO_UPPER,
                                .index = left,
                                .old   = a->upper
                        }
                )
        ) {
                return T2_RELATION_COMPLEXITY;
        }

        a->lower = lower;
        a->upper = upper;
        if (
                !push_undo(
                        solver,
                        (T2Undo) {
                                .kind  = T2_UNDO_SOLUTION,
                                .index = left,
                                .old   = a->solution
                        }
                )
        ) {
                return T2_RELATION_COMPLEXITY;
        }

        a->solution = solution;

        for (usize i = 0; i < vN(b->watchers); ++i) {
                if (!push_watch(solver, left, v__(b->watchers, i))) {
                        return T2_RELATION_COMPLEXITY;
                }
        }

        wake_meta(solver, left);

        return T2_RELATION_YES;
}

T2Relation
t2_solver_unify(
        T2Solver   *solver,
        T2Type      left,
        T2Type      right,
        char const *provenance
)
{
        if (solver == NULL || solver->failed) {
                return T2_RELATION_NO;
        }

        if (left == right) {
                return T2_RELATION_YES;
        }

        provenance = record_cause(
                solver,
                T2_CAUSE_EQUALITY,
                left,
                right,
                provenance
        );

        if (solver->failed) {
                return T2_RELATION_NO;
        }

        u32 a_meta = meta_from_type(solver, left);
        u32 b_meta = meta_from_type(solver, right);
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
        if (solver == NULL) {
                return T2_TYPE_INVALID;
        }

        u32 id = meta_from_type(solver, meta);
        if (id == 0) {
                return T2_TYPE_INVALID;
        }

        id = find_root(solver, id);

        return v__(solver->metas, id - 1).lower;
}

T2Type
t2_solver_upper_bound(T2Solver *solver, T2Type meta)
{
        if (solver == NULL) {
                return T2_TYPE_INVALID;
        }

        u32 id = meta_from_type(solver, meta);
        if (id == 0) {
                return T2_TYPE_INVALID;
        }

        id = find_root(solver, id);

        return v__(solver->metas, id - 1).upper;
}

T2Type
t2_solver_solution(
        T2Solver            *solver,
        T2Type               meta,
        T2SolutionPreference preference
)
{
        if (solver == NULL) {
                return T2_TYPE_INVALID;
        }

        u32 id = meta_from_type(solver, meta);
        if (id == 0) {
                return T2_TYPE_INVALID;
        }

        id = find_root(solver, id);
        if (v__(solver->metas, id - 1).solution != T2_TYPE_INVALID) {
                return v__(solver->metas, id - 1).solution;
        }

        T2Type lower = t2_solver_lower_bound(solver, meta);
        T2Type upper = t2_solver_upper_bound(solver, meta);
        if (lower == T2_TYPE_INVALID || upper == T2_TYPE_INVALID) {
                return T2_TYPE_INVALID;
        }

        T2Type never = t2_primitive(solver->universe, T2_TYPE_NEVER);
        T2Type any   = t2_primitive(solver->universe, T2_TYPE_ANY);

        if (v__(solver->metas, id - 1).retired) {
                if (lower != never) {
                        return lower;
                }
                if (upper != any) {
                        return upper;
                }
                return meta;
        }

        if (preference == T2_PREFER_SOLUTION_ONLY) {
                return meta;
        }

        if (preference == T2_PREFER_KNOWN_VALUE) {
                return (lower != never) ? lower : meta;
        }

        if (preference == T2_PREFER_UPPER_BOUND) {
                if (upper != any) {
                        return upper;
                }
                if (lower != never) {
                        return lower;
                }
        } else {
                if (lower != never) {
                        return lower;
                }
                if (upper != any) {
                        return upper;
                }
        }

        return meta;
}

bool
t2_solver_failed(T2Solver const *solver)
{
        return (solver == NULL) || solver->failed;
}

char const *
t2_solver_error(T2Solver const *solver)
{
        return (solver == NULL) ? "invalid types2 solver" : solver->error;
}

static char *
solver_explain_from(T2Solver const *solver, usize cause_start)
{
        if (solver == NULL) {
                return S2("invalid types2 solver");
        }

        if (cause_start > vN(solver->causes)) {
                cause_start = vN(solver->causes);
        }

        T2StringBuffer buffer = { 0 };
        if (solver->error[0] != '\0') {
                buffer_text(&buffer, solver->error);
                buffer_text(&buffer, "\n");
        }

        for (usize i = cause_start; i < vN(solver->causes); ++i) {
                T2Cause const *cause = v_(solver->causes, i);
                char const *kind = "predicate";
                switch (cause->kind) {
                case T2_CAUSE_LOWER:     kind = "lower bound"; break;
                case T2_CAUSE_UPPER:     kind = "upper bound"; break;
                case T2_CAUSE_EDGE:      kind = "subtype edge"; break;
                case T2_CAUSE_EQUALITY:  kind = "equality"; break;
                case T2_CAUSE_PREDICATE: break;
                }
                char *left  = t2_type_string(solver->universe, cause->left);
                char *right = t2_type_string(solver->universe, cause->right);
                buffer_format(
                        &buffer,
                        "%s: %s <: %s",
                        kind,
                        (left == NULL) ? "<type>" : left,
                        (right == NULL) ? "<type>" : right
                );
                if (cause->provenance != NULL) {
                        buffer_text(&buffer, " from ");
                        buffer_text(&buffer, cause->provenance);
                }
                buffer_text(&buffer, "\n");
                ty_free(left);
                ty_free(right);
        }

        return (vv(buffer) == NULL) ? S2("") : vv(buffer);
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

usize
t2_solver_pending_obligations(T2Solver const *solver)
{
        if (solver == NULL) {
                return 0;
        }

        usize count = 0;
        for (usize i = 0; i < vN(solver->obligations); ++i) {
                count += v__(solver->obligations, i).active;
        }

        return count;
}

bool
t2_solver_pending_obligation(
        T2Solver const *solver,
        usize           index,
        T2Predicate    *predicate
)
{
        if (solver == NULL || predicate == NULL) {
                return false;
        }

        for (usize i = 0; i < vN(solver->obligations); ++i) {
                T2Obligation const *obligation = v_(solver->obligations, i);
                if (!obligation->active) {
                        continue;
                }
                if (index-- != 0) {
                        continue;
                }
                *predicate = obligation->predicate;
                return true;
        }

        return false;
}

usize
t2_solver_meta_count(T2Solver const *solver)
{
        return (solver == NULL) ? 0 : vN(solver->metas);
}

usize
t2_solver_edge_count(T2Solver const *solver)
{
        return (solver == NULL) ? 0 : vN(solver->edges);
}

u64
t2_solver_work_steps(T2Solver const *solver)
{
        return (solver == NULL) ? 0 : solver->work_steps;
}

T2SolverMark
t2_solver_mark(T2Solver *solver)
{
        if (solver == NULL) {
                return (T2SolverMark) { 0 };
        }

        T2SolverMark mark = {
                .undo_count        = vN(solver->undo),
                .meta_count        = vN(solver->metas),
                .edge_count        = vN(solver->edges),
                .obligation_count  = vN(solver->obligations),
                .work_count        = vN(solver->work),
                .work_index        = solver->work_index,
                .cause_count       = vN(solver->causes),
                .transaction_depth = solver->transaction_depth,
                .failed = solver->failed
        };

        solver->transaction_depth += 1;

        return mark;
}

void
t2_solver_commit(T2Solver *solver, T2SolverMark mark)
{
        if (
                (solver == NULL)
             || (solver->transaction_depth != mark.transaction_depth + 1)
        ) {
                return;
        }

        solver->transaction_depth = mark.transaction_depth;

        if (solver->transaction_depth == 0) {
                vN(solver->undo) = 0;
        }
}

bool
t2_solver_cancel_obligations_since(T2Solver *solver, T2SolverMark mark)
{
        if (
                (solver == NULL)
             || (solver->transaction_depth != mark.transaction_depth + 1)
             || (mark.obligation_count > vN(solver->obligations))
        ) {
                return false;
        }

        for (usize i = mark.obligation_count; i < vN(solver->obligations); ++i) {
                T2Obligation *obligation = v_(solver->obligations, i);
                if (!obligation->active) {
                        continue;
                }
                if (
                        !push_undo(
                                solver,
                                (T2Undo) {
                                        .kind  = T2_UNDO_OBLIGATION_ACTIVE,
                                        .index = (u32)i,
                                        .old   = obligation->active
                                }
                        )
                ) {
                        return false;
                }
                obligation->active = false;
        }

        return true;
}

void
t2_solver_rollback(T2Solver *solver, T2SolverMark mark)
{
        if (
                (solver == NULL)
             || (solver->transaction_depth != mark.transaction_depth + 1)
        ) {
                return;
        }

        while (vN(solver->undo) > mark.undo_count) {
                T2Undo undo = v__(solver->undo, --vN(solver->undo));
                switch (undo.kind) {
                case T2_UNDO_PARENT:
                        v__(solver->metas, undo.index - 1).parent = (u32)undo.old;
                        break;
                case T2_UNDO_RANK:
                        v__(solver->metas, undo.index - 1).rank = (uint8_t)undo.old;
                        break;
                case T2_UNDO_VARIABLE_KIND:
                        v__(solver->metas, undo.index - 1).variable_kind = (T2VariableKind)undo.old;
                        break;
                case T2_UNDO_LOWER:
                        v__(solver->metas, undo.index - 1).lower = (T2Type)undo.old;
                        break;
                case T2_UNDO_UPPER:
                        v__(solver->metas, undo.index - 1).upper = (T2Type)undo.old;
                        break;
                case T2_UNDO_SOLUTION:
                        v__(solver->metas, undo.index - 1).solution = (T2Type)undo.old;
                        break;
                case T2_UNDO_WATCH_COUNT:
                        v__(solver->metas, undo.index - 1).watchers.count = (usize)undo.old;
                        break;
                case T2_UNDO_OBLIGATION_ACTIVE:
                        v__(solver->obligations, undo.index).active = undo.old;
                        break;
                }
        }

        for (usize i = mark.meta_count; i < vN(solver->metas); ++i) {
                xvF(v__(solver->metas, i).watchers);
                ty_free(v__(solver->metas, i).provenance);
                memset(v_(solver->metas, i), 0, sizeof v__(solver->metas, i));
        }

        for (usize i = mark.cause_count; i < vN(solver->causes); ++i) {
                ty_free(v__(solver->causes, i).provenance);
                memset(v_(solver->causes, i), 0, sizeof v__(solver->causes, i));
        }

        for (usize i = mark.obligation_count; i < vN(solver->obligations); ++i) {
                ty_free(v__(solver->obligations, i).name);
                ty_free(v__(solver->obligations, i).provenance);
                memset(v_(solver->obligations, i), 0, sizeof v__(solver->obligations, i));
        }

        vN(solver->metas)       = mark.meta_count;
        vN(solver->edges)       = mark.edge_count;
        vN(solver->obligations) = mark.obligation_count;
        vN(solver->work)        = mark.work_count;
        solver->work_index      = mark.work_index;
        vN(solver->causes)      = mark.cause_count;
        solver->transaction_depth = mark.transaction_depth;
        solver->failed = mark.failed;
        if (!solver->failed) {
                clear_solver_failure(solver);
        }

        if (solver->transaction_depth == 0) {
                vN(solver->undo) = 0;
        }
}

T2Scheme *
t2_scheme_new(
        T2Universe         *universe,
        T2Quantifier const *quantifiers,
        usize               quantifier_count,
        T2Type              body,
        T2Predicate const  *predicates,
        usize               predicate_count
)
{
        if (
                (universe == NULL)
             || (get_node(universe, body) == NULL)
             || ((quantifier_count != 0) && (quantifiers == NULL))
             || ((predicate_count != 0) && (predicates == NULL))
        ) {
                return NULL;
        }

        for (usize i = 0; i < quantifier_count; ++i) {
                if (
                        (quantifiers[i].kind == T2_VARIABLE_RIGID)
                     || (quantifiers[i].kind == T2_VARIABLE_WEAK)
                ) {
                        return NULL;
                }

                for (usize j = 0; j < i; ++j) {
                        if (quantifiers[j].id == quantifiers[i].id) {
                                return NULL;
                        }
                }
        }

        for (usize i = 0; i < predicate_count; ++i) {
                if (
                        (get_node(universe, predicates[i].subtype) == NULL)
                     || (get_node(universe, predicates[i].supertype) == NULL)
                     || (
                                (predicates[i].kind != T2_PREDICATE_SUBTYPE)
                             && (get_node(universe, predicates[i].operand) == NULL)
                        )
                ) {
                        return NULL;
                }
        }

        T2Scheme *scheme = ty_calloc(1, sizeof *scheme);
        if (scheme == NULL) {
                return NULL;
        }

        scheme->universe = universe;
        scheme->body     = body;

        if (quantifier_count != 0) {
                scheme->quantifiers = ty_malloc(
                        quantifier_count * sizeof *scheme->quantifiers
                );
                if (scheme->quantifiers == NULL) {
                        goto Fail;
                }
                memcpy(
                        scheme->quantifiers,
                        quantifiers,
                        quantifier_count * sizeof *scheme->quantifiers
                );
                scheme->quantifier_count = quantifier_count;
        }

        if (predicate_count != 0) {
                scheme->predicates = ty_calloc(predicate_count, sizeof *scheme->predicates);
                if (scheme->predicates == NULL) {
                        goto Fail;
                }
                scheme->predicate_count = predicate_count;
                for (usize i = 0; i < predicate_count; ++i) {
                        scheme->predicates[i] = predicates[i];
                        scheme->predicates[i].name = S2N(
                                predicates[i].name
                        );
                        scheme->predicates[i].provenance = S2N(
                                predicates[i].provenance
                        );
                        if (
                                (
                                        (predicates[i].name != NULL)
                                     && (scheme->predicates[i].name == NULL)
                                )
                             || (
                                        (predicates[i].provenance != NULL)
                                     && (scheme->predicates[i].provenance == NULL)
                                )
                        ) {
                                goto Fail;
                        }
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
        if (scheme == NULL) {
                return;
        }

        for (usize i = 0; i < scheme->predicate_count; ++i) {
                ty_free((char *)scheme->predicates[i].name);
                ty_free((char *)scheme->predicates[i].provenance);
        }

        ty_free(scheme->predicates);
        for (
                usize i = 0;
                (scheme->names != NULL)
             && (i < scheme->quantifier_count);
                ++i
        ) {
                ty_free(scheme->names[i]);
        }

        ty_free(scheme->names);
        ty_free(scheme->quantifiers);
        ty_free(scheme);
}

bool
t2_scheme_name_quantifier(T2Scheme *scheme, usize index, char const *name)
{
        if (scheme == NULL || index >= scheme->quantifier_count) {
                return false;
        }

        if (scheme->names == NULL) {
                scheme->names = ty_calloc(scheme->quantifier_count, sizeof *scheme->names);
                if (scheme->names == NULL) {
                        return false;
                }
        }

        char *owned = S2N(name);
        if (name != NULL && owned == NULL) {
                return false;
        }

        ty_free(scheme->names[index]);
        scheme->names[index] = owned;

        return true;
}

char const *
t2_scheme_quantifier_name(T2Scheme const *scheme, usize index)
{
        if (
                (scheme == NULL)
             || (scheme->names == NULL)
             || (index >= scheme->quantifier_count)
        ) {
                return NULL;
        }

        return scheme->names[index];
}

T2Type
t2_scheme_type(T2Universe *universe, T2Scheme const *scheme)
{
        if (universe == NULL || scheme == NULL) {
                return T2_TYPE_INVALID;
        }

        usize arity = scheme->quantifier_count + 1 + scheme->predicate_count;
        T2Type *children = ty_malloc(arity * sizeof *children);
        if (children == NULL) {
                return T2_TYPE_INVALID;
        }

        usize count = 0;
        for (usize i = 0; i < scheme->quantifier_count; ++i) {
                T2Quantifier const *quantifier = &scheme->quantifiers[i];
                children[count++] = intern_type(
                        universe,
                        T2_TYPE_BINDER,
                        quantifier->kind,
                        quantifier->id,
                        t2_scheme_quantifier_name(scheme, i),
                        NULL,
                        0
                );
        }

        children[count++] = scheme->body;
        for (usize i = 0; i < scheme->predicate_count; ++i) {
                T2Predicate const *predicate = &scheme->predicates[i];
                T2Type parts[3] = {
                        predicate->subtype,
                        predicate->supertype,
                        predicate->operand
                };
                children[count++] = intern_type(
                        universe,
                        T2_TYPE_PREDICATE,
                        T2_VARIABLE_FLEXIBLE,
                        (u64)predicate->kind,
                        predicate->name,
                        parts,
                        (predicate->operand == T2_TYPE_INVALID) ? 2 : 3
                );
        }

        T2Type result = intern_type(
                universe,
                T2_TYPE_SCHEME,
                T2_VARIABLE_FLEXIBLE,
                scheme->quantifier_count,
                NULL,
                children,
                arity
        );
        ty_free(children);

        return result;
}

static T2Predicate
predicate_from_node(T2Node const *node)
{
        return (T2Predicate) {
                .kind      = (T2PredicateKind)node->payload,
                .subtype   = node->children[0],
                .supertype = node->children[1],
                .operand   = (node->arity > 2) ? node->children[2] : T2_TYPE_INVALID,
                .name      = node->text
        };
}

T2Scheme *
t2_type_scheme(T2Universe *universe, T2Type type)
{
        T2Node const *node = get_node(universe, type);
        if (node == NULL || node->kind != T2_TYPE_SCHEME) {
                return NULL;
        }

        usize quantifier_count = (usize)node->payload;
        usize predicate_count  = node->arity - quantifier_count - 1;
        T2Quantifier *quantifiers = ty_calloc(
                quantifier_count + 1,
                sizeof *quantifiers
        );
        T2Predicate *predicates = ty_calloc(predicate_count + 1, sizeof *predicates);
        if (quantifiers == NULL || predicates == NULL) {
                ty_free(quantifiers);
                ty_free(predicates);
                return NULL;
        }

        for (usize i = 0; i < quantifier_count; ++i) {
                T2Node const *binder = get_node(universe, node->children[i]);
                quantifiers[i] = (T2Quantifier) {
                        .id   = (u32)binder->payload,
                        .kind = binder->variable_kind
                };
        }

        for (usize i = 0; i < predicate_count; ++i) {
                predicates[i] = predicate_from_node(
                        get_node(universe, node->children[quantifier_count + 1 + i])
                );
        }

        T2Scheme *scheme = t2_scheme_new(
                universe,
                quantifiers,
                quantifier_count,
                node->children[quantifier_count],
                predicates,
                predicate_count
        );
        for (usize i = 0; scheme != NULL && i < quantifier_count; ++i) {
                T2Node const *binder = get_node(universe, node->children[i]);
                if (binder->text != NULL) {
                        (void)t2_scheme_name_quantifier(scheme, i, binder->text);
                }
        }

        ty_free(quantifiers);
        ty_free(predicates);

        return scheme;
}

typedef struct t2_occurrence {
        unsigned positive;
        unsigned negative;
} T2Occurrence;

static void
count_occurrences(
        T2Universe const *universe,
        T2Type            type,
        u32               id,
        bool              positive,
        T2Occurrence     *out,
        unsigned          depth
)
{
        T2Node const *node = get_node(universe, type);
        if (node == NULL || depth > T2_RELATION_DEPTH_LIMIT) {
                return;
        }

        switch (node->kind) {
        case T2_TYPE_VARIABLE:
                if (node->payload != id) {
                        return;
                }
                if (positive) {
                        out->positive += 1;
                } else {
                        out->negative += 1;
                }

                return;
        case T2_TYPE_FUNCTION:
        {
                usize count = (usize)node->payload;
                for (usize i = 0; i < count; ++i) {
                        count_occurrences(
                                universe,
                                node->children[i],
                                id,
                                !positive,
                                out,
                                depth + 1
                        );
                }

                count_occurrences(
                        universe,
                        node->children[count],
                        id,
                        positive,
                        out,
                        depth + 1
                );
                count_occurrences(
                        universe,
                        node->children[count + 1],
                        id,
                        positive,
                        out,
                        depth + 1
                );
                count_occurrences(
                        universe,
                        node->children[count + 2],
                        id,
                        !positive,
                        out,
                        depth + 1
                );
                return;
        }
        case T2_TYPE_NOMINAL:
        {
                T2NominalInfo const *info = find_nominal(universe, node->payload);
                for (usize i = 0; i < node->arity; ++i) {
                        T2Variance variance = (info != NULL)
                                           && (info->variance != NULL)
                                           && (i < info->arity)
                                            ? info->variance[i]
                                            : T2_INVARIANT;
                        if (variance != T2_CONTRAVARIANT) {
                                count_occurrences(
                                        universe,
                                        node->children[i],
                                        id,
                                        positive,
                                        out,
                                        depth + 1
                                );
                        }

                        if (variance == T2_CONTRAVARIANT || variance == T2_INVARIANT) {
                                count_occurrences(
                                        universe,
                                        node->children[i],
                                        id,
                                        !positive,
                                        out,
                                        depth + 1
                                );
                        }
                }

                return;
        }
        case T2_TYPE_FIELD:
                count_occurrences(
                        universe,
                        node->children[0],
                        id,
                        positive,
                        out,
                        depth + 1
                )
                ;
                if ((node->payload & T2_FIELD_WRITABLE_BIT) != 0) {
                        count_occurrences(
                                universe,
                                node->children[0],
                                id,
                                !positive,
                                out,
                                depth + 1
                        );
                }

                return;
        case T2_TYPE_TYPE_VALUE:
                for (usize i = 0; i < node->arity; ++i) {
                        count_occurrences(
                                universe,
                                node->children[i],
                                id,
                                positive,
                                out,
                                depth + 1
                        );
                        count_occurrences(
                                universe,
                                node->children[i],
                                id,
                                !positive,
                                out,
                                depth + 1
                        );
                }

                return;
        default:
                for (usize i = 0; i < node->arity; ++i) {
                        count_occurrences(
                                universe,
                                node->children[i],
                                id,
                                positive,
                                out,
                                depth + 1
                        );
                }

                return;
        }
}

static bool
mentions_variable(T2Universe const *universe, T2Type type, u32 id)
{
        T2Occurrence occurrence = { 0 };
        if (type == T2_TYPE_INVALID) {
                return false;
        }

        count_occurrences(universe, type, id, true, &occurrence, 0);

        return (occurrence.positive != 0) || (occurrence.negative != 0);
}

static void
remove_predicate(T2Scheme *scheme, usize index)
{
        ty_free((char *)scheme->predicates[index].name);
        ty_free((char *)scheme->predicates[index].provenance);
        memmove(
                &scheme->predicates[index],
                &scheme->predicates[index + 1],
                (scheme->predicate_count - index - 1) * sizeof *scheme->predicates
        );
        scheme->predicate_count -= 1;
}

static void
remove_quantifier(T2Scheme *scheme, usize index)
{
        memmove(
                &scheme->quantifiers[index],
                &scheme->quantifiers[index + 1],
                (scheme->quantifier_count - index - 1) * sizeof *scheme->quantifiers
        );
        if (scheme->names != NULL) {
                ty_free(scheme->names[index]);
                memmove(
                        &scheme->names[index],
                        &scheme->names[index + 1],
                        (scheme->quantifier_count - index - 1) * sizeof *scheme->names
                );
        }

        scheme->quantifier_count -= 1;
}

static bool
write_predicate(T2PredicateKind kind)
{
        return (kind == T2_PREDICATE_SUBSCRIPT_WRITE)
            || (
                    kind == T2_PREDICATE_MEMBER_WRITE
               )
        ;
}

static bool
substitution_preserves_predicate(
        T2Universe const  *universe,
        T2Predicate const *predicate,
        u32                id,
        bool               minimal
)
{
        bool in_subtype   = mentions_variable(universe, predicate->subtype, id);
        bool in_supertype = mentions_variable(universe, predicate->supertype, id);
        bool in_operand   = mentions_variable(universe, predicate->operand, id);
        if (minimal) {
                return !in_supertype || write_predicate(predicate->kind);
        }

        if (in_subtype || in_operand) {
                return false;
        }

        return !in_supertype
            || (
                       !write_predicate(predicate->kind)
                    && (predicate->kind != T2_PREDICATE_KEYWORD_SPREAD)
               )
        ;
}

static T2Type
substitute_variable(
        T2Universe *universe,
        T2Type      type,
        u32         id,
        T2Type      replacement
)
{
        return (type == T2_TYPE_INVALID)
             ? type
             : t2_type_substitute(universe, type, &id, &replacement, 1);
}

static bool
eliminate_bound_variable(T2Scheme *scheme, usize index, bool minimal)
{
        T2Universe *universe         = scheme->universe;
        T2Predicate const *predicate = &scheme->predicates[index];
        T2Type variable    = minimal ? predicate->supertype : predicate->subtype;
        T2Type replacement = minimal ? predicate->subtype : predicate->supertype;
        T2Node const *node = get_node(universe, variable);
        if (node == NULL || node->kind != T2_TYPE_VARIABLE) {
                return false;
        }

        if (node->variable_kind != T2_VARIABLE_QUANTIFIED) {
                return false;
        }

        u32 id = (u32)node->payload;
        usize quantifier = scheme->quantifier_count;
        for (usize i = 0; i < scheme->quantifier_count; ++i) {
                if (scheme->quantifiers[i].id == id) {
                        quantifier = i;
                }
        }

        if (quantifier == scheme->quantifier_count) {
                return false;
        }

        if (mentions_variable(universe, replacement, id)) {
                return false;
        }

        T2Occurrence body = { 0 };
        count_occurrences(universe, scheme->body, id, true, &body, 0);
        if (minimal ? body.negative != 0 : body.positive != 0) {
                return false;
        }

        for (usize i = 0; i < scheme->predicate_count; ++i) {
                if (i == index) {
                        continue;
                }
                if (
                        !substitution_preserves_predicate(
                                universe,
                                &scheme->predicates[i],
                                id,
                                minimal
                        )
                ) {
                        return false;
                }
        }

        T2Type substituted = substitute_variable(
                universe,
                scheme->body,
                id,
                replacement
        );
        if (substituted == T2_TYPE_INVALID) {
                return false;
        }

        for (usize i = 0; i < scheme->predicate_count; ++i) {
                T2Predicate *other = &scheme->predicates[i];
                if (i == index) {
                        continue;
                }
                other->subtype = substitute_variable(
                        universe,
                        other->subtype,
                        id,
                        replacement
                );
                other->supertype = substitute_variable(
                        universe,
                        other->supertype,
                        id,
                        replacement
                );
                other->operand = substitute_variable(
                        universe,
                        other->operand,
                        id,
                        replacement
                );
        }

        scheme->body = substituted;
        remove_predicate(scheme, index);
        remove_quantifier(scheme, quantifier);

        return true;
}

static bool
same_predicate(T2Predicate const *a, T2Predicate const *b)
{
        return (a->kind == b->kind)
            && (a->subtype == b->subtype)
            && (a->supertype == b->supertype)
            && (a->operand == b->operand)
            && (
                       (a->name == b->name)
                    || ((a->name != NULL) && (b->name != NULL) && s_eq(a->name, b->name))
               )
        ;
}

static bool
drop_duplicate_predicate(T2Scheme *scheme)
{
        for (usize i = 0; i < scheme->predicate_count; ++i) {
                for (usize j = i + 1; j < scheme->predicate_count; ++j) {
                        if (!same_predicate(&scheme->predicates[i], &scheme->predicates[j])) {
                                continue;
                        }
                        remove_predicate(scheme, j);
                        return true;
                }
        }

        return false;
}

static bool
quantified_variable_id(T2Universe const *universe, T2Type type, u32 *id)
{
        T2Node const *node = get_node(universe, type);
        if (
                (node == NULL)
             || (node->kind != T2_TYPE_VARIABLE)
             || (node->variable_kind != T2_VARIABLE_QUANTIFIED)
        ) {
                return false;
        }

        *id = (u32)node->payload;

        return true;
}

static bool
merge_bounds(T2Scheme *scheme, bool lower)
{
        T2Universe *universe = scheme->universe;
        for (usize i = 0; i < scheme->predicate_count; ++i) {
                T2Predicate const *first = &scheme->predicates[i];
                u32 id;
                if (
                        (first->kind != T2_PREDICATE_SUBTYPE)
                     || !quantified_variable_id(
                             universe,
                             lower ? first->supertype : first->subtype,
                             &id
                        )
                ) {
                        continue;
                }

                T2Type variable = lower ? first->supertype : first->subtype;
                usize count     = 0;
                for (usize j = 0; j < scheme->predicate_count; ++j) {
                        T2Predicate const *other = &scheme->predicates[j];
                        if (
                                (other->kind == T2_PREDICATE_SUBTYPE)
                             && ((lower ? other->supertype : other->subtype) == variable)
                        ) {
                                count += 1;
                        }
                }

                if (count < 2) {
                        continue;
                }
                T2Type *arms = ty_malloc(count * sizeof *arms);
                if (arms == NULL) {
                        return false;
                }
                usize filled = 0;
                for (usize j = scheme->predicate_count; j != 0; --j) {
                        T2Predicate const *other = &scheme->predicates[j - 1];
                        if (
                                (other->kind != T2_PREDICATE_SUBTYPE)
                             || ((lower ? other->supertype : other->subtype) != variable)
                        ) {
                                continue;
                        }

                        arms[filled++] = lower ? other->subtype : other->supertype;
                        if (j - 1 != i) {
                                remove_predicate(scheme, j - 1);
                        }
                }

                T2Type merged = lower
                              ? t2_union(universe, arms, filled)
                              : t2_intersection(universe, arms, filled);
                ty_free(arms);
                if (merged == T2_TYPE_INVALID) {
                        return false;
                }
                if (lower) {
                        scheme->predicates[i].subtype = merged;
                } else {
                        scheme->predicates[i].supertype = merged;
                }

                return true;
        }

        return false;
}

T2Scheme *
t2_scheme_simplify(T2Scheme *scheme)
{
        if (scheme == NULL) {
                return NULL;
        }

        for (bool changed = true; changed;) {
                changed = drop_duplicate_predicate(scheme)
                       || merge_bounds(scheme, true)
                       || merge_bounds(scheme, false);
                for (usize i = 0; i < scheme->predicate_count && !changed; ++i) {
                        if (scheme->predicates[i].kind != T2_PREDICATE_SUBTYPE) {
                                continue;
                        }
                        changed = eliminate_bound_variable(scheme, i, true)
                               || eliminate_bound_variable(scheme, i, false);
                }
        }

        return scheme;
}

T2Type
t2_type_scheme_body(T2Universe const *universe, T2Type type)
{
        for (;;) {
                T2Node const *node = get_node(universe, type);
                if (node == NULL || node->kind != T2_TYPE_SCHEME) {
                        return type;
                }
                type = node->children[node->payload];
        }
}

usize
t2_scheme_quantifier_count(T2Scheme const *scheme)
{
        return (scheme == NULL) ? 0 : scheme->quantifier_count;
}

bool
t2_scheme_quantifier(
        T2Scheme const *scheme,
        usize           index,
        T2Quantifier   *quantifier
)
{
        if (
                (scheme == NULL)
             || (quantifier == NULL)
             || (index >= scheme->quantifier_count)
        ) {
                return false;
        }

        *quantifier = scheme->quantifiers[index];

        return true;
}

T2Type
t2_scheme_body(T2Scheme const *scheme)
{
        return (scheme == NULL) ? T2_TYPE_INVALID : scheme->body;
}

bool
t2_scheme_has_metas(T2Scheme const *scheme)
{
        if (scheme == NULL) {
                return false;
        }
        if (t2_type_has_metas(scheme->universe, scheme->body)) {
                return true;
        }
        for (usize i = 0; i < scheme->predicate_count; ++i) {
                T2Predicate const *predicate = &scheme->predicates[i];
                if (
                        t2_type_has_metas(scheme->universe, predicate->subtype)
                     || t2_type_has_metas(scheme->universe, predicate->supertype)
                     || t2_type_has_metas(scheme->universe, predicate->operand)
                ) {
                        return true;
                }
        }
        return false;
}

bool
t2_solver_zonk_scheme(T2Solver *solver, T2Scheme *scheme)
{
        if (scheme == NULL) {
                return true;
        }
        scheme->body = t2_solver_zonk(solver, scheme->body, T2_PREFER_LOWER_BOUND);
        if (scheme->body == T2_TYPE_INVALID) {
                return false;
        }
        for (usize i = 0; i < scheme->predicate_count; ++i) {
                T2Predicate *predicate = &scheme->predicates[i];
                predicate->subtype = t2_solver_zonk(
                        solver,
                        predicate->subtype,
                        T2_PREFER_LOWER_BOUND
                );
                predicate->supertype = t2_solver_zonk(
                        solver,
                        predicate->supertype,
                        T2_PREFER_LOWER_BOUND
                );
                if (
                        (predicate->subtype == T2_TYPE_INVALID)
                     || (predicate->supertype == T2_TYPE_INVALID)
                ) {
                        return false;
                }
                if (predicate->operand != T2_TYPE_INVALID) {
                        predicate->operand = t2_solver_zonk(
                                solver,
                                predicate->operand,
                                T2_PREFER_LOWER_BOUND
                        );
                        if (predicate->operand == T2_TYPE_INVALID) {
                                return false;
                        }
                }
        }
        return true;
}

usize
t2_scheme_predicate_count(T2Scheme const *scheme)
{
        return (scheme == NULL) ? 0 : scheme->predicate_count;
}

bool
t2_scheme_predicate(
        T2Scheme const *scheme,
        usize           index,
        T2Predicate    *predicate
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
        u32 source;
        u32 result;
} T2BinderSubstitution;

typedef struct t2_instantiation {
        T2Scheme const           *scheme;
        T2Solver                 *solver;
        T2Type                   *replacements;
        vec(T2InstantiatedNode)   nodes;
        vec(T2BinderSubstitution) binders;
        bool failed;
} T2Instantiation;

static bool
collect_generalization_polarity(
        T2Solver *solver,
        T2Type    type,
        unsigned  polarity,
        unsigned *polarities,
        unsigned  depth
)
{
        if (depth > T2_RELATION_DEPTH_LIMIT) {
                return false;
        }

        u32 meta = meta_from_type(solver, type);
        if (meta != 0) {
                meta = find_root(solver, meta);
                T2Meta const *node = v_(solver->metas, meta - 1);
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
        if (node == NULL) {
                return false;
        }

        if ((node->flags & T2_NODE_META) == 0) {
                return true;
        }

        if (node->kind == T2_TYPE_NOMINAL) {
                T2NominalInfo const *nominal = find_nominal(
                        solver->universe,
                        node->payload
                );
                if (nominal == NULL) {
                        return false;
                }
                for (usize i = 0; i < node->arity; ++i) {
                        unsigned child = polarity;
                        if (nominal->variance[i] == T2_CONTRAVARIANT) {
                                child = flip_polarity(polarity);
                        } else if (nominal->variance[i] == T2_INVARIANT) {
                                child = T2_POLARITY_POSITIVE | T2_POLARITY_NEGATIVE;
                        }

                        if (
                                !collect_generalization_polarity(
                                        solver,
                                        node->children[i],
                                        child,
                                        polarities,
                                        depth + 1
                                )
                        ) {
                                return false;
                        }
                }

                return true;
        }

        if (node->kind == T2_TYPE_FUNCTION) {
                usize count = (usize)node->payload;
                for (usize i = 0; i < count; ++i) {
                        T2Node const *parameter = get_node(
                                solver->universe,
                                node->children[i]
                        );
                        if (
                                !collect_generalization_polarity(
                                        solver,
                                        parameter->children[0],
                                        flip_polarity(polarity),
                                        polarities,
                                        depth + 1
                                )
                        ) {
                                return false;
                        }
                }

                return (
                        collect_generalization_polarity(
                                solver,
                                node->children[count],
                                polarity,
                                polarities,
                                depth + 1
                        )
                     && collect_generalization_polarity(
                                solver,
                                node->children[count + 1],
                                polarity,
                                polarities,
                                depth + 1
                        )
                     && collect_generalization_polarity(
                                solver,
                                node->children[count + 2],
                                flip_polarity(polarity),
                                polarities,
                                depth + 1
                        )
                );
        }

        if (node->kind == T2_TYPE_RECORD || node->kind == T2_TYPE_ROW) {
                for (usize i = 0; i + 1 < node->arity; ++i) {
                        T2Node const *field = get_node(
                                solver->universe,
                                node->children[i]
                        );
                        unsigned child = (field->payload & T2_FIELD_WRITABLE_BIT)
                                       ? T2_POLARITY_POSITIVE | T2_POLARITY_NEGATIVE
                                       : polarity;
                        if (
                                !collect_generalization_polarity(
                                        solver,
                                        field->children[0],
                                        child,
                                        polarities,
                                        depth + 1
                                )
                        ) {
                                return false;
                        }
                }

                return collect_generalization_polarity(
                        solver,
                        node->children[node->arity - 1],
                        polarity,
                        polarities,
                        depth + 1
                );
        }

        for (usize i = 0; i < node->arity; ++i) {
                if (
                        !collect_generalization_polarity(
                                solver,
                                node->children[i],
                                polarity,
                                polarities,
                                depth + 1
                        )
                ) {
                        return false;
                }
        }

        return true;
}

static bool
type_touches_marked_meta(
        T2Solver       *solver,
        T2Type          type,
        unsigned const *marks,
        unsigned        depth
)
{
        if (depth > T2_RELATION_DEPTH_LIMIT) {
                return false;
        }

        u32 meta = meta_from_type(solver, type);
        if (meta != 0) {
                meta = find_root(solver, meta);
                T2Meta const *node = v_(solver->metas, meta - 1);
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
        if (node == NULL || (node->flags & T2_NODE_META) == 0) {
                return false;
        }

        for (usize i = 0; i < node->arity; ++i) {
                if (type_touches_marked_meta(
                        solver,
                        node->children[i],
                        marks,
                        depth + 1
                )) {
                        return true;
                }
        }

        return false;
}

static bool
type_contains_variable(
        T2Solver      *solver,
        T2Type         type,
        T2VariableKind variable_kind,
        u32            variable_id,
        unsigned       depth
)
{
        if (depth > T2_RELATION_DEPTH_LIMIT) {
                return false;
        }

        u32 meta = meta_from_type(solver, type);
        if (meta != 0) {
                meta = find_root(solver, meta);
                T2Type solution = v__(solver->metas, meta - 1).solution;
                return (solution != T2_TYPE_INVALID)
                    && type_contains_variable(
                            solver,
                            solution,
                            variable_kind,
                            variable_id,
                            depth + 1
                       )
                ;
        }

        T2Node const *node = get_node(solver->universe, type);
        if (node == NULL) {
                return false;
        }

        if (
                (node->kind == T2_TYPE_VARIABLE)
             && (node->variable_kind == variable_kind)
             && (node->payload == variable_id)
        ) {
                return true;
        }

        for (usize i = 0; i < node->arity; ++i) {
                if (
                        type_contains_variable(
                                solver,
                                node->children[i],
                                variable_kind,
                                variable_id,
                                depth + 1
                        )
                ) {
                        return true;
                }
        }

        return false;
}

static bool
type_reaches_variable(
        T2Solver      *solver,
        T2Type         type,
        T2VariableKind variable_kind,
        u32            variable_id,
        unsigned       depth
);

static bool
types_share_variable(
        T2Solver *solver,
        T2Type    exported,
        T2Type    candidate,
        unsigned  depth
)
{
        if (depth > T2_RELATION_DEPTH_LIMIT) {
                return false;
        }

        u32 meta = meta_from_type(solver, exported);
        if (meta != 0) {
                meta = find_root(solver, meta);
                T2Type solution = v__(solver->metas, meta - 1).solution;
                return (solution != T2_TYPE_INVALID)
                    && types_share_variable(
                            solver,
                            solution,
                            candidate,
                            depth + 1
                       )
                ;
        }

        T2Node const *node = get_node(solver->universe, exported);
        if (node == NULL) {
                return false;
        }

        if (node->kind == T2_TYPE_VARIABLE) {
                return type_reaches_variable(
                        solver,
                        candidate,
                        node->variable_kind,
                        (u32)node->payload,
                        0
                );
        }

        for (usize i = 0; i < node->arity; ++i) {
                if (types_share_variable(
                        solver,
                        node->children[i],
                        candidate,
                        depth + 1
                )) {
                        return true;
                }
        }

        return false;
}

static bool
type_reaches_variable(
        T2Solver      *solver,
        T2Type         type,
        T2VariableKind variable_kind,
        u32            variable_id,
        unsigned       depth
)
{
        if (depth > T2_RELATION_DEPTH_LIMIT) {
                return false;
        }

        u32 meta = meta_from_type(solver, type);
        if (meta != 0) {
                meta = find_root(solver, meta);
                T2Meta const *node = v_(solver->metas, meta - 1);
                if (node->solution != T2_TYPE_INVALID) {
                        return type_reaches_variable(
                                solver,
                                node->solution,
                                variable_kind,
                                variable_id,
                                depth + 1
                        );
                }

                return (
                        (
                                (node->lower != T2_TYPE_INVALID)
                             && type_reaches_variable(
                                        solver,
                                        node->lower,
                                        variable_kind,
                                        variable_id,
                                        depth + 1
                                )
                        )
                     || (
                                (node->upper != T2_TYPE_INVALID)
                             && type_reaches_variable(
                                        solver,
                                        node->upper,
                                        variable_kind,
                                        variable_id,
                                        depth + 1
                                )
                        )
                );
        }

        T2Node const *node = get_node(solver->universe, type);
        if (node == NULL) {
                return false;
        }

        if (
                (node->kind == T2_TYPE_VARIABLE)
             && (node->variable_kind == variable_kind)
             && (node->payload == variable_id)
        ) {
                return true;
        }

        for (usize i = 0; i < node->arity; ++i) {
                if (
                        type_reaches_variable(
                                solver,
                                node->children[i],
                                variable_kind,
                                variable_id,
                                depth + 1
                        )
                ) {
                        return true;
                }
        }

        return false;
}

static bool
predicate_shares_exported_variable(
        T2Solver          *solver,
        T2Type             exported,
        T2Predicate const *predicate
)
{
        return types_share_variable(solver, exported, predicate->subtype, 0)
            || types_share_variable(solver, exported, predicate->supertype, 0)
            || (
                       (predicate->operand != T2_TYPE_INVALID)
                    && types_share_variable(
                               solver,
                               exported,
                               predicate->operand,
                               0
                       )
               )
        ;
}

static bool
close_generalization_constraints(T2Solver *solver, unsigned *polarities)
{
        if (vN(solver->metas) == 0) {
                return true;
        }

        unsigned *previous = ty_malloc(vN(solver->metas) * sizeof *previous);
        if (previous == NULL) {
                return false;
        }

        usize remaining = vN(solver->metas) * 2 + 1;
        bool changed;
        do {
                memcpy(
                        previous,
                        polarities,
                        vN(solver->metas) * sizeof *previous
                );
                for (usize i = 0; i < vN(solver->metas); ++i) {
                        if (polarities[i] == 0) {
                                continue;
                        }
                        if (find_root(solver, (u32)i + 1) != i + 1) {
                                continue;
                        }
                        T2Meta const *meta = v_(solver->metas, i);
                        unsigned polarity = polarities[i];
                        if (
                                !collect_generalization_polarity(
                                        solver,
                                        meta->lower,
                                        polarity,
                                        polarities,
                                        0
                                )
                             || !collect_generalization_polarity(
                                     solver,
                                     meta->upper,
                                     polarity,
                                     polarities,
                                     0
                                )
                        ) {
                                goto Fail;
                        }
                }

                for (usize i = 0; i < vN(solver->edges); ++i) {
                        u32 subtype   = find_root(solver, v__(solver->edges, i).subtype);
                        u32 supertype = find_root(solver, v__(solver->edges, i).supertype);
                        unsigned connected = polarities[subtype - 1]
                                           | polarities[supertype - 1];
                        if (connected == 0) {
                                continue;
                        }
                        polarities[subtype - 1] |= connected;
                        polarities[supertype - 1] |= connected;
                }

                for (usize i = 0; i < vN(solver->obligations); ++i) {
                        T2Obligation const *obligation = v_(solver->obligations, i);
                        if (!obligation->active) {
                                continue;
                        }
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
                                        (predicate->operand == T2_TYPE_INVALID)
                                     || !type_touches_marked_meta(
                                                solver,
                                                predicate->operand,
                                                polarities,
                                                0
                                        )
                                )
                        ) {
                                continue;
                        }

                        if (
                                !collect_generalization_polarity(
                                        solver,
                                        predicate->subtype,
                                        T2_POLARITY_POSITIVE | T2_POLARITY_NEGATIVE,
                                        polarities,
                                        0
                                )
                             || !collect_generalization_polarity(
                                     solver,
                                     predicate->supertype,
                                     T2_POLARITY_POSITIVE | T2_POLARITY_NEGATIVE,
                                     polarities,
                                     0
                                )
                        ) {
                                goto Fail;
                        }

                        if (
                                (predicate->operand != T2_TYPE_INVALID)
                             && !collect_generalization_polarity(
                                     solver,
                                     predicate->operand,
                                     T2_POLARITY_POSITIVE | T2_POLARITY_NEGATIVE,
                                     polarities,
                                     0
                                )
                        ) {
                                goto Fail;
                        }
                }

                changed = (
                                  memcmp(
                                          previous,
                                          polarities,
                                          vN(solver->metas) * sizeof *previous
                                  )
                               != 0
                          )
                ;
        } while (changed && remaining-- != 0);

        ty_free(previous);
        return !changed;

Fail:
        ty_free(previous);

        return false;
}

static bool
type_touches_replacement(
        T2Solver     *solver,
        T2Type        type,
        T2Type const *replacements,
        unsigned      depth
)
{
        if (depth > T2_RELATION_DEPTH_LIMIT) {
                return false;
        }

        u32 meta = meta_from_type(solver, type);
        if (meta != 0) {
                meta = find_root(solver, meta);
                if (replacements[meta - 1] != T2_TYPE_INVALID) {
                        return true;
                }
                T2Type solution = v__(solver->metas, meta - 1).solution;
                return (solution != T2_TYPE_INVALID)
                    && type_touches_replacement(
                            solver,
                            solution,
                            replacements,
                            depth + 1
                       )
                ;
        }

        T2Node const *node = get_node(solver->universe, type);
        if (node == NULL) {
                return false;
        }

        for (usize i = 0; i < node->arity; ++i) {
                if (
                        type_touches_replacement(
                                solver,
                                node->children[i],
                                replacements,
                                depth + 1
                        )
                ) {
                        return true;
                }
        }

        return false;
}

static bool
type_contains_solver_meta(T2Solver *solver, T2Type type, unsigned depth)
{
        if (depth > T2_RELATION_DEPTH_LIMIT) {
                return true;
        }

        if (meta_from_type(solver, type) != 0) {
                return true;
        }

        T2Node const *node = get_node(solver->universe, type);
        if (node == NULL) {
                return true;
        }

        for (usize i = 0; i < node->arity; ++i) {
                if (type_contains_solver_meta(
                        solver,
                        node->children[i],
                        depth + 1
                )) {
                        return true;
                }
        }

        return false;
}

typedef struct t2_generalization_entry {
        T2Type source;
        T2Type result;
} T2GeneralizationEntry;

typedef struct t2_generalization {
        T2Solver                  *solver;
        T2Type                    *replacements;
        vec(T2GeneralizationEntry) entries;
        vec(T2BinderSubstitution)  binders;
} T2Generalization;

static T2Type
generalize_type(T2Generalization *generalization, T2Type source);

static T2Type
generalize_recursive(T2Generalization *generalization, T2Node const *node)
{
        T2Universe *universe = generalization->solver->universe;
        u32 binder = t2_universe_fresh_recursive_binder(universe);
        if (binder == 0) {
                return T2_TYPE_INVALID;
        }

        usize mark = vN(generalization->binders);
        xvP(generalization->binders, ((T2BinderSubstitution) {
                .source = (u32)node->payload,
                .result = binder
        }));
        T2Type body = generalize_type(generalization, node->children[0]);
        vN(generalization->binders) = mark;

        return (body == T2_TYPE_INVALID)
             ? body
             : t2_recursive(universe, binder, body);
}

static T2Type
generalize_type(T2Generalization *generalization, T2Type source)
{
        T2Solver *solver = generalization->solver;
        u32 meta = meta_from_type(solver, source);
        if (meta != 0) {
                meta = find_root(solver, meta);
                if (generalization->replacements[meta - 1] != T2_TYPE_INVALID) {
                        return generalization->replacements[meta - 1];
                }
                T2Type solution = v__(solver->metas, meta - 1).solution;
                return (solution == T2_TYPE_INVALID)
                     ? meta_type(solver, meta)
                     : generalize_type(generalization, solution);
        }

        T2Node const *node = get_node(solver->universe, source);
        if (node == NULL) {
                return T2_TYPE_INVALID;
        }

        if ((node->flags & (T2_NODE_META | T2_NODE_RECURSIVE_VARIABLE)) == 0) {
                return source;
        }

        if (node->kind == T2_TYPE_RECURSIVE_VARIABLE) {
                for (usize i = vN(generalization->binders); i != 0; --i) {
                        T2BinderSubstitution const *binder = v_(generalization->binders, i - 1);
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

        for (usize i = 0; i < vN(generalization->entries); ++i) {
                if (v__(generalization->entries, i).source == source) {
                        return v__(generalization->entries, i).result;
                }
        }

        if (node->arity == 0) {
                return source;
        }

        T2Type *children = ty_malloc(node->arity * sizeof *children);
        if (children == NULL) {
                return T2_TYPE_INVALID;
        }

        bool changed = false;
        for (usize i = 0; i < node->arity; ++i) {
                children[i] = generalize_type(generalization, node->children[i]);
                if (children[i] == T2_TYPE_INVALID) {
                        ty_free(children);
                        return T2_TYPE_INVALID;
                }
                changed |= children[i] != node->children[i];
        }

        T2Type result = changed
                      ? rebuild_type(solver->universe, node, children)
                      : source;
        ty_free(children);
        if (result == T2_TYPE_INVALID) {
                return result;
        }

        xvP(generalization->entries, ((T2GeneralizationEntry) {
                .source = source,
                .result = result
        }));

        return result;
}

static T2Type
weak_lower_view(
        T2Solver  *solver,
        T2Type     type,
        u32 const *active,
        usize      active_count
)
{
        if (active_count > T2_RELATION_DEPTH_LIMIT) {
                return type;
        }

        u32 meta = meta_from_type(solver, type);
        if (meta != 0) {
                meta = find_root(solver, meta);
                T2Meta const *node = v_(solver->metas, meta - 1);
                if (node->solution != T2_TYPE_INVALID) {
                        return weak_lower_view(
                                solver,
                                node->solution,
                                active,
                                active_count
                        );
                }

                if (node->variable_kind != T2_VARIABLE_WEAK) {
                        return meta_type(solver, meta);
                }
                for (usize i = 0; i < active_count; ++i) {
                        if (active[i] == meta) {
                                return meta_type(solver, meta);
                        }
                }

                u32 stack[T2_RELATION_DEPTH_LIMIT + 2];
                if (active_count != 0) {
                        memcpy(stack, active, active_count * sizeof *stack);
                }
                stack[active_count] = meta;
                T2Type never = t2_primitive(solver->universe, T2_TYPE_NEVER);
                T2Type view  = node->lower;
                for (usize i = 0; i < vN(solver->edges); ++i) {
                        u32 sub = find_root(solver, v__(solver->edges, i).subtype);
                        u32 sup = find_root(solver, v__(solver->edges, i).supertype);
                        if (sub == meta || sup != meta) {
                                continue;
                        }
                        T2Type below = weak_lower_view(
                                solver,
                                meta_type(solver, sub),
                                stack,
                                active_count + 1
                        );
                        if (below == T2_TYPE_INVALID) {
                                return below;
                        }
                        view = t2_join(solver->universe, view, below);
                        if (view == T2_TYPE_INVALID) {
                                return view;
                        }
                }

                return (view == never) ? meta_type(solver, meta) : view;
        }

        T2Node const *node = get_node(solver->universe, type);
        if (
                (node == NULL)
             || (node->arity == 0)
             || (node->kind == T2_TYPE_RECURSIVE)
        ) {
                return type;
        }

        T2Type *children = ty_malloc(node->arity * sizeof *children);
        if (children == NULL) {
                return T2_TYPE_INVALID;
        }

        bool changed = false;
        for (usize i = 0; i < node->arity; ++i) {
                children[i] = weak_lower_view(
                        solver,
                        node->children[i],
                        active,
                        active_count
                );
                if (children[i] == T2_TYPE_INVALID) {
                        ty_free(children);
                        return T2_TYPE_INVALID;
                }
                changed |= children[i] != node->children[i];
        }

        T2Type result = changed
                      ? rebuild_type(solver->universe, node, children)
                      : type;
        ty_free(children);

        return result;
}

static T2Predicate
obligation_view(T2Solver *solver, T2Predicate const *predicate)
{
        T2Predicate view = *predicate;
        view.subtype   = weak_lower_view(solver, predicate->subtype, NULL, 0);
        view.supertype = weak_lower_view(solver, predicate->supertype, NULL, 0);
        if (predicate->operand != T2_TYPE_INVALID) {
                view.operand = weak_lower_view(
                        solver,
                        predicate->operand,
                        NULL,
                        0
                );
        }

        return view;
}

static bool
generalizable_meta(
        T2Solver *solver,
        usize     index,
        unsigned  polarity,
        u32       binding_level,
        bool      expansive
)
{
        if (polarity == 0) {
                return false;
        }

        if (find_root(solver, (u32)index + 1) != index + 1) {
                return false;
        }

        T2Meta const *meta = v_(solver->metas, index);

        return (meta->level > binding_level)
            && (meta->variable_kind != T2_VARIABLE_WEAK)
            && (meta->solution == T2_TYPE_INVALID)
            && (!expansive || (polarity == T2_POLARITY_POSITIVE));
}

static T2Scheme *
solver_generalize(
        T2Solver     *solver,
        T2Type        type,
        T2Type const *environment,
        usize         environment_count,
        u32           binding_level,
        bool          expansive,
        usize         scoped_obligation_start
)
{
        if (
                (solver == NULL)
             || solver->failed
             || (get_node(solver->universe, type) == NULL)
             || ((environment_count != 0) && (environment == NULL))
        ) {
                return NULL;
        }

        usize count = vN(solver->metas);
        unsigned *polarities   = ty_calloc(count, sizeof *polarities);
        bool *environment_free = ty_calloc(count, sizeof *environment_free);
        T2Type *replacements = ty_calloc(count, sizeof *replacements);
        if (
                (count != 0)
             && (
                        (polarities == NULL)
                     || (environment_free == NULL)
                     || (
                                replacements == NULL
                        )
                )
        ) {
                goto Fail;
        }

        if (
                !collect_generalization_polarity(
                        solver,
                        type,
                        T2_POLARITY_POSITIVE,
                        polarities,
                        0
                )
        ) {
                goto Fail;
        }

        if (scoped_obligation_start != SIZE_MAX) {
                for (
                        usize i = scoped_obligation_start;
                        i < vN(solver->obligations);
                        ++i
                ) {
                        T2Obligation const *obligation = v_(solver->obligations, i);
                        if (!obligation->active) {
                                continue;
                        }
                        T2Predicate viewed = obligation_view(
                                solver,
                                &obligation->predicate
                        );
                        T2Predicate const *predicate = &viewed;
                        if (!predicate_shares_exported_variable(
                                solver,
                                type,
                                predicate
                        )) {
                                continue;
                        }

                        if (
                                !collect_generalization_polarity(
                                        solver,
                                        predicate->subtype,
                                        T2_POLARITY_POSITIVE | T2_POLARITY_NEGATIVE,
                                        polarities,
                                        0
                                )
                             || !collect_generalization_polarity(
                                     solver,
                                     predicate->supertype,
                                     T2_POLARITY_POSITIVE | T2_POLARITY_NEGATIVE,
                                     polarities,
                                     0
                                )
                        ) {
                                goto Fail;
                        }

                        if (
                                (predicate->operand != T2_TYPE_INVALID)
                             && !collect_generalization_polarity(
                                     solver,
                                     predicate->operand,
                                     T2_POLARITY_POSITIVE | T2_POLARITY_NEGATIVE,
                                     polarities,
                                     0
                                )
                        ) {
                                goto Fail;
                        }
                }
        }

        if (!close_generalization_constraints(solver, polarities)) {
                goto Fail;
        }

        bool candidates = false;
        for (usize i = 0; i < count && !candidates; ++i) {
                candidates = generalizable_meta(
                        solver,
                        i,
                        polarities[i],
                        binding_level,
                        expansive
                );
        }

        if (candidates) {
                unsigned *environment_marks = ty_calloc(count, sizeof *environment_marks);
                if (count != 0 && environment_marks == NULL) {
                        goto Fail;
                }
                for (usize i = 0; i < environment_count; ++i) {
                        if (
                                !collect_generalization_polarity(
                                        solver,
                                        environment[i],
                                        T2_POLARITY_POSITIVE | T2_POLARITY_NEGATIVE,
                                        environment_marks,
                                        0
                                )
                        ) {
                                ty_free(environment_marks);
                                goto Fail;
                        }
                }

                if (!close_generalization_constraints(solver, environment_marks)) {
                        ty_free(environment_marks);
                        goto Fail;
                }
                for (usize i = 0; i < count; ++i) {
                        environment_free[i] = (environment_marks[i] == 0);
                }
                ty_free(environment_marks);
        }

        usize quantifier_count = 0;
        for (usize i = 0; i < count; ++i) {
                if (
                        environment_free[i]
                     && generalizable_meta(solver, i, polarities[i], binding_level, expansive)
                ) {
                        quantifier_count += 1;
                }
        }

        T2Quantifier *quantifiers = (quantifier_count == 0)
                                  ? NULL
                                  : ty_malloc(quantifier_count * sizeof *quantifiers);
        if (quantifier_count != 0 && quantifiers == NULL) {
                goto Fail;
        }

        usize qi = 0;
        for (usize i = 0; i < count; ++i) {
                if (
                        !environment_free[i]
                     || !generalizable_meta(
                             solver,
                             i,
                             polarities[i],
                             binding_level,
                             expansive
                        )
                ) {
                        continue;
                }

                T2Meta const *meta = v_(solver->metas, i);
                T2VariableKind variable_kind = meta->variable_kind;
                if (
                        (variable_kind != T2_VARIABLE_ROW)
                     && (variable_kind != T2_VARIABLE_PACK)
                ) {
                        variable_kind = T2_VARIABLE_QUANTIFIED;
                }

                quantifiers[qi] = (T2Quantifier) {
                        .id   = (u32)qi + 1,
                        .kind = variable_kind
                };
                replacements[i] = t2_variable(
                        solver->universe,
                        variable_kind,
                        (u32)qi + 1
                );
                qi += 1;
        }

        T2Generalization generalization = {
                .solver       = solver,
                .replacements = replacements
        };
        T2Type body = generalize_type(&generalization, type);
        if (body == T2_TYPE_INVALID) {
                ty_free(quantifiers);
                xvF(generalization.entries);
                xvF(generalization.binders);
                goto Fail;
        }

        usize predicate_capacity = quantifier_count * 2
                                 + vN(solver->edges)
                                 + vN(solver->obligations);
        T2Predicate *predicates = (predicate_capacity == 0)
                                ? NULL
                                : ty_calloc(predicate_capacity, sizeof *predicates);
        usize *captured_obligations = (vN(solver->obligations) == 0)
                                    ? NULL
                                    : ty_malloc(
                                            vN(solver->obligations)
                                          * sizeof *captured_obligations
                                      )
        ;
        if (predicate_capacity != 0 && predicates == NULL) {
                ty_free(quantifiers);
                xvF(generalization.entries);
                xvF(generalization.binders);
                ty_free(captured_obligations);
                goto Fail;
        }

        if (
                (vN(solver->obligations) != 0)
             && (captured_obligations == NULL)
        ) {
                ty_free(predicates);
                ty_free(quantifiers);
                xvF(generalization.entries);
                xvF(generalization.binders);
                goto Fail;
        }

        usize predicate_count = 0;
        usize captured_count  = 0;
        T2Type never = t2_primitive(solver->universe, T2_TYPE_NEVER);
        T2Type any   = t2_primitive(solver->universe, T2_TYPE_ANY);
        for (usize i = 0; i < count; ++i) {
                if (replacements[i] == T2_TYPE_INVALID) {
                        continue;
                }
                T2Meta const *meta = v_(solver->metas, i);
                if (meta->lower != never) {
                        predicates[predicate_count++] = (T2Predicate) {
                                .subtype    = generalize_type(
                                        &generalization,
                                        weak_lower_view(solver, meta->lower, NULL, 0)
                                ),
                                .supertype  = replacements[i],
                                .provenance = meta->provenance
                        };
                }

                if (meta->upper != any) {
                        predicates[predicate_count++] = (T2Predicate) {
                                .subtype    = replacements[i],
                                .supertype  = generalize_type(
                                        &generalization,
                                        weak_lower_view(solver, meta->upper, NULL, 0)
                                ),
                                .provenance = meta->provenance
                        };
                }
        }

        for (usize i = 0; i < vN(solver->edges); ++i) {
                u32 sub = find_root(solver, v__(solver->edges, i).subtype);
                u32 sup = find_root(solver, v__(solver->edges, i).supertype);
                if (
                        (replacements[sub - 1] == T2_TYPE_INVALID)
                     && (replacements[sup - 1] == T2_TYPE_INVALID)
                ) {
                        continue;
                }

                T2Predicate edge = {
                        .subtype    = meta_type(solver, sub),
                        .supertype  = meta_type(solver, sup),
                        .provenance = v__(solver->edges, i).provenance
                };
                T2Predicate viewed = obligation_view(solver, &edge);
                if (viewed.subtype == viewed.supertype) {
                        continue;
                }

                predicates[predicate_count++] = (T2Predicate) {
                        .subtype = generalize_type(
                                &generalization,
                                viewed.subtype
                        ),
                        .supertype = generalize_type(
                                &generalization,
                                viewed.supertype
                        ),
                        .provenance = viewed.provenance
                };
        }

        for (usize i = 0; i < vN(solver->obligations); ++i) {
                T2Obligation const *obligation = v_(solver->obligations, i);
                if (!obligation->active) {
                        continue;
                }
                T2Predicate viewed = obligation_view(
                        solver,
                        &obligation->predicate
                );
                T2Predicate const *predicate = &viewed;
                bool scoped = (i >= scoped_obligation_start);
                bool touches_replacement = (
                        type_touches_replacement(
                                solver,
                                predicate->subtype,
                                replacements,
                                0
                        )
                     || type_touches_replacement(
                                solver,
                                predicate->supertype,
                                replacements,
                                0
                        )
                     || (
                                (predicate->operand != T2_TYPE_INVALID)
                             && type_touches_replacement(
                                        solver,
                                        predicate->operand,
                                        replacements,
                                        0
                                )
                        )
                );
                bool shares = scoped
                           && predicate_shares_exported_variable(
                                   solver,
                                   type,
                                   predicate
                              )
                ;
                if (!touches_replacement && !shares) {
                        continue;
                }
                T2Type subtype = generalize_type(
                        &generalization,
                        predicate->subtype
                );
                T2Type supertype = generalize_type(
                        &generalization,
                        predicate->supertype
                );
                T2Type operand = (predicate->operand == T2_TYPE_INVALID)
                               ? T2_TYPE_INVALID
                               : generalize_type(
                                       &generalization,
                                       predicate->operand
                                 )
                ;
                if (
                        (subtype == T2_TYPE_INVALID)
                     || (supertype == T2_TYPE_INVALID)
                     || (
                                (predicate->operand != T2_TYPE_INVALID)
                             && (operand == T2_TYPE_INVALID)
                        )
                     || type_contains_solver_meta(solver, subtype, 0)
                     || type_contains_solver_meta(solver, supertype, 0)
                     || (
                                (operand != T2_TYPE_INVALID)
                             && type_contains_solver_meta(solver, operand, 0)
                        )
                ) {
                        continue;
                }

                predicates[predicate_count]         = *predicate;
                predicates[predicate_count].subtype = subtype;
                predicates[predicate_count].supertype = supertype;
                predicates[predicate_count].operand   = operand;
                predicate_count += 1;
                captured_obligations[captured_count++] = i;
        }

        bool valid = (body != T2_TYPE_INVALID);
        for (usize i = 0; i < predicate_count; ++i) {
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
                for (usize i = 0; i < captured_count; ++i) {
                        usize index = captured_obligations[i];
                        T2Obligation *obligation = v_(solver->obligations, index);
                        if (!obligation->active) {
                                continue;
                        }
                        if (
                                !push_undo(
                                        solver,
                                        (T2Undo) {
                                                .kind  = T2_UNDO_OBLIGATION_ACTIVE,
                                                .index = (u32)index,
                                                .old   = obligation->active
                                        }
                                )
                        ) {
                                t2_scheme_free(scheme);
                                scheme = NULL;
                                break;
                        }
                        obligation->active = false;
                }
        }

        ty_free(captured_obligations);
        ty_free(predicates);
        ty_free(quantifiers);
        xvF(generalization.entries);
        xvF(generalization.binders);
        ty_free(polarities);
        ty_free(environment_free);
        ty_free(replacements);
        return scheme;

Fail:
        ty_free(polarities);
        ty_free(environment_free);
        ty_free(replacements);

        return NULL;
}

T2Scheme *
t2_solver_generalize(
        T2Solver     *solver,
        T2Type        type,
        T2Type const *environment,
        usize         environment_count,
        u32           binding_level,
        bool          expansive
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
        T2Solver     *solver,
        T2Type        type,
        T2Type const *environment,
        usize         environment_count,
        u32           binding_level,
        bool          expansive,
        T2SolverMark  scope
)
{
        if (
                (solver == NULL)
             || (scope.obligation_count > vN(solver->obligations))
             || (solver->transaction_depth != scope.transaction_depth + 1)
        ) {
                return NULL;
        }

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

static usize
find_quantifier(T2Scheme const *scheme, T2Node const *variable)
{
        for (usize i = 0; i < scheme->quantifier_count; ++i) {
                T2Quantifier const *quantifier = &scheme->quantifiers[i];
                if (quantifier->id != variable->payload) {
                        continue;
                }
                if (
                        (quantifier->kind == T2_VARIABLE_ROW)
                     || (quantifier->kind == T2_VARIABLE_PACK)
                ) {
                        if (quantifier->kind == variable->variable_kind) {
                                return i;
                        }
                } else if (
                        (variable->variable_kind == T2_VARIABLE_QUANTIFIED)
                     || (variable->variable_kind == T2_VARIABLE_FLEXIBLE)
                ) {
                        return i;
                }
        }

        return SIZE_MAX;
}

static T2Type
instantiate_type(T2Instantiation *instantiation, T2Type source);

static T2Type
instantiate_recursive(T2Instantiation *instantiation, T2Node const *node)
{
        T2Universe *universe = instantiation->solver->universe;
        u32 binder = t2_universe_fresh_recursive_binder(universe);
        if (binder == 0) {
                return T2_TYPE_INVALID;
        }

        usize mark = vN(instantiation->binders);
        xvP(instantiation->binders, ((T2BinderSubstitution) {
                .source = (u32)node->payload,
                .result = binder
        }));

        T2Type body = instantiate_type(instantiation, node->children[0]);
        vN(instantiation->binders) = mark;
        if (body == T2_TYPE_INVALID) {
                return body;
        }

        return t2_recursive(universe, binder, body);
}

static T2Type
instantiate_type(T2Instantiation *instantiation, T2Type source)
{
        T2Universe *universe = instantiation->solver->universe;
        T2Node const *node   = get_node(universe, source);
        if (node == NULL) {
                return T2_TYPE_INVALID;
        }

        if ((node->flags & (T2_NODE_VARIABLE | T2_NODE_RECURSIVE_VARIABLE)) == 0) {
                return source;
        }

        if (node->kind == T2_TYPE_VARIABLE) {
                usize quantifier = find_quantifier(instantiation->scheme, node);
                if (quantifier != SIZE_MAX) {
                        return instantiation->replacements[quantifier];
                }
        }

        if (node->kind == T2_TYPE_RECURSIVE_VARIABLE) {
                for (usize i = vN(instantiation->binders); i != 0; --i) {
                        T2BinderSubstitution const *binder = v_(instantiation->binders, i - 1);
                        if (binder->source == node->payload) {
                                return t2_recursive_variable(universe, binder->result);
                        }
                }

                return source;
        }

        if (node->kind == T2_TYPE_RECURSIVE) {
                return instantiate_recursive(instantiation, node);
        }

        for (usize i = 0; i < vN(instantiation->nodes); ++i) {
                if (v__(instantiation->nodes, i).source == source) {
                        return v__(instantiation->nodes, i).result;
                }
        }

        if (node->arity == 0) {
                return source;
        }

        T2Type *children = ty_malloc(node->arity * sizeof *children);
        if (children == NULL) {
                return T2_TYPE_INVALID;
        }

        bool changed = false;
        for (usize i = 0; i < node->arity; ++i) {
                children[i] = instantiate_type(instantiation, node->children[i]);
                if (children[i] == T2_TYPE_INVALID) {
                        ty_free(children);
                        return T2_TYPE_INVALID;
                }
                changed |= children[i] != node->children[i];
        }

        T2Type result = changed
                      ? rebuild_type(universe, node, children)
                      : source;
        ty_free(children);
        if (result == T2_TYPE_INVALID) {
                return result;
        }

        xvP(instantiation->nodes, ((T2InstantiatedNode) {
                .source = source,
                .result = result
        }));

        return result;
}

T2Type
t2_scheme_instantiate(
        T2Scheme const *scheme,
        T2Solver       *solver,
        u32             level,
        char const     *provenance
)
{
        if (
                (scheme == NULL)
             || (solver == NULL)
             || solver->failed
             || (solver->universe != scheme->universe)
        ) {
                return T2_TYPE_INVALID;
        }

        T2SolverMark mark = t2_solver_mark(solver);
        T2Instantiation instantiation = {
                .scheme = scheme,
                .solver = solver
        };
        if (scheme->quantifier_count != 0) {
                instantiation.replacements = ty_malloc(
                        scheme->quantifier_count * sizeof *instantiation.replacements
                );
                if (instantiation.replacements == NULL) {
                        goto Fail;
                }
        }

        for (usize i = 0; i < scheme->quantifier_count; ++i) {
                T2VariableKind kind = scheme->quantifiers[i].kind;
                if (
                        (kind != T2_VARIABLE_ROW)
                     && (kind != T2_VARIABLE_PACK)
                     && (kind != T2_VARIABLE_WEAK)
                ) {
                        kind = T2_VARIABLE_FLEXIBLE;
                }

                instantiation.replacements[i] = t2_solver_new_meta(
                        solver,
                        kind,
                        level,
                        provenance
                );
                if (instantiation.replacements[i] == T2_TYPE_INVALID) {
                        goto Fail;
                }
        }

        T2Type body = instantiate_type(&instantiation, scheme->body);
        if (body == T2_TYPE_INVALID) {
                goto Fail;
        }

        for (usize i = 0; i < scheme->predicate_count; ++i) {
                T2Type subtype = instantiate_type(
                        &instantiation,
                        scheme->predicates[i].subtype
                );
                T2Type supertype = instantiate_type(
                        &instantiation,
                        scheme->predicates[i].supertype
                );
                T2Type operand = (scheme->predicates[i].kind == T2_PREDICATE_SUBTYPE)
                               ? T2_TYPE_INVALID
                               : instantiate_type(
                                       &instantiation,
                                       scheme->predicates[i].operand
                                 )
                ;
                T2Predicate predicate = scheme->predicates[i];
                predicate.subtype   = subtype;
                predicate.supertype = supertype;
                predicate.operand   = operand;
                if (provenance != NULL) {
                        predicate.provenance = provenance;
                }
                if (
                        (subtype == T2_TYPE_INVALID)
                     || (supertype == T2_TYPE_INVALID)
                     || (
                                (predicate.kind != T2_PREDICATE_SUBTYPE)
                             && (operand == T2_TYPE_INVALID)
                        )
                     || (t2_solver_constrain_predicate(
                             solver,
                             &predicate
                        ) == T2_RELATION_NO)
                ) {
                        goto Fail;
                }
        }

        ty_free(instantiation.replacements);
        xvF(instantiation.nodes);
        xvF(instantiation.binders);
        t2_solver_commit(solver, mark);
        return body;

Fail:
        ty_free(instantiation.replacements);
        xvF(instantiation.nodes);
        xvF(instantiation.binders);
        t2_solver_rollback(solver, mark);

        return T2_TYPE_INVALID;
}

static T2Type
scheme_apply_x(
        T2Scheme const *scheme,
        T2Solver       *solver,
        T2Type const   *arguments,
        usize           argument_count,
        char const     *provenance,
        bool            relaxed
)
{
        if (
                (scheme == NULL)
             || (solver == NULL)
             || solver->failed
             || (solver->universe != scheme->universe)
             || (argument_count != scheme->quantifier_count)
             || ((argument_count != 0) && (arguments == NULL))
        ) {
                return T2_TYPE_INVALID;
        }

        for (usize i = 0; i < argument_count; ++i) {
                if (get_node(solver->universe, arguments[i]) == NULL) {
                        return T2_TYPE_INVALID;
                }
                T2VariableKind kind = scheme->quantifiers[i].kind;
                if (
                        ((kind == T2_VARIABLE_ROW) || (kind == T2_VARIABLE_PACK))
                     && (term_sort(solver->universe, arguments[i]) != kind)
                ) {
                        return T2_TYPE_INVALID;
                }
        }

        T2SolverMark mark = t2_solver_mark(solver);
        T2Instantiation instantiation = {
                .scheme = scheme,
                .solver = solver
        };
        if (argument_count != 0) {
                instantiation.replacements = ty_malloc(
                        argument_count * sizeof *instantiation.replacements
                );
                if (instantiation.replacements == NULL) {
                        goto Fail;
                }
                memcpy(
                        instantiation.replacements,
                        arguments,
                        argument_count * sizeof *instantiation.replacements
                );
        }

        T2Type body = instantiate_type(&instantiation, scheme->body);
        if (body == T2_TYPE_INVALID) {
                goto Fail;
        }

        for (usize i = 0; i < scheme->predicate_count; ++i) {
                T2Type subtype = instantiate_type(
                        &instantiation,
                        scheme->predicates[i].subtype
                );
                T2Type supertype = instantiate_type(
                        &instantiation,
                        scheme->predicates[i].supertype
                );
                T2Type operand = (scheme->predicates[i].kind == T2_PREDICATE_SUBTYPE)
                               ? T2_TYPE_INVALID
                               : instantiate_type(
                                       &instantiation,
                                       scheme->predicates[i].operand
                                 )
                ;
                T2Predicate predicate = scheme->predicates[i];
                predicate.subtype   = subtype;
                predicate.supertype = supertype;
                predicate.operand   = operand;
                if (provenance != NULL) {
                        predicate.provenance = provenance;
                }
                if (
                        (subtype == T2_TYPE_INVALID)
                     || (supertype == T2_TYPE_INVALID)
                     || (
                                (predicate.kind != T2_PREDICATE_SUBTYPE)
                             && (operand == T2_TYPE_INVALID)
                        )
                ) {
                        goto Fail;
                }

                T2SolverMark step = t2_solver_mark(solver);
                if (t2_solver_constrain_predicate(solver, &predicate) != T2_RELATION_NO) {
                        t2_solver_commit(solver, step);
                        continue;
                }
                if (!relaxed) {
                        goto Fail;
                }
                t2_solver_rollback(solver, step);
        }

        ty_free(instantiation.replacements);
        xvF(instantiation.nodes);
        xvF(instantiation.binders);
        t2_solver_commit(solver, mark);
        return body;

Fail:
        ty_free(instantiation.replacements);
        xvF(instantiation.nodes);
        xvF(instantiation.binders);
        t2_solver_rollback(solver, mark);

        return T2_TYPE_INVALID;
}

T2Type
t2_scheme_apply(
        T2Scheme const *scheme,
        T2Solver       *solver,
        T2Type const   *arguments,
        usize           argument_count,
        char const     *provenance
)
{
        return scheme_apply_x(
                scheme,
                solver,
                arguments,
                argument_count,
                provenance,
                false
        );
}

T2Type
t2_scheme_apply_relaxed(
        T2Scheme const *scheme,
        T2Solver       *solver,
        T2Type const   *arguments,
        usize           argument_count,
        char const     *provenance
)
{
        return scheme_apply_x(
                scheme,
                solver,
                arguments,
                argument_count,
                provenance,
                true
        );
}

typedef struct t2_zonk_entry {
        T2Type source;
        T2Type result;
} T2ZonkEntry;

typedef struct t2_zonk_context {
        T2Solver                 *solver;
        T2SolutionPreference      preference;
        vec(T2ZonkEntry)          entries;
        vec(u32)                  active_metas;
        vec(T2BinderSubstitution) binders;
        bool failed;
} T2ZonkContext;

static T2Type
zonk_type(T2ZonkContext *context, T2Type source);

static T2Type
zonk_recursive(T2ZonkContext *context, T2Node const *node)
{
        T2Universe *universe = context->solver->universe;
        u32 binder = t2_universe_fresh_recursive_binder(universe);
        if (binder == 0) {
                return T2_TYPE_INVALID;
        }

        usize mark = vN(context->binders);
        xvP(context->binders, ((T2BinderSubstitution) {
                .source = (u32)node->payload,
                .result = binder
        }));
        T2Type body = zonk_type(context, node->children[0]);
        vN(context->binders) = mark;

        return (body == T2_TYPE_INVALID)
             ? body
             : t2_recursive(universe, binder, body);
}

static T2Type
zonk_type(T2ZonkContext *context, T2Type source)
{
        T2Solver *solver = context->solver;
        u32 meta = meta_from_type(solver, source);
        if (meta != 0) {
                meta = find_root(solver, meta);
                T2Type root_type = meta_type(solver, meta);
                for (usize i = 0; i < vN(context->active_metas); ++i) {
                        if (v__(context->active_metas, i) == meta) {
                                return root_type;
                        }
                }

                T2Type solution = t2_solver_solution(
                        solver,
                        root_type,
                        context->preference
                );
                if (solution == root_type) {
                        return root_type;
                }
                xvP(context->active_metas, meta);
                T2Type result = zonk_type(context, solution);
                vN(context->active_metas) -= 1;
                return result;
        }

        T2Node const *node = get_node(solver->universe, source);
        if (node == NULL) {
                return T2_TYPE_INVALID;
        }

        if ((node->flags & (T2_NODE_META | T2_NODE_RECURSIVE_VARIABLE)) == 0) {
                return source;
        }

        if (node->kind == T2_TYPE_RECURSIVE_VARIABLE) {
                for (usize i = vN(context->binders); i != 0; --i) {
                        T2BinderSubstitution const *binder = v_(context->binders, i - 1);
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
                return zonk_recursive(context, node);
        }

        for (usize i = 0; i < vN(context->entries); ++i) {
                if (v__(context->entries, i).source == source) {
                        return v__(context->entries, i).result;
                }
        }

        if (node->arity == 0) {
                return source;
        }

        T2Type *children = ty_malloc(node->arity * sizeof *children);
        if (children == NULL) {
                return T2_TYPE_INVALID;
        }

        bool changed = false;
        for (usize i = 0; i < node->arity; ++i) {
                children[i] = zonk_type(context, node->children[i]);
                if (children[i] == T2_TYPE_INVALID) {
                        ty_free(children);
                        return T2_TYPE_INVALID;
                }
                changed |= children[i] != node->children[i];
        }

        T2Type result = changed
                      ? rebuild_type(solver->universe, node, children)
                      : source;
        ty_free(children);
        if (result == T2_TYPE_INVALID) {
                return result;
        }

        xvP(context->entries, ((T2ZonkEntry) {
                .source = source,
                .result = result
        }));

        return result;
}

T2Type
t2_solver_resolve_packs(T2Solver *solver, T2Type type)
{
        if (solver == NULL || type == T2_TYPE_INVALID) {
                return type;
        }

        return type_contains_solved_pack_meta(solver, type, 0)
             ? resolve_pack_solutions(solver, type, 0)
             : type;
}

T2Type
t2_solver_zonk(
        T2Solver            *solver,
        T2Type               type,
        T2SolutionPreference preference
)
{
        if (solver == NULL || solver->failed) {
                return T2_TYPE_INVALID;
        }

        T2ZonkContext context = {
                .solver     = solver,
                .preference = preference
        };
        T2Type result = zonk_type(&context, type);
        xvF(context.entries);
        xvF(context.active_metas);
        xvF(context.binders);

        return result;
}

static T2Type
zonk_for_display(T2Solver *solver, T2Type type)
{
        if (solver == NULL || type == T2_TYPE_INVALID) {
                return type;
        }

        T2ZonkContext context = {
                .solver     = solver,
                .preference = T2_PREFER_LOWER_BOUND
        };
        T2Type result = zonk_type(&context, type);
        xvF(context.entries);
        xvF(context.active_metas);
        xvF(context.binders);

        return (result == T2_TYPE_INVALID) ? type : result;
}

usize
t2_solver_cause_count(T2Solver const *solver)
{
        return (solver == NULL) ? 0 : vN(solver->causes);
}

bool
t2_solver_cause(T2Solver *solver, usize index, T2CauseInfo *info)
{
        if (
                (solver == NULL)
             || (info == NULL)
             || (index >= vN(solver->causes))
        ) {
                return false;
        }

        T2Cause const *cause = v_(solver->causes, index);
        *info = (T2CauseInfo) {
                .kind       = cause->kind,
                .left       = zonk_for_display(solver, cause->left),
                .right      = zonk_for_display(solver, cause->right),
                .provenance = cause->provenance
        };

        return true;
}

bool
t2_solver_failure(T2Solver *solver, T2CauseInfo *info)
{
        if (solver == NULL || info == NULL || !solver->failed) {
                return false;
        }

        *info = (T2CauseInfo) {
                .kind  = T2_CAUSE_FAILURE,
                .left  = zonk_for_display(solver, solver->failure_left),
                .right = zonk_for_display(solver, solver->failure_right),
                .message = (solver->failure_message != NULL)
                         ? solver->failure_message
                         : solver->error,
                .provenance = solver->failure_provenance
        };

        return true;
}

bool
t2_definitely_disjoint(T2Universe const *universe, T2Type left, T2Type right)
{
        return definitely_disjoint(universe, left, right);
}

bool
t2_solver_meta_solved(T2Solver *solver, T2Type meta)
{
        if (solver == NULL) {
                return false;
        }

        u32 id = meta_from_type(solver, meta);
        if (id == 0) {
                return false;
        }

        id = find_root(solver, id);

        return v__(solver->metas, id - 1).solution != T2_TYPE_INVALID;
}

void
t2_solver_retire_metas_since(T2Solver *solver, T2SolverMark mark)
{
        if (solver == NULL) {
                return;
        }

        for (usize id = mark.meta_count + 1; id <= vN(solver->metas); ++id) {
                v__(solver->metas, id - 1).retired = true;
        }
}

/* vim: set sts=8 sw=8 expandtab: */
