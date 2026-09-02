#include <ctype.h>
#include <errno.h>
#include <inttypes.h>
#include <limits.h>
#include <stdint.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#include "ast.h"
#include "class.h"
#include "compiler.h"
#include "types.h"
#include "types2.h"
#include "types2_core.h"
#include "value.h"

enum {
        TYPES2_ROLE_EXPRESSION = 1 << 0,
        TYPES2_ROLE_TYPE       = 1 << 1,
        TYPES2_ROLE_PATTERN    = 1 << 2,
        TYPES2_ROLE_LVALUE     = 1 << 3,
        TYPES2_ROLE_STATEMENT  = 1 << 4
};

typedef struct types2_node {
        void const *syntax;
        uint64_t id;
        uint32_t roles;
        uint8_t construct;
        T2Type type;
        bool inferred;
} Types2Node;

typedef struct types2_binding {
        Symbol const *symbol;
        T2Type type;
        T2Type refinement;
        T2Scheme *scheme;
        bool mutable;
        bool initialized;
        bool active;
        bool forward;
        bool imported;
        bool persistent;
        bool member;
        Symbol const *alias;
} Types2Binding;

typedef enum types2_alias_state {
        TYPES2_ALIAS_UNRESOLVED,
        TYPES2_ALIAS_RESOLVING,
        TYPES2_ALIAS_RESOLVED,
        TYPES2_ALIAS_FAILED
} Types2AliasState;

typedef struct types2_alias {
        Symbol const *symbol;
        ClassDefinition const *definition;
        T2Scheme *scheme;
        T2Type monotype;
        uint32_t binder;
        size_t arity;
        Types2AliasState state;
} Types2Alias;

typedef struct types2_nominal {
        int class_id;
        int tag_id;
        uint64_t symbol;
        char const *name;
        size_t arity;
        bool declared;
        bool complete;
        bool populating;
} Types2Nominal;

typedef enum types2_member_kind {
        TYPES2_MEMBER_FIELD,
        TYPES2_MEMBER_METHOD,
        TYPES2_MEMBER_GETTER,
        TYPES2_MEMBER_SETTER
} Types2MemberKind;

typedef struct types2_member {
        int class_id;
        char const *name;
        Types2MemberKind kind;
        T2Scheme *scheme;
        Expr const *declaration;
        size_t class_arity;
        bool is_static;
        bool required;
        bool writable;
} Types2Member;

typedef struct types2_class_contract {
        Stmt const *statement;
        int class_id;
        T2Type receiver;
} Types2ClassContract;

typedef struct types2_operator {
        char const *name;
        Expr const *declaration;
        T2Scheme *scheme;
} Types2Operator;

typedef struct types2_type_variable {
        Symbol const *symbol;
        T2Type type;
} Types2TypeVariable;

typedef struct types2_upper_assumption {
        T2Type subtype;
        T2Type supertype;
} Types2UpperAssumption;

typedef enum types2_diagnostic_severity {
        TYPES2_DIAGNOSTIC_ERROR,
        TYPES2_DIAGNOSTIC_WARNING,
        TYPES2_DIAGNOSTIC_NOTE
} Types2DiagnosticSeverity;

typedef struct types2_diagnostic {
        uint64_t node;
        Location location;
        Types2DiagnosticSeverity severity;
        char *code;
        char *message;
        char *actual;
        char *expected;
        uint64_t actual_hash;
        uint64_t expected_hash;
} Types2Diagnostic;

typedef enum types2_flow_bit {
        TYPES2_FLOW_FALLS_THROUGH = 1 << 0,
        TYPES2_FLOW_RETURNS       = 1 << 1,
        TYPES2_FLOW_THROWS        = 1 << 2,
        TYPES2_FLOW_BREAKS        = 1 << 3,
        TYPES2_FLOW_CONTINUES     = 1 << 4
} Types2FlowBit;

typedef struct types2_flow {
        unsigned outcomes;
        T2Type value;
        T2Type returns;
} Types2Flow;

typedef struct types2_function_frame {
        Expr const *function;
        T2Type result;
        T2Type yields;
        T2Type sends;
        uint32_t level;
        bool generator;
        bool effectful;
        bool inferred_result;
} Types2FunctionFrame;

typedef struct types2_call_effect {
        T2Type yields;
        T2Type sends;
        bool active;
} Types2CallEffect;

#define TYPES2_DEFER_REASONS                                                  \
        X(DYNAMIC_CALLEE,         "dynamic-callee",         RUNTIME)           \
        X(CALLABLE_TOP,           "callable-top",           RUNTIME)           \
        X(DYNAMIC_OPERAND,        "dynamic-operand",        RUNTIME)           \
        X(DYNAMIC_SPREAD,         "dynamic-spread",         RUNTIME)           \
        X(DYNAMIC_KEYWORD_SPREAD, "dynamic-keyword-spread", RUNTIME)           \
        X(DYNAMIC_MEMBER_NAME,    "dynamic-member-name",    RUNTIME)           \
        X(DYNAMIC_METHOD_NAME,    "dynamic-method-name",    RUNTIME)           \
        X(RUNTIME_CONTEXT,        "runtime-context",        RUNTIME)           \
        X(RUNTIME_VALUE,          "runtime-value",          RUNTIME)           \
        X(UNSAFE_EVAL,            "unsafe-eval",            RUNTIME)           \
        X(SPREAD_ARITY,           "spread-arity",           INCOMPLETE)        \
        X(KEYWORD_ROW,            "keyword-row",            INCOMPLETE)        \
        X(TUPLE_SPREAD,           "tuple-spread",           INCOMPLETE)        \
        X(TEMPLATE,               "template",               INCOMPLETE)        \
        X(TEMPLATE_HOLE,          "template-hole",          INCOMPLETE)        \
        X(PACK_FOLD,              "pack-fold",              INCOMPLETE)        \
        X(OPERATOR_VALUE,         "operator-value",         INCOMPLETE)        \
        X(OPERATOR_PROTOCOL,      "operator-protocol",      INCOMPLETE)        \
        X(OPERATOR_OPEN_OPERAND,  "operator-open-operand",  INCOMPLETE)        \
        X(INCOMPLETE_INTERFACE,   "incomplete-interface",   INCOMPLETE)        \
        X(COMPUTED_TYPE,          "computed-type",          INCOMPLETE)        \
        X(COMPILE_TIME,           "compile-time",           INCOMPLETE)        \
        X(TYPEOF_UNRESOLVED,      "typeof-unresolved",      INCOMPLETE)        \
        X(IFDEF,                  "ifdef",                  INCOMPLETE)        \
        X(MACRO_DEFINITION,       "macro-definition",       INCOMPLETE)        \
        X(SET_TYPE,               "set-type",               INCOMPLETE)        \
        X(UNSUPPORTED_BOUND,      "unsupported-bound",      INCOMPLETE)        \
        X(UNSUPPORTED_HIERARCHY,  "unsupported-hierarchy",  INCOMPLETE)        \
        X(UNSUPPORTED_PATTERN,    "unsupported-pattern",    INCOMPLETE)        \
        X(UNRESOLVED_BINDING,     "unresolved-binding",     EXTERNAL)          \
        X(UNRESOLVED_NOMINAL,     "unresolved-nominal",     EXTERNAL)          \
        X(UNRESOLVED_TAG,         "unresolved-tag",         EXTERNAL)          \
        X(UNRESOLVED_MATCHER,     "unresolved-matcher",     EXTERNAL)          \
        X(HIERARCHY_REJECTED,     "hierarchy-rejected",     RECOVERY)

typedef enum types2_defer_class {
        TYPES2_DEFER_CLASS_RUNTIME,
        TYPES2_DEFER_CLASS_INCOMPLETE,
        TYPES2_DEFER_CLASS_EXTERNAL,
        TYPES2_DEFER_CLASS_RECOVERY,
        TYPES2_DEFER_CLASS_COUNT
} Types2DeferClass;

typedef enum types2_defer_reason {
#define X(id, name, class) TYPES2_DEFER_##id,
        TYPES2_DEFER_REASONS
#undef X
        TYPES2_DEFER_REASON_COUNT
} Types2DeferReason;

static char const *const defer_reason_names[TYPES2_DEFER_REASON_COUNT] = {
#define X(id, name, class) [TYPES2_DEFER_##id] = name,
        TYPES2_DEFER_REASONS
#undef X
};

static Types2DeferClass const defer_reason_classes[TYPES2_DEFER_REASON_COUNT] = {
#define X(id, name, class) [TYPES2_DEFER_##id] = TYPES2_DEFER_CLASS_##class,
        TYPES2_DEFER_REASONS
#undef X
};

static char const *const defer_class_names[TYPES2_DEFER_CLASS_COUNT] = {
        [TYPES2_DEFER_CLASS_RUNTIME]    = "runtime",
        [TYPES2_DEFER_CLASS_INCOMPLETE] = "incomplete",
        [TYPES2_DEFER_CLASS_EXTERNAL]   = "external",
        [TYPES2_DEFER_CLASS_RECOVERY]   = "recovery"
};

struct types2_shadow {
        char const *unit;
        char const *path;
        char const *source;

        T2Universe *universe;
        T2Solver *solver;
        Ty *ty;

        FILE *log;
        bool close_log;
        bool trace_nodes;
        bool trace_deferred;
        bool importing;
        bool failed;
        bool reported_failure;
        bool building_interface;
        int member_class_id;
        T2Type member_receiver;

        Types2Node *nodes;
        size_t node_count;
        size_t node_capacity;
        uint64_t next_node_id;

        uint64_t checkpoints[TYPES2_SHADOW_CHECKPOINT_COUNT];
        uint64_t constructs[UINT8_MAX + 1];
        uint64_t unsupported_constructs[UINT8_MAX + 1];
        uint64_t role_visits[5];

        Types2Binding *bindings;
        size_t binding_count;
        size_t binding_capacity;

        char const **imported_operators;
        size_t imported_operator_count;
        size_t imported_operator_capacity;

        Types2Alias *aliases;
        size_t alias_count;
        size_t alias_capacity;

        Types2Nominal *nominals;
        size_t nominal_count;
        size_t nominal_capacity;
        uint64_t next_nominal_symbol;

        Types2Member *members;
        size_t member_count;
        size_t member_capacity;

        Types2ClassContract *class_contracts;
        size_t class_contract_count;
        size_t class_contract_capacity;
        bool class_contracts_validated;

        Types2Operator *operators;
        size_t operator_count;
        size_t operator_capacity;

        Types2TypeVariable *type_variables;
        size_t type_variable_count;
        size_t type_variable_capacity;

        Types2UpperAssumption *upper_assumptions;
        size_t upper_assumption_count;
        size_t upper_assumption_capacity;

        Types2Diagnostic *diagnostics;
        size_t diagnostic_count;
        size_t diagnostic_capacity;

        char **provenances;
        size_t provenance_count;
        size_t provenance_capacity;

        Types2FunctionFrame *functions;
        size_t function_count;
        size_t function_capacity;
        Types2CallEffect *call_effect_sink;
        uint32_t refutable_pattern_depth;

        uint32_t level;
        uint32_t next_quantified_id;
        uint64_t inferred_nodes;
        uint64_t unsupported_nodes;
        uint64_t deferred_nodes;
        uint64_t deferred_reasons[TYPES2_DEFER_REASON_COUNT];
        uint64_t candidate_trials;
        uint64_t union_call_splits;
        uint64_t union_call_arms;
        uint64_t computed_type_terms;
        uint64_t materialized_computed_types;
};

typedef struct types2_walk {
        Types2Shadow *shadow;
} Types2Walk;

#define X(name) [EXPRESSION_##name] = #name
static char const *const construct_names[UINT8_MAX + 1] = {
        TY_EXPRESSION_TYPES,
#undef X
#define X(name) [STATEMENT_##name] = #name
        TY_STATEMENT_TYPES
};
#undef X

static char const *
construct_name(uint8_t construct)
{
        char const *name = construct_names[construct];
        return name == NULL ? "UNKNOWN" : name;
}

static Expr const *
declared_parameter_annotation(Expr const *function, size_t index)
{
        if (
                index < (size_t)vN(function->constraints)
             && v__(function->constraints, (int)index) != NULL
        ) return v__(function->constraints, (int)index);
        if (index < (size_t)vN(function->retained_constraints)) {
                return v__(function->retained_constraints, (int)index);
        }
        return NULL;
}

static bool
ascii_case_equal(char const *left, char const *right)
{
        while (*left != '\0' && *right != '\0') {
                if (
                        tolower((unsigned char)*left)
                     != tolower((unsigned char)*right)
                ) {
                        return false;
                }
                ++left;
                ++right;
        }
        return *left == *right;
}

static bool
shadow_disabled(void)
{
        char const *value = getenv("TY_TYPES2_SHADOW");

        return value != NULL
            && (
                       strcmp(value, "0") == 0
                    || ascii_case_equal(value, "off")
                    || ascii_case_equal(value, "false")
            );
}

static bool
shadow_option_enabled(char const *name)
{
        char const *value = getenv(name);
        return value != NULL
            && *value != '\0'
            && strcmp(value, "0") != 0
            && !ascii_case_equal(value, "off")
            && !ascii_case_equal(value, "false");
}

static FILE *
open_shadow_log(bool *close_log)
{
        char const *target = getenv("TY_TYPES2_LOG");

        *close_log = false;

        if (target == NULL || *target == '\0') {
                return NULL;
        }

        if (strcmp(target, "1") == 0 || strcmp(target, "-") == 0) {
                return stderr;
        }

        if (ascii_case_equal(target, "stderr")) {
                return stderr;
        }

        FILE *log = fopen(target, "a");
        if (log != NULL) {
                *close_log = true;
        }

        return log;
}

static void
json_string(FILE *out, char const *s)
{
        fputc('"', out);

        if (s != NULL) {
                for (unsigned char const *p = (unsigned char const *)s; *p != '\0'; ++p) {
                        switch (*p) {
                        case '"':
                                fputs("\\\"", out);
                                break;
                        case '\\':
                                fputs("\\\\", out);
                                break;
                        case '\b':
                                fputs("\\b", out);
                                break;
                        case '\f':
                                fputs("\\f", out);
                                break;
                        case '\n':
                                fputs("\\n", out);
                                break;
                        case '\r':
                                fputs("\\r", out);
                                break;
                        case '\t':
                                fputs("\\t", out);
                                break;
                        default:
                                if (*p < 0x20) {
                                        fprintf(out, "\\u%04x", *p);
                                } else {
                                        fputc(*p, out);
                                }
                        }
                }
        }

        fputc('"', out);
}

static void
log_prefix(Types2Shadow *shadow, char const *event)
{
        fputs("{\"schema\":\"ty.types2.shadow.v1\",\"event\":", shadow->log);
        json_string(shadow->log, event);
        fputs(",\"unit\":", shadow->log);
        json_string(shadow->log, shadow->unit);
        fputs(",\"path\":", shadow->log);
        json_string(shadow->log, shadow->path);
}

static void
log_end(Types2Shadow *shadow)
{
        fputs("}\n", shadow->log);
        fflush(shadow->log);
}

static void
log_type_hash(Types2Shadow *shadow, char const *snapshot, uint64_t hash)
{
        if (snapshot == NULL) {
                fputs("null", shadow->log);
        } else {
                fprintf(shadow->log, "\"%016" PRIx64 "\"", hash);
        }
}

static char const *
checkpoint_name(Types2ShadowCheckpoint checkpoint)
{
        switch (checkpoint) {
        case TYPES2_SHADOW_DECLARATION:
                return "declaration";
        case TYPES2_SHADOW_CLASS_OPERATOR_DECLARATION:
                return "class_operator_declaration";
        case TYPES2_SHADOW_STATEMENT:
                return "statement";
        case TYPES2_SHADOW_CLASS_OPERATOR:
                return "class_operator";
        case TYPES2_SHADOW_CHECKPOINT_COUNT:
                break;
        }

        return "invalid";
}

static char const *
predicate_kind_name(T2PredicateKind kind)
{
        switch (kind) {
        case T2_PREDICATE_SUBTYPE:
                return "subtype";
        case T2_PREDICATE_OPERATOR:
                return "operator";
        case T2_PREDICATE_SUBSCRIPT_READ:
                return "subscript_read";
        case T2_PREDICATE_SUBSCRIPT_WRITE:
                return "subscript_write";
        case T2_PREDICATE_MEMBER_READ:
                return "member_read";
        case T2_PREDICATE_MEMBER_WRITE:
                return "member_write";
        case T2_PREDICATE_KEYWORD_SPREAD:
                return "keyword_spread";
        }

        return "invalid";
}

static char const *
runtime_kind_name(T2RuntimeKind kind)
{
        switch (kind) {
        case T2_RUNTIME_UNKNOWN: return "unknown";
        case T2_RUNTIME_NEVER: return "never";
        case T2_RUNTIME_NIL: return "nil";
        case T2_RUNTIME_BOOL: return "bool";
        case T2_RUNTIME_INT: return "int";
        case T2_RUNTIME_FLOAT: return "float";
        case T2_RUNTIME_STRING: return "string";
        case T2_RUNTIME_FUNCTION: return "function";
        case T2_RUNTIME_TUPLE: return "tuple";
        case T2_RUNTIME_RECORD: return "record";
        case T2_RUNTIME_NOMINAL: return "nominal";
        case T2_RUNTIME_TYPE_VALUE: return "type_value";
        }
        return "unknown";
}

static size_t
pointer_hash(void const *p)
{
        uintptr_t x = (uintptr_t)p;

#if UINTPTR_MAX > UINT32_MAX
        x ^= x >> 30;
        x *= UINT64_C(0xbf58476d1ce4e5b9);
        x ^= x >> 27;
        x *= UINT64_C(0x94d049bb133111eb);
        x ^= x >> 31;
#else
        x ^= x >> 16;
        x *= UINT32_C(0x7feb352d);
        x ^= x >> 15;
        x *= UINT32_C(0x846ca68b);
        x ^= x >> 16;
#endif

        return (size_t)x;
}

static bool
shadow_reserve(
        Types2Shadow *shadow,
        void **items,
        size_t *capacity,
        size_t needed,
        size_t item_size
)
{
        if (*capacity >= needed) return true;
        size_t next = *capacity == 0 ? 8 : *capacity;
        while (next < needed) {
                if (next > SIZE_MAX / 2) {
                        shadow->failed = true;
                        return false;
                }
                next *= 2;
        }
        if (item_size != 0 && next > SIZE_MAX / item_size) {
                shadow->failed = true;
                return false;
        }
        void *resized = realloc(*items, next * item_size);
        if (resized == NULL) {
                shadow->failed = true;
                return false;
        }
        *items = resized;
        *capacity = next;
        return true;
}

static char *
shadow_copy_string(Types2Shadow *shadow, char const *text)
{
        if (text == NULL) return NULL;
        size_t length = strlen(text) + 1;
        char *copy = malloc(length);
        if (copy == NULL) {
                shadow->failed = true;
                return NULL;
        }
        memcpy(copy, text, length);
        return copy;
}

static char const *
source_provenance(
        Types2Shadow *shadow,
        Expr const *site,
        char const *description
)
{
        if (site == NULL || description == NULL) return description;
        char const *path = shadow->path == NULL ? "<unknown>" : shadow->path;
        int length = snprintf(
                NULL,
                0,
                "%s at %s:%u:%u",
                description,
                path,
                site->start.line + 1,
                site->start.col + 1
        );
        if (length < 0) return description;
        char *text = malloc((size_t)length + 1);
        if (text == NULL) {
                shadow->failed = true;
                return description;
        }
        snprintf(
                text,
                (size_t)length + 1,
                "%s at %s:%u:%u",
                description,
                path,
                site->start.line + 1,
                site->start.col + 1
        );
        if (!shadow_reserve(
                shadow,
                (void **)&shadow->provenances,
                &shadow->provenance_capacity,
                shadow->provenance_count + 1,
                sizeof *shadow->provenances
        )) {
                free(text);
                return description;
        }
        shadow->provenances[shadow->provenance_count++] = text;
        return text;
}

static bool
resize_nodes(Types2Shadow *shadow, size_t capacity)
{
        Types2Node *nodes = calloc(capacity, sizeof *nodes);

        if (nodes == NULL) {
                shadow->failed = true;
                return false;
        }

        for (size_t i = 0; i < shadow->node_capacity; ++i) {
                Types2Node node = shadow->nodes[i];
                if (node.syntax == NULL) {
                        continue;
                }

                size_t slot = pointer_hash(node.syntax) & (capacity - 1);
                while (nodes[slot].syntax != NULL) {
                        slot = (slot + 1) & (capacity - 1);
                }
                nodes[slot] = node;
        }

        free(shadow->nodes);
        shadow->nodes = nodes;
        shadow->node_capacity = capacity;

        return true;
}

static Types2Node *
remember_node(
        Types2Shadow *shadow,
        void const *syntax,
        uint8_t construct,
        uint32_t role
)
{
        if (shadow == NULL || shadow->failed || syntax == NULL) {
                return NULL;
        }

        if (
                shadow->node_capacity == 0
             || shadow->node_count + 1
                    >= shadow->node_capacity - shadow->node_capacity / 4
        ) {
                if (shadow->node_capacity > SIZE_MAX / 2) {
                        shadow->failed = true;
                        return NULL;
                }
                size_t capacity = shadow->node_capacity == 0
                                ? 256
                                : shadow->node_capacity * 2;
                if (!resize_nodes(shadow, capacity)) {
                        return NULL;
                }
        }

        size_t slot = pointer_hash(syntax) & (shadow->node_capacity - 1);
        while (shadow->nodes[slot].syntax != NULL) {
                if (shadow->nodes[slot].syntax == syntax) {
                        shadow->nodes[slot].roles |= role;
                        return &shadow->nodes[slot];
                }
                slot = (slot + 1) & (shadow->node_capacity - 1);
        }

        Types2Node *node = &shadow->nodes[slot];
        *node = (Types2Node) {
                .syntax = syntax,
                .id = shadow->next_node_id++,
                .roles = role,
                .construct = construct
        };

        shadow->node_count += 1;
        shadow->constructs[construct] += 1;

        return node;
}

static char *diagnostic_type_snapshot(Types2Shadow *shadow, T2Type type);

static void
set_node_type(Types2Shadow *shadow, Expr const *expr, T2Type type)
{
        if (
                expr == NULL
             || type == T2_TYPE_INVALID
             || shadow->building_interface
        ) return;
        Types2Node *node = remember_node(
                shadow,
                expr,
                expr->type,
                IsStmt(expr) ? TYPES2_ROLE_STATEMENT : TYPES2_ROLE_EXPRESSION
        );
        if (node == NULL) return;
        if (!node->inferred) shadow->inferred_nodes += 1;
        node->type = type;
        node->inferred = true;
        if (
                shadow->trace_nodes
             && shadow->log != NULL
             && !shadow->failed
             && !shadow->importing
        ) {
                char *display = diagnostic_type_snapshot(shadow, type);
                log_prefix(shadow, "node_type");
                fprintf(
                        shadow->log,
                        ",\"node\":%" PRIu64
                        ",\"line\":%u,\"column\":%u,\"construct\":",
                        node->id,
                        expr->start.line + 1,
                        expr->start.col + 1
                );
                json_string(shadow->log, construct_name(expr->type));
                fputs(",\"type\":", shadow->log);
                if (display == NULL) fputs("null", shadow->log);
                else json_string(shadow->log, display);
                T2Type zonked = t2_solver_zonk(
                        shadow->solver,
                        type,
                        T2_PREFER_LOWER_BOUND
                );
                T2RuntimeFacts facts;
                if (
                        zonked != T2_TYPE_INVALID
                     && t2_type_runtime_facts(
                            shadow->universe,
                            zonked,
                            &facts
                        )
                ) {
                        fputs(",\"runtime_kind\":", shadow->log);
                        json_string(shadow->log, runtime_kind_name(facts.kind));
                        fprintf(
                                shadow->log,
                                ",\"runtime_exact\":%s,\"runtime_nullable\":%s",
                                facts.exact ? "true" : "false",
                                facts.nullable ? "true" : "false"
                        );
                        if (facts.kind == T2_RUNTIME_NOMINAL && facts.exact) {
                                fprintf(
                                        shadow->log,
                                        ",\"runtime_nominal\":%" PRIu64,
                                        facts.nominal_symbol
                                );
                        }
                }
                log_end(shadow);
                free(display);
        }
}

static T2Type
node_type(Types2Shadow *shadow, Expr const *expr)
{
        if (expr == NULL || shadow->node_capacity == 0) return T2_TYPE_INVALID;
        size_t slot = pointer_hash(expr) & (shadow->node_capacity - 1);
        while (shadow->nodes[slot].syntax != NULL) {
                if (shadow->nodes[slot].syntax == expr) {
                        return shadow->nodes[slot].type;
                }
                slot = (slot + 1) & (shadow->node_capacity - 1);
        }
        return T2_TYPE_INVALID;
}

static void
emit_deferral(
        Types2Shadow *shadow,
        Types2DeferReason reason,
        Expr const *site,
        char const *name,
        char const *module
)
{
        if (shadow->importing) return;
        shadow->deferred_nodes += 1;
        shadow->deferred_reasons[reason] += 1;
        if (!shadow->trace_deferred || shadow->log == NULL || shadow->failed) {
                return;
        }
        log_prefix(shadow, "deferred");
        fputs(",\"reason\":", shadow->log);
        json_string(shadow->log, defer_reason_names[reason]);
        fputs(",\"class\":", shadow->log);
        json_string(shadow->log, defer_class_names[defer_reason_classes[reason]]);
        if (site != NULL) {
                fprintf(
                        shadow->log,
                        ",\"line\":%u,\"column\":%u,\"construct\":",
                        site->start.line + 1,
                        site->start.col + 1
                );
                json_string(shadow->log, construct_name(site->type));
        }
        if (name != NULL) {
                fputs(",\"name\":", shadow->log);
                json_string(shadow->log, name);
        }
        if (module != NULL) {
                fputs(",\"module\":", shadow->log);
                json_string(shadow->log, module);
        }
        log_end(shadow);
}

static void
defer_node(
        Types2Shadow *shadow,
        Types2DeferReason reason,
        Expr const *site,
        char const *name
)
{
        emit_deferral(shadow, reason, site, name, NULL);
}

static void
defer_symbol(
        Types2Shadow *shadow,
        Types2DeferReason reason,
        Expr const *site,
        Symbol const *symbol
)
{
        emit_deferral(
                shadow,
                reason,
                site,
                symbol == NULL ? NULL : symbol->identifier,
                symbol == NULL || symbol->mod == NULL ? NULL : symbol->mod->name
        );
}

static void
retract_deferral(Types2Shadow *shadow, Types2DeferReason reason)
{
        if (shadow->deferred_reasons[reason] == 0) return;
        shadow->deferred_reasons[reason] -= 1;
        shadow->deferred_nodes -= 1;
}

static uint64_t
deferred_class_total(Types2Shadow const *shadow, Types2DeferClass class)
{
        uint64_t total = 0;
        for (size_t i = 0; i < TYPES2_DEFER_REASON_COUNT; ++i) {
                if (defer_reason_classes[i] == class) {
                        total += shadow->deferred_reasons[i];
                }
        }
        return total;
}

static char *
diagnostic_type_snapshot(Types2Shadow *shadow, T2Type type)
{
        if (type == T2_TYPE_INVALID) return NULL;

        T2Type display = type;
        if (!t2_solver_failed(shadow->solver)) {
                T2Type zonked = t2_solver_zonk(
                        shadow->solver,
                        type,
                        T2_PREFER_LOWER_BOUND
                );
                if (zonked != T2_TYPE_INVALID) display = zonked;
        }
        return t2_type_string(shadow->universe, display);
}

static void
add_diagnostic(
        Types2Shadow *shadow,
        Expr const *expr,
        Types2DiagnosticSeverity severity,
        char const *code,
        T2Type actual,
        T2Type expected,
        char const *format,
        ...
)
{
        if (
                shadow == NULL
             || shadow->failed
             || shadow->building_interface
             || shadow->importing
        ) return;
        if (!shadow_reserve(
                shadow,
                (void **)&shadow->diagnostics,
                &shadow->diagnostic_capacity,
                shadow->diagnostic_count + 1,
                sizeof *shadow->diagnostics
        )) return;

        va_list arguments;
        va_start(arguments, format);
        va_list copy;
        va_copy(copy, arguments);
        int length = vsnprintf(NULL, 0, format, copy);
        va_end(copy);
        if (length < 0) {
                va_end(arguments);
                shadow->failed = true;
                return;
        }
        char *message = malloc((size_t)length + 1);
        if (message == NULL) {
                va_end(arguments);
                shadow->failed = true;
                return;
        }
        vsnprintf(message, (size_t)length + 1, format, arguments);
        va_end(arguments);

        Types2Node *node = expr == NULL
                         ? NULL
                         : remember_node(
                                 shadow,
                                 expr,
                                 expr->type,
                                 IsStmt(expr)
                                    ? TYPES2_ROLE_STATEMENT
                                    : TYPES2_ROLE_EXPRESSION
                           );
        char *owned_code = shadow_copy_string(shadow, code);
        if (owned_code == NULL) {
                free(message);
                return;
        }
        char *actual_snapshot = diagnostic_type_snapshot(shadow, actual);
        char *expected_snapshot = diagnostic_type_snapshot(shadow, expected);
        if (
                (actual != T2_TYPE_INVALID && actual_snapshot == NULL)
             || (expected != T2_TYPE_INVALID && expected_snapshot == NULL)
        ) {
                free(owned_code);
                free(message);
                free(actual_snapshot);
                free(expected_snapshot);
                shadow->failed = true;
                return;
        }
        shadow->diagnostics[shadow->diagnostic_count++] = (Types2Diagnostic) {
                .node = node == NULL ? 0 : node->id,
                .location = expr == NULL ? (Location){0} : expr->start,
                .severity = severity,
                .code = owned_code,
                .message = message,
                .actual = actual_snapshot,
                .expected = expected_snapshot,
                .actual_hash = actual == T2_TYPE_INVALID
                             ? 0
                             : t2_type_hash(shadow->universe, actual),
                .expected_hash = expected == T2_TYPE_INVALID
                               ? 0
                               : t2_type_hash(shadow->universe, expected)
        };
}

static Types2Binding *
find_binding(Types2Shadow *shadow, Symbol const *symbol)
{
        if (symbol == NULL) return NULL;
        for (size_t i = shadow->binding_count; i != 0; --i) {
                if (
                        shadow->bindings[i - 1].active
                     && shadow->bindings[i - 1].symbol == symbol
                ) return &shadow->bindings[i - 1];
        }
        return NULL;
}

static Types2Binding *
ensure_binding(Types2Shadow *shadow, Symbol const *symbol)
{
        Types2Binding *binding = find_binding(shadow, symbol);
        if (binding != NULL || symbol == NULL) return binding;
        if (!shadow_reserve(
                shadow,
                (void **)&shadow->bindings,
                &shadow->binding_capacity,
                shadow->binding_count + 1,
                sizeof *shadow->bindings
        )) return NULL;
        binding = &shadow->bindings[shadow->binding_count++];
        *binding = (Types2Binding) {
                .symbol = symbol,
                .refinement = T2_TYPE_INVALID,
                .mutable = (symbol->flags & SYM_CONST) == 0,
                .active = true
        };
        return binding;
}

static T2Type
instantiate_binding(
        Types2Shadow *shadow,
        Types2Binding *binding,
        Expr const *site
)
{
        if (binding == NULL) return T2_TYPE_INVALID;
        if (binding->alias != NULL) {
                Types2Binding *target = find_binding(shadow, binding->alias);
                if (target != NULL && target != binding) {
                        return instantiate_binding(shadow, target, site);
                }
        }
        if (binding->scheme != NULL) {
                T2Type type = t2_scheme_instantiate(
                        binding->scheme,
                        shadow->solver,
                        shadow->level,
                        source_provenance(
                                shadow,
                                site,
                                binding->symbol->identifier
                        )
                );
                if (type == T2_TYPE_INVALID) {
                        add_diagnostic(
                                shadow,
                                site,
                                TYPES2_DIAGNOSTIC_ERROR,
                                "scheme-instantiation",
                                T2_TYPE_INVALID,
                                T2_TYPE_INVALID,
                                "could not instantiate the type scheme for `%s`",
                                binding->symbol->identifier
                        );
                }
                return type;
        }
        if (binding->refinement != T2_TYPE_INVALID) {
                return binding->refinement;
        }
        if (
                t2_type_kind(shadow->universe, binding->type) == T2_TYPE_META
             && t2_type_variable_kind(shadow->universe, binding->type)
                == T2_VARIABLE_WEAK
        ) {
                T2Type zonked = t2_solver_zonk(
                        shadow->solver,
                        binding->type,
                        T2_PREFER_LOWER_BOUND
                );
                if (zonked != T2_TYPE_INVALID) return zonked;
        }
        return binding->type;
}

static size_t
push_type_variables(Types2Shadow *shadow)
{
        return shadow->type_variable_count;
}

static void
pop_type_variables(Types2Shadow *shadow, size_t mark)
{
        if (mark <= shadow->type_variable_count) shadow->type_variable_count = mark;
}

static bool
add_type_variable(Types2Shadow *shadow, Symbol const *symbol, T2Type type)
{
        if (!shadow_reserve(
                shadow,
                (void **)&shadow->type_variables,
                &shadow->type_variable_capacity,
                shadow->type_variable_count + 1,
                sizeof *shadow->type_variables
        )) return false;
        shadow->type_variables[shadow->type_variable_count++] = (Types2TypeVariable) {
                .symbol = symbol,
                .type = type
        };
        return true;
}

static T2Type
find_type_variable(Types2Shadow *shadow, Symbol const *symbol)
{
        for (size_t i = shadow->type_variable_count; i != 0; --i) {
                if (shadow->type_variables[i - 1].symbol == symbol) {
                        return shadow->type_variables[i - 1].type;
                }
        }
        return T2_TYPE_INVALID;
}

static T2Type
primitive_named(Types2Shadow *shadow, char const *name)
{
        if (name == NULL) return T2_TYPE_INVALID;
        if (strcmp(name, "Int") == 0) return t2_primitive(shadow->universe, T2_TYPE_INT);
        if (strcmp(name, "String") == 0) return t2_primitive(shadow->universe, T2_TYPE_STRING);
        if (strcmp(name, "Bool") == 0) return t2_primitive(shadow->universe, T2_TYPE_BOOL);
        if (strcmp(name, "Float") == 0) return t2_primitive(shadow->universe, T2_TYPE_FLOAT);
        if (strcmp(name, "Object") == 0) return t2_primitive(shadow->universe, T2_TYPE_OBJECT);
        if (strcmp(name, "Any") == 0) return t2_primitive(shadow->universe, T2_TYPE_ANY);
        if (strcmp(name, "Unknown") == 0) return t2_primitive(shadow->universe, T2_TYPE_UNKNOWN);
        if (strcmp(name, "Dynamic") == 0) return t2_primitive(shadow->universe, T2_TYPE_DYNAMIC);
        if (strcmp(name, "Never") == 0 || strcmp(name, "Bottom") == 0) {
                return t2_primitive(shadow->universe, T2_TYPE_NEVER);
        }
        if (strcmp(name, "Nil") == 0) {
                return t2_primitive(shadow->universe, T2_TYPE_NIL);
        }
        if (strcmp(name, "Error") == 0) return t2_primitive(shadow->universe, T2_TYPE_ERROR);
        if (strcmp(name, "Type") == 0) {
                T2Type dynamic = t2_primitive(
                        shadow->universe,
                        T2_TYPE_DYNAMIC
                );
                return t2_type_value(shadow->universe, dynamic, dynamic);
        }
        return T2_TYPE_INVALID;
}

static T2Type
literal_symbol_type(Types2Shadow *shadow, Symbol const *symbol)
{
        CompilerLiteral literal;
        if (!compiler_symbol_literal(symbol, &literal)) return T2_TYPE_INVALID;

        switch (literal.kind) {
        case COMPILER_LITERAL_INTEGER:
                return t2_literal_int(shadow->universe, literal.integer);
        case COMPILER_LITERAL_BOOLEAN:
                return t2_literal_bool(shadow->universe, literal.boolean);
        case COMPILER_LITERAL_STRING:
        {
                if (literal.string_length == SIZE_MAX) return T2_TYPE_INVALID;
                char *text = malloc(literal.string_length + 1);
                if (text == NULL) {
                        shadow->failed = true;
                        return T2_TYPE_INVALID;
                }
                memcpy(text, literal.string, literal.string_length);
                text[literal.string_length] = '\0';
                T2Type result = t2_literal_string(shadow->universe, text);
                free(text);
                return result;
        }
        case COMPILER_LITERAL_NONE:
                break;
        }
        return T2_TYPE_INVALID;
}

static Types2Nominal *
find_class_nominal(Types2Shadow *shadow, int class_id)
{
        for (size_t i = 0; i < shadow->nominal_count; ++i) {
                if (
                        shadow->nominals[i].tag_id < 0
                     && shadow->nominals[i].class_id == class_id
                ) return &shadow->nominals[i];
        }
        return NULL;
}

static Types2Nominal *
find_tag_nominal(Types2Shadow *shadow, int tag_id)
{
        for (size_t i = 0; i < shadow->nominal_count; ++i) {
                if (shadow->nominals[i].tag_id == tag_id) return &shadow->nominals[i];
        }
        return NULL;
}

static size_t
builtin_nominal_arity(int class_id)
{
        switch (class_id) {
        case CLASS_ARRAY:
        case CLASS_PTR:
        case CLASS_QUEUE:
        case CLASS_SHARED_QUEUE:
        case CLASS_ITERABLE:
        case CLASS_ITER:
                return 1;
        case CLASS_DICT:
        case CLASS_GENERATOR:
                return 2;
        default:
                return 0;
        }
}

static T2Type
primitive_class_type(Types2Shadow *shadow, int class_id)
{
        T2TypeKind kind;
        switch (class_id) {
        case CLASS_NIL: kind = T2_TYPE_NIL; break;
        case CLASS_OBJECT: kind = T2_TYPE_OBJECT; break;
        case CLASS_STRING: kind = T2_TYPE_STRING; break;
        case CLASS_INT: kind = T2_TYPE_INT; break;
        case CLASS_FLOAT: kind = T2_TYPE_FLOAT; break;
        case CLASS_BOOL: kind = T2_TYPE_BOOL; break;
        default: return T2_TYPE_INVALID;
        }
        return t2_primitive(shadow->universe, kind);
}

static Types2Nominal *
ensure_nominal(
        Types2Shadow *shadow,
        int class_id,
        char const *fallback_name,
        size_t fallback_arity
)
{
        Types2Nominal *nominal = find_class_nominal(shadow, class_id);
        if (nominal != NULL) return nominal;
        if (class_id < 0 || shadow->ty == NULL) return NULL;

        Class *class = class_get(shadow->ty, class_id);
        char const *name = class != NULL && class->name != NULL
                         ? class->name
                         : fallback_name;
        size_t arity = fallback_arity;
        if (class != NULL && class->def != NULL) {
                arity = (size_t)vN(class->def->class.type_params);
                if (class->def->type == STATEMENT_TAG_DEFINITION) arity = 1;
        } else if (arity == 0) {
                arity = builtin_nominal_arity(class_id);
        }
        if (!shadow_reserve(
                shadow,
                (void **)&shadow->nominals,
                &shadow->nominal_capacity,
                shadow->nominal_count + 1,
                sizeof *shadow->nominals
        )) return NULL;
        size_t index = shadow->nominal_count++;
        shadow->nominals[index] = (Types2Nominal) {
                .class_id = class_id,
                .tag_id = -1,
                .symbol = shadow->next_nominal_symbol++,
                .name = name == NULL ? "<class>" : name,
                .arity = arity
        };
        nominal = &shadow->nominals[index];

        T2Variance *variance = arity == 0 ? NULL : calloc(arity, sizeof *variance);
        if (arity != 0 && variance == NULL) {
                shadow->failed = true;
                return NULL;
        }
        if (
                class_id == CLASS_ITERABLE
             || class_id == CLASS_ITER
             || (class != NULL
              && class->def != NULL
              && class->def->type == STATEMENT_TAG_DEFINITION)
        ) {
                for (size_t i = 0; i < arity; ++i) variance[i] = T2_COVARIANT;
        }
        bool declared = t2_declare_nominal(
                shadow->universe,
                nominal->symbol,
                nominal->name,
                arity,
                variance
        );
        free(variance);
        nominal->declared = declared;
        if (!declared) return NULL;

        if (class != NULL && class->super != NULL && class->super->i >= 0) {
                Types2Nominal *super = ensure_nominal(
                        shadow,
                        class->super->i,
                        class->super->name,
                        0
                );
                nominal = find_class_nominal(shadow, class_id);
                if (super != NULL) {
                        T2Type *arguments = super->arity == 0
                                          ? NULL
                                          : malloc(super->arity * sizeof *arguments);
                        if (super->arity != 0 && arguments == NULL) {
                                shadow->failed = true;
                                return nominal;
                        }
                        for (size_t i = 0; i < super->arity; ++i) {
                                arguments[i] = i < nominal->arity
                                             ? t2_nominal_type_parameter(
                                                     shadow->universe,
                                                     (uint32_t)i
                                               )
                                             : t2_primitive(
                                                     shadow->universe,
                                                     T2_TYPE_DYNAMIC
                                               );
                        }
                        T2Type supertype = t2_nominal(
                                shadow->universe,
                                super->symbol,
                                arguments,
                                super->arity
                        );
                        free(arguments);
                        if (supertype != T2_TYPE_INVALID) {
                                (void)t2_nominal_add_super(
                                        shadow->universe,
                                        nominal->symbol,
                                        supertype
                                );
                        }
                }
        }
        return find_class_nominal(shadow, class_id);
}

static Types2Nominal *
ensure_tag_nominal(
        Types2Shadow *shadow,
        int tag_id,
        char const *fallback_name
)
{
        Types2Nominal *nominal = find_tag_nominal(shadow, tag_id);
        if (nominal != NULL) return nominal;
        if (tag_id <= 0 || shadow->ty == NULL) return NULL;

        Class *class = tags_get_class(shadow->ty, tag_id);
        char const *name = fallback_name == NULL
                         ? tags_name(shadow->ty, tag_id)
                         : fallback_name;
        if (!shadow_reserve(
                shadow,
                (void **)&shadow->nominals,
                &shadow->nominal_capacity,
                shadow->nominal_count + 1,
                sizeof *shadow->nominals
        )) return NULL;
        size_t index = shadow->nominal_count++;
        shadow->nominals[index] = (Types2Nominal) {
                .class_id = class == NULL ? -1 : class->i,
                .tag_id = tag_id,
                .symbol = shadow->next_nominal_symbol++,
                .name = name == NULL ? "<tag>" : name,
                .arity = 1
        };
        nominal = &shadow->nominals[index];
        T2Variance variance = T2_COVARIANT;
        nominal->declared = t2_declare_nominal(
                shadow->universe,
                nominal->symbol,
                nominal->name,
                1,
                &variance
        );
        if (!nominal->declared) return NULL;
        uint64_t symbol = nominal->symbol;
        Types2Nominal *tag_class = ensure_nominal(shadow, CLASS_TAG, "Tag", 0);
        if (tag_class != NULL) {
                (void)t2_nominal_add_super(
                        shadow->universe,
                        symbol,
                        t2_nominal(shadow->universe, tag_class->symbol, NULL, 0)
                );
        }
        return find_tag_nominal(shadow, tag_id);
}

static Types2Nominal *
ensure_symbol_nominal(
        Types2Shadow *shadow,
        Symbol const *symbol,
        char const *fallback_name
)
{
        if (symbol == NULL) return NULL;
        if (
                (SymbolIsTag(symbol) || SymbolIsBuiltin(symbol))
             && symbol->tag > 0
        ) {
                return ensure_tag_nominal(shadow, symbol->tag, fallback_name);
        }
        /* Qualified tag references are represented by member symbols.  Their
         * resolved tag slot is useful, but arbitrary symbols can contain a
         * non-tag value in that slot.  Validate the identity through the tag
         * registry before using it as an index. */
        if (
                SymbolIsMember(symbol)
             && fallback_name != NULL
             && shadow->ty != NULL
        ) {
                int tag = tags_lookup(shadow->ty, fallback_name);
                if (tag > 0) {
                        return ensure_tag_nominal(shadow, tag, fallback_name);
                }
        }
        if (SymbolIsClass(symbol) && symbol->class >= 0) {
                return ensure_nominal(shadow, symbol->class, fallback_name, 0);
        }
        if (
                SymbolIsMember(symbol)
             && symbol->class >= 0
             && shadow->ty != NULL
             && symbol->class < class_count(shadow->ty)
             && fallback_name != NULL
        ) {
                char const *name = class_name(shadow->ty, symbol->class);
                if (name != NULL && strcmp(name, fallback_name) == 0) {
                        return ensure_nominal(
                                shadow,
                                symbol->class,
                                fallback_name,
                                0
                        );
                }
        }
        return NULL;
}

static T2Type
apply_nominal(
        Types2Shadow *shadow,
        Types2Nominal *nominal,
        T2Type const *arguments,
        size_t argument_count,
        Expr const *site
)
{
        if (nominal == NULL) return T2_TYPE_INVALID;
        T2Type defaulted_arguments[2];
        if (
                nominal->class_id == CLASS_GENERATOR
             && nominal->arity == 2
             && argument_count == 1
        ) {
                defaulted_arguments[0] = arguments[0];
                defaulted_arguments[1] = t2_primitive(
                        shadow->universe,
                        T2_TYPE_NIL
                );
                arguments = defaulted_arguments;
                argument_count = 2;
        }
        T2Type dynamic_arguments[8];
        if (
                argument_count == 0
             && nominal->arity != 0
             && nominal->arity <= sizeof dynamic_arguments / sizeof dynamic_arguments[0]
        ) {
                for (size_t i = 0; i < nominal->arity; ++i) {
                        dynamic_arguments[i] = t2_primitive(
                                shadow->universe,
                                T2_TYPE_DYNAMIC
                        );
                }
                arguments = dynamic_arguments;
                argument_count = nominal->arity;
        }
        if (nominal->arity != argument_count) {
                if (shadow->building_interface) {
                        return t2_primitive(shadow->universe, T2_TYPE_DYNAMIC);
                }
                add_diagnostic(
                        shadow,
                        site,
                        TYPES2_DIAGNOSTIC_ERROR,
                        "generic-arity",
                        T2_TYPE_INVALID,
                        T2_TYPE_INVALID,
                        "`%s` expects %zu type argument%s, but %zu were provided",
                        nominal->name,
                        nominal->arity,
                        nominal->arity == 1 ? "" : "s",
                        argument_count
                );
                return t2_primitive(shadow->universe, T2_TYPE_ERROR);
        }
        return t2_nominal(
                shadow->universe,
                nominal->symbol,
                arguments,
                argument_count
        );
}

static bool ensure_class_interface(Types2Shadow *shadow, int class_id);

static T2Type
nominal_application(
        Types2Shadow *shadow,
        int class_id,
        char const *name,
        T2Type const *arguments,
        size_t argument_count,
        Expr const *site
)
{
        Types2Nominal *nominal = ensure_nominal(
                shadow,
                class_id,
                name,
                argument_count
        );
        if (nominal != NULL) {
                (void)ensure_class_interface(shadow, class_id);
                nominal = find_class_nominal(shadow, class_id);
        }
        return apply_nominal(shadow, nominal, arguments, argument_count, site);
}

static Types2Member *
find_direct_member(
        Types2Shadow *shadow,
        int class_id,
        char const *name,
        Types2MemberKind kind,
        bool is_static
)
{
        if (name == NULL) return NULL;
        for (size_t i = shadow->member_count; i != 0; --i) {
                Types2Member *member = &shadow->members[i - 1];
                if (
                        member->class_id == class_id
                     && member->kind == kind
                     && member->is_static == is_static
                     && strcmp(member->name, name) == 0
                ) return member;
        }
        return NULL;
}

static Expr const *
member_reference_leaf(Expr const *source)
{
        Expr const *expression = source == NULL ? NULL : unfurl(source);
        size_t remaining = 1024;
        while (expression != NULL && remaining-- != 0) {
                if (expression->type == EXPRESSION_SUBSCRIPT) {
                        expression = unfurl(expression->container);
                        continue;
                }
                if (
                        expression->type == EXPRESSION_MEMBER_ACCESS
                     || expression->type == EXPRESSION_SELF_ACCESS
                ) {
                        expression = unfurl(expression->member);
                        continue;
                }
                if (expression->type == EXPRESSION_RESOLVED) {
                        expression = unfurl(expression->value);
                        continue;
                }
                break;
        }
        return expression;
}

static Types2Member *
find_member_x(
        Types2Shadow *shadow,
        int class_id,
        char const *name,
        Types2MemberKind kind,
        bool is_static,
        unsigned depth
)
{
        if (class_id < 0 || depth > 256) return NULL;
        Types2Member *member = find_direct_member(
                shadow,
                class_id,
                name,
                kind,
                is_static
        );
        if (member != NULL) return member;

        Class *class = shadow->ty == NULL ? NULL : class_get(shadow->ty, class_id);
        if (class == NULL) return NULL;
        if (class->super != NULL && class->super->i != class_id) {
                (void)ensure_class_interface(shadow, class->super->i);
                member = find_member_x(
                        shadow,
                        class->super->i,
                        name,
                        kind,
                        is_static,
                        depth + 1
                );
                if (member != NULL) return member;
        }
        if (class->def == NULL) return NULL;
        ClassDefinition const *definition = &class->def->class;
        for (int i = 0; i < vN(definition->traits); ++i) {
                Expr const *leaf = member_reference_leaf(v__(definition->traits, i));
                if (
                        leaf == NULL
                     || leaf->symbol == NULL
                     || !SymbolIsClass(leaf->symbol)
                     || leaf->symbol->class < 0
                     || leaf->symbol->class == class_id
                ) continue;
                (void)ensure_class_interface(shadow, leaf->symbol->class);
                member = find_member_x(
                        shadow,
                        leaf->symbol->class,
                        name,
                        kind,
                        is_static,
                        depth + 1
                );
                if (member != NULL) return member;
        }
        return NULL;
}

static Types2Member *
find_member(
        Types2Shadow *shadow,
        int class_id,
        char const *name,
        Types2MemberKind kind,
        bool is_static
)
{
        return find_member_x(shadow, class_id, name, kind, is_static, 0);
}

static T2Scheme *
prepend_scheme_quantifiers(
        Types2Shadow *shadow,
        T2Quantifier const *prefix,
        size_t prefix_count,
        T2Scheme const *inner,
        T2Type body
)
{
        size_t inner_quantifiers = t2_scheme_quantifier_count(inner);
        size_t inner_predicates = t2_scheme_predicate_count(inner);
        size_t count = prefix_count + inner_quantifiers;
        T2Quantifier *quantifiers = count == 0
                                  ? NULL
                                  : malloc(count * sizeof *quantifiers);
        T2Predicate *predicates = inner_predicates == 0
                                ? NULL
                                : malloc(inner_predicates * sizeof *predicates);
        if (
                (count != 0 && quantifiers == NULL)
             || (inner_predicates != 0 && predicates == NULL)
        ) {
                free(quantifiers);
                free(predicates);
                shadow->failed = true;
                return NULL;
        }
        if (prefix_count != 0) {
                memcpy(quantifiers, prefix, prefix_count * sizeof *quantifiers);
        }
        for (size_t i = 0; i < inner_quantifiers; ++i) {
                if (!t2_scheme_quantifier(inner, i, &quantifiers[prefix_count + i])) {
                        free(quantifiers);
                        free(predicates);
                        return NULL;
                }
        }
        for (size_t i = 0; i < inner_predicates; ++i) {
                if (!t2_scheme_predicate(inner, i, &predicates[i])) {
                        free(quantifiers);
                        free(predicates);
                        return NULL;
                }
        }
        if (inner != NULL) body = t2_scheme_body(inner);
        T2Scheme *result = t2_scheme_new(
                shadow->universe,
                quantifiers,
                count,
                body,
                predicates,
                inner_predicates
        );
        free(quantifiers);
        free(predicates);
        return result;
}

static T2Scheme *
copy_scheme(Types2Shadow *shadow, T2Scheme const *scheme)
{
        if (scheme == NULL) return NULL;
        return prepend_scheme_quantifiers(
                shadow,
                NULL,
                0,
                scheme,
                T2_TYPE_INVALID
        );
}

static bool
add_operator_scheme(
        Types2Shadow *shadow,
        char const *name,
        Expr const *declaration,
        T2Scheme *scheme
)
{
        if (name == NULL || declaration == NULL || scheme == NULL) {
                t2_scheme_free(scheme);
                return false;
        }
        for (size_t i = 0; i < shadow->operator_count; ++i) {
                Types2Operator *operator = &shadow->operators[i];
                if (operator->declaration != declaration) continue;
                t2_scheme_free(operator->scheme);
                operator->scheme = scheme;
                operator->name = name;
                return true;
        }
        if (!shadow_reserve(
                shadow,
                (void **)&shadow->operators,
                &shadow->operator_capacity,
                shadow->operator_count + 1,
                sizeof *shadow->operators
        )) {
                t2_scheme_free(scheme);
                return false;
        }
        shadow->operators[shadow->operator_count++] = (Types2Operator) {
                .name = name,
                .declaration = declaration,
                .scheme = scheme
        };
        return true;
}

static Types2Operator *
find_operator_declaration(Types2Shadow *shadow, Expr const *declaration)
{
        for (size_t i = 0; i < shadow->operator_count; ++i) {
                if (shadow->operators[i].declaration == declaration) {
                        return &shadow->operators[i];
                }
        }
        return NULL;
}

static Types2Member *
add_member(
        Types2Shadow *shadow,
        int class_id,
        char const *name,
        Types2MemberKind kind,
        bool is_static,
        bool required,
        bool writable,
        size_t class_arity,
        T2Scheme *scheme,
        Expr const *declaration
)
{
        if (name == NULL || scheme == NULL) return NULL;
        Types2Member *old = find_direct_member(
                shadow,
                class_id,
                name,
                kind,
                is_static
        );
        if (old != NULL) {
                t2_scheme_free(old->scheme);
                *old = (Types2Member) {
                        .class_id = class_id,
                        .name = name,
                        .kind = kind,
                        .scheme = scheme,
                        .declaration = declaration,
                        .class_arity = class_arity,
                        .is_static = is_static,
                        .required = required,
                        .writable = writable
                };
                return old;
        }
        if (!shadow_reserve(
                shadow,
                (void **)&shadow->members,
                &shadow->member_capacity,
                shadow->member_count + 1,
                sizeof *shadow->members
        )) return NULL;
        Types2Member *member = &shadow->members[shadow->member_count++];
        *member = (Types2Member) {
                .class_id = class_id,
                .name = name,
                .kind = kind,
                .scheme = scheme,
                .declaration = declaration,
                .class_arity = class_arity,
                .is_static = is_static,
                .required = required,
                .writable = writable
        };
        return member;
}

static T2Type
instantiate_member(
        Types2Shadow *shadow,
        Types2Member const *member,
        T2Type receiver,
        Expr const *site
)
{
        if (member == NULL || member->scheme == NULL) return T2_TYPE_INVALID;
        /* Interface discovery performed by an instantiated predicate may grow
         * the member vector.  The scheme itself is immutable and separately
         * allocated, so a by-value descriptor is the stable call boundary. */
        Types2Member selected = *member;
        member = &selected;
        Types2Nominal *declaration = find_class_nominal(
                shadow,
                member->class_id
        );
        if (declaration != NULL) {
                T2Type source = receiver;
                if (t2_type_kind(shadow->universe, source) != T2_TYPE_NOMINAL) {
                        int receiver_class = -1;
                        switch (t2_type_kind(shadow->universe, source)) {
                        case T2_TYPE_STRING:
                        case T2_TYPE_LITERAL_STRING: receiver_class = CLASS_STRING; break;
                        case T2_TYPE_INT:
                        case T2_TYPE_LITERAL_INT: receiver_class = CLASS_INT; break;
                        case T2_TYPE_FLOAT: receiver_class = CLASS_FLOAT; break;
                        case T2_TYPE_BOOL:
                        case T2_TYPE_LITERAL_BOOL: receiver_class = CLASS_BOOL; break;
                        case T2_TYPE_OBJECT: receiver_class = CLASS_OBJECT; break;
                        default: break;
                        }
                        Types2Nominal *native = find_class_nominal(
                                shadow,
                                receiver_class
                        );
                        if (native != NULL && native->arity == 0) {
                                source = t2_nominal(
                                        shadow->universe,
                                        native->symbol,
                                        NULL,
                                        0
                                );
                        }
                }
                T2Type projected = t2_nominal_project(
                        shadow->universe,
                        source,
                        declaration->symbol
                );
                if (projected != T2_TYPE_INVALID) receiver = projected;
        }
        size_t count = t2_scheme_quantifier_count(member->scheme);
        T2Type *arguments = count == 0 ? NULL : malloc(count * sizeof *arguments);
        if (count != 0 && arguments == NULL) {
                shadow->failed = true;
                return T2_TYPE_INVALID;
        }
        bool receiver_nominal = t2_type_kind(shadow->universe, receiver)
                             == T2_TYPE_NOMINAL;
        size_t receiver_arity = receiver_nominal
                              ? t2_type_arity(shadow->universe, receiver)
                              : 0;
        for (size_t i = 0; i < count; ++i) {
                T2Quantifier quantifier;
                if (!t2_scheme_quantifier(member->scheme, i, &quantifier)) {
                        free(arguments);
                        return T2_TYPE_INVALID;
                }
                if (i < member->class_arity && i < receiver_arity) {
                        arguments[i] = t2_type_child(shadow->universe, receiver, i);
                } else {
                        T2VariableKind kind = quantifier.kind;
                        if (
                                kind != T2_VARIABLE_ROW
                             && kind != T2_VARIABLE_PACK
                             && kind != T2_VARIABLE_WEAK
                        ) kind = T2_VARIABLE_FLEXIBLE;
                        arguments[i] = t2_solver_new_meta(
                                shadow->solver,
                                kind,
                                shadow->level + 1,
                                member->name
                        );
                }
        }
        T2Type result = t2_scheme_apply(
                member->scheme,
                shadow->solver,
                arguments,
                count,
                member->name
        );
        free(arguments);
        if (result == T2_TYPE_INVALID) {
                add_diagnostic(
                        shadow,
                        site,
                        TYPES2_DIAGNOSTIC_ERROR,
                        "member-instantiation",
                        receiver,
                        T2_TYPE_INVALID,
                        "could not instantiate member `%s` for this receiver",
                        member->name
                );
                return t2_primitive(shadow->universe, T2_TYPE_ERROR);
        }
        return result;
}

static Types2Alias *
find_alias(Types2Shadow *shadow, Symbol const *symbol)
{
        for (size_t i = 0; i < shadow->alias_count; ++i) {
                if (shadow->aliases[i].symbol == symbol) return &shadow->aliases[i];
        }
        return NULL;
}

static void register_type_alias(
        Types2Shadow *shadow,
        ClassDefinition const *definition
);
static void register_nominal_hierarchy(
        Types2Shadow *shadow,
        ClassDefinition const *definition,
        Types2Nominal const *nominal
);

static ClassDefinition const *
find_alias_definition_in_statement(Stmt const *statement, Symbol const *symbol)
{
        if (statement == NULL || symbol == NULL) return NULL;
        if (
                statement->type == STATEMENT_BLOCK
             || statement->type == STATEMENT_MULTI
        ) {
                for (int i = 0; i < vN(statement->statements); ++i) {
                        ClassDefinition const *definition =
                                find_alias_definition_in_statement(
                                        v__(statement->statements, i),
                                        symbol
                                );
                        if (definition != NULL) return definition;
                }
                return NULL;
        }
        if (statement->type != STATEMENT_TYPE_DEFINITION) return NULL;
        ClassDefinition const *definition = &statement->class;
        if (definition->var == symbol) return definition;
        if (
                definition->var != NULL
             && definition->name != NULL
             && symbol->identifier != NULL
             && definition->var->mod == symbol->mod
             && strcmp(definition->name, symbol->identifier) == 0
        ) return definition;
        return NULL;
}

static Types2Alias *
find_or_import_alias(Types2Shadow *shadow, Symbol const *symbol)
{
        Types2Alias *alias = find_alias(shadow, symbol);
        if (
                alias != NULL
             || symbol == NULL
             || !SymbolIsTypeAlias(symbol)
             || symbol->mod == NULL
             || symbol->mod->prog == NULL
        ) return alias;

        ClassDefinition const *definition = NULL;
        for (size_t i = 0; symbol->mod->prog[i] != NULL; ++i) {
                definition = find_alias_definition_in_statement(
                        symbol->mod->prog[i],
                        symbol
                );
                if (definition != NULL) break;
        }
        if (definition == NULL) return NULL;
        register_type_alias(shadow, definition);
        return find_alias(shadow, definition->var);
}

static T2Type lower_type(Types2Shadow *shadow, Expr const *expression);
static void log_native_type(Types2Shadow *shadow, T2Type type);
static Types2Nominal *nominal_from_type(Types2Shadow *shadow, T2Type type);

static T2Type
resolve_alias(Types2Shadow *shadow, Types2Alias *alias, Expr const *site)
{
        if (alias == NULL) return T2_TYPE_INVALID;
        if (alias->state == TYPES2_ALIAS_RESOLVED) return alias->monotype;
        if (alias->state == TYPES2_ALIAS_RESOLVING) {
                return t2_recursive_variable(shadow->universe, alias->binder);
        }
        if (alias->state == TYPES2_ALIAS_FAILED) {
                return t2_primitive(shadow->universe, T2_TYPE_ERROR);
        }

        size_t alias_index = (size_t)(alias - shadow->aliases);
        Symbol const *alias_symbol = alias->symbol;
        ClassDefinition const *definition = alias->definition;
        uint32_t binder = alias->binder;
        alias->state = TYPES2_ALIAS_RESOLVING;
        size_t mark = push_type_variables(shadow);
        size_t arity = (size_t)vN(definition->type_params);
        T2Quantifier *quantifiers = arity == 0
                                  ? NULL
                                  : malloc(arity * sizeof *quantifiers);
        if (arity != 0 && quantifiers == NULL) {
                shadow->failed = true;
                alias->state = TYPES2_ALIAS_FAILED;
                return T2_TYPE_INVALID;
        }
        for (size_t i = 0; i < arity; ++i) {
                Expr const *parameter = v__(definition->type_params, (int)i);
                T2VariableKind kind = parameter->symbol != NULL
                                   && (parameter->symbol->flags & SYM_PARAM_PACK)
                                    ? T2_VARIABLE_PACK
                                    : T2_VARIABLE_QUANTIFIED;
                T2Type variable = t2_variable(
                        shadow->universe,
                        kind,
                        (uint32_t)i + 1
                );
                quantifiers[i] = (T2Quantifier) {
                        .id = (uint32_t)i + 1,
                        .kind = kind
                };
                if (!add_type_variable(shadow, parameter->symbol, variable)) {
                        free(quantifiers);
                        pop_type_variables(shadow, mark);
                        alias->state = TYPES2_ALIAS_FAILED;
                        return T2_TYPE_INVALID;
                }
        }

        T2Type body = lower_type(shadow, definition->type);
        /* Recursive lowering may discover and append imported aliases.  The
         * alias table is a vector, so reacquire this entry by its stable append
         * index before touching it again. */
        alias = alias_index < shadow->alias_count
              ? &shadow->aliases[alias_index]
              : NULL;
        pop_type_variables(shadow, mark);
        if (alias == NULL || alias->symbol != alias_symbol) {
                free(quantifiers);
                shadow->failed = true;
                return T2_TYPE_INVALID;
        }
        if (body != T2_TYPE_INVALID && t2_type_kind(shadow->universe, body) != T2_TYPE_ERROR) {
                body = t2_recursive(shadow->universe, binder, body);
        }
        if (body == T2_TYPE_INVALID) {
                add_diagnostic(
                        shadow,
                        site,
                        TYPES2_DIAGNOSTIC_ERROR,
                        "unguarded-recursive-alias",
                        T2_TYPE_INVALID,
                        T2_TYPE_INVALID,
                        "type alias `%s` is recursively defined without a guarded constructor",
                        alias_symbol->identifier
                );
                alias->state = TYPES2_ALIAS_FAILED;
                free(quantifiers);
                return t2_primitive(shadow->universe, T2_TYPE_ERROR);
        }
        alias->scheme = t2_scheme_new(
                shadow->universe,
                quantifiers,
                arity,
                body,
                NULL,
                0
        );
        free(quantifiers);
        if (alias->scheme == NULL) {
                shadow->failed = true;
                alias->state = TYPES2_ALIAS_FAILED;
                return T2_TYPE_INVALID;
        }
        alias->monotype = body;
        alias->arity = arity;
        alias->state = TYPES2_ALIAS_RESOLVED;
        return body;
}

static bool
regular_recursive_alias_arguments(
        Types2Shadow *shadow,
        Types2Alias const *alias,
        T2Type const *arguments,
        size_t argument_count
)
{
        if (alias == NULL || argument_count != alias->arity) return false;
        for (size_t i = 0; i < argument_count; ++i) {
                Expr const *parameter = v__(
                        alias->definition->type_params,
                        (int)i
                );
                T2Type variable = find_type_variable(shadow, parameter->symbol);
                if (variable == T2_TYPE_INVALID || arguments[i] != variable) {
                        return false;
                }
        }
        return true;
}

static bool
tuple_has_names(Expr const *expression)
{
        for (int i = 0; i < vN(expression->names); ++i) {
                if (v__(expression->names, i) != NULL) return true;
        }
        return false;
}

static bool
tuple_is_record(Expr const *expression)
{
        /* Empty tuple and empty record literals have the same AST kind and no
         * names to distinguish them.  The parser does preserve the opening
         * delimiter in the source location, which is stable for the complete
         * shadow pass. */
        return tuple_has_names(expression)
            || (
                       expression != NULL
                    && expression->start.s != NULL
                    && *expression->start.s == '{'
               );
}

static bool
tuple_is_pure_record(Expr const *expression)
{
        for (int i = 0; i < vN(expression->es); ++i) {
                Expr const *item = v__(expression->es, i);
                bool spread = item != NULL && item->type == EXPRESSION_SPREAD;
                char const *name = i < vN(expression->names)
                                 ? v__(expression->names, i)
                                 : NULL;
                if (!spread && name == NULL) return false;
        }
        return true;
}

static bool
is_pack_type(Types2Shadow *shadow, T2Type type)
{
        switch (t2_type_kind(shadow->universe, type)) {
        case T2_TYPE_PACK:
        case T2_TYPE_PACK_EMPTY:
        case T2_TYPE_PACK_ANY:
        case T2_TYPE_PACK_EXPANSION:
                return true;
        case T2_TYPE_META:
        case T2_TYPE_VARIABLE:
                return t2_type_variable_kind(shadow->universe, type)
                    == T2_VARIABLE_PACK;
        default:
                return false;
        }
}

static Expr const *
type_reference_leaf(Expr const *source)
{
        Expr const *expression = source == NULL ? NULL : unfurl(source);
        size_t remaining = 1024;
        while (expression != NULL && remaining-- != 0) {
                if (
                        expression->type == EXPRESSION_MEMBER_ACCESS
                     || expression->type == EXPRESSION_SELF_ACCESS
                ) {
                        expression = unfurl(expression->member);
                        continue;
                }
                if (expression->type == EXPRESSION_RESOLVED) {
                        expression = unfurl(expression->value);
                        continue;
                }
                break;
        }
        return expression;
}

static int
type_symbol_class_id(Types2Shadow *shadow, Symbol const *symbol)
{
        if (symbol == NULL) return -1;
        if (
                symbol->class >= 0
             && shadow->ty != NULL
             && symbol->class < class_count(shadow->ty)
        ) return symbol->class;
        if (!SymbolIsTag(symbol) || symbol->tag <= 0 || shadow->ty == NULL) {
                return -1;
        }
        Class *class = tags_get_class(shadow->ty, symbol->tag);
        return class == NULL ? -1 : class->i;
}

static T2Type
lower_named_type(
        Types2Shadow *shadow,
        Expr const *site,
        Expr const *name_expression,
        bool allow_primitive
)
{
        Expr const *name = type_reference_leaf(name_expression);
        if (name == NULL) return T2_TYPE_INVALID;

        T2Type result = find_type_variable(shadow, name->symbol);
        if (result != T2_TYPE_INVALID) return result;
        if (allow_primitive) {
                result = primitive_named(shadow, name->identifier);
                if (result != T2_TYPE_INVALID) return result;
        }

        result = literal_symbol_type(shadow, name->symbol);
        if (result != T2_TYPE_INVALID) return result;

        Types2Alias *alias = find_or_import_alias(shadow, name->symbol);
        if (alias != NULL) {
                Symbol const *alias_symbol = alias->symbol;
                (void)resolve_alias(shadow, alias, site);
                alias = find_alias(shadow, alias_symbol);
                if (alias == NULL) {
                        shadow->failed = true;
                        return T2_TYPE_INVALID;
                }
                if (alias->arity != 0) {
                        add_diagnostic(
                                shadow,
                                site,
                                TYPES2_DIAGNOSTIC_ERROR,
                                "generic-arity",
                                T2_TYPE_INVALID,
                                T2_TYPE_INVALID,
                                "generic type alias `%s` requires %zu type argument%s",
                                alias->symbol->identifier,
                                alias->arity,
                                alias->arity == 1 ? "" : "s"
                        );
                        return t2_primitive(shadow->universe, T2_TYPE_ERROR);
                }
                return t2_scheme_instantiate(
                        alias->scheme,
                        shadow->solver,
                        shadow->level,
                        alias->symbol->identifier
                );
        }

        Types2Nominal *nominal = ensure_symbol_nominal(
                shadow,
                name->symbol,
                name->identifier
        );
        if (nominal != NULL) {
                if (nominal->tag_id > 0) {
                        T2Type payload = t2_primitive(
                                shadow->universe,
                                T2_TYPE_NEVER
                        );
                        return t2_nominal(
                                shadow->universe,
                                nominal->symbol,
                                &payload,
                                1
                        );
                }
                if (nominal->arity == 0) {
                        return t2_nominal(
                                shadow->universe,
                                nominal->symbol,
                                NULL,
                                0
                        );
                }
                return apply_nominal(shadow, nominal, NULL, 0, site);
        }

        if (shadow->building_interface) {
                return t2_primitive(shadow->universe, T2_TYPE_DYNAMIC);
        }
        add_diagnostic(
                shadow,
                site,
                TYPES2_DIAGNOSTIC_ERROR,
                "unknown-type",
                T2_TYPE_INVALID,
                T2_TYPE_INVALID,
                "cannot resolve type name `%s`",
                name->identifier == NULL ? "<type>" : name->identifier
        );
        return t2_primitive(shadow->universe, T2_TYPE_ERROR);
}

static T2Type
lower_function_type(Types2Shadow *shadow, Expr const *expression)
{
        Expr const *input = expression->left;
        size_t count = 1;
        bool sequence = input != NULL
                     && (
                                input->type == EXPRESSION_LIST
                             || input->type == EXPRESSION_TUPLE
                             || input->type == EXPRESSION_TUPLE_SPEC
                        );
        if (sequence) count = (size_t)vN(input->es);
        T2ParameterSpec *parameters = count == 0
                                    ? NULL
                                    : calloc(count, sizeof *parameters);
        if (count != 0 && parameters == NULL) {
                shadow->failed = true;
                return T2_TYPE_INVALID;
        }
        bool positional_closed = false;
        for (size_t i = 0; i < count; ++i) {
                Expr const *parameter = sequence ? v__(input->es, (int)i) : input;
                T2ParameterKind kind = T2_PARAMETER_POSITIONAL_ONLY;
                Expr const *annotation = parameter;
                if (parameter->type == EXPRESSION_SPREAD) {
                        kind = T2_PARAMETER_POSITIONAL_REST;
                        annotation = parameter->value;
                } else if (parameter->type == EXPRESSION_SPLAT) {
                        kind = T2_PARAMETER_KEYWORD_REST;
                        annotation = parameter->value;
                } else if (sequence && input->type != EXPRESSION_LIST) {
                        kind = T2_PARAMETER_POSITIONAL_OR_KEYWORD;
                }
                if (
                        positional_closed
                     && kind == T2_PARAMETER_POSITIONAL_OR_KEYWORD
                ) kind = T2_PARAMETER_KEYWORD_ONLY;
                char const *name = sequence && i < (size_t)vN(input->names)
                                 ? v__(input->names, (int)i)
                                 : NULL;
                if (kind != T2_PARAMETER_POSITIONAL_ONLY && name == NULL) {
                        kind = parameter->type == EXPRESSION_SPREAD
                             ? T2_PARAMETER_POSITIONAL_REST
                             : parameter->type == EXPRESSION_SPLAT
                                ? T2_PARAMETER_KEYWORD_REST
                                : T2_PARAMETER_POSITIONAL_ONLY;
                }
                bool required = sequence
                             && i < (size_t)vN(input->required)
                              ? v__(input->required, (int)i)
                              : true;
                if (
                        kind == T2_PARAMETER_POSITIONAL_REST
                     || kind == T2_PARAMETER_KEYWORD_REST
                ) required = false;
                T2Type parameter_type = lower_type(shadow, annotation);
                if (
                        is_pack_type(shadow, parameter_type)
                     && kind != T2_PARAMETER_KEYWORD_REST
                ) kind = T2_PARAMETER_PACK;
                positional_closed |= kind == T2_PARAMETER_POSITIONAL_REST
                                  || kind == T2_PARAMETER_PACK;
                parameters[i] = (T2ParameterSpec) {
                        .name = name,
                        .type = parameter_type,
                        .kind = kind,
                        .required = required
                };
        }
        T2Type result = lower_type(shadow, expression->right);
        T2Type callable = t2_callable(
                shadow->universe,
                parameters,
                count,
                result,
                t2_primitive(shadow->universe, T2_TYPE_NEVER),
                t2_primitive(shadow->universe, T2_TYPE_NIL)
        );
        free(parameters);
        return callable;
}

typedef struct types2_legacy_type_entry {
        Type const *source;
        T2Type result;
        bool active;
} Types2LegacyTypeEntry;

typedef struct types2_legacy_type_import {
        Types2Shadow *shadow;
        Types2LegacyTypeEntry *entries;
        size_t count;
        size_t capacity;
} Types2LegacyTypeImport;

static T2Type
import_materialized_legacy_type_x(
        Types2LegacyTypeImport *import,
        Type const *source,
        unsigned depth
);

static bool
import_materialized_legacy_types(
        Types2LegacyTypeImport *import,
        TypeVector const *sources,
        unsigned depth,
        T2Type **types_out,
        size_t *count_out
)
{
        size_t count = (size_t)vN(*sources);
        T2Type *types = count == 0 ? NULL : malloc(count * sizeof *types);
        if (count != 0 && types == NULL) {
                import->shadow->failed = true;
                return false;
        }
        for (size_t i = 0; i < count; ++i) {
                types[i] = import_materialized_legacy_type_x(
                        import,
                        v__(*sources, (int)i),
                        depth + 1
                );
                if (types[i] == T2_TYPE_INVALID) {
                        free(types);
                        return false;
                }
        }
        *types_out = types;
        *count_out = count;
        return true;
}

static T2Type
import_materialized_legacy_object(
        Types2LegacyTypeImport *import,
        Type const *source,
        unsigned depth
)
{
        Types2Shadow *shadow = import->shadow;
        if (source->class == NULL) return T2_TYPE_INVALID;
        T2Type primitive = primitive_class_type(shadow, source->class->i);
        if (primitive != T2_TYPE_INVALID && vN(source->args) == 0) {
                return primitive;
        }

        Types2Nominal *nominal = ensure_nominal(
                shadow,
                source->class->i,
                source->class->name,
                (size_t)vN(source->args)
        );
        if (nominal == NULL) return T2_TYPE_INVALID;
        /* Importing nested arguments can discover more nominal declarations
         * and grow shadow->nominals.  Copy the immutable identity first. */
        uint64_t nominal_symbol = nominal->symbol;
        size_t nominal_arity = nominal->arity;
        T2Type *arguments = NULL;
        size_t count = 0;
        if (!import_materialized_legacy_types(
                import,
                &source->args,
                depth,
                &arguments,
                &count
        )) return T2_TYPE_INVALID;
        T2Type result = T2_TYPE_INVALID;
        if (
                (source->class->i == CLASS_REGEX || source->class->i == CLASS_REGEXV)
             && count == 1
             && nominal_arity == 0
        ) {
                T2Type base = t2_nominal(
                        shadow->universe,
                        nominal_symbol,
                        NULL,
                        0
                );
                result = t2_refinement(shadow->universe, base, arguments[0]);
        } else if (count == nominal_arity) {
                result = t2_nominal(
                        shadow->universe,
                        nominal_symbol,
                        arguments,
                        count
                );
        }
        free(arguments);
        return result;
}

static T2Type
import_materialized_legacy_tuple(
        Types2LegacyTypeImport *import,
        Type const *source,
        unsigned depth
)
{
        Types2Shadow *shadow = import->shadow;
        size_t count = (size_t)vN(source->types);
        bool named = false;
        for (size_t i = 0; i < count; ++i) {
                named |= i < (size_t)vN(source->names)
                      && v__(source->names, (int)i) != NULL;
        }
        if (!named) {
                T2Type *items = NULL;
                size_t item_count = 0;
                if (!import_materialized_legacy_types(
                        import,
                        &source->types,
                        depth,
                        &items,
                        &item_count
                )) return T2_TYPE_INVALID;
                T2Type result = t2_tuple(
                        shadow->universe,
                        items,
                        item_count
                );
                free(items);
                return result;
        }

        T2FieldSpec *fields = count == 0 ? NULL : calloc(count, sizeof *fields);
        if (count != 0 && fields == NULL) {
                shadow->failed = true;
                return T2_TYPE_INVALID;
        }
        for (size_t i = 0; i < count; ++i) {
                char const *name = i < (size_t)vN(source->names)
                                 ? v__(source->names, (int)i)
                                 : NULL;
                if (name == NULL) {
                        free(fields);
                        return T2_TYPE_INVALID;
                }
                fields[i] = (T2FieldSpec) {
                        .name = name,
                        .type = import_materialized_legacy_type_x(
                                import,
                                v__(source->types, (int)i),
                                depth + 1
                        ),
                        .presence = i < (size_t)vN(source->required)
                                 && !v__(source->required, (int)i)
                                  ? T2_PRESENCE_OPTIONAL
                                  : T2_PRESENCE_REQUIRED,
                        .capability = T2_FIELD_WRITABLE
                };
                if (fields[i].type == T2_TYPE_INVALID) {
                        free(fields);
                        return T2_TYPE_INVALID;
                }
        }
        T2Type result = t2_record(
                shadow->universe,
                fields,
                count,
                T2_TYPE_INVALID,
                source->closed ? T2_RECORD_EXACT : T2_RECORD_OPEN
        );
        free(fields);
        return result;
}

static T2Type
import_materialized_legacy_function(
        Types2LegacyTypeImport *import,
        Type const *source,
        unsigned depth
)
{
        Types2Shadow *shadow = import->shadow;
        if (vN(source->constraints) != 0) return T2_TYPE_INVALID;
        size_t count = (size_t)vN(source->params);
        T2ParameterSpec *parameters = count == 0
                                    ? NULL
                                    : calloc(count, sizeof *parameters);
        if (count != 0 && parameters == NULL) {
                shadow->failed = true;
                return T2_TYPE_INVALID;
        }
        bool positional_closed = false;
        for (size_t i = 0; i < count; ++i) {
                Param const *parameter = v_(source->params, (int)i);
                T2ParameterKind kind = parameter->pack
                                     ? T2_PARAMETER_PACK
                                     : parameter->kws
                                       ? T2_PARAMETER_KEYWORD_REST
                                       : parameter->rest
                                         ? T2_PARAMETER_POSITIONAL_REST
                                         : parameter->name == NULL
                                           ? T2_PARAMETER_POSITIONAL_ONLY
                                           : T2_PARAMETER_POSITIONAL_OR_KEYWORD;
                if (
                        positional_closed
                     && kind == T2_PARAMETER_POSITIONAL_OR_KEYWORD
                ) kind = T2_PARAMETER_KEYWORD_ONLY;
                positional_closed |= kind == T2_PARAMETER_POSITIONAL_REST
                                  || kind == T2_PARAMETER_PACK;
                parameters[i] = (T2ParameterSpec) {
                        .name = parameter->name,
                        .type = import_materialized_legacy_type_x(
                                import,
                                parameter->type,
                                depth + 1
                        ),
                        .kind = kind,
                        .required = kind == T2_PARAMETER_POSITIONAL_REST
                                 || kind == T2_PARAMETER_KEYWORD_REST
                                 || kind == T2_PARAMETER_PACK
                                  ? false
                                  : parameter->required
                };
                if (parameters[i].type == T2_TYPE_INVALID) {
                        free(parameters);
                        return T2_TYPE_INVALID;
                }
        }
        T2Type result = import_materialized_legacy_type_x(
                import,
                source->rt,
                depth + 1
        );
        T2Type yields = source->yields == NULL
                      ? t2_primitive(shadow->universe, T2_TYPE_NEVER)
                      : import_materialized_legacy_type_x(
                              import,
                              source->yields,
                              depth + 1
                        );
        T2Type sends = source->sends == NULL
                    ? t2_primitive(shadow->universe, T2_TYPE_NIL)
                    : import_materialized_legacy_type_x(
                            import,
                            source->sends,
                            depth + 1
                      );
        T2Type callable = result == T2_TYPE_INVALID
                       || yields == T2_TYPE_INVALID
                       || sends == T2_TYPE_INVALID
                        ? T2_TYPE_INVALID
                        : t2_callable(
                                shadow->universe,
                                parameters,
                                count,
                                result,
                                yields,
                                sends
                          );
        free(parameters);
        return callable;
}

static T2Type
import_materialized_legacy_type_x(
        Types2LegacyTypeImport *import,
        Type const *source,
        unsigned depth
)
{
        Types2Shadow *shadow = import->shadow;
        if (source == NULL || depth > 256) return T2_TYPE_INVALID;
        source = type_resolve_var(source);
        if (source == NULL) return T2_TYPE_INVALID;

        for (size_t i = 0; i < import->count; ++i) {
                if (import->entries[i].source != source) continue;
                return import->entries[i].active
                     ? T2_TYPE_INVALID
                     : import->entries[i].result;
        }
        if (!shadow_reserve(
                shadow,
                (void **)&import->entries,
                &import->capacity,
                import->count + 1,
                sizeof *import->entries
        )) return T2_TYPE_INVALID;
        size_t entry = import->count++;
        import->entries[entry] = (Types2LegacyTypeEntry) {
                .source = source,
                .active = true
        };

        T2Type result = T2_TYPE_INVALID;
        if (source == TYPE_ANY) {
                result = t2_primitive(shadow->universe, T2_TYPE_ANY);
                goto Done;
        }
        if (source == UNKNOWN_TYPE) {
                result = t2_primitive(shadow->universe, T2_TYPE_DYNAMIC);
                goto Done;
        }
        if (source == BOTTOM_TYPE) {
                result = t2_primitive(shadow->universe, T2_TYPE_NEVER);
                goto Done;
        }

        switch (TypeType(source)) {
        case TYPE_NIL:
        case TYPE_NONE:
                result = t2_primitive(shadow->universe, T2_TYPE_NIL);
                break;
        case TYPE_INT:
                result = t2_literal_int(shadow->universe, source->z);
                break;
        case TYPE_STRING:
                result = source->str == NULL
                       ? T2_TYPE_INVALID
                       : t2_literal_string(shadow->universe, source->str);
                break;
        case TYPE_BOOL:
                result = t2_literal_bool(shadow->universe, source->z != 0);
                break;
        case TYPE_RANGE:
        {
                T2Type lower = source->lo == NULL
                             ? T2_TYPE_INVALID
                             : import_materialized_legacy_type_x(
                                     import,
                                     source->lo,
                                     depth + 1
                               );
                T2Type upper = source->hi == NULL
                             ? T2_TYPE_INVALID
                             : import_materialized_legacy_type_x(
                                     import,
                                     source->hi,
                                     depth + 1
                               );
                result = (source->lo != NULL && lower == T2_TYPE_INVALID)
                      || (source->hi != NULL && upper == T2_TYPE_INVALID)
                       ? T2_TYPE_INVALID
                       : t2_integer_range(shadow->universe, lower, upper, false);
                break;
        }
        case TYPE_OBJECT:
                result = import_materialized_legacy_object(import, source, depth);
                break;
        case TYPE_TAG:
        {
                Types2Nominal *nominal = ensure_tag_nominal(
                        shadow,
                        source->tag,
                        shadow->ty == NULL ? NULL : tags_name(shadow->ty, source->tag)
                );
                T2Type payload = t2_primitive(shadow->universe, T2_TYPE_NEVER);
                result = nominal == NULL
                       ? T2_TYPE_INVALID
                       : t2_nominal(shadow->universe, nominal->symbol, &payload, 1);
                break;
        }
        case TYPE_CLASS:
        {
                if (source->class == NULL) break;
                Types2Nominal *nominal = ensure_nominal(
                        shadow,
                        source->class->i,
                        source->class->name,
                        0
                );
                if (nominal == NULL) break;
                T2Type *arguments = nominal->arity == 0
                                  ? NULL
                                  : malloc(nominal->arity * sizeof *arguments);
                if (nominal->arity != 0 && arguments == NULL) {
                        shadow->failed = true;
                        break;
                }
                for (size_t i = 0; i < nominal->arity; ++i) {
                        arguments[i] = t2_primitive(shadow->universe, T2_TYPE_DYNAMIC);
                }
                T2Type instance = t2_nominal(
                        shadow->universe,
                        nominal->symbol,
                        arguments,
                        nominal->arity
                );
                free(arguments);
                T2Type dynamic = t2_primitive(shadow->universe, T2_TYPE_DYNAMIC);
                result = t2_type_value(shadow->universe, instance, dynamic);
                break;
        }
        case TYPE_TUPLE:
                result = import_materialized_legacy_tuple(import, source, depth);
                break;
        case TYPE_LIST:
        {
                T2Type *items = NULL;
                size_t count = 0;
                if (import_materialized_legacy_types(
                        import,
                        &source->types,
                        depth,
                        &items,
                        &count
                )) {
                        result = t2_tuple(shadow->universe, items, count);
                }
                free(items);
                break;
        }
        case TYPE_SEQUENCE:
        {
                T2Type *items = NULL;
                size_t count = 0;
                if (import_materialized_legacy_types(
                        import,
                        &source->types,
                        depth,
                        &items,
                        &count
                )) {
                        result = t2_pack(
                                shadow->universe,
                                items,
                                count,
                                T2_TYPE_INVALID
                        );
                }
                free(items);
                break;
        }
        case TYPE_UNION:
        case TYPE_INTERSECT:
        {
                T2Type *arms = NULL;
                size_t count = 0;
                if (import_materialized_legacy_types(
                        import,
                        &source->types,
                        depth,
                        &arms,
                        &count
                )) {
                        result = TypeType(source) == TYPE_UNION
                               ? t2_union(shadow->universe, arms, count)
                               : t2_intersection(shadow->universe, arms, count);
                }
                free(arms);
                break;
        }
        case TYPE_FUNCTION:
                result = import_materialized_legacy_function(import, source, depth);
                break;
        case TYPE_TYPE:
        {
                T2Type instance = import_materialized_legacy_type_x(
                        import,
                        source->_type,
                        depth + 1
                );
                T2Type dynamic = t2_primitive(shadow->universe, T2_TYPE_DYNAMIC);
                result = instance == T2_TYPE_INVALID
                       ? T2_TYPE_INVALID
                       : t2_type_value(shadow->universe, instance, dynamic);
                break;
        }
        case TYPE_ALIAS:
                result = import_materialized_legacy_type_x(
                        import,
                        source->_type,
                        depth + 1
                );
                break;
        case TYPE_COMPUTED:
                if (source->val != NULL) {
                        result = import_materialized_legacy_type_x(
                                import,
                                source->val,
                                depth + 1
                        );
                }
                break;
        case TYPE_ERROR:
                result = t2_primitive(shadow->universe, T2_TYPE_ERROR);
                break;
        case TYPE_BOTTOM:
                result = source->fixed
                       ? t2_primitive(shadow->universe, T2_TYPE_DYNAMIC)
                       : t2_primitive(shadow->universe, T2_TYPE_NEVER);
                break;
        case TYPE_VARIABLE:
        case TYPE_SUBSCRIPT:
        case TYPE_SLICE:
                break;
        }

Done:
        import->entries[entry].result = result;
        import->entries[entry].active = false;
        return result;
}

static T2Type
materialized_computed_type_result(
        Types2Shadow *shadow,
        Expr const *expression
)
{
        if (
                expression == NULL
             || expression->type != EXPRESSION_TYPE
             || expression->_type == NULL
             || TypeType(expression->_type) != TYPE_COMPUTED
             || expression->_type->val == NULL
        ) return T2_TYPE_INVALID;
        Types2LegacyTypeImport import = { .shadow = shadow };
        T2Type result = import_materialized_legacy_type_x(
                &import,
                expression->_type->val,
                0
        );
        free(import.entries);
        return result;
}

static T2Type
lower_type(Types2Shadow *shadow, Expr const *source)
{
        Expr const *expression = source == NULL ? NULL : unfurl(source);
        if (expression == NULL) return T2_TYPE_INVALID;

        T2Type result = T2_TYPE_INVALID;
        switch (expression->type) {
        case EXPRESSION_IDENTIFIER:
        case EXPRESSION_PACK:
        case EXPRESSION_MATCH_REST:
                result = lower_named_type(shadow, expression, expression, true);
                break;

        case EXPRESSION_MEMBER_ACCESS:
        case EXPRESSION_SELF_ACCESS:
        case EXPRESSION_RESOLVED:
                result = lower_named_type(shadow, expression, expression, false);
                break;

        case EXPRESSION_MATCH_ANY:
                result = t2_primitive(shadow->universe, T2_TYPE_DYNAMIC);
                break;
        case EXPRESSION_NIL:
                result = t2_primitive(shadow->universe, T2_TYPE_NIL);
                break;
        case EXPRESSION_INTEGER:
                result = t2_literal_int(shadow->universe, expression->integer);
                break;
        case EXPRESSION_STRING:
                result = t2_literal_string(shadow->universe, expression->string);
                break;
        case EXPRESSION_BOOLEAN:
                result = t2_literal_bool(shadow->universe, expression->boolean);
                break;
        case EXPRESSION_TYPE:
                result = lower_type(shadow, expression->constraint);
                if (t2_type_kind(shadow->universe, result) == T2_TYPE_COMPUTED) {
                        T2Type materialized = materialized_computed_type_result(
                                shadow,
                                expression
                        );
                        if (
                                materialized != T2_TYPE_INVALID
                             && t2_computed_type_set_result(
                                    shadow->universe,
                                    result,
                                    materialized
                                )
                        ) {
                                shadow->materialized_computed_types += 1;
                                retract_deferral(shadow, TYPES2_DEFER_COMPUTED_TYPE);
                        }
                }
                break;
        case EXPRESSION_PREFIX_QUESTION:
        {
                T2Type inner = lower_type(shadow, expression->operand);
                T2Type nil = t2_primitive(shadow->universe, T2_TYPE_NIL);
                result = t2_union(shadow->universe, (T2Type[]){ inner, nil }, 2);
                break;
        }
        case EXPRESSION_SPREAD:
                result = t2_pack_expansion(
                        shadow->universe,
                        lower_type(shadow, expression->value)
                );
                break;
        case EXPRESSION_DOT_DOT_DOT:
                result = t2_pack_expansion(
                        shadow->universe,
                        lower_type(shadow, expression->right)
                );
                break;
        case EXPRESSION_PACK_UNION:
                result = t2_pack_fold_union(
                        shadow->universe,
                        lower_type(shadow, expression->operand)
                );
                break;
        case EXPRESSION_PACK_INTERSECT:
                result = t2_pack_fold_intersection(
                        shadow->universe,
                        lower_type(shadow, expression->operand)
                );
                break;
        case EXPRESSION_DOT_DOT:
                result = t2_integer_range(
                        shadow->universe,
                        expression->left == NULL
                            ? T2_TYPE_INVALID
                            : lower_type(shadow, expression->left),
                        expression->right == NULL
                            ? T2_TYPE_INVALID
                            : lower_type(shadow, expression->right),
                        false
                );
                break;
        case EXPRESSION_TYPE_UNION:
        case EXPRESSION_LIST:
        {
                size_t count = (size_t)vN(expression->es);
                T2Type *types = count == 0 ? NULL : malloc(count * sizeof *types);
                if (count != 0 && types == NULL) {
                        shadow->failed = true;
                        break;
                }
                for (size_t i = 0; i < count; ++i) {
                        types[i] = lower_type(shadow, v__(expression->es, (int)i));
                }
                bool invalid_pack_placement = false;
                for (size_t i = 0; i < count; ++i) {
                        invalid_pack_placement |= is_pack_type(shadow, types[i])
                                               && (
                                                        expression->type
                                                            == EXPRESSION_TYPE_UNION
                                                     || i + 1 != count
                                                  );
                }
                if (invalid_pack_placement) {
                        add_diagnostic(
                                shadow,
                                expression,
                                TYPES2_DIAGNOSTIC_ERROR,
                                "pack-placement",
                                T2_TYPE_INVALID,
                                T2_TYPE_INVALID,
                                "a type pack may only appear in the final sequence position"
                        );
                        result = t2_primitive(shadow->universe, T2_TYPE_ERROR);
                        free(types);
                        break;
                }
                if (expression->type == EXPRESSION_TYPE_UNION) {
                        result = t2_union(shadow->universe, types, count);
                } else if (count != 0 && is_pack_type(shadow, types[count - 1])) {
                        result = t2_pack(
                                shadow->universe,
                                types,
                                count - 1,
                                types[count - 1]
                        );
                } else {
                        result = t2_pack(
                                shadow->universe,
                                types,
                                count,
                                T2_TYPE_INVALID
                        );
                }
                free(types);
                break;
        }
        case EXPRESSION_BIT_OR:
        case EXPRESSION_BIT_AND:
        {
                T2Type left = lower_type(shadow, expression->left);
                T2Type right = lower_type(shadow, expression->right);
                result = expression->type == EXPRESSION_BIT_OR
                       ? t2_union(shadow->universe, (T2Type[]){ left, right }, 2)
                       : t2_intersection(shadow->universe, (T2Type[]){ left, right }, 2);
                break;
        }
        case EXPRESSION_TUPLE:
        case EXPRESSION_TUPLE_SPEC:
        {
                size_t count = (size_t)vN(expression->es);
                if (tuple_is_record(expression)) {
                        T2FieldSpec *fields = count == 0
                                            ? NULL
                                            : calloc(count, sizeof *fields);
                        if (count != 0 && fields == NULL) {
                                shadow->failed = true;
                                break;
                        }
                        for (size_t i = 0; i < count; ++i) {
                                fields[i] = (T2FieldSpec) {
                                        .name = i < (size_t)vN(expression->names)
                                              ? v__(expression->names, (int)i)
                                              : NULL,
                                        .type = lower_type(
                                                shadow,
                                                v__(expression->es, (int)i)
                                        ),
                                        .presence = i < (size_t)vN(expression->required)
                                                 && !v__(expression->required, (int)i)
                                                  ? T2_PRESENCE_OPTIONAL
                                                  : T2_PRESENCE_REQUIRED,
                                        .capability = T2_FIELD_WRITABLE
                                };
                        }
                        bool packed_field = false;
                        for (size_t i = 0; i < count; ++i) {
                                packed_field |= is_pack_type(shadow, fields[i].type);
                        }
                        if (packed_field) {
                                add_diagnostic(
                                        shadow,
                                        expression,
                                        TYPES2_DIAGNOSTIC_ERROR,
                                        "pack-placement",
                                        T2_TYPE_INVALID,
                                        T2_TYPE_INVALID,
                                        "a pack cannot be used as a named record field"
                                );
                                result = t2_primitive(
                                        shadow->universe,
                                        T2_TYPE_ERROR
                                );
                        } else {
                                result = t2_record(
                                        shadow->universe,
                                        fields,
                                        count,
                                        T2_TYPE_INVALID,
                                        T2_RECORD_OPEN
                                );
                        }
                        free(fields);
                } else {
                        T2Type *items = count == 0 ? NULL : malloc(count * sizeof *items);
                        if (count != 0 && items == NULL) {
                                shadow->failed = true;
                                break;
                        }
                        for (size_t i = 0; i < count; ++i) {
                                items[i] = lower_type(shadow, v__(expression->es, (int)i));
                        }
                        bool invalid_pack_placement = false;
                        for (size_t i = 0; i + 1 < count; ++i) {
                                invalid_pack_placement |= is_pack_type(
                                        shadow,
                                        items[i]
                                );
                        }
                        if (invalid_pack_placement) {
                                add_diagnostic(
                                        shadow,
                                        expression,
                                        TYPES2_DIAGNOSTIC_ERROR,
                                        "pack-placement",
                                        T2_TYPE_INVALID,
                                        T2_TYPE_INVALID,
                                        "a tuple pack may only appear in final position"
                                );
                                result = t2_primitive(
                                        shadow->universe,
                                        T2_TYPE_ERROR
                                );
                        } else if (
                                count != 0
                             && is_pack_type(shadow, items[count - 1])
                        ) {
                                result = t2_variadic_tuple(
                                        shadow->universe,
                                        items,
                                        count - 1,
                                        items[count - 1]
                                );
                        } else {
                                result = t2_tuple(shadow->universe, items, count);
                        }
                        free(items);
                }
                break;
        }
        case EXPRESSION_FUNCTION_TYPE:
                result = lower_function_type(shadow, expression);
                break;
        case EXPRESSION_SUBSCRIPT:
        {
                Expr const *container = unfurl(expression->container);
                Expr const *name = type_reference_leaf(container);
                bool tag_application = false;
                if (name != NULL && name->symbol != NULL) {
                        if (
                                (
                                        SymbolIsTag(name->symbol)
                                     || SymbolIsBuiltin(name->symbol)
                                )
                             && name->symbol->tag > 0
                        ) {
                                tag_application = true;
                        } else if (
                                SymbolIsMember(name->symbol)
                             && name->identifier != NULL
                             && shadow->ty != NULL
                        ) {
                                int tag = tags_lookup(shadow->ty, name->identifier);
                                tag_application = tag > 0;
                        }
                }
                size_t count;
                if (tag_application) {
                        /* A tag always has one payload.  Parenthesized tuple
                         * payloads are not a list of generic arguments. */
                        count = 1;
                } else if (expression->subscript->type == EXPRESSION_LIST) {
                        count = (size_t)vN(expression->subscript->es);
                }
                else count = 1;
                T2Type *arguments = count == 0 ? NULL : malloc(count * sizeof *arguments);
                if (count != 0 && arguments == NULL) {
                        shadow->failed = true;
                        break;
                }
                for (size_t i = 0; i < count; ++i) {
                        Expr const *argument = tag_application
                                             ? expression->subscript
                                             : count == 1
                                             && expression->subscript->type != EXPRESSION_LIST
                                              ? expression->subscript
                                              : v__(expression->subscript->es, (int)i);
                        arguments[i] = lower_type(shadow, argument);
                }
                if (
                        name != NULL
                     && name->identifier != NULL
                     && strcmp(name->identifier, "Type") == 0
                ) {
                        if (count == 1) {
                                T2Type dynamic = t2_primitive(
                                        shadow->universe,
                                        T2_TYPE_DYNAMIC
                                );
                                result = t2_type_value(
                                        shadow->universe,
                                        arguments[0],
                                        dynamic
                                );
                        } else if (shadow->building_interface) {
                                result = t2_primitive(
                                        shadow->universe,
                                        T2_TYPE_DYNAMIC
                                );
                        } else {
                                add_diagnostic(
                                        shadow,
                                        expression,
                                        TYPES2_DIAGNOSTIC_ERROR,
                                        "generic-arity",
                                        T2_TYPE_INVALID,
                                        T2_TYPE_INVALID,
                                        "`Type` expects 1 type argument, but %zu were provided",
                                        count
                                );
                                result = t2_primitive(
                                        shadow->universe,
                                        T2_TYPE_ERROR
                                );
                        }
                        free(arguments);
                        break;
                }
                Types2Alias *alias = name == NULL
                                   ? NULL
                                   : find_or_import_alias(shadow, name->symbol);
                if (alias != NULL) {
                        Symbol const *alias_symbol = alias->symbol;
                        if (alias->state == TYPES2_ALIAS_RESOLVING) {
                                result = regular_recursive_alias_arguments(
                                        shadow,
                                        alias,
                                        arguments,
                                        count
                                ) ? t2_recursive_variable(
                                        shadow->universe,
                                        alias->binder
                                    ) : T2_TYPE_INVALID;
                                if (
                                        result == T2_TYPE_INVALID
                                     && !shadow->building_interface
                                ) {
                                        if (count == alias->arity) {
                                                add_diagnostic(
                                                        shadow,
                                                        expression,
                                                        TYPES2_DIAGNOSTIC_ERROR,
                                                        "nonregular-recursive-alias",
                                                        T2_TYPE_INVALID,
                                                        T2_TYPE_INVALID,
                                                        "recursive alias `%s` must recur with its declared type parameters in the same order",
                                                        alias->symbol->identifier
                                                );
                                        } else {
                                                add_diagnostic(
                                                        shadow,
                                                        expression,
                                                        TYPES2_DIAGNOSTIC_ERROR,
                                                        "generic-arity",
                                                        T2_TYPE_INVALID,
                                                        T2_TYPE_INVALID,
                                                        "`%s` expects %zu type argument%s, but %zu were provided",
                                                        alias->symbol->identifier,
                                                        alias->arity,
                                                        alias->arity == 1 ? "" : "s",
                                                        count
                                                );
                                        }
                                        result = t2_primitive(
                                                shadow->universe,
                                                T2_TYPE_ERROR
                                        );
                                }
                        } else {
                                (void)resolve_alias(shadow, alias, name);
                                alias = find_alias(shadow, alias_symbol);
                                if (alias == NULL) {
                                        free(arguments);
                                        shadow->failed = true;
                                        return T2_TYPE_INVALID;
                                }
                                result = t2_scheme_apply(
                                        alias->scheme,
                                        shadow->solver,
                                        arguments,
                                        count,
                                        alias->symbol->identifier
                                );
                        }
                        if (result == T2_TYPE_INVALID) {
                                if (shadow->building_interface) {
                                        result = t2_primitive(
                                                shadow->universe,
                                                T2_TYPE_DYNAMIC
                                        );
                                } else {
                                if (count == alias->arity) {
                                        add_diagnostic(
                                                shadow,
                                                expression,
                                                TYPES2_DIAGNOSTIC_ERROR,
                                                "invalid-type-application",
                                                T2_TYPE_INVALID,
                                                T2_TYPE_INVALID,
                                                "could not instantiate type alias `%s` with the supplied arguments",
                                                alias->symbol->identifier
                                        );
                                } else {
                                        add_diagnostic(
                                                shadow,
                                                expression,
                                                TYPES2_DIAGNOSTIC_ERROR,
                                                "generic-arity",
                                                T2_TYPE_INVALID,
                                                T2_TYPE_INVALID,
                                                "`%s` expects %zu type argument%s, but %zu were provided",
                                                alias->symbol->identifier,
                                                alias->arity,
                                                alias->arity == 1 ? "" : "s",
                                                count
                                        );
                                }
                                result = t2_primitive(shadow->universe, T2_TYPE_ERROR);
                                }
                        }
                } else if (name != NULL) {
                        Types2Nominal *nominal = ensure_symbol_nominal(
                                shadow,
                                name->symbol,
                                name->identifier
                        );
                        if (nominal != NULL) {
                                if (
                                        nominal->class_id == CLASS_REGEX
                                     && nominal->arity == 0
                                     && count == 1
                                ) {
                                        T2Type base = t2_nominal(
                                                shadow->universe,
                                                nominal->symbol,
                                                NULL,
                                                0
                                        );
                                        result = t2_refinement(
                                                shadow->universe,
                                                base,
                                                arguments[0]
                                        );
                                } else {
                                        result = apply_nominal(
                                                shadow,
                                                nominal,
                                                arguments,
                                                count,
                                                expression
                                        );
                                }
                        } else {
                                if (shadow->building_interface) {
                                        result = t2_primitive(
                                                shadow->universe,
                                                T2_TYPE_DYNAMIC
                                        );
                                } else {
                                        add_diagnostic(
                                                shadow,
                                                expression,
                                                TYPES2_DIAGNOSTIC_ERROR,
                                                "not-generic",
                                                T2_TYPE_INVALID,
                                                T2_TYPE_INVALID,
                                                "type application target `%s` is not a generic class or alias",
                                                name->identifier == NULL
                                                        ? "<type>"
                                                        : name->identifier
                                        );
                                        result = t2_primitive(
                                                shadow->universe,
                                                T2_TYPE_ERROR
                                        );
                                }
                        }
                } else {
                        if (shadow->building_interface) {
                                result = t2_primitive(shadow->universe, T2_TYPE_DYNAMIC);
                                free(arguments);
                                break;
                        }
                        add_diagnostic(
                                shadow,
                                expression,
                                TYPES2_DIAGNOSTIC_ERROR,
                                "not-generic",
                                T2_TYPE_INVALID,
                                T2_TYPE_INVALID,
                                "type application target expression `%s` is not a generic class or alias",
                                container == NULL
                                        ? "<missing>"
                                        : construct_name(container->type)
                        );
                        result = t2_primitive(shadow->universe, T2_TYPE_ERROR);
                }
                free(arguments);
                break;
        }
        case EXPRESSION_ARRAY:
        {
                T2Type argument = vN(expression->elements) == 0
                                ? t2_primitive(shadow->universe, T2_TYPE_DYNAMIC)
                                : lower_type(shadow, v__(expression->elements, 0));
                result = nominal_application(
                        shadow,
                        CLASS_ARRAY,
                        "Array",
                        &argument,
                        1,
                        expression
                );
                break;
        }
        case EXPRESSION_TYPE_OF:
                result = node_type(shadow, expression->operand);
                if (result == T2_TYPE_INVALID) {
                        defer_node(shadow, TYPES2_DEFER_TYPEOF_UNRESOLVED, expression, NULL);
                        result = t2_primitive(shadow->universe, T2_TYPE_DYNAMIC);
                }
                break;
        case EXPRESSION_FUNCTION_CALL:
        {
                size_t count = (size_t)vN(expression->args);
                T2Type *arguments = count == 0
                                  ? NULL
                                  : malloc(count * sizeof *arguments);
                if (count != 0 && arguments == NULL) {
                        shadow->failed = true;
                        break;
                }
                for (size_t i = 0; i < count; ++i) {
                        arguments[i] = lower_type(
                                shadow,
                                v__(expression->args, (int)i)
                        );
                }
                Expr const *callee = type_reference_leaf(expression->function);
                Types2Node *node = remember_node(
                        shadow,
                        expression->function,
                        expression->function == NULL
                            ? EXPRESSION_ERROR
                            : expression->function->type,
                        TYPES2_ROLE_TYPE
                );
                char const *name = callee != NULL && callee->identifier != NULL
                                 ? callee->identifier
                                 : expression->function == NULL
                                   ? "<type-function>"
                                   : construct_name(expression->function->type);
                result = node == NULL
                       ? T2_TYPE_INVALID
                       : t2_computed_type(
                               shadow->universe,
                               node->id,
                               name,
                               arguments,
                               count
                         );
                free(arguments);
                shadow->computed_type_terms += result != T2_TYPE_INVALID;
                defer_node(shadow, TYPES2_DEFER_COMPUTED_TYPE, expression, name);
                break;
        }
        default:
                shadow->unsupported_nodes += 1;
                shadow->unsupported_constructs[expression->type] += 1;
                result = t2_primitive(shadow->universe, T2_TYPE_DYNAMIC);
                break;
        }

        if (result == T2_TYPE_INVALID && !shadow->failed) {
                result = t2_primitive(shadow->universe, T2_TYPE_ERROR);
        }
        set_node_type(shadow, expression, result);
        return result;
}

static T2Type
resolved_type_head(
        Types2Shadow *shadow,
        T2Type type,
        T2SolutionPreference preference
)
{
        for (unsigned depth = 0; depth < 64; ++depth) {
                T2Type computed = t2_type_resolve_computed(
                        shadow->universe,
                        type
                );
                if (computed == T2_TYPE_INVALID) return type;
                if (computed != type) {
                        type = computed;
                        continue;
                }
                T2TypeKind kind = t2_type_kind(shadow->universe, type);
                /* An unresolved compile-time type promise is an explicit
                 * shadow boundary, not evidence that an operation is invalid.
                 * Keep the canonical promise in annotations and snapshots,
                 * but use Dynamic for elimination until the single-evaluation
                 * broker supplies its concrete result.  The creation site has
                 * already been counted as deferred. */
                if (kind == T2_TYPE_COMPUTED) {
                        return t2_primitive(
                                shadow->universe,
                                T2_TYPE_DYNAMIC
                        );
                }
                if (kind != T2_TYPE_META) return type;
                T2Type solution = t2_solver_solution(
                        shadow->solver,
                        type,
                        preference
                );
                if (solution == T2_TYPE_INVALID || solution == type) return type;
                type = solution;
        }
        return type;
}

static bool
is_dynamic_type(Types2Shadow *shadow, T2Type type)
{
        return t2_type_kind(
                shadow->universe,
                resolved_type_head(shadow, type, T2_PREFER_LOWER_BOUND)
        ) == T2_TYPE_DYNAMIC;
}

static T2Type
resolved_operation_type(
        Types2Shadow *shadow,
        T2Type type,
        T2SolutionPreference preference
)
{
        type = resolved_type_head(shadow, type, preference);
        for (unsigned depth = 0; depth < 64; ++depth) {
                T2TypeKind kind = t2_type_kind(shadow->universe, type);
                if (kind != T2_TYPE_META && kind != T2_TYPE_VARIABLE) break;
                T2Type assumed = T2_TYPE_INVALID;
                for (size_t i = 0; i < shadow->upper_assumption_count; ++i) {
                        Types2UpperAssumption const *entry =
                                &shadow->upper_assumptions[i];
                        if (entry->subtype != type) continue;
                        assumed = assumed == T2_TYPE_INVALID
                                ? entry->supertype
                                : t2_meet(
                                        shadow->universe,
                                        assumed,
                                        entry->supertype
                                  );
                }
                if (assumed == T2_TYPE_INVALID || assumed == type) break;
                type = resolved_type_head(shadow, assumed, preference);
        }
        if (t2_type_kind(shadow->universe, type) != T2_TYPE_RECORD) return type;
        T2Type zonked = t2_solver_zonk(shadow->solver, type, preference);
        return zonked == T2_TYPE_INVALID ? type : zonked;
}

static bool
type_contains_dynamic_x(Types2Shadow *shadow, T2Type type, unsigned depth)
{
        if (type == T2_TYPE_INVALID || depth > 256) return false;
        type = resolved_type_head(shadow, type, T2_PREFER_LOWER_BOUND);
        T2TypeKind kind = t2_type_kind(shadow->universe, type);
        if (kind == T2_TYPE_DYNAMIC) return true;
        for (size_t i = 0; i < t2_type_arity(shadow->universe, type); ++i) {
                if (type_contains_dynamic_x(
                        shadow,
                        t2_type_child(shadow->universe, type, i),
                        depth + 1
                )) return true;
        }
        return false;
}

static bool
type_contains_dynamic(Types2Shadow *shadow, T2Type type)
{
        return type_contains_dynamic_x(shadow, type, 0);
}

static bool
type_admits_nil(Types2Shadow *shadow, T2Type type)
{
        T2TypeKind kind = t2_type_kind(
                shadow->universe,
                resolved_type_head(shadow, type, T2_PREFER_LOWER_BOUND)
        );
        if (
                kind == T2_TYPE_DYNAMIC
             || kind == T2_TYPE_UNKNOWN
             || kind == T2_TYPE_ANY
             || kind == T2_TYPE_ERROR
        ) return true;
        return t2_subtype(
                shadow->universe,
                t2_primitive(shadow->universe, T2_TYPE_NIL),
                type
        ) == T2_RELATION_YES;
}

static void default_dynamic_callable_metas(
        Types2Shadow *shadow,
        T2Type type,
        unsigned depth
);

static bool
constrain_gradually(
        Types2Shadow *shadow,
        Expr const *site,
        T2Type actual,
        T2Type expected,
        char const *description
)
{
        /* Preserve every ordinary constraint that remains meaningful around
         * an explicit Dynamic leaf.  A pure consistency probe would accept a
         * value such as pack[Int, Dynamic] against a fresh pack meta without
         * ever binding that meta, leaving the instantiated scheme's
         * predicates permanently asleep.  Strict solving is therefore the
         * first transaction.  A deferred strict result is still ambiguous:
         * roll it back before defaulting otherwise unconstrained metas to
         * Dynamic, rather than retaining an obligation that gradual
         * consistency has already authorized. */
        T2SolverMark mark = t2_solver_mark(shadow->solver);
        T2Relation relation = t2_solver_constrain_subtype(
                shadow->solver,
                actual,
                expected,
                source_provenance(shadow, site, description)
        );
        if (relation == T2_RELATION_YES && !t2_solver_failed(shadow->solver)) {
                t2_solver_commit(shadow->solver, mark);
                return true;
        }
        t2_solver_rollback(shadow->solver, mark);

        default_dynamic_callable_metas(shadow, actual, 0);
        default_dynamic_callable_metas(shadow, expected, 0);
        return !shadow->failed
            && !t2_solver_failed(shadow->solver)
            && t2_consistent(shadow->universe, actual, expected)
                != T2_RELATION_NO;
}

static bool
constrain_type(
        Types2Shadow *shadow,
        Expr const *site,
        T2Type actual,
        T2Type expected,
        char const *code,
        char const *description
)
{
        if (
                actual == T2_TYPE_INVALID
             || expected == T2_TYPE_INVALID
             || t2_type_kind(shadow->universe, actual) == T2_TYPE_ERROR
             || t2_type_kind(shadow->universe, expected) == T2_TYPE_ERROR
        ) return true;
        if (
                type_contains_dynamic(shadow, actual)
             || type_contains_dynamic(shadow, expected)
        ) {
                return constrain_gradually(
                        shadow,
                        site,
                        actual,
                        expected,
                        description
                );
        }

        T2SolverMark mark = t2_solver_mark(shadow->solver);
        char const *provenance = source_provenance(shadow, site, description);
        T2Relation relation = t2_solver_constrain_subtype(
                shadow->solver,
                actual,
                expected,
                provenance
        );
        if (relation != T2_RELATION_NO && !t2_solver_failed(shadow->solver)) {
                t2_solver_commit(shadow->solver, mark);
                return true;
        }
        char *explanation = t2_solver_explain_since(shadow->solver, mark);
        t2_solver_rollback(shadow->solver, mark);
        add_diagnostic(
                shadow,
                site,
                TYPES2_DIAGNOSTIC_ERROR,
                code,
                actual,
                expected,
                "%s%s%s",
                description,
                explanation == NULL || *explanation == '\0' ? "" : ": ",
                explanation == NULL ? "" : explanation
        );
        free(explanation);
        return false;
}

static bool
constrain_type_maybe_diagnose(
        Types2Shadow *shadow,
        Expr const *site,
        T2Type actual,
        T2Type expected,
        bool diagnose,
        char const *code,
        char const *description
)
{
        if (diagnose) {
                return constrain_type(
                        shadow,
                        site,
                        actual,
                        expected,
                        code,
                        description
                );
        }
        if (
                actual == T2_TYPE_INVALID
             || expected == T2_TYPE_INVALID
             || t2_type_kind(shadow->universe, actual) == T2_TYPE_ERROR
             || t2_type_kind(shadow->universe, expected) == T2_TYPE_ERROR
        ) return true;
        if (
                type_contains_dynamic(shadow, actual)
             || type_contains_dynamic(shadow, expected)
        ) {
                return constrain_gradually(
                        shadow,
                        site,
                        actual,
                        expected,
                        description
                );
        }

        T2SolverMark mark = t2_solver_mark(shadow->solver);
        T2Relation relation = t2_solver_constrain_subtype(
                shadow->solver,
                actual,
                expected,
                source_provenance(shadow, site, description)
        );
        bool valid = relation != T2_RELATION_NO
                  && relation != T2_RELATION_COMPLEXITY
                  && !t2_solver_failed(shadow->solver);
        if (valid) t2_solver_commit(shadow->solver, mark);
        else t2_solver_rollback(shadow->solver, mark);
        return valid;
}

static bool
constrain_predicate(
        Types2Shadow *shadow,
        Expr const *site,
        T2Predicate predicate,
        char const *code,
        char const *description
)
{
        if (
                predicate.subtype == T2_TYPE_INVALID
             || predicate.supertype == T2_TYPE_INVALID
             || predicate.operand == T2_TYPE_INVALID
        ) return false;
        T2SolverMark mark = t2_solver_mark(shadow->solver);
        predicate.provenance = source_provenance(shadow, site, description);
        T2Relation relation = t2_solver_constrain_predicate(
                shadow->solver,
                &predicate
        );
        if (relation != T2_RELATION_NO && !t2_solver_failed(shadow->solver)) {
                t2_solver_commit(shadow->solver, mark);
                return true;
        }
        char *explanation = t2_solver_explain_since(shadow->solver, mark);
        t2_solver_rollback(shadow->solver, mark);
        add_diagnostic(
                shadow,
                site,
                TYPES2_DIAGNOSTIC_ERROR,
                code,
                predicate.subtype,
                predicate.supertype,
                "%s%s%s",
                description,
                explanation == NULL || *explanation == '\0' ? "" : ": ",
                explanation == NULL ? "" : explanation
        );
        free(explanation);
        return false;
}

static bool
constrain_predicate_maybe_diagnose(
        Types2Shadow *shadow,
        Expr const *site,
        T2Predicate predicate,
        bool diagnose,
        char const *code,
        char const *description
)
{
        if (diagnose) {
                return constrain_predicate(
                        shadow,
                        site,
                        predicate,
                        code,
                        description
                );
        }
        if (
                predicate.subtype == T2_TYPE_INVALID
             || predicate.supertype == T2_TYPE_INVALID
             || predicate.operand == T2_TYPE_INVALID
        ) return false;

        T2SolverMark mark = t2_solver_mark(shadow->solver);
        predicate.provenance = source_provenance(shadow, site, description);
        T2Relation relation = t2_solver_constrain_predicate(
                shadow->solver,
                &predicate
        );
        bool valid = relation != T2_RELATION_NO
                  && relation != T2_RELATION_COMPLEXITY
                  && !t2_solver_failed(shadow->solver);
        if (valid) t2_solver_commit(shadow->solver, mark);
        else t2_solver_rollback(shadow->solver, mark);
        return valid;
}

static bool function_has_body(Expr const *function);
static T2Type class_receiver_type(
        Types2Shadow *shadow,
        int class_id,
        T2Type const *arguments,
        size_t arity,
        Expr const *site
);
static void infer_member_fields(
        Types2Shadow *shadow,
        int class_id,
        ExprVec const *fields,
        bool is_static,
        T2Quantifier const *class_quantifiers,
        size_t class_arity
);
static bool propagate_call_effect(
        Types2Shadow *shadow,
        Types2CallEffect const *effect,
        Expr const *site
);

static T2Type
declared_function_receiver(Types2Shadow *shadow, Expr const *function)
{
        if (function == NULL || function->class == NULL) {
                return T2_TYPE_INVALID;
        }
        ClassDefinition const *definition = function->class->def == NULL
                                          ? NULL
                                          : &function->class->def->class;
        size_t arity = definition == NULL
                     ? 0
                     : (size_t)vN(definition->type_params);
        T2Type *arguments = arity == 0 ? NULL : malloc(arity * sizeof *arguments);
        if (arity != 0 && arguments == NULL) {
                shadow->failed = true;
                return T2_TYPE_INVALID;
        }
        for (size_t i = 0; i < arity; ++i) {
                Expr const *parameter = v__(definition->type_params, (int)i);
                arguments[i] = find_type_variable(shadow, parameter->symbol);
                if (arguments[i] == T2_TYPE_INVALID) {
                        free(arguments);
                        return T2_TYPE_INVALID;
                }
        }
        T2Type receiver = class_receiver_type(
                shadow,
                function->class->i,
                arguments,
                arity,
                function
        );
        free(arguments);
        return receiver;
}

static bool
callable_channels_from_result(
        Types2Shadow *shadow,
        T2Type result,
        T2Type *yields,
        T2Type *sends
)
{
        Types2Nominal *generator_type = nominal_from_type(shadow, result);
        if (generator_type == NULL) return false;

        size_t arity = t2_type_arity(shadow->universe, result);
        if (generator_type->class_id == CLASS_GENERATOR && arity == 2) {
                *yields = t2_type_child(shadow->universe, result, 0);
                *sends = t2_type_child(shadow->universe, result, 1);
                return true;
        }
        if (
                (
                           generator_type->class_id == CLASS_ITERABLE
                        || generator_type->class_id == CLASS_ITER
                )
             && arity == 1
        ) {
                *yields = t2_type_child(shadow->universe, result, 0);
                *sends = t2_primitive(shadow->universe, T2_TYPE_NIL);
                return true;
        }
        return false;
}

static T2Scheme *
interface_function_scheme(
        Types2Shadow *shadow,
        Expr const *function,
        T2Quantifier const *class_quantifiers,
        size_t class_arity
)
{
        size_t method_arity = (size_t)vN(function->type_params);
        size_t quantifier_count = class_arity + method_arity;
        T2Quantifier *quantifiers = quantifier_count == 0
                                  ? NULL
                                  : malloc(quantifier_count * sizeof *quantifiers);
        if (quantifier_count != 0 && quantifiers == NULL) {
                shadow->failed = true;
                return NULL;
        }
        if (class_arity != 0) {
                memcpy(
                        quantifiers,
                        class_quantifiers,
                        class_arity * sizeof *quantifiers
                );
        }
        size_t type_mark = push_type_variables(shadow);
        for (size_t i = 0; i < method_arity; ++i) {
                Expr const *parameter = v__(function->type_params, (int)i);
                T2VariableKind kind = parameter->symbol != NULL
                                   && SymbolIsParamPack(parameter->symbol)
                                    ? T2_VARIABLE_PACK
                                    : T2_VARIABLE_QUANTIFIED;
                uint32_t id = shadow->next_quantified_id++;
                quantifiers[class_arity + i] = (T2Quantifier) { .id = id, .kind = kind };
                (void)add_type_variable(
                        shadow,
                        parameter->symbol,
                        t2_variable(shadow->universe, kind, id)
                );
        }

        size_t parameter_count = (size_t)vN(function->params);
        T2ParameterSpec *parameters = parameter_count == 0
                                    ? NULL
                                    : calloc(parameter_count, sizeof *parameters);
        if (parameter_count != 0 && parameters == NULL) {
                free(quantifiers);
                pop_type_variables(shadow, type_mark);
                shadow->failed = true;
                return NULL;
        }
        for (size_t i = 0; i < parameter_count; ++i) {
                Expr const *annotation = declared_parameter_annotation(function, i);
                T2Type annotation_type = T2_TYPE_INVALID;
                if (
                        i == 0
                     && function->mtype == MT_2OP
                     && annotation != NULL
                     && annotation->type == EXPRESSION_TYPE
                     && annotation->constraint == NULL
                ) annotation_type = declared_function_receiver(shadow, function);
                T2ParameterKind kind = T2_PARAMETER_POSITIONAL_OR_KEYWORD;
                if ((int)i == function->rest) kind = T2_PARAMETER_POSITIONAL_REST;
                if ((int)i == function->ikwargs) kind = T2_PARAMETER_KEYWORD_REST;
                if (
                        function->rest >= 0
                     && (int)i > function->rest
                     && kind == T2_PARAMETER_POSITIONAL_OR_KEYWORD
                ) kind = T2_PARAMETER_KEYWORD_ONLY;
                T2Type parameter_type = annotation == NULL
                                      ? t2_primitive(
                                              shadow->universe,
                                              T2_TYPE_DYNAMIC
                                        )
                                      : annotation_type != T2_TYPE_INVALID
                                        ? annotation_type
                                        : lower_type(shadow, annotation);
                parameters[i] = (T2ParameterSpec) {
                        .name = v__(function->params, (int)i),
                        .type = parameter_type,
                        .kind = kind,
                        .required = kind != T2_PARAMETER_POSITIONAL_REST
                                 && kind != T2_PARAMETER_KEYWORD_REST
                                 && (
                                            i >= (size_t)vN(function->dflts)
                                         || v__(function->dflts, (int)i) == NULL
                                    )
                                 && !type_admits_nil(shadow, parameter_type)
                };
                if (
                        is_pack_type(shadow, parameters[i].type)
                     && parameters[i].kind != T2_PARAMETER_KEYWORD_REST
                ) {
                        parameters[i].kind = T2_PARAMETER_PACK;
                        parameters[i].required = false;
                }
        }
        bool generator = function->type == EXPRESSION_GENERATOR || function->star;
        T2Type result = function->return_type == NULL
                      ? t2_primitive(shadow->universe, T2_TYPE_DYNAMIC)
                      : lower_type(shadow, function->return_type);
        T2Type yields = t2_primitive(
                shadow->universe,
                generator ? T2_TYPE_DYNAMIC : T2_TYPE_NEVER
        );
        T2Type sends = t2_primitive(
                shadow->universe,
                generator ? T2_TYPE_DYNAMIC : T2_TYPE_NIL
        );
        (void)callable_channels_from_result(shadow, result, &yields, &sends);
        T2Type callable = t2_callable(
                shadow->universe,
                parameters,
                parameter_count,
                result,
                yields,
                sends
        );
        T2Scheme *scheme = t2_scheme_new(
                shadow->universe,
                quantifiers,
                quantifier_count,
                callable,
                NULL,
                0
        );
        free(parameters);
        free(quantifiers);
        pop_type_variables(shadow, type_mark);
        return scheme;
}

static void
free_scheme_array(T2Scheme **schemes, size_t count)
{
        if (schemes == NULL) return;
        for (size_t i = 0; i < count; ++i) t2_scheme_free(schemes[i]);
        free(schemes);
}

static T2Scheme *
interface_callable_scheme(
        Types2Shadow *shadow,
        Expr const *function,
        T2Quantifier const *class_quantifiers,
        size_t class_arity
)
{
        if (function == NULL) return NULL;
        if (function->type != EXPRESSION_MULTI_FUNCTION) {
                return interface_function_scheme(
                        shadow,
                        function,
                        class_quantifiers,
                        class_arity
                );
        }

        size_t entry_count = (size_t)vN(function->functions);
        T2Scheme **schemes = entry_count == 0
                           ? NULL
                           : calloc(entry_count, sizeof *schemes);
        if (entry_count != 0 && schemes == NULL) {
                shadow->failed = true;
                return NULL;
        }
        size_t scheme_count = 0;
        size_t quantifier_capacity = 0;
        size_t predicate_count = 0;
        size_t arm_count = 0;
        for (size_t i = 0; i < entry_count; ++i) {
                Expr const *candidate = v__(function->functions, (int)i);
                if (candidate != NULL && IsStmt(candidate)) {
                        candidate = ((Stmt const *)candidate)->value;
                }
                if (candidate == NULL) continue;
                T2Scheme *scheme = interface_callable_scheme(
                        shadow,
                        candidate,
                        class_quantifiers,
                        class_arity
                );
                if (scheme == NULL) {
                        free_scheme_array(schemes, scheme_count);
                        return NULL;
                }
                schemes[scheme_count++] = scheme;
                quantifier_capacity += t2_scheme_quantifier_count(scheme);
                predicate_count += t2_scheme_predicate_count(scheme);
                T2Type body = t2_scheme_body(scheme);
                arm_count += t2_type_kind(shadow->universe, body) == T2_TYPE_OVERLOAD
                           ? t2_type_arity(shadow->universe, body)
                           : 1;
        }
        if (scheme_count == 0) {
                free(schemes);
                return NULL;
        }

        T2Quantifier *quantifiers = quantifier_capacity == 0
                                  ? NULL
                                  : malloc(quantifier_capacity * sizeof *quantifiers);
        T2Predicate *predicates = predicate_count == 0
                                ? NULL
                                : malloc(predicate_count * sizeof *predicates);
        T2Type *arms = arm_count == 0 ? NULL : malloc(arm_count * sizeof *arms);
        if (
                (quantifier_capacity != 0 && quantifiers == NULL)
             || (predicate_count != 0 && predicates == NULL)
             || (arm_count != 0 && arms == NULL)
        ) {
                free(quantifiers);
                free(predicates);
                free(arms);
                free_scheme_array(schemes, scheme_count);
                shadow->failed = true;
                return NULL;
        }

        size_t quantifier_count = 0;
        size_t predicates_used = 0;
        size_t arms_used = 0;
        for (size_t i = 0; i < scheme_count; ++i) {
                size_t count = t2_scheme_quantifier_count(schemes[i]);
                for (size_t j = 0; j < count; ++j) {
                        T2Quantifier quantifier;
                        if (!t2_scheme_quantifier(schemes[i], j, &quantifier)) continue;
                        bool duplicate = false;
                        for (size_t k = 0; k < quantifier_count; ++k) {
                                duplicate |= quantifiers[k].id == quantifier.id
                                          && quantifiers[k].kind == quantifier.kind;
                        }
                        if (!duplicate) quantifiers[quantifier_count++] = quantifier;
                }
                count = t2_scheme_predicate_count(schemes[i]);
                for (size_t j = 0; j < count; ++j) {
                        if (t2_scheme_predicate(
                                schemes[i],
                                j,
                                &predicates[predicates_used]
                        )) predicates_used += 1;
                }
                T2Type body = t2_scheme_body(schemes[i]);
                if (t2_type_kind(shadow->universe, body) == T2_TYPE_OVERLOAD) {
                        count = t2_type_arity(shadow->universe, body);
                        for (size_t j = 0; j < count; ++j) {
                                arms[arms_used++] = t2_type_child(
                                        shadow->universe,
                                        body,
                                        j
                                );
                        }
                } else {
                        arms[arms_used++] = body;
                }
        }
        T2Type body = t2_overload(shadow->universe, arms, arms_used);
        T2Scheme *result = body == T2_TYPE_INVALID
                         ? NULL
                         : t2_scheme_new(
                                 shadow->universe,
                                 quantifiers,
                                 quantifier_count,
                                 body,
                                 predicates,
                                 predicates_used
                           );
        free(quantifiers);
        free(predicates);
        free(arms);
        free_scheme_array(schemes, scheme_count);
        return result;
}

static void
interface_function_members(
        Types2Shadow *shadow,
        int class_id,
        ExprVec const *functions,
        Types2MemberKind kind,
        bool is_static,
        T2Quantifier const *class_quantifiers,
        size_t class_arity
)
{
        for (int i = 0; i < vN(*functions); ++i) {
                Expr const *function = v__(*functions, i);
                T2Scheme *scheme = interface_callable_scheme(
                        shadow,
                        function,
                        class_quantifiers,
                        class_arity
                );
                if (scheme == NULL) return;
                (void)add_member(
                        shadow,
                        class_id,
                        function->name == NULL ? "<member>" : function->name,
                        kind,
                        is_static,
                        !function_has_body(function),
                        kind == TYPES2_MEMBER_SETTER,
                        class_arity,
                        scheme,
                        function
                );
        }
}

static void
register_operator_expression(Types2Shadow *shadow, Expr const *function)
{
        if (function == NULL) return;
        if (function->type == EXPRESSION_MULTI_FUNCTION) {
                for (int i = 0; i < vN(function->functions); ++i) {
                        Expr const *candidate = v__(function->functions, i);
                        if (candidate != NULL && IsStmt(candidate)) {
                                candidate = ((Stmt const *)candidate)->value;
                        }
                        register_operator_expression(shadow, candidate);
                }
                return;
        }
        T2Scheme *scheme = interface_function_scheme(
                shadow,
                function,
                NULL,
                0
        );
        if (scheme == NULL) return;
        (void)add_operator_scheme(
                shadow,
                function->name,
                function,
                scheme
        );
}

static bool
operator_expression_contains(Expr const *function, Expr const *candidate)
{
        if (function == candidate) return true;
        if (function == NULL || function->type != EXPRESSION_MULTI_FUNCTION) return false;
        for (int i = 0; i < vN(function->functions); ++i) {
                Expr const *arm = v__(function->functions, i);
                if (arm != NULL && IsStmt(arm)) arm = ((Stmt const *)arm)->value;
                if (operator_expression_contains(arm, candidate)) return true;
        }
        return false;
}

static void
replace_operator_expression_scheme(
        Types2Shadow *shadow,
        Expr const *function,
        T2Scheme const *scheme
)
{
        if (function == NULL || scheme == NULL) return;
        for (size_t i = 0; i < shadow->operator_count;) {
                if (!operator_expression_contains(
                        function,
                        shadow->operators[i].declaration
                )) {
                        ++i;
                        continue;
                }
                t2_scheme_free(shadow->operators[i].scheme);
                memmove(
                        &shadow->operators[i],
                        &shadow->operators[i + 1],
                        (shadow->operator_count - i - 1) * sizeof *shadow->operators
                );
                shadow->operator_count -= 1;
        }
        T2Scheme *copy = copy_scheme(shadow, scheme);
        if (copy == NULL) return;
        (void)add_operator_scheme(
                shadow,
                function->name,
                function,
                copy
        );
}

static void
interface_field_members(
        Types2Shadow *shadow,
        int class_id,
        ExprVec const *fields,
        bool is_static,
        T2Quantifier const *class_quantifiers,
        size_t class_arity
)
{
        for (int i = 0; i < vN(*fields); ++i) {
                Expr const *field = v__(*fields, i);
                Expr const *identifier = field != NULL && field->type == EXPRESSION_EQ
                                       ? field->target
                                       : field;
                if (identifier == NULL || identifier->identifier == NULL) continue;
                T2Type type = identifier->constraint == NULL
                            ? t2_primitive(shadow->universe, T2_TYPE_DYNAMIC)
                            : lower_type(shadow, identifier->constraint);
                T2Scheme *scheme = prepend_scheme_quantifiers(
                        shadow,
                        class_quantifiers,
                        class_arity,
                        NULL,
                        type
                );
                if (scheme == NULL) return;
                (void)add_member(
                        shadow,
                        class_id,
                        identifier->identifier,
                        TYPES2_MEMBER_FIELD,
                        is_static,
                        false,
                        true,
                        class_arity,
                        scheme,
                        identifier
                );
        }
}

static T2Type
builtin_method_callable(
        Types2Shadow *shadow,
        T2ParameterSpec const *parameters,
        size_t parameter_count,
        T2Type result
)
{
        return t2_callable(
                shadow->universe,
                parameters,
                parameter_count,
                result,
                t2_primitive(shadow->universe, T2_TYPE_NEVER),
                t2_primitive(shadow->universe, T2_TYPE_NIL)
        );
}

static bool
add_builtin_method(
        Types2Shadow *shadow,
        int class_id,
        char const *name,
        T2Type body,
        T2Quantifier const *class_quantifiers,
        size_t class_arity
)
{
        if (
                body == T2_TYPE_INVALID
             || find_direct_member(
                        shadow,
                        class_id,
                        name,
                        TYPES2_MEMBER_METHOD,
                        false
                ) != NULL
        ) return body != T2_TYPE_INVALID;
        T2Scheme *scheme = prepend_scheme_quantifiers(
                shadow,
                class_quantifiers,
                class_arity,
                NULL,
                body
        );
        if (scheme == NULL) return false;
        if (add_member(
                shadow,
                class_id,
                name,
                TYPES2_MEMBER_METHOD,
                false,
                false,
                false,
                class_arity,
                scheme,
                NULL
        ) == NULL) {
                t2_scheme_free(scheme);
                return false;
        }
        return true;
}

static bool
add_builtin_field(
        Types2Shadow *shadow,
        int class_id,
        char const *name,
        T2Type body,
        T2Quantifier const *class_quantifiers,
        size_t class_arity
)
{
        if (
                body == T2_TYPE_INVALID
             || find_direct_member(
                        shadow,
                        class_id,
                        name,
                        TYPES2_MEMBER_FIELD,
                        false
                ) != NULL
        ) return body != T2_TYPE_INVALID;
        T2Scheme *scheme = prepend_scheme_quantifiers(
                shadow,
                class_quantifiers,
                class_arity,
                NULL,
                body
        );
        if (scheme == NULL) return false;
        if (add_member(
                shadow,
                class_id,
                name,
                TYPES2_MEMBER_FIELD,
                false,
                false,
                false,
                class_arity,
                scheme,
                NULL
        ) == NULL) {
                t2_scheme_free(scheme);
                return false;
        }
        return true;
}

static void
interface_builtin_methods(
        Types2Shadow *shadow,
        int class_id,
        T2Quantifier const *class_quantifiers,
        size_t class_arity
)
{
        T2Type nil = t2_primitive(shadow->universe, T2_TYPE_NIL);
        T2Type integer = t2_primitive(shadow->universe, T2_TYPE_INT);
        T2Type string = t2_primitive(shadow->universe, T2_TYPE_STRING);
        T2Type dynamic = t2_primitive(shadow->universe, T2_TYPE_DYNAMIC);
        T2Type boolean = t2_primitive(shadow->universe, T2_TYPE_BOOL);

        if (class_id == CLASS_FUNCTION) {
                /* VM function-like values expose this metadata field directly.
                 * It is nil for free/foreign functions and a class value for
                 * bound methods. */
                T2Type class_or_nil = t2_join(
                        shadow->universe,
                        t2_primitive(shadow->universe, T2_TYPE_OBJECT),
                        nil
                );
                (void)add_builtin_field(
                        shadow,
                        class_id,
                        "__class__",
                        class_or_nil,
                        class_quantifiers,
                        class_arity
                );
        }

        if (class_id == CLASS_ARRAY && class_arity == 1) {
                T2Type element = t2_variable(
                        shadow->universe,
                        class_quantifiers[0].kind,
                        class_quantifiers[0].id
                );
                T2Type array = nominal_application(
                        shadow,
                        CLASS_ARRAY,
                        "Array",
                        &element,
                        1,
                        NULL
                );
                T2Type nested = nominal_application(
                        shadow,
                        CLASS_ARRAY,
                        "Array",
                        &array,
                        1,
                        NULL
                );
                T2Type next = t2_join(shadow->universe, array, nil);
                T2Type next_callable = builtin_method_callable(
                        shadow,
                        NULL,
                        0,
                        next
                );
                (void)add_builtin_method(
                        shadow,
                        class_id,
                        "nextPermutation!",
                        next_callable,
                        class_quantifiers,
                        class_arity
                );
                (void)add_builtin_method(
                        shadow,
                        class_id,
                        "nextPermutation",
                        next_callable,
                        class_quantifiers,
                        class_arity
                );

                T2Type key_function = builtin_method_callable(
                        shadow,
                        &(T2ParameterSpec) {
                                .type = element,
                                .kind = T2_PARAMETER_POSITIONAL_ONLY,
                                .required = true
                        },
                        1,
                        t2_primitive(shadow->universe, T2_TYPE_ANY)
                );
                T2Type group_callable = builtin_method_callable(
                        shadow,
                        &(T2ParameterSpec) {
                                .name = "f",
                                .type = key_function,
                                .kind = T2_PARAMETER_POSITIONAL_OR_KEYWORD,
                                .required = true
                        },
                        1,
                        nested
                );
                (void)add_builtin_method(
                        shadow,
                        class_id,
                        "groupBy!",
                        group_callable,
                        class_quantifiers,
                        class_arity
                );
                (void)add_builtin_method(
                        shadow,
                        class_id,
                        "groupBy",
                        group_callable,
                        class_quantifiers,
                        class_arity
                );
                T2ParameterSpec swap_parameters[] = {
                        {
                                .name = "left",
                                .type = integer,
                                .kind = T2_PARAMETER_POSITIONAL_OR_KEYWORD,
                                .required = true
                        },
                        {
                                .name = "right",
                                .type = integer,
                                .kind = T2_PARAMETER_POSITIONAL_OR_KEYWORD,
                                .required = true
                        }
                };
                (void)add_builtin_method(
                        shadow,
                        class_id,
                        "swap",
                        builtin_method_callable(
                                shadow,
                                swap_parameters,
                                2,
                                array
                        ),
                        class_quantifiers,
                        class_arity
                );
                T2Type one_key = builtin_method_callable(
                        shadow,
                        &(T2ParameterSpec) {
                                .type = element,
                                .kind = T2_PARAMETER_POSITIONAL_ONLY,
                                .required = true
                        },
                        1,
                        t2_primitive(shadow->universe, T2_TYPE_ANY)
                );
                T2ParameterSpec comparison_parameters[] = {
                        {
                                .type = element,
                                .kind = T2_PARAMETER_POSITIONAL_ONLY,
                                .required = true
                        },
                        {
                                .type = element,
                                .kind = T2_PARAMETER_POSITIONAL_ONLY,
                                .required = true
                        }
                };
                T2Type comparison = builtin_method_callable(
                        shadow,
                        comparison_parameters,
                        2,
                        t2_primitive(shadow->universe, T2_TYPE_ANY)
                );
                T2Type element_or_nil = t2_join(
                        shadow->universe,
                        element,
                        nil
                );
                T2Type max_by_arms[] = {
                        builtin_method_callable(
                                shadow,
                                &(T2ParameterSpec) {
                                        .name = "f",
                                        .type = one_key,
                                        .kind = T2_PARAMETER_POSITIONAL_OR_KEYWORD,
                                        .required = true
                                },
                                1,
                                element_or_nil
                        ),
                        builtin_method_callable(
                                shadow,
                                &(T2ParameterSpec) {
                                        .name = "f",
                                        .type = comparison,
                                        .kind = T2_PARAMETER_POSITIONAL_OR_KEYWORD,
                                        .required = true
                                },
                                1,
                                element_or_nil
                        )
                };
                (void)add_builtin_method(
                        shadow,
                        class_id,
                        "maxBy",
                        t2_overload(shadow->universe, max_by_arms, 2),
                        class_quantifiers,
                        class_arity
                );
                return;
        }

        if (class_id == CLASS_DICT && class_arity == 2) {
                T2Type key = t2_variable(
                        shadow->universe,
                        class_quantifiers[0].kind,
                        class_quantifiers[0].id
                );
                T2Type value = t2_variable(
                        shadow->universe,
                        class_quantifiers[1].kind,
                        class_quantifiers[1].id
                );
                T2Type dictionary = nominal_application(
                        shadow,
                        CLASS_DICT,
                        "Dict",
                        (T2Type[]) { key, value },
                        2,
                        NULL
                );
                T2Type contains = builtin_method_callable(
                        shadow,
                        &(T2ParameterSpec) {
                                .name = "key",
                                .type = key,
                                .kind = T2_PARAMETER_POSITIONAL_OR_KEYWORD,
                                .required = true
                        },
                        1,
                        boolean
                );
                (void)add_builtin_method(
                        shadow,
                        class_id,
                        "has?",
                        contains,
                        class_quantifiers,
                        class_arity
                );
                (void)add_builtin_method(
                        shadow,
                        class_id,
                        "contains?",
                        contains,
                        class_quantifiers,
                        class_arity
                );
                (void)add_builtin_method(
                        shadow,
                        class_id,
                        "clear",
                        builtin_method_callable(
                                shadow,
                                NULL,
                                0,
                                dictionary
                        ),
                        class_quantifiers,
                        class_arity
                );
                (void)add_builtin_method(
                        shadow,
                        class_id,
                        "remove",
                        builtin_method_callable(
                                shadow,
                                &(T2ParameterSpec) {
                                        .name = "key",
                                        .type = key,
                                        .kind = T2_PARAMETER_POSITIONAL_OR_KEYWORD,
                                        .required = true
                                },
                                1,
                                t2_join(shadow->universe, value, nil)
                        ),
                        class_quantifiers,
                        class_arity
                );
                return;
        }

        if (class_id == CLASS_STRING) {
                T2Type no_arguments = builtin_method_callable(
                        shadow,
                        NULL,
                        0,
                        string
                );
                (void)add_builtin_method(
                        shadow,
                        class_id,
                        "plain",
                        no_arguments,
                        class_quantifiers,
                        class_arity
                );
                (void)add_builtin_method(
                        shadow,
                        class_id,
                        "unchalk",
                        no_arguments,
                        class_quantifiers,
                        class_arity
                );
                T2Type integer_or_nil = t2_join(
                        shadow->universe,
                        integer,
                        nil
                );
                T2Type string_or_nil = t2_join(
                        shadow->universe,
                        string,
                        nil
                );
                T2Type array_of_integer = nominal_application(
                        shadow,
                        CLASS_ARRAY,
                        "Array",
                        &integer,
                        1,
                        NULL
                );
                T2Type integer_argument = builtin_method_callable(
                        shadow,
                        &(T2ParameterSpec) {
                                .name = "index",
                                .type = integer,
                                .kind = T2_PARAMETER_POSITIONAL_OR_KEYWORD,
                                .required = true
                        },
                        1,
                        string_or_nil
                );
                (void)add_builtin_method(
                        shadow,
                        class_id,
                        "char",
                        integer_argument,
                        class_quantifiers,
                        class_arity
                );
                integer_argument = builtin_method_callable(
                        shadow,
                        &(T2ParameterSpec) {
                                .name = "index",
                                .type = integer,
                                .kind = T2_PARAMETER_POSITIONAL_OR_KEYWORD,
                                .required = true
                        },
                        1,
                        integer_or_nil
                );
                (void)add_builtin_method(
                        shadow,
                        class_id,
                        "byte",
                        integer_argument,
                        class_quantifiers,
                        class_arity
                );
                (void)add_builtin_method(
                        shadow,
                        class_id,
                        "charCount",
                        builtin_method_callable(shadow, NULL, 0, integer),
                        class_quantifiers,
                        class_arity
                );
                (void)add_builtin_method(
                        shadow,
                        class_id,
                        "clone",
                        no_arguments,
                        class_quantifiers,
                        class_arity
                );
                T2ParameterSpec pattern_and_offset[] = {
                        {
                                .name = "pattern",
                                .type = dynamic,
                                .kind = T2_PARAMETER_POSITIONAL_OR_KEYWORD,
                                .required = true
                        },
                        {
                                .name = "offset",
                                .type = integer,
                                .kind = T2_PARAMETER_POSITIONAL_OR_KEYWORD,
                                .required = false
                        }
                };
                (void)add_builtin_method(
                        shadow,
                        class_id,
                        "searchAll",
                        builtin_method_callable(
                                shadow,
                                pattern_and_offset,
                                2,
                                array_of_integer
                        ),
                        class_quantifiers,
                        class_arity
                );
                (void)add_builtin_method(
                        shadow,
                        class_id,
                        "contains?",
                        builtin_method_callable(
                                shadow,
                                pattern_and_offset,
                                2,
                                boolean
                        ),
                        class_quantifiers,
                        class_arity
                );
                (void)add_builtin_method(
                        shadow,
                        class_id,
                        "comb?",
                        builtin_method_callable(
                                shadow,
                                pattern_and_offset,
                                1,
                                string_or_nil
                        ),
                        class_quantifiers,
                        class_arity
                );
                T2ParameterSpec padding[] = {
                        {
                                .name = "width",
                                .type = integer,
                                .kind = T2_PARAMETER_POSITIONAL_OR_KEYWORD,
                                .required = true
                        },
                        {
                                .name = "padding",
                                .type = string,
                                .kind = T2_PARAMETER_POSITIONAL_OR_KEYWORD,
                                .required = false
                        }
                };
                (void)add_builtin_method(
                        shadow,
                        class_id,
                        "lpad",
                        builtin_method_callable(shadow, padding, 2, string),
                        class_quantifiers,
                        class_arity
                );
                T2Type chalk = builtin_method_callable(
                        shadow,
                        &(T2ParameterSpec) {
                                .name = "styles",
                                .type = dynamic,
                                .kind = T2_PARAMETER_POSITIONAL_OR_KEYWORD,
                                .required = false
                        },
                        1,
                        string
                );
                (void)add_builtin_method(
                        shadow,
                        class_id,
                        "chalk",
                        chalk,
                        class_quantifiers,
                        class_arity
                );
                T2Type pointer = nominal_application(
                        shadow,
                        CLASS_PTR,
                        "Ptr",
                        &integer,
                        1,
                        NULL
                );
                (void)add_builtin_method(
                        shadow,
                        class_id,
                        "ptr",
                        builtin_method_callable(shadow, NULL, 0, pointer),
                        class_quantifiers,
                        class_arity
                );
                return;
        }

        if (class_id == CLASS_BLOB) {
                T2Type blob = nominal_application(
                        shadow,
                        CLASS_BLOB,
                        "Blob",
                        NULL,
                        0,
                        NULL
                );
                (void)add_builtin_method(
                        shadow,
                        class_id,
                        "hex",
                        builtin_method_callable(shadow, NULL, 0, string),
                        class_quantifiers,
                        class_arity
                );
                T2Type pointer = nominal_application(
                        shadow,
                        CLASS_PTR,
                        "Ptr",
                        &dynamic,
                        1,
                        NULL
                );
                T2Type value = t2_union(
                        shadow->universe,
                        (T2Type[]) { integer, string, blob, pointer },
                        4
                );
                T2Type arms[4];
                arms[0] = builtin_method_callable(
                        shadow,
                        &(T2ParameterSpec) {
                                .name = "value",
                                .type = value,
                                .kind = T2_PARAMETER_POSITIONAL_OR_KEYWORD,
                                .required = true
                        },
                        1,
                        blob
                );
                arms[1] = builtin_method_callable(
                        shadow,
                        (T2ParameterSpec[]) {
                                {
                                        .name = "index",
                                        .type = integer,
                                        .kind = T2_PARAMETER_POSITIONAL_OR_KEYWORD,
                                        .required = true
                                },
                                {
                                        .name = "value",
                                        .type = value,
                                        .kind = T2_PARAMETER_POSITIONAL_OR_KEYWORD,
                                        .required = true
                                }
                        },
                        2,
                        blob
                );
                arms[2] = builtin_method_callable(
                        shadow,
                        (T2ParameterSpec[]) {
                                {
                                        .name = "pointer",
                                        .type = pointer,
                                        .kind = T2_PARAMETER_POSITIONAL_OR_KEYWORD,
                                        .required = true
                                },
                                {
                                        .name = "count",
                                        .type = integer,
                                        .kind = T2_PARAMETER_POSITIONAL_OR_KEYWORD,
                                        .required = true
                                }
                        },
                        2,
                        blob
                );
                arms[3] = builtin_method_callable(
                        shadow,
                        (T2ParameterSpec[]) {
                                {
                                        .name = "index",
                                        .type = integer,
                                        .kind = T2_PARAMETER_POSITIONAL_OR_KEYWORD,
                                        .required = true
                                },
                                {
                                        .name = "pointer",
                                        .type = pointer,
                                        .kind = T2_PARAMETER_POSITIONAL_OR_KEYWORD,
                                        .required = true
                                },
                                {
                                        .name = "count",
                                        .type = integer,
                                        .kind = T2_PARAMETER_POSITIONAL_OR_KEYWORD,
                                        .required = true
                                }
                        },
                        3,
                        blob
                );
                (void)add_builtin_method(
                        shadow,
                        class_id,
                        "push",
                        t2_overload(shadow->universe, arms, 4),
                        class_quantifiers,
                        class_arity
                );
        }
}

static bool
ensure_class_interface(Types2Shadow *shadow, int class_id)
{
        Types2Nominal *nominal = ensure_nominal(shadow, class_id, NULL, 0);
        if (nominal == NULL) return false;
        if (nominal->complete) return true;
        if (nominal->populating) return true;
        nominal->populating = true;
        bool previous_interface_state = shadow->building_interface;
        shadow->building_interface = true;

        Class *class = shadow->ty == NULL ? NULL : class_get(shadow->ty, class_id);
        if (class == NULL || class->def == NULL) {
                nominal->populating = false;
                shadow->building_interface = previous_interface_state;
                return false;
        }
        ClassDefinition const *definition = &class->def->class;
        /* A shadow universe is compilation-local.  Classes first encountered
         * through imported annotations therefore need their superclass and
         * trait templates installed when the native interface is materialized,
         * not only in the unit that declared them. */
        register_nominal_hierarchy(shadow, definition, nominal);
        nominal = find_class_nominal(shadow, class_id);
        if (nominal == NULL) {
                shadow->failed = true;
                shadow->building_interface = previous_interface_state;
                return false;
        }
        size_t declared_arity = (size_t)vN(definition->type_params);
        bool tag_interface = class->def->type == STATEMENT_TAG_DEFINITION;
        size_t arity = tag_interface ? 1 : declared_arity;
        size_t type_mark = push_type_variables(shadow);
        T2Quantifier *quantifiers = arity == 0
                                  ? NULL
                                  : malloc(arity * sizeof *quantifiers);
        if (arity != 0 && quantifiers == NULL) {
                shadow->failed = true;
                nominal = find_class_nominal(shadow, class_id);
                if (nominal != NULL) nominal->populating = false;
                shadow->building_interface = previous_interface_state;
                return false;
        }
        for (size_t i = 0; i < arity; ++i) {
                Expr const *parameter = i < declared_arity
                                      ? v__(definition->type_params, (int)i)
                                      : NULL;
                T2VariableKind kind = parameter != NULL
                                   && parameter->symbol != NULL
                                   && SymbolIsParamPack(parameter->symbol)
                                    ? T2_VARIABLE_PACK
                                    : T2_VARIABLE_QUANTIFIED;
                uint32_t id = shadow->next_quantified_id++;
                quantifiers[i] = (T2Quantifier) { .id = id, .kind = kind };
                if (parameter != NULL) {
                        (void)add_type_variable(
                                shadow,
                                parameter->symbol,
                                t2_variable(shadow->universe, kind, id)
                        );
                }
        }

        interface_field_members(
                shadow,
                class_id,
                &definition->fields,
                false,
                quantifiers,
                arity
        );
        interface_field_members(
                shadow,
                class_id,
                &definition->s_fields,
                true,
                quantifiers,
                arity
        );
        interface_function_members(
                shadow,
                class_id,
                &definition->methods,
                TYPES2_MEMBER_METHOD,
                false,
                quantifiers,
                arity
        );
        interface_function_members(
                shadow,
                class_id,
                &definition->getters,
                TYPES2_MEMBER_GETTER,
                false,
                quantifiers,
                arity
        );
        interface_function_members(
                shadow,
                class_id,
                &definition->setters,
                TYPES2_MEMBER_SETTER,
                false,
                quantifiers,
                arity
        );
        interface_function_members(
                shadow,
                class_id,
                &definition->s_methods,
                TYPES2_MEMBER_METHOD,
                true,
                quantifiers,
                arity
        );
        interface_function_members(
                shadow,
                class_id,
                &definition->s_getters,
                TYPES2_MEMBER_GETTER,
                true,
                quantifiers,
                arity
        );
        interface_function_members(
                shadow,
                class_id,
                &definition->s_setters,
                TYPES2_MEMBER_SETTER,
                true,
                quantifiers,
                arity
        );
        interface_builtin_methods(
                shadow,
                class_id,
                quantifiers,
                arity
        );
        if (class->super != NULL && class->super->i != class_id) {
                (void)ensure_class_interface(shadow, class->super->i);
        }
        free(quantifiers);
        pop_type_variables(shadow, type_mark);
        nominal = find_class_nominal(shadow, class_id);
        if (nominal != NULL) {
                nominal->complete = true;
                nominal->populating = false;
        }
        shadow->building_interface = previous_interface_state;
        return true;
}

static Types2Nominal *
nominal_from_type(Types2Shadow *shadow, T2Type type)
{
        if (t2_type_kind(shadow->universe, type) != T2_TYPE_NOMINAL) return NULL;
        uint64_t symbol = t2_type_payload(shadow->universe, type);
        for (size_t i = 0; i < shadow->nominal_count; ++i) {
                if (shadow->nominals[i].symbol == symbol) return &shadow->nominals[i];
        }
        return NULL;
}

static T2Type
relax_literal(Types2Shadow *shadow, T2Type type)
{
        switch (t2_type_kind(shadow->universe, type)) {
        case T2_TYPE_LITERAL_INT:
                return t2_primitive(shadow->universe, T2_TYPE_INT);
        case T2_TYPE_LITERAL_STRING:
                return t2_primitive(shadow->universe, T2_TYPE_STRING);
        case T2_TYPE_LITERAL_BOOL:
                return t2_primitive(shadow->universe, T2_TYPE_BOOL);
        default:
                return type;
        }
}

static T2Type infer_expression(Types2Shadow *shadow, Expr const *expression);
static Types2Flow infer_statement(Types2Shadow *shadow, Stmt const *statement);
static bool contextual_fresh_literal(
        Types2Shadow *shadow,
        Expr const *source,
        T2Type expected
);
static bool tuple_is_record(Expr const *expression);
static bool import_operator_definitions(Types2Shadow *shadow, char const *name);
static Types2Binding *member_refinement_binding(Types2Shadow *shadow, Symbol const *symbol, Expr const *site);
static Types2Binding *ensure_resolved_binding(Types2Shadow *shadow, Symbol const *symbol);
static T2Type iterated_type(Types2Shadow *shadow, T2Type source, Expr const *site);
static T2Type without_nil(Types2Shadow *shadow, T2Type type);
static bool infer_pattern(Types2Shadow *shadow, Expr const *pattern, T2Type subject);
static bool infer_refutable_pattern(
        Types2Shadow *shadow,
        Expr const *pattern,
        T2Type subject
);
static T2Type pattern_coverage(
        Types2Shadow *shadow,
        Expr const *pattern,
        T2Type subject,
        bool *certain
);
static T2Type subtract_pattern_coverage(
        Types2Shadow *shadow,
        T2Type subject,
        T2Type coverage,
        bool covers_open_domain
);
static bool match_domain_is_closed(Types2Shadow *shadow, T2Type subject);
static bool pattern_is_catch_all(Expr const *pattern);
static bool function_has_body(Expr const *function);
static T2Type callable_set_result(
        Types2Shadow *shadow,
        T2Type callable,
        T2Type result
);
static T2Scheme *scheme_with_body(
        Types2Shadow *shadow,
        T2Scheme const *source,
        T2Type body
);
static void infer_member_fields(
        Types2Shadow *shadow,
        int class_id,
        ExprVec const *fields,
        bool is_static,
        T2Quantifier const *class_quantifiers,
        size_t class_arity
);

static void
default_dynamic_callable_metas(
        Types2Shadow *shadow,
        T2Type type,
        unsigned depth
)
{
        if (depth > 64 || shadow->failed) return;
        T2TypeKind kind = t2_type_kind(shadow->universe, type);
        if (kind == T2_TYPE_META) {
                T2Type never = t2_primitive(
                        shadow->universe,
                        T2_TYPE_NEVER
                );
                T2Type any = t2_primitive(shadow->universe, T2_TYPE_ANY);
                T2Type lower = t2_solver_lower_bound(shadow->solver, type);
                T2Type upper = t2_solver_upper_bound(shadow->solver, type);
                if (lower == never && upper == any) {
                        T2SolverMark mark = t2_solver_mark(shadow->solver);
                        T2Relation relation = t2_solver_unify(
                                shadow->solver,
                                type,
                                t2_primitive(
                                        shadow->universe,
                                        T2_TYPE_DYNAMIC
                                ),
                                "dynamic callback context"
                        );
                        if (
                                relation != T2_RELATION_NO
                             && !t2_solver_failed(shadow->solver)
                        ) t2_solver_commit(shadow->solver, mark);
                        else t2_solver_rollback(shadow->solver, mark);
                        return;
                }
                if (lower != T2_TYPE_INVALID && lower != never) {
                        default_dynamic_callable_metas(
                                shadow,
                                lower,
                                depth + 1
                        );
                }
                if (upper != T2_TYPE_INVALID && upper != any) {
                        default_dynamic_callable_metas(
                                shadow,
                                upper,
                                depth + 1
                        );
                }
                return;
        }
        for (size_t i = 0; i < t2_type_arity(shadow->universe, type); ++i) {
                default_dynamic_callable_metas(
                        shadow,
                        t2_type_child(shadow->universe, type, i),
                        depth + 1
                );
        }
}

static bool
is_callable_literal(Expr const *source)
{
        Expr const *expression = source == NULL ? NULL : unfurl(source);
        if (expression == NULL) return false;
        return expression->type == EXPRESSION_FUNCTION
            || expression->type == EXPRESSION_IMPLICIT_FUNCTION
            || expression->type == EXPRESSION_GENERATOR
            || expression->type == EXPRESSION_MULTI_FUNCTION;
}

static void
default_dynamic_callback_arguments(
        Types2Shadow *shadow,
        ExprVec const *expressions,
        T2Type const *types,
        size_t count
)
{
        if (expressions == NULL || types == NULL) return;
        for (size_t i = 0; i < count; ++i) {
                if (!is_callable_literal(v__(*expressions, (int)i))) continue;
                default_dynamic_callable_metas(shadow, types[i], 0);
        }
}

static bool
fresh_literal_expression(Expr const *expression)
{
        Expr const *unfurled = unfurl(expression);
        if (unfurled == NULL) return false;
        return unfurled->type == EXPRESSION_ARRAY
            || (unfurled->type == EXPRESSION_TUPLE && tuple_is_record(unfurled));
}

static Expr const *
positional_argument_expression(Expr const *site, size_t index)
{
        if (site == NULL) return NULL;
        ExprVec const *arguments = site->type == EXPRESSION_FUNCTION_CALL
                                 ? &site->args
                                 : site->type == EXPRESSION_METHOD_CALL
                                   ? &site->method_args
                                   : NULL;
        if (arguments == NULL || index >= (size_t)vN(*arguments)) return NULL;
        for (size_t i = 0; i <= index; ++i) {
                Expr const *argument = v__(*arguments, (int)i);
                if (argument == NULL || argument->type == EXPRESSION_SPREAD) {
                        return NULL;
                }
        }
        return v__(*arguments, (int)index);
}

static bool
candidate_argument(
        Types2Shadow *shadow,
        T2Type argument,
        T2Type parameter,
        Expr const *site
)
{
        if (is_dynamic_type(shadow, argument)) {
                /* A gradual argument still commits this candidate's generic
                 * instantiation.  Leaving its parameter metas unconstrained
                 * would strand receiver/member predicates after the call. */
                default_dynamic_callable_metas(shadow, parameter, 0);
                return !shadow->failed && !t2_solver_failed(shadow->solver);
        }
        if (is_dynamic_type(shadow, parameter)) {
                /* Dynamic is an elimination permission on the parameter side,
                 * not an equality constraint on the value flowing into it.
                 * Binding an otherwise principal argument meta to Dynamic
                 * here makes a later precise use fail (and made call results
                 * depend on which Dynamic consumer ran first). */
                return true;
        }
        T2Type resolved_argument = resolved_type_head(
                shadow,
                argument,
                T2_PREFER_LOWER_BOUND
        );
        T2Type resolved_parameter = resolved_type_head(
                shadow,
                parameter,
                T2_PREFER_UPPER_BOUND
        );
        Types2Nominal *argument_nominal = nominal_from_type(
                shadow,
                resolved_argument
        );
        Types2Nominal *parameter_nominal = nominal_from_type(
                shadow,
                resolved_parameter
        );
        T2TypeKind argument_kind = t2_type_kind(
                shadow->universe,
                resolved_argument
        );
        T2TypeKind parameter_kind = t2_type_kind(
                shadow->universe,
                resolved_parameter
        );
        if (
                parameter_nominal != NULL
             && parameter_nominal->class_id == CLASS_FUNCTION
             && (
                        argument_kind == T2_TYPE_FUNCTION
                     || argument_kind == T2_TYPE_OVERLOAD
                     || argument_kind == T2_TYPE_INTERSECTION
                )
        ) return true;
        if (
                argument_nominal != NULL
             && argument_nominal->class_id == CLASS_FUNCTION
             && (
                        parameter_kind == T2_TYPE_FUNCTION
                     || parameter_kind == T2_TYPE_OVERLOAD
                     || parameter_kind == T2_TYPE_INTERSECTION
                )
        ) {
                /* `Function` is the library's gradual callable top.  It says
                 * that invocation is runtime checked, so a result related to
                 * such a callback is Dynamic rather than an unsolved generic
                 * or an impossible nominal/function subtype constraint. */
                default_dynamic_callable_metas(shadow, parameter, 0);
                return !shadow->failed && !t2_solver_failed(shadow->solver);
        }
        if (
                type_contains_dynamic(shadow, argument)
             || type_contains_dynamic(shadow, parameter)
        ) {
                return constrain_gradually(
                        shadow,
                        site,
                        argument,
                        parameter,
                        "call argument"
                );
        }
        return t2_solver_constrain_subtype(
                shadow->solver,
                argument,
                parameter,
                source_provenance(shadow, site, "call argument")
        ) != T2_RELATION_NO && !t2_solver_failed(shadow->solver);
}

static void
record_call_effect(Types2Shadow *shadow, T2Type callable)
{
        Types2CallEffect *effect = shadow->call_effect_sink;
        if (
                effect == NULL
             || t2_type_kind(shadow->universe, callable) != T2_TYPE_FUNCTION
             || !t2_callable_is_effectful(shadow->universe, callable)
        ) return;
        T2Type yields = t2_callable_yield(shadow->universe, callable);
        if (t2_type_kind(shadow->universe, yields) == T2_TYPE_NEVER) return;
        T2Type sends = t2_callable_send(shadow->universe, callable);
        if (!effect->active) {
                *effect = (Types2CallEffect) {
                        .yields = yields,
                        .sends = sends,
                        .active = true
                };
                return;
        }
        effect->yields = t2_join(shadow->universe, effect->yields, yields);
        effect->sends = t2_meet(shadow->universe, effect->sends, sends);
        if (
                effect->yields == T2_TYPE_INVALID
             || effect->sends == T2_TYPE_INVALID
        ) shadow->failed = true;
}

static T2Type
apply_callable_candidate(
        Types2Shadow *shadow,
        T2Type callable,
        T2Type const *arguments,
        size_t argument_count,
        T2Type const *keyword_arguments,
        char const *const *keywords,
        size_t keyword_count,
        Expr const *site
)
{
        size_t parameter_count = t2_callable_parameter_count(
                shadow->universe,
                callable
        );
        if (
                t2_type_kind(shadow->universe, callable) != T2_TYPE_FUNCTION
             || parameter_count > SIZE_MAX / sizeof (bool)
        ) return T2_TYPE_INVALID;
        bool *assigned = parameter_count == 0
                       ? NULL
                       : calloc(parameter_count, sizeof *assigned);
        if (parameter_count != 0 && assigned == NULL) {
                shadow->failed = true;
                return T2_TYPE_INVALID;
        }

        size_t positional_parameter = 0;
        bool gradual_positional_spread = false;
        for (size_t i = 0; i < argument_count; ++i) {
                T2ParameterSpec parameter = {0};
                bool found = false;
                size_t selected = SIZE_MAX;
                for (; positional_parameter < parameter_count; ++positional_parameter) {
                        if (!t2_callable_parameter(
                                shadow->universe,
                                callable,
                                positional_parameter,
                                &parameter
                        )) break;
                        if (
                                parameter.kind == T2_PARAMETER_POSITIONAL_ONLY
                             || parameter.kind == T2_PARAMETER_POSITIONAL_OR_KEYWORD
                        ) {
                                found = true;
                                selected = positional_parameter;
                                assigned[positional_parameter++] = true;
                                break;
                        }
                        if (
                                parameter.kind == T2_PARAMETER_POSITIONAL_REST
                             || parameter.kind == T2_PARAMETER_PACK
                        ) {
                                found = true;
                                selected = positional_parameter;
                                assigned[positional_parameter] = true;
                                break;
                        }
                }
                T2TypeKind argument_kind = t2_type_kind(
                        shadow->universe,
                        arguments[i]
                );
                if (argument_kind == T2_TYPE_PACK_EXPANSION) {
                        T2Type element = t2_type_child(
                                shadow->universe,
                                arguments[i],
                                0
                        );
                        T2Type resolved_element = resolved_type_head(
                                shadow,
                                element,
                                T2_PREFER_LOWER_BOUND
                        );
                        T2TypeKind element_kind = t2_type_kind(
                                shadow->universe,
                                resolved_element
                        );
                        T2VariableKind element_variable =
                                element_kind == T2_TYPE_META
                             || element_kind == T2_TYPE_VARIABLE
                                ? t2_type_variable_kind(
                                          shadow->universe,
                                          resolved_element
                                  )
                                : T2_VARIABLE_RIGID;
                        bool gradual = element_kind == T2_TYPE_DYNAMIC
                                    || element_variable == T2_VARIABLE_FLEXIBLE
                                    || element_variable == T2_VARIABLE_WEAK;
                        if (
                                gradual
                             && i + 1 == argument_count
                             && (
                                        !found
                                     || (
                                                parameter.kind
                                             != T2_PARAMETER_POSITIONAL_REST
                                             && parameter.kind != T2_PARAMETER_PACK
                                        )
                                )
                        ) {
                                /* A spread sourced from Dynamic or an
                                 * unconstrained homogeneous rest parameter has
                                 * an unknown runtime length.  It may satisfy
                                 * zero or more fixed positional slots; keep
                                 * named slots available for explicit keyword
                                 * arguments and defer only this gradual arity
                                 * choice.  Rigid/typed iterable spreads remain
                                 * strict. */
                                if (selected != SIZE_MAX) assigned[selected] = false;
                                gradual_positional_spread = true;
                                defer_node(
                                        shadow,
                                        element_kind == T2_TYPE_DYNAMIC
                                                ? TYPES2_DEFER_DYNAMIC_SPREAD
                                                : TYPES2_DEFER_SPREAD_ARITY,
                                        site,
                                        NULL
                                );
                                continue;
                        }
                        if (!found) {
                                free(assigned);
                                return T2_TYPE_INVALID;
                        }
                        if (parameter.kind == T2_PARAMETER_POSITIONAL_REST) {
                                if (!candidate_argument(
                                        shadow,
                                        element,
                                        parameter.type,
                                        site
                                )) {
                                        free(assigned);
                                        return T2_TYPE_INVALID;
                                }
                                continue;
                        }
                        if (
                                parameter.kind == T2_PARAMETER_PACK
                             && i + 1 == argument_count
                             && candidate_argument(
                                        shadow,
                                        arguments[i],
                                        parameter.type,
                                        site
                                )
                        ) break;
                        free(assigned);
                        return T2_TYPE_INVALID;
                }
                if (found && parameter.kind == T2_PARAMETER_PACK) {
                        T2Type pack = t2_pack(
                                shadow->universe,
                                arguments + i,
                                argument_count - i,
                                T2_TYPE_INVALID
                        );
                        if (!candidate_argument(shadow, pack, parameter.type, site)) {
                                free(assigned);
                                return T2_TYPE_INVALID;
                        }
                        break;
                }
                if (!found) {
                        free(assigned);
                        return T2_TYPE_INVALID;
                }
                Expr const *literal = positional_argument_expression(site, i);
                if (
                        literal != NULL
                     && fresh_literal_expression(literal)
                     && contextual_fresh_literal(shadow, literal, parameter.type)
                ) continue;
                if (!candidate_argument(
                        shadow,
                        arguments[i],
                        parameter.type,
                        site
                )) {
                        free(assigned);
                        return T2_TYPE_INVALID;
                }
        }

        for (size_t i = 0; i < parameter_count; ++i) {
                T2ParameterSpec parameter;
                if (
                        assigned[i]
                     || !t2_callable_parameter(
                            shadow->universe,
                            callable,
                            i,
                            &parameter
                        )
                     || parameter.kind != T2_PARAMETER_PACK
                ) continue;
                T2Type empty = t2_pack(
                        shadow->universe,
                        NULL,
                        0,
                        T2_TYPE_INVALID
                );
                if (!candidate_argument(shadow, empty, parameter.type, site)) {
                        free(assigned);
                        return T2_TYPE_INVALID;
                }
                assigned[i] = true;
        }

        for (size_t i = 0; i < keyword_count; ++i) {
                if (keywords[i] != NULL && strcmp(keywords[i], "*") == 0) {
                        if (!constrain_predicate_maybe_diagnose(
                                shadow,
                                site,
                                (T2Predicate) {
                                        .kind = T2_PREDICATE_KEYWORD_SPREAD,
                                        .subtype = keyword_arguments[i],
                                        .supertype = callable,
                                        .operand = t2_primitive(
                                                shadow->universe,
                                                T2_TYPE_NEVER
                                        ),
                                        .name = "*"
                                },
                                false,
                                "keyword-spread",
                                "spread value must provide keywords accepted by the callable"
                        )) {
                                free(assigned);
                                return T2_TYPE_INVALID;
                        }
                        continue;
                }
                T2ParameterSpec parameter = {0};
                size_t selected = SIZE_MAX;
                size_t keyword_rest = SIZE_MAX;
                for (size_t j = 0; j < parameter_count; ++j) {
                        T2ParameterSpec candidate;
                        if (!t2_callable_parameter(
                                shadow->universe,
                                callable,
                                j,
                                &candidate
                        )) continue;
                        if (candidate.kind == T2_PARAMETER_KEYWORD_REST) keyword_rest = j;
                        if (
                                candidate.name != NULL
                             && strcmp(candidate.name, keywords[i]) == 0
                             && (
                                        candidate.kind == T2_PARAMETER_POSITIONAL_OR_KEYWORD
                                     || candidate.kind == T2_PARAMETER_KEYWORD_ONLY
                                )
                        ) {
                                selected = j;
                                parameter = candidate;
                                break;
                        }
                }
                if (selected == SIZE_MAX && keyword_rest != SIZE_MAX) {
                        selected = keyword_rest;
                        (void)t2_callable_parameter(
                                shadow->universe,
                                callable,
                                selected,
                                &parameter
                        );
                }
                if (
                        selected == SIZE_MAX
                     || (
                                parameter.kind != T2_PARAMETER_KEYWORD_REST
                             && assigned[selected]
                        )
                     || !candidate_argument(
                            shadow,
                            keyword_arguments[i],
                            parameter.type,
                            site
                        )
                ) {
                        free(assigned);
                        return T2_TYPE_INVALID;
                }
                if (parameter.kind != T2_PARAMETER_KEYWORD_REST) {
                        assigned[selected] = true;
                }
        }

        for (size_t i = 0; i < parameter_count; ++i) {
                T2ParameterSpec parameter;
                if (!t2_callable_parameter(
                        shadow->universe,
                        callable,
                        i,
                        &parameter
                )) continue;
                if (parameter.required && !assigned[i]) {
                        if (
                                gradual_positional_spread
                             && (
                                        parameter.kind == T2_PARAMETER_POSITIONAL_ONLY
                                     || parameter.kind
                                        == T2_PARAMETER_POSITIONAL_OR_KEYWORD
                                )
                        ) continue;
                        free(assigned);
                        return T2_TYPE_INVALID;
                }
        }
        free(assigned);
        return t2_callable_result(shadow->universe, callable);
}

static T2Type
infer_call_types(
        Types2Shadow *shadow,
        T2Type callee,
        T2Type const *arguments,
        size_t argument_count,
        T2Type const *keyword_arguments,
        char const *const *keywords,
        size_t keyword_count,
        Expr const *site,
        bool diagnose
)
{
        callee = resolved_type_head(
                shadow,
                callee,
                T2_PREFER_LOWER_BOUND
        );
        T2TypeKind kind = t2_type_kind(shadow->universe, callee);
        if (kind == T2_TYPE_ERROR) return callee;
        if (kind == T2_TYPE_TYPE_VALUE) {
                return infer_call_types(
                        shadow,
                        t2_type_value_constructor(shadow->universe, callee),
                        arguments,
                        argument_count,
                        keyword_arguments,
                        keywords,
                        keyword_count,
                        site,
                        diagnose
                );
        }
        if (kind == T2_TYPE_DYNAMIC) {
                for (size_t i = 0; i < argument_count; ++i) {
                        T2TypeKind argument_kind = t2_type_kind(
                                shadow->universe,
                                arguments[i]
                        );
                        if (
                                argument_kind == T2_TYPE_FUNCTION
                             || argument_kind == T2_TYPE_OVERLOAD
                             || argument_kind == T2_TYPE_INTERSECTION
                        ) default_dynamic_callable_metas(
                                shadow,
                                arguments[i],
                                0
                        );
                }
                for (size_t i = 0; i < keyword_count; ++i) {
                        T2TypeKind argument_kind = t2_type_kind(
                                shadow->universe,
                                keyword_arguments[i]
                        );
                        if (
                                argument_kind == T2_TYPE_FUNCTION
                             || argument_kind == T2_TYPE_OVERLOAD
                             || argument_kind == T2_TYPE_INTERSECTION
                        ) default_dynamic_callable_metas(
                                shadow,
                                keyword_arguments[i],
                                0
                        );
                }
                defer_node(shadow, TYPES2_DEFER_DYNAMIC_CALLEE, site, NULL);
                return callee;
        }
        if (kind == T2_TYPE_NOMINAL) {
                Types2Nominal *nominal = nominal_from_type(shadow, callee);
                bool gradual_callable = nominal != NULL
                                      && nominal->class_id == CLASS_FUNCTION;
                if (nominal != NULL && !gradual_callable) {
                        Types2Nominal *function_nominal = ensure_nominal(
                                shadow,
                                CLASS_FUNCTION,
                                "Function",
                                0
                        );
                        nominal = nominal_from_type(shadow, callee);
                        gradual_callable = function_nominal != NULL
                                         && nominal != NULL
                                         && t2_nominal_project(
                                                    shadow->universe,
                                                    callee,
                                                    function_nominal->symbol
                                            ) != T2_TYPE_INVALID;
                }
                if (gradual_callable) {
                        for (size_t i = 0; i < argument_count; ++i) {
                                T2TypeKind argument_kind = t2_type_kind(
                                        shadow->universe,
                                        arguments[i]
                                );
                                if (
                                        argument_kind == T2_TYPE_FUNCTION
                                     || argument_kind == T2_TYPE_OVERLOAD
                                     || argument_kind == T2_TYPE_INTERSECTION
                                ) default_dynamic_callable_metas(
                                        shadow,
                                        arguments[i],
                                        0
                                );
                        }
                        defer_node(shadow, TYPES2_DEFER_CALLABLE_TOP, site, NULL);
                        return t2_primitive(
                                shadow->universe,
                                T2_TYPE_DYNAMIC
                        );
                }
        }
        if (kind == T2_TYPE_META) {
                if (argument_count > SIZE_MAX - keyword_count) {
                        shadow->failed = true;
                        return T2_TYPE_INVALID;
                }
                size_t count = argument_count + keyword_count;
                T2ParameterSpec *parameters = count == 0
                                            ? NULL
                                            : calloc(count, sizeof *parameters);
                if (count != 0 && parameters == NULL) {
                        shadow->failed = true;
                        return T2_TYPE_INVALID;
                }
                for (size_t i = 0; i < argument_count; ++i) {
                        T2Type parameter = is_dynamic_type(shadow, arguments[i])
                                         ? t2_solver_new_meta(
                                                 shadow->solver,
                                                 T2_VARIABLE_FLEXIBLE,
                                                 shadow->level,
                                                 "dynamic call argument"
                                           )
                                         : arguments[i];
                        parameters[i] = (T2ParameterSpec) {
                                .type = parameter,
                                .kind = T2_PARAMETER_POSITIONAL_ONLY,
                                .required = true
                        };
                }
                for (size_t i = 0; i < keyword_count; ++i) {
                        T2Type parameter = is_dynamic_type(
                                                   shadow,
                                                   keyword_arguments[i]
                                           )
                                         ? t2_solver_new_meta(
                                                 shadow->solver,
                                                 T2_VARIABLE_FLEXIBLE,
                                                 shadow->level,
                                                 "dynamic keyword argument"
                                           )
                                         : keyword_arguments[i];
                        parameters[argument_count + i] = (T2ParameterSpec) {
                                .name = keywords[i],
                                .type = parameter,
                                .kind = T2_PARAMETER_KEYWORD_ONLY,
                                .required = true
                        };
                }
                T2Type result = t2_solver_new_meta(
                        shadow->solver,
                        T2_VARIABLE_FLEXIBLE,
                        shadow->level,
                        "call result"
                );
                T2Type expected = t2_callable(
                        shadow->universe,
                        parameters,
                        count,
                        result,
                        t2_primitive(shadow->universe, T2_TYPE_NEVER),
                        t2_primitive(shadow->universe, T2_TYPE_NIL)
                );
                free(parameters);
                if (constrain_type_maybe_diagnose(
                        shadow,
                        site,
                        callee,
                        expected,
                        diagnose,
                        "not-callable",
                        "value must support this call protocol"
                )) return result;
                return t2_primitive(shadow->universe, T2_TYPE_ERROR);
        }
        if (kind == T2_TYPE_UNION) {
                T2SolverMark mark = t2_solver_mark(shadow->solver);
                T2Type result = t2_primitive(shadow->universe, T2_TYPE_NEVER);
                size_t count = t2_type_arity(shadow->universe, callee);
                for (size_t i = 0; i < count; ++i) {
                        T2Type arm_result = infer_call_types(
                                shadow,
                                t2_type_child(shadow->universe, callee, i),
                                arguments,
                                argument_count,
                                keyword_arguments,
                                keywords,
                                keyword_count,
                                site,
                                false
                        );
                        if (
                                arm_result == T2_TYPE_INVALID
                             || t2_type_kind(shadow->universe, arm_result) == T2_TYPE_ERROR
                             || t2_solver_failed(shadow->solver)
                        ) {
                                t2_solver_rollback(shadow->solver, mark);
                                if (diagnose) {
                                        add_diagnostic(
                                                shadow,
                                                site,
                                                TYPES2_DIAGNOSTIC_ERROR,
                                                "union-call-coverage",
                                                callee,
                                                T2_TYPE_INVALID,
                                                "every reachable union arm must support the call"
                                        );
                                }
                                return t2_primitive(shadow->universe, T2_TYPE_ERROR);
                        }
                        result = t2_join(shadow->universe, result, arm_result);
                }
                t2_solver_commit(shadow->solver, mark);
                return result;
        }
        if (kind == T2_TYPE_OVERLOAD || kind == T2_TYPE_INTERSECTION) {
                size_t count = t2_type_arity(shadow->universe, callee);
                for (size_t i = 0; i < count; ++i) {
                        T2SolverMark mark = t2_solver_mark(shadow->solver);
                        T2Type result = infer_call_types(
                                shadow,
                                t2_type_child(shadow->universe, callee, i),
                                arguments,
                                argument_count,
                                keyword_arguments,
                                keywords,
                                keyword_count,
                                site,
                                false
                        );
                        if (
                                result != T2_TYPE_INVALID
                             && t2_type_kind(shadow->universe, result) != T2_TYPE_ERROR
                             && !t2_solver_failed(shadow->solver)
                        ) {
                                t2_solver_commit(shadow->solver, mark);
                                return result;
                        }
                        t2_solver_rollback(shadow->solver, mark);
                }

                size_t split_argument = SIZE_MAX;
                size_t split_keyword = SIZE_MAX;
                T2Type split = T2_TYPE_INVALID;
                for (size_t i = 0; i < argument_count; ++i) {
                        if (
                                t2_type_kind(shadow->universe, arguments[i])
                             == T2_TYPE_UNION
                        ) {
                                split_argument = i;
                                split = arguments[i];
                                break;
                        }
                }
                if (split == T2_TYPE_INVALID) {
                        for (size_t i = 0; i < keyword_count; ++i) {
                                if (
                                        t2_type_kind(
                                                shadow->universe,
                                                keyword_arguments[i]
                                        ) == T2_TYPE_UNION
                                ) {
                                        split_keyword = i;
                                        split = keyword_arguments[i];
                                        break;
                                }
                        }
                }
                if (split != T2_TYPE_INVALID) {
                        T2Type *positional = argument_count == 0
                                           ? NULL
                                           : malloc(argument_count * sizeof *positional);
                        T2Type *named = keyword_count == 0
                                     ? NULL
                                     : malloc(keyword_count * sizeof *named);
                        if (
                                (argument_count != 0 && positional == NULL)
                             || (keyword_count != 0 && named == NULL)
                        ) {
                                free(positional);
                                free(named);
                                shadow->failed = true;
                                return T2_TYPE_INVALID;
                        }
                        if (argument_count != 0) {
                                memcpy(
                                        positional,
                                        arguments,
                                        argument_count * sizeof *positional
                                );
                        }
                        if (keyword_count != 0) {
                                memcpy(
                                        named,
                                        keyword_arguments,
                                        keyword_count * sizeof *named
                                );
                        }

                        shadow->union_call_splits += 1;
                        T2SolverMark coverage = t2_solver_mark(shadow->solver);
                        T2Type result = t2_primitive(
                                shadow->universe,
                                T2_TYPE_NEVER
                        );
                        bool covered = true;
                        size_t arm_count = t2_type_arity(shadow->universe, split);
                        for (size_t i = 0; i < arm_count; ++i) {
                                T2Type arm = t2_type_child(
                                        shadow->universe,
                                        split,
                                        i
                                );
                                if (split_argument != SIZE_MAX) {
                                        positional[split_argument] = arm;
                                } else {
                                        named[split_keyword] = arm;
                                }
                                shadow->union_call_arms += 1;
                                T2Type arm_result = infer_call_types(
                                        shadow,
                                        callee,
                                        positional,
                                        argument_count,
                                        named,
                                        keywords,
                                        keyword_count,
                                        site,
                                        false
                                );
                                if (
                                        arm_result == T2_TYPE_INVALID
                                     || t2_type_kind(
                                                shadow->universe,
                                                arm_result
                                        ) == T2_TYPE_ERROR
                                     || t2_solver_failed(shadow->solver)
                                ) {
                                        covered = false;
                                        break;
                                }
                                result = t2_join(
                                        shadow->universe,
                                        result,
                                        arm_result
                                );
                        }
                        free(positional);
                        free(named);
                        if (covered) {
                                t2_solver_commit(shadow->solver, coverage);
                                return result;
                        }
                        t2_solver_rollback(shadow->solver, coverage);
                }
                if (diagnose) {
                        add_diagnostic(
                                shadow,
                                site,
                                TYPES2_DIAGNOSTIC_ERROR,
                                "no-overload",
                                callee,
                                T2_TYPE_INVALID,
                                "no overload accepts this complete call shape"
                        );
                }
                return t2_primitive(shadow->universe, T2_TYPE_ERROR);
        }
        if (kind == T2_TYPE_FUNCTION) {
                shadow->candidate_trials += 1;
                T2SolverMark mark = t2_solver_mark(shadow->solver);
                T2Type result = apply_callable_candidate(
                        shadow,
                        callee,
                        arguments,
                        argument_count,
                        keyword_arguments,
                        keywords,
                        keyword_count,
                        site
                );
                if (result != T2_TYPE_INVALID && !t2_solver_failed(shadow->solver)) {
                        t2_solver_commit(shadow->solver, mark);
                        record_call_effect(shadow, callee);
                        return result;
                }
                char *reason = t2_solver_explain_since(shadow->solver, mark);
                t2_solver_rollback(shadow->solver, mark);
                if (diagnose) {
                        add_diagnostic(
                                shadow,
                                site,
                                TYPES2_DIAGNOSTIC_ERROR,
                                "bad-call",
                                callee,
                                T2_TYPE_INVALID,
                                "arguments do not satisfy the callable's names, defaults, rests, and types%s%s",
                                reason == NULL || *reason == '\0' ? "" : ": ",
                                reason == NULL ? "" : reason
                        );
                }
                free(reason);
                return t2_primitive(shadow->universe, T2_TYPE_ERROR);
        }

        int callable_class = -1;
        T2Type receiver = callee;
        if (kind == T2_TYPE_NOMINAL) {
                Types2Nominal *nominal = nominal_from_type(shadow, callee);
                if (nominal != NULL) callable_class = nominal->class_id;
        } else {
                switch (kind) {
                case T2_TYPE_STRING:
                case T2_TYPE_LITERAL_STRING: callable_class = CLASS_STRING; break;
                case T2_TYPE_INT:
                case T2_TYPE_LITERAL_INT: callable_class = CLASS_INT; break;
                case T2_TYPE_FLOAT: callable_class = CLASS_FLOAT; break;
                case T2_TYPE_BOOL:
                case T2_TYPE_LITERAL_BOOL: callable_class = CLASS_BOOL; break;
                case T2_TYPE_OBJECT: callable_class = CLASS_OBJECT; break;
                default: break;
                }
        }
        if (callable_class >= 0) {
                bool super_call = site != NULL
                               && site->type == EXPRESSION_FUNCTION_CALL
                               && site->function != NULL
                               && site->function->type == EXPRESSION_SUPER;
                if (super_call && shadow->function_count != 0) {
                        Expr const *function = shadow->functions[
                                shadow->function_count - 1
                        ].function;
                        Class *owner = function == NULL ? NULL : function->class;
                        if (owner != NULL && owner->super != NULL) {
                                callable_class = owner->super->i;
                                Types2Nominal *super_nominal = ensure_nominal(
                                        shadow,
                                        callable_class,
                                        owner->super->name,
                                        builtin_nominal_arity(callable_class)
                                );
                                if (
                                        super_nominal != NULL
                                     && t2_type_kind(shadow->universe, receiver)
                                        == T2_TYPE_NOMINAL
                                ) {
                                        T2Type projected = t2_nominal_project(
                                                shadow->universe,
                                                receiver,
                                                super_nominal->symbol
                                        );
                                        if (projected != T2_TYPE_INVALID) {
                                                receiver = projected;
                                        }
                                }
                        }
                }
                (void)ensure_class_interface(shadow, callable_class);
                Types2Member const *protocol = find_member(
                        shadow,
                        callable_class,
                        super_call ? "init" : "__call__",
                        TYPES2_MEMBER_METHOD,
                        false
                );
                if (protocol != NULL) {
                        T2Type callable = instantiate_member(
                                shadow,
                                protocol,
                                receiver,
                                site
                        );
                        return infer_call_types(
                                shadow,
                                callable,
                                arguments,
                                argument_count,
                                keyword_arguments,
                                keywords,
                                keyword_count,
                                site,
                                diagnose
                        );
                }
                if (callable_class == CLASS_FUNCTION) {
                        defer_node(shadow, TYPES2_DEFER_CALLABLE_TOP, site, NULL);
                        return t2_primitive(shadow->universe, T2_TYPE_DYNAMIC);
                }
        }
        if (diagnose) {
                add_diagnostic(
                        shadow,
                        site,
                        TYPES2_DIAGNOSTIC_ERROR,
                        "not-callable",
                        callee,
                        T2_TYPE_INVALID,
                        "value is not callable on every reachable path"
                );
        }
        return t2_primitive(shadow->universe, T2_TYPE_ERROR);
}

static T2Type
infer_runtime_call_types(
        Types2Shadow *shadow,
        T2Type callee,
        T2Type const *arguments,
        size_t argument_count,
        T2Type const *keyword_arguments,
        char const *const *keywords,
        size_t keyword_count,
        Expr const *site,
        bool diagnose
)
{
        Types2CallEffect effect = { 0 };
        Types2CallEffect *previous = shadow->call_effect_sink;
        shadow->call_effect_sink = &effect;
        T2Type result = infer_call_types(
                shadow,
                callee,
                arguments,
                argument_count,
                keyword_arguments,
                keywords,
                keyword_count,
                site,
                diagnose
        );
        shadow->call_effect_sink = previous;
        if (
                result != T2_TYPE_INVALID
             && t2_type_kind(shadow->universe, result) != T2_TYPE_ERROR
             && !t2_solver_failed(shadow->solver)
             && !propagate_call_effect(shadow, &effect, site)
        ) return t2_primitive(shadow->universe, T2_TYPE_ERROR);
        return result;
}

static T2Type
call_operator_scheme_args(
        Types2Shadow *shadow,
        T2Scheme const *scheme,
        T2Type const *arguments,
        size_t argument_count,
        Expr const *site
)
{
        T2Type callable = t2_scheme_instantiate(
                scheme,
                shadow->solver,
                shadow->level,
                source_provenance(shadow, site, "operator candidate")
        );
        if (callable == T2_TYPE_INVALID) {
                return t2_primitive(shadow->universe, T2_TYPE_ERROR);
        }
        return infer_call_types(
                shadow,
                callable,
                arguments,
                argument_count,
                NULL,
                NULL,
                0,
                site,
                false
        );
}

static unsigned
operator_type_specificity(Types2Shadow *shadow, T2Type type, unsigned depth)
{
        if (depth > 64) return 0;
        switch (t2_type_kind(shadow->universe, type)) {
        case T2_TYPE_VARIABLE:
        case T2_TYPE_META:
        case T2_TYPE_UNKNOWN:
        case T2_TYPE_DYNAMIC:
        case T2_TYPE_ANY:
        case T2_TYPE_ROW_ANY:
        case T2_TYPE_PACK_ANY:
                return 0;
        case T2_TYPE_UNION:
        {
                size_t count = t2_type_arity(shadow->universe, type);
                unsigned score = UINT_MAX;
                for (size_t i = 0; i < count; ++i) {
                        unsigned arm = operator_type_specificity(
                                shadow,
                                t2_type_child(shadow->universe, type, i),
                                depth + 1
                        );
                        if (arm < score) score = arm;
                }
                return score == UINT_MAX ? 0 : score;
        }
        default:
        {
                unsigned score = 2;
                size_t count = t2_type_arity(shadow->universe, type);
                for (size_t i = 0; i < count; ++i) {
                        score += operator_type_specificity(
                                shadow,
                                t2_type_child(shadow->universe, type, i),
                                depth + 1
                        );
                }
                return score;
        }
        }
}

static unsigned
operator_scheme_specificity(Types2Shadow *shadow, T2Scheme const *scheme)
{
        T2Type callable = t2_scheme_body(scheme);
        if (t2_type_kind(shadow->universe, callable) != T2_TYPE_FUNCTION) return 0;
        unsigned score = 0;
        size_t count = t2_callable_parameter_count(shadow->universe, callable);
        for (size_t i = 0; i < count; ++i) {
                T2ParameterSpec parameter;
                if (t2_callable_parameter(
                        shadow->universe,
                        callable,
                        i,
                        &parameter
                )) score += operator_type_specificity(
                        shadow,
                        parameter.type,
                        0
                );
        }
        return score;
}

static bool
operator_type_is_open(Types2Shadow *shadow, T2Type type, unsigned depth)
{
        if (depth > 64) return true;
        switch (t2_type_kind(shadow->universe, type)) {
        case T2_TYPE_META:
        case T2_TYPE_VARIABLE:
                return true;
        default:
                break;
        }
        for (size_t i = 0; i < t2_type_arity(shadow->universe, type); ++i) {
                if (operator_type_is_open(
                        shadow,
                        t2_type_child(shadow->universe, type, i),
                        depth + 1
                )) return true;
        }
        return false;
}

static T2Type
infer_registered_operator_call(
        Types2Shadow *shadow,
        char const *name,
        T2Type const *arguments,
        size_t argument_count,
        Expr const *site,
        bool diagnose
)
{
        bool found = false;
        size_t best = SIZE_MAX;
        unsigned best_score = 0;
        bool ambiguous = false;
        for (size_t i = 0; i < shadow->operator_count; ++i) {
                Types2Operator const *candidate = &shadow->operators[i];
                if (strcmp(candidate->name, name) != 0) continue;
                found = true;
                T2SolverMark mark = t2_solver_mark(shadow->solver);
                shadow->candidate_trials += 1;
                T2Type result = call_operator_scheme_args(
                        shadow,
                        candidate->scheme,
                        arguments,
                        argument_count,
                        site
                );
                bool applicable = result != T2_TYPE_INVALID
                               && t2_type_kind(shadow->universe, result) != T2_TYPE_ERROR
                               && !t2_solver_failed(shadow->solver);
                t2_solver_rollback(shadow->solver, mark);
                if (shadow_option_enabled("TY_TYPES2_DEBUG_OPERATORS")) {
                        char *body = t2_type_string(
                                shadow->universe,
                                t2_scheme_body(candidate->scheme)
                        );
                        fprintf(
                                stderr,
                                "operator %s candidate %s applicable=%d score=%u\n",
                                name,
                                body == NULL ? "?" : body,
                                (int)applicable,
                                operator_scheme_specificity(shadow, candidate->scheme)
                        );
                        free(body);
                }
                if (!applicable) continue;
                unsigned score = operator_scheme_specificity(
                        shadow,
                        candidate->scheme
                );
                if (best == SIZE_MAX || score > best_score) {
                        best = i;
                        best_score = score;
                }
        }
        if (!found) {
                if (!import_operator_definitions(shadow, name)) return T2_TYPE_INVALID;
                return infer_registered_operator_call(
                        shadow,
                        name,
                        arguments,
                        argument_count,
                        site,
                        diagnose
                );
        }
        if (best == SIZE_MAX || ambiguous) {
                for (size_t i = 0; i < argument_count; ++i) {
                        if (operator_type_is_open(shadow, arguments[i], 0)) {
                                defer_node(shadow, TYPES2_DEFER_OPERATOR_OPEN_OPERAND, site, name);
                                return t2_primitive(
                                        shadow->universe,
                                        T2_TYPE_DYNAMIC
                                );
                        }
                }
        }
        if (best == SIZE_MAX || ambiguous) {
                if (diagnose) add_diagnostic(
                        shadow,
                        site,
                        TYPES2_DIAGNOSTIC_ERROR,
                        best == SIZE_MAX ? "unsupported-operator" : "ambiguous-operator",
                        argument_count == 0 ? T2_TYPE_INVALID : arguments[0],
                        argument_count < 2 ? T2_TYPE_INVALID : arguments[1],
                        best == SIZE_MAX
                            ? "no registered operator accepts these operand types"
                            : "more than one equally specific operator accepts these operand types"
                );
                return t2_primitive(shadow->universe, T2_TYPE_ERROR);
        }

        T2SolverMark mark = t2_solver_mark(shadow->solver);
        T2Type result = call_operator_scheme_args(
                shadow,
                shadow->operators[best].scheme,
                arguments,
                argument_count,
                site
        );
        if (
                result != T2_TYPE_INVALID
             && t2_type_kind(shadow->universe, result) != T2_TYPE_ERROR
             && !t2_solver_failed(shadow->solver)
        ) {
                t2_solver_commit(shadow->solver, mark);
                return result;
        }
        t2_solver_rollback(shadow->solver, mark);
        return t2_primitive(shadow->universe, T2_TYPE_ERROR);
}

static T2Type
infer_registered_operator(
        Types2Shadow *shadow,
        char const *name,
        T2Type left,
        T2Type right,
        Expr const *site,
        bool diagnose
)
{
        return infer_registered_operator_call(
                shadow,
                name,
                (T2Type[]) { left, right },
                2,
                site,
                diagnose
        );
}

static char const *
binary_operation_name(uint8_t operation)
{
        switch (operation) {
        case EXPRESSION_PLUS: return "+";
        case EXPRESSION_MINUS: return "-";
        case EXPRESSION_STAR: return "*";
        case EXPRESSION_DIV: return "/";
        case EXPRESSION_PERCENT: return "%";
        case EXPRESSION_BIT_AND: return "&";
        case EXPRESSION_BIT_OR: return "|";
        case EXPRESSION_XOR: return "^";
        case EXPRESSION_SHL: return "<<";
        case EXPRESSION_SHR: return ">>";
        case EXPRESSION_LT: return "<";
        case EXPRESSION_LEQ: return "<=";
        case EXPRESSION_GT: return ">";
        case EXPRESSION_GEQ: return ">=";
        case EXPRESSION_CMP: return "<=>";
        case EXPRESSION_DBL_EQ: return "==";
        case EXPRESSION_NOT_EQ: return "!=";
        case EXPRESSION_CHECK_MATCH: return "::";
        default: return NULL;
        }
}

static bool
open_operand_kind(T2TypeKind kind)
{
        switch (kind) {
        case T2_TYPE_META:
        case T2_TYPE_VARIABLE:
        case T2_TYPE_PACK_FOLD_UNION:
        case T2_TYPE_PACK_FOLD_INTERSECTION:
        case T2_TYPE_PACK_EXPANSION:
                return true;
        default:
                return false;
        }
}

static T2Type
infer_binary_pair(
        Types2Shadow *shadow,
        uint8_t operation,
        T2Type left,
        T2Type right,
        Expr const *site,
        bool diagnose
)
{
        left = resolved_operation_type(
                shadow,
                left,
                T2_PREFER_LOWER_BOUND
        );
        right = resolved_operation_type(
                shadow,
                right,
                T2_PREFER_LOWER_BOUND
        );
        T2TypeKind left_kind = t2_type_kind(shadow->universe, left);
        T2TypeKind right_kind = t2_type_kind(shadow->universe, right);
        if (left_kind == T2_TYPE_ERROR || right_kind == T2_TYPE_ERROR) {
                return t2_primitive(shadow->universe, T2_TYPE_ERROR);
        }
        if (left_kind == T2_TYPE_DYNAMIC || right_kind == T2_TYPE_DYNAMIC) {
                defer_node(shadow, TYPES2_DEFER_DYNAMIC_OPERAND, site, NULL);
                return t2_primitive(shadow->universe, T2_TYPE_DYNAMIC);
        }
        if (left_kind == T2_TYPE_UNION || right_kind == T2_TYPE_UNION) {
                T2Type union_type = left_kind == T2_TYPE_UNION ? left : right;
                T2Type other = left_kind == T2_TYPE_UNION ? right : left;
                size_t count = t2_type_arity(shadow->universe, union_type);
                T2Type result = t2_primitive(shadow->universe, T2_TYPE_NEVER);
                for (size_t i = 0; i < count; ++i) {
                        T2Type arm = t2_type_child(shadow->universe, union_type, i);
                        T2Type arm_result = left_kind == T2_TYPE_UNION
                                          ? infer_binary_pair(
                                                  shadow,
                                                  operation,
                                                  arm,
                                                  other,
                                                  site,
                                                  false
                                            )
                                          : infer_binary_pair(
                                                  shadow,
                                                  operation,
                                                  other,
                                                  arm,
                                                  site,
                                                  false
                                            );
                        if (t2_type_kind(shadow->universe, arm_result) == T2_TYPE_ERROR) {
                                if (diagnose) {
                                        add_diagnostic(
                                                shadow,
                                                site,
                                                TYPES2_DIAGNOSTIC_ERROR,
                                                "union-operator-coverage",
                                                left,
                                                right,
                                                "every reachable union operand combination must support the operator"
                                        );
                                }
                                return arm_result;
                        }
                        result = t2_join(shadow->universe, result, arm_result);
                }
                return result;
        }

        left_kind = t2_type_kind(shadow->universe, relax_literal(shadow, left));
        right_kind = t2_type_kind(shadow->universe, relax_literal(shadow, right));
        T2Type integer = t2_primitive(shadow->universe, T2_TYPE_INT);
        T2Type floating = t2_primitive(shadow->universe, T2_TYPE_FLOAT);
        T2Type string = t2_primitive(shadow->universe, T2_TYPE_STRING);
        T2Type boolean = t2_primitive(shadow->universe, T2_TYPE_BOOL);

        if (
                left_kind == T2_TYPE_TUPLE
             && right_kind == T2_TYPE_TUPLE
             && (
                        operation == EXPRESSION_LT
                     || operation == EXPRESSION_LEQ
                     || operation == EXPRESSION_GT
                     || operation == EXPRESSION_GEQ
                     || operation == EXPRESSION_CMP
                )
        ) {
                size_t left_count = t2_type_arity(shadow->universe, left);
                size_t right_count = t2_type_arity(shadow->universe, right);
                size_t count = left_count < right_count ? left_count : right_count;
                for (size_t i = 0; i < count; ++i) {
                        T2Type compared = infer_binary_pair(
                                shadow,
                                EXPRESSION_CMP,
                                t2_type_child(shadow->universe, left, i),
                                t2_type_child(shadow->universe, right, i),
                                site,
                                false
                        );
                        if (
                                compared == T2_TYPE_INVALID
                             || t2_type_kind(shadow->universe, compared)
                                == T2_TYPE_ERROR
                        ) {
                                if (diagnose) add_diagnostic(
                                        shadow,
                                        site,
                                        TYPES2_DIAGNOSTIC_ERROR,
                                        "unsupported-operator",
                                        left,
                                        right,
                                        "tuple comparison requires every corresponding element pair to be comparable"
                                );
                                return t2_primitive(
                                        shadow->universe,
                                        T2_TYPE_ERROR
                                );
                        }
                }
                return operation == EXPRESSION_CMP ? integer : boolean;
        }

        switch (operation) {
        case EXPRESSION_PLUS:
                if (left_kind == T2_TYPE_INT && right_kind == T2_TYPE_INT) return integer;
                if (
                        (left_kind == T2_TYPE_INT || left_kind == T2_TYPE_FLOAT)
                     && (right_kind == T2_TYPE_INT || right_kind == T2_TYPE_FLOAT)
                ) return floating;
                if (left_kind == T2_TYPE_STRING && right_kind == T2_TYPE_STRING) return string;
                if (
                        left_kind == T2_TYPE_STRING
                     && (right_kind == T2_TYPE_INT || right_kind == T2_TYPE_BOOL)
                ) return string;
                break;
        case EXPRESSION_MINUS:
                if (
                        left_kind == T2_TYPE_STRING
                     && (right_kind == T2_TYPE_INT || right_kind == T2_TYPE_BOOL)
                ) return string;
                if (left_kind == T2_TYPE_INT && right_kind == T2_TYPE_INT) {
                        return integer;
                }
                if (
                        (left_kind == T2_TYPE_INT || left_kind == T2_TYPE_FLOAT)
                     && (right_kind == T2_TYPE_INT || right_kind == T2_TYPE_FLOAT)
                ) return floating;
                break;
        case EXPRESSION_STAR:
                if (left_kind == T2_TYPE_STRING && right_kind == T2_TYPE_INT) {
                        return string;
                }
                if (left_kind == T2_TYPE_INT && right_kind == T2_TYPE_INT) {
                        return integer;
                }
                if (
                        (left_kind == T2_TYPE_INT || left_kind == T2_TYPE_FLOAT)
                     && (right_kind == T2_TYPE_INT || right_kind == T2_TYPE_FLOAT)
                ) return floating;
                break;
        case EXPRESSION_DIV:
        case EXPRESSION_PERCENT:
                if (left_kind == T2_TYPE_INT && right_kind == T2_TYPE_INT) {
                        return integer;
                }
                if (
                        (left_kind == T2_TYPE_INT || left_kind == T2_TYPE_FLOAT)
                     && (right_kind == T2_TYPE_INT || right_kind == T2_TYPE_FLOAT)
                ) return floating;
                break;
        case EXPRESSION_BIT_AND:
        case EXPRESSION_BIT_OR:
        case EXPRESSION_XOR:
        case EXPRESSION_SHL:
        case EXPRESSION_SHR:
                if (left_kind == T2_TYPE_INT && right_kind == T2_TYPE_INT) return integer;
                break;
        case EXPRESSION_LT:
        case EXPRESSION_LEQ:
        case EXPRESSION_GT:
        case EXPRESSION_GEQ:
        case EXPRESSION_CMP:
                if (
                        (left_kind == T2_TYPE_INT || left_kind == T2_TYPE_FLOAT)
                     && (right_kind == T2_TYPE_INT || right_kind == T2_TYPE_FLOAT)
                ) return operation == EXPRESSION_CMP ? integer : boolean;
                if (left_kind == T2_TYPE_STRING && right_kind == T2_TYPE_STRING) {
                        return operation == EXPRESSION_CMP ? integer : boolean;
                }
                break;
        case EXPRESSION_DBL_EQ:
        case EXPRESSION_NOT_EQ:
        case EXPRESSION_CHECK_MATCH:
                return boolean;
        default:
                break;
        }

        char const *name = binary_operation_name(operation);
        if (name != NULL) {
                T2Type registered = infer_registered_operator(
                        shadow,
                        name,
                        left,
                        right,
                        site,
                        diagnose
                );
                if (registered != T2_TYPE_INVALID) return registered;
        }

        if (open_operand_kind(left_kind) || open_operand_kind(right_kind)) {
                defer_node(shadow, TYPES2_DEFER_OPERATOR_OPEN_OPERAND, site, name);
                switch (operation) {
                case EXPRESSION_LT:
                case EXPRESSION_LEQ:
                case EXPRESSION_GT:
                case EXPRESSION_GEQ:
                        return boolean;
                case EXPRESSION_CMP:
                        return integer;
                default:
                        return t2_primitive(shadow->universe, T2_TYPE_DYNAMIC);
                }
        }
        if (left_kind == T2_TYPE_NOMINAL || right_kind == T2_TYPE_NOMINAL) {
                defer_node(shadow, TYPES2_DEFER_OPERATOR_PROTOCOL, site, name);
                return t2_primitive(shadow->universe, T2_TYPE_DYNAMIC);
        }
        if (diagnose) {
                add_diagnostic(
                        shadow,
                        site,
                        TYPES2_DIAGNOSTIC_ERROR,
                        "unsupported-operator",
                        left,
                        right,
                        "operator is not defined for these operand types"
                );
        }
        return t2_primitive(shadow->universe, T2_TYPE_ERROR);
}

static T2Type
infer_subscript_protocol(
        Types2Shadow *shadow,
        T2Type container,
        T2Type const *arguments,
        size_t argument_count,
        char const *name,
        Expr const *site
)
{
        container = resolved_operation_type(
                shadow,
                container,
                T2_PREFER_LOWER_BOUND
        );
        if (t2_type_kind(shadow->universe, container) == T2_TYPE_TYPE_VALUE) {
                T2Type instance = t2_type_value_instance(
                        shadow->universe,
                        container
                );
                Types2Nominal *nominal = nominal_from_type(shadow, instance);
                int class_id = nominal == NULL ? -1 : nominal->class_id;
                if (class_id >= 0) {
                        (void)ensure_class_interface(shadow, class_id);
                        Types2Member const *member = find_member(
                                shadow,
                                class_id,
                                name,
                                TYPES2_MEMBER_METHOD,
                                true
                        );
                        if (member != NULL) {
                                T2Type callable = instantiate_member(
                                        shadow,
                                        member,
                                        instance,
                                        site
                                );
                                return infer_call_types(
                                        shadow,
                                        callable,
                                        arguments,
                                        argument_count,
                                        NULL,
                                        NULL,
                                        0,
                                        site,
                                        false
                                );
                        }
                }
        }
        if (t2_type_kind(shadow->universe, container) == T2_TYPE_RECORD) {
                T2Type member = t2_record_field_type(
                        shadow->universe,
                        container,
                        name,
                        NULL,
                        NULL
                );
                if (member != T2_TYPE_INVALID) {
                        return infer_call_types(
                                shadow,
                                member,
                                arguments,
                                argument_count,
                                NULL,
                                NULL,
                                0,
                                site,
                                false
                        );
                }

                /*
                 * An inferred structural receiver can acquire a subscript
                 * capability after its original metavariable has already
                 * been zonked to a record.  Retain that information in the
                 * open row instead of leaving the external predicate asleep
                 * forever.  Exact records and unconstrained ROW_ANY tails
                 * correctly reject the requirement in the subtype solver.
                 */
                T2SolverMark protocol = t2_solver_mark(shadow->solver);
                T2Type *parameters = argument_count == 0
                                   ? NULL
                                   : malloc(argument_count * sizeof *parameters);
                if (argument_count != 0 && parameters == NULL) {
                        shadow->failed = true;
                        t2_solver_rollback(shadow->solver, protocol);
                        return T2_TYPE_INVALID;
                }
                bool valid = true;
                for (size_t i = 0; i < argument_count; ++i) {
                        parameters[i] = t2_solver_new_meta(
                                shadow->solver,
                                T2_VARIABLE_FLEXIBLE,
                                shadow->level,
                                name
                        );
                        valid = valid
                             && parameters[i] != T2_TYPE_INVALID
                             && constrain_type_maybe_diagnose(
                                        shadow,
                                        site,
                                        arguments[i],
                                        parameters[i],
                                        false,
                                        "subscript-protocol-argument",
                                        "subscript argument must satisfy the inferred protocol"
                                );
                }
                T2Type result = t2_solver_new_meta(
                        shadow->solver,
                        T2_VARIABLE_FLEXIBLE,
                        shadow->level,
                        name
                );
                T2Type callable = t2_function(
                        shadow->universe,
                        parameters,
                        argument_count,
                        result
                );
                free(parameters);
                T2Type row = t2_solver_new_meta(
                        shadow->solver,
                        T2_VARIABLE_ROW,
                        shadow->level,
                        "subscript protocol row"
                );
                T2FieldSpec requirement = {
                        .name = name,
                        .type = callable,
                        .presence = T2_PRESENCE_REQUIRED,
                        .capability = T2_FIELD_READONLY
                };
                T2Type record = t2_record(
                        shadow->universe,
                        &requirement,
                        1,
                        row,
                        T2_RECORD_OPEN
                );
                valid = valid
                     && result != T2_TYPE_INVALID
                     && callable != T2_TYPE_INVALID
                     && row != T2_TYPE_INVALID
                     && record != T2_TYPE_INVALID
                     && constrain_type_maybe_diagnose(
                                shadow,
                                site,
                                container,
                                record,
                                false,
                                "subscript-protocol-requirement",
                                "value must provide the inferred subscript protocol"
                        )
                     && !t2_solver_failed(shadow->solver);
                if (valid) {
                        t2_solver_commit(shadow->solver, protocol);
                        return result;
                }
                t2_solver_rollback(shadow->solver, protocol);
        }

        Types2Nominal *nominal = nominal_from_type(shadow, container);
        if (nominal != NULL) {
                /* Interface discovery may grow the nominal table.  Keep only
                 * the stable class id across that operation. */
                int class_id = nominal->class_id;
                (void)ensure_class_interface(shadow, class_id);
                Types2Member const *member = find_member(
                        shadow,
                        class_id,
                        name,
                        TYPES2_MEMBER_METHOD,
                        false
                );
                if (member != NULL) {
                        T2SolverMark mark = t2_solver_mark(shadow->solver);
                        T2Type callable = instantiate_member(
                                shadow,
                                member,
                                container,
                                site
                        );
                        T2Type result = infer_call_types(
                                shadow,
                                callable,
                                arguments,
                                argument_count,
                                NULL,
                                NULL,
                                0,
                                site,
                                false
                        );
                        if (
                                result != T2_TYPE_INVALID
                             && t2_type_kind(shadow->universe, result)
                                != T2_TYPE_ERROR
                             && !t2_solver_failed(shadow->solver)
                        ) {
                                t2_solver_commit(shadow->solver, mark);
                                return result;
                        }
                        t2_solver_rollback(shadow->solver, mark);
                }
        }

        if (argument_count == SIZE_MAX) {
                shadow->failed = true;
                return T2_TYPE_INVALID;
        }
        T2Type *operator_arguments = malloc(
                (argument_count + 1) * sizeof *operator_arguments
        );
        if (operator_arguments == NULL) {
                shadow->failed = true;
                return T2_TYPE_INVALID;
        }
        operator_arguments[0] = container;
        if (argument_count != 0) {
                memcpy(
                        operator_arguments + 1,
                        arguments,
                        argument_count * sizeof *operator_arguments
                );
        }
        T2Type result = infer_registered_operator_call(
                shadow,
                name,
                operator_arguments,
                argument_count + 1,
                site,
                false
        );
        free(operator_arguments);
        return result;
}

static T2Type
infer_subscript_type(
        Types2Shadow *shadow,
        T2Type container,
        T2Type index,
        Expr const *index_expression,
        Expr const *site,
        bool diagnose
)
{
        container = resolved_operation_type(
                shadow,
                container,
                T2_PREFER_LOWER_BOUND
        );
        T2TypeKind kind = t2_type_kind(shadow->universe, container);
        if (kind == T2_TYPE_UNION) {
                T2SolverMark coverage = t2_solver_mark(shadow->solver);
                T2Type result = t2_primitive(shadow->universe, T2_TYPE_NEVER);
                size_t count = t2_type_arity(shadow->universe, container);
                for (size_t i = 0; i < count; ++i) {
                        T2Type arm = infer_subscript_type(
                                shadow,
                                t2_type_child(shadow->universe, container, i),
                                index,
                                index_expression,
                                site,
                                false
                        );
                        if (t2_type_kind(shadow->universe, arm) == T2_TYPE_ERROR) {
                                t2_solver_rollback(shadow->solver, coverage);
                                if (diagnose) {
                                        add_diagnostic(
                                                shadow,
                                                site,
                                                TYPES2_DIAGNOSTIC_ERROR,
                                                "union-subscript-coverage",
                                                container,
                                                index,
                                                "every reachable union arm must support this subscript"
                                        );
                                }
                                return arm;
                        }
                        result = t2_join(shadow->universe, result, arm);
                }
                t2_solver_commit(shadow->solver, coverage);
                return result;
        }
        if (kind == T2_TYPE_DYNAMIC || kind == T2_TYPE_ERROR) return container;
        if (kind == T2_TYPE_STRING || kind == T2_TYPE_LITERAL_STRING) {
                if (!constrain_type_maybe_diagnose(
                        shadow,
                        site,
                        index,
                        t2_primitive(shadow->universe, T2_TYPE_INT),
                        diagnose,
                        "bad-subscript",
                        "string index must be an Int"
                )) return t2_primitive(shadow->universe, T2_TYPE_ERROR);
                return t2_union(
                        shadow->universe,
                        (T2Type[]){
                                t2_primitive(shadow->universe, T2_TYPE_STRING),
                                t2_primitive(shadow->universe, T2_TYPE_NIL)
                        },
                        2
                );
        }
        if (kind == T2_TYPE_TUPLE) {
                if (
                        index_expression != NULL
                     && index_expression->type == EXPRESSION_INTEGER
                ) {
                        intmax_t position = index_expression->integer;
                        size_t count = t2_type_arity(shadow->universe, container);
                        if (position < 0) position += (intmax_t)count;
                        if (position >= 0 && (uintmax_t)position < count) {
                                return t2_type_child(
                                        shadow->universe,
                                        container,
                                        (size_t)position
                                );
                        }
                        if (diagnose) {
                                add_diagnostic(
                                        shadow,
                                        site,
                                        TYPES2_DIAGNOSTIC_ERROR,
                                        "tuple-index-range",
                                        index,
                                        container,
                                        "constant tuple index is out of range"
                                );
                        }
                        return t2_primitive(shadow->universe, T2_TYPE_ERROR);
                }
                if (!constrain_type_maybe_diagnose(
                        shadow,
                        site,
                        index,
                        t2_primitive(shadow->universe, T2_TYPE_INT),
                        diagnose,
                        "bad-subscript",
                        "tuple index must be an Int"
                )) return t2_primitive(shadow->universe, T2_TYPE_ERROR);
                /* Ordinary tuple subscripting is strict at runtime.  An
                 * unknown integer index may select any positional element,
                 * but an out-of-range index throws rather than producing
                 * nil. */
                T2Type result = t2_primitive(shadow->universe, T2_TYPE_NEVER);
                for (size_t i = 0; i < t2_type_arity(shadow->universe, container); ++i) {
                        result = t2_join(
                                shadow->universe,
                                result,
                                t2_type_child(shadow->universe, container, i)
                        );
                }
                return result;
        }
        Types2Nominal *nominal = nominal_from_type(shadow, container);
        if (nominal != NULL) {
                if (nominal->class_id == CLASS_ARRAY) {
                        T2Type integer = t2_primitive(
                                shadow->universe,
                                T2_TYPE_INT
                        );
                        T2Relation integer_index = is_dynamic_type(shadow, index)
                                                 ? T2_RELATION_YES
                                                 : t2_consistent(
                                                         shadow->universe,
                                                         index,
                                                         integer
                                                   );
                        if (integer_index == T2_RELATION_NO) {
                                T2Type overloaded = infer_subscript_protocol(
                                        shadow,
                                        container,
                                        &index,
                                        1,
                                        "[]",
                                        site
                                );
                                if (overloaded != T2_TYPE_INVALID) return overloaded;
                        }
                        if (!constrain_type_maybe_diagnose(
                                shadow,
                                site,
                                index,
                                integer,
                                diagnose,
                                "bad-subscript",
                                "array index must be an Int"
                        )) return t2_primitive(shadow->universe, T2_TYPE_ERROR);
                        /* ArraySubscript(..., strict=true) raises IndexError
                         * for an invalid position.  Model that partial
                         * operation as a throwing T read, not as T | nil. */
                        return t2_type_child(shadow->universe, container, 0);
                }
                if (nominal->class_id == CLASS_DICT) {
                        if (!constrain_type_maybe_diagnose(
                                shadow,
                                site,
                                index,
                                t2_type_child(shadow->universe, container, 0),
                                diagnose,
                                "bad-subscript",
                                "dictionary key has the wrong type"
                        )) return t2_primitive(shadow->universe, T2_TYPE_ERROR);
                        return t2_union(
                                shadow->universe,
                                (T2Type[]){
                                        t2_type_child(shadow->universe, container, 1),
                                        t2_primitive(shadow->universe, T2_TYPE_NIL)
                                },
                                2
                        );
                }
                T2Type overloaded = infer_subscript_protocol(
                        shadow,
                        container,
                        &index,
                        1,
                        "[]",
                        site
                );
                if (overloaded != T2_TYPE_INVALID) return overloaded;
        }
        if (kind == T2_TYPE_RECORD || kind == T2_TYPE_TYPE_VALUE) {
                T2Type overloaded = infer_subscript_protocol(
                        shadow,
                        container,
                        &index,
                        1,
                        "[]",
                        site
                );
                if (overloaded != T2_TYPE_INVALID) return overloaded;
        }
        if (kind == T2_TYPE_META) {
                T2Type result = t2_solver_new_meta(
                        shadow->solver,
                        T2_VARIABLE_FLEXIBLE,
                        shadow->level,
                        "subscript result"
                );
                if (result == T2_TYPE_INVALID) return result;
                if (constrain_predicate(
                        shadow,
                        site,
                        (T2Predicate) {
                                .kind = T2_PREDICATE_SUBSCRIPT_READ,
                                .subtype = container,
                                .supertype = result,
                                .operand = index,
                                .name = "[]"
                        },
                        "subscript-read-contract",
                        "value must expose a compatible subscript read contract"
                )) return result;
                return t2_primitive(shadow->universe, T2_TYPE_ERROR);
        }
        if (diagnose) {
                add_diagnostic(
                        shadow,
                        site,
                        TYPES2_DIAGNOSTIC_ERROR,
                        "not-subscriptable",
                        container,
                        index,
                        "value does not support this subscript operation"
                );
        }
        return t2_primitive(shadow->universe, T2_TYPE_ERROR);
}

static Types2Member *
find_missing_member(Types2Shadow *shadow, int class_id, Types2MemberKind kind)
{
        Types2Member *member = find_member(shadow, class_id, "__missing__", kind, false);
        if (member == NULL) {
                member = find_member(shadow, class_id, "__missing__=", kind, false);
        }
        return member;
}

static T2Type
infer_member_type(
        Types2Shadow *shadow,
        T2Type object,
        char const *name,
        bool safe,
        Expr const *site,
        bool diagnose
)
{
        object = resolved_operation_type(
                shadow,
                object,
                T2_PREFER_LOWER_BOUND
        );
        T2TypeKind kind = t2_type_kind(shadow->universe, object);
        T2Type nil = t2_primitive(shadow->universe, T2_TYPE_NIL);
        if (kind == T2_TYPE_UNION) {
                T2Type result = t2_primitive(shadow->universe, T2_TYPE_NEVER);
                size_t count = t2_type_arity(shadow->universe, object);
                for (size_t i = 0; i < count; ++i) {
                        T2Type arm_type = t2_type_child(shadow->universe, object, i);
                        if (safe && t2_type_kind(shadow->universe, arm_type) == T2_TYPE_NIL) {
                                result = t2_join(shadow->universe, result, nil);
                                continue;
                        }
                        T2Type arm = infer_member_type(
                                shadow,
                                arm_type,
                                name,
                                safe,
                                site,
                                false
                        );
                        if (t2_type_kind(shadow->universe, arm) == T2_TYPE_ERROR) {
                                if (safe) arm = nil;
                                else {
                                        if (diagnose) {
                                                add_diagnostic(
                                                        shadow,
                                                        site,
                                                        TYPES2_DIAGNOSTIC_ERROR,
                                                        "union-member-coverage",
                                                        object,
                                                        T2_TYPE_INVALID,
                                                        "field `%s` must exist on every reachable union arm",
                                                        name
                                                );
                                        }
                                        return arm;
                                }
                        }
                        result = t2_join(shadow->universe, result, arm);
                }
                return safe ? t2_join(shadow->universe, result, nil) : result;
        }
        if (kind == T2_TYPE_INTERSECTION) {
                T2Type result = T2_TYPE_INVALID;
                size_t count = t2_type_arity(shadow->universe, object);
                for (size_t i = 0; i < count; ++i) {
                        T2SolverMark trial = t2_solver_mark(shadow->solver);
                        T2Type arm = infer_member_type(
                                shadow,
                                t2_type_child(shadow->universe, object, i),
                                name,
                                false,
                                site,
                                false
                        );
                        if (
                                t2_type_kind(shadow->universe, arm)
                                == T2_TYPE_ERROR
                             || t2_solver_failed(shadow->solver)
                        ) {
                                t2_solver_rollback(shadow->solver, trial);
                                continue;
                        }
                        t2_solver_commit(shadow->solver, trial);
                        result = result == T2_TYPE_INVALID
                               ? arm
                               : t2_meet(shadow->universe, result, arm);
                }
                if (result != T2_TYPE_INVALID) {
                        return safe
                             ? t2_join(shadow->universe, result, nil)
                             : result;
                }
                if (safe) return nil;
        }
        if (kind == T2_TYPE_TYPE_VALUE) {
                T2Type instance = t2_type_value_instance(
                        shadow->universe,
                        object
                );
                Types2Nominal *nominal = nominal_from_type(shadow, instance);
                int class_id = nominal == NULL ? -1 : nominal->class_id;
                if (class_id >= 0) {
                        (void)ensure_class_interface(shadow, class_id);
                        Types2Member *member = find_member(
                                shadow,
                                class_id,
                                name,
                                TYPES2_MEMBER_FIELD,
                                true
                        );
                        bool getter = false;
                        if (member == NULL) {
                                member = find_member(
                                        shadow,
                                        class_id,
                                        name,
                                        TYPES2_MEMBER_GETTER,
                                        true
                                );
                                getter = member != NULL;
                        }
                        if (member == NULL) {
                                member = find_member(
                                        shadow,
                                        class_id,
                                        name,
                                        TYPES2_MEMBER_METHOD,
                                        true
                                );
                        }
                        if (member != NULL) {
                                T2Type value = instantiate_member(
                                        shadow,
                                        member,
                                        instance,
                                        site
                                );
                                if (getter) {
                                        value = infer_call_types(
                                                shadow,
                                                value,
                                                NULL,
                                                0,
                                                NULL,
                                                NULL,
                                                0,
                                                site,
                                                diagnose
                                        );
                                }
                                return safe
                                     ? t2_join(shadow->universe, value, nil)
                                     : value;
                        }
                }
                if (safe) return nil;
                if (diagnose) add_diagnostic(
                        shadow,
                        site,
                        TYPES2_DIAGNOSTIC_ERROR,
                        "missing-static-member",
                        object,
                        T2_TYPE_INVALID,
                        "static member `%s` is not present",
                        name
                );
                return t2_primitive(shadow->universe, T2_TYPE_ERROR);
        }
        if (kind == T2_TYPE_NIL && safe) return nil;
        if (kind == T2_TYPE_DYNAMIC || kind == T2_TYPE_ERROR) return object;
        if (kind == T2_TYPE_RECORD) {
                T2Presence presence;
                T2Type field = t2_record_field_type(
                        shadow->universe,
                        object,
                        name,
                        &presence,
                        NULL
                );
                if (field != T2_TYPE_INVALID) {
                        if (presence != T2_PRESENCE_REQUIRED || safe) {
                                field = t2_join(shadow->universe, field, nil);
                        }
                        return field;
                }
                if (safe) return nil;
        }
        if (kind == T2_TYPE_META) {
                T2Type field = t2_solver_new_meta(
                        shadow->solver,
                        T2_VARIABLE_FLEXIBLE,
                        shadow->level,
                        name
                );
                T2Type none = t2_primitive(
                        shadow->universe,
                        T2_TYPE_NEVER
                );
                bool valid = constrain_predicate_maybe_diagnose(
                        shadow,
                        site,
                        (T2Predicate) {
                                .kind = T2_PREDICATE_MEMBER_READ,
                                .subtype = object,
                                .supertype = field,
                                .operand = none,
                                .name = name
                        },
                        diagnose,
                        "member-requirement",
                        "value must provide the accessed field"
                );
                if (valid) {
                        return safe
                             ? t2_join(shadow->universe, field, nil)
                             : field;
                }
                return t2_primitive(shadow->universe, T2_TYPE_ERROR);
        }
        int class_id = -1;
        Types2Nominal *nominal = NULL;
        if (kind == T2_TYPE_NOMINAL) {
                nominal = nominal_from_type(shadow, object);
                if (nominal != NULL) class_id = nominal->class_id;
        } else {
                switch (kind) {
                case T2_TYPE_STRING:
                case T2_TYPE_LITERAL_STRING: class_id = CLASS_STRING; break;
                case T2_TYPE_INT:
                case T2_TYPE_LITERAL_INT: class_id = CLASS_INT; break;
                case T2_TYPE_FLOAT: class_id = CLASS_FLOAT; break;
                case T2_TYPE_BOOL:
                case T2_TYPE_LITERAL_BOOL: class_id = CLASS_BOOL; break;
                case T2_TYPE_FUNCTION:
                case T2_TYPE_OVERLOAD: class_id = CLASS_FUNCTION; break;
                case T2_TYPE_TUPLE: class_id = CLASS_TUPLE; break;
                default: break;
                }
        }
        if (class_id >= 0) {
                (void)ensure_class_interface(shadow, class_id);
                nominal = find_class_nominal(shadow, class_id);
                Types2Member *member = find_member(
                        shadow,
                        class_id,
                        name,
                        TYPES2_MEMBER_FIELD,
                        false
                );
                if (member == NULL) {
                        member = find_member(
                                shadow,
                                class_id,
                                name,
                                TYPES2_MEMBER_GETTER,
                                false
                        );
                }
                bool getter = member != NULL && member->kind == TYPES2_MEMBER_GETTER;
                if (member == NULL) {
                        member = find_member(
                                shadow,
                                class_id,
                                name,
                                TYPES2_MEMBER_METHOD,
                                false
                        );
                }
                if (member != NULL) {
                        T2Type value = instantiate_member(shadow, member, object, site);
                        if (getter) {
                                value = infer_call_types(
                                        shadow,
                                        value,
                                        NULL,
                                        0,
                                        NULL,
                                        NULL,
                                        0,
                                        site,
                                        diagnose
                                );
                        }
                        return safe ? t2_join(shadow->universe, value, nil) : value;
                }
                Types2Member *missing = find_missing_member(
                        shadow,
                        class_id,
                        TYPES2_MEMBER_METHOD
                );
                if (missing != NULL) {
                        T2Type handler = instantiate_member(shadow, missing, object, site);
                        T2Type field_name = t2_literal_string(shadow->universe, name);
                        T2Type value = infer_call_types(
                                shadow,
                                handler,
                                &field_name,
                                1,
                                NULL,
                                NULL,
                                0,
                                site,
                                diagnose
                        );
                        return safe ? t2_join(shadow->universe, value, nil) : value;
                }
                /* A recursive member lookup can discover trait/superclass
                 * nominals and reallocate the nominal table. */
                nominal = find_class_nominal(shadow, class_id);
                if (nominal == NULL || !nominal->complete) {
                        defer_node(shadow, TYPES2_DEFER_INCOMPLETE_INTERFACE, site, name);
                        return t2_primitive(shadow->universe, T2_TYPE_DYNAMIC);
                }
                if (safe) return nil;
        }
        if (diagnose) {
                add_diagnostic(
                        shadow,
                        site,
                        TYPES2_DIAGNOSTIC_ERROR,
                        "missing-field",
                        object,
                        T2_TYPE_INVALID,
                        "field `%s` is not present",
                        name
                );
        }
        return t2_primitive(shadow->universe, T2_TYPE_ERROR);
}

static T2Type
infer_method_type(
        Types2Shadow *shadow,
        T2Type object,
        char const *name,
        bool safe,
        Expr const *site,
        bool diagnose
)
{
        object = resolved_type_head(
                shadow,
                object,
                T2_PREFER_LOWER_BOUND
        );
        T2TypeKind kind = t2_type_kind(shadow->universe, object);
        T2Type nil = t2_primitive(shadow->universe, T2_TYPE_NIL);
        if (kind == T2_TYPE_UNION) {
                T2SolverMark coverage = t2_solver_mark(shadow->solver);
                T2Type result = t2_primitive(shadow->universe, T2_TYPE_NEVER);
                for (size_t i = 0; i < t2_type_arity(shadow->universe, object); ++i) {
                        T2Type arm_type = t2_type_child(
                                shadow->universe,
                                object,
                                i
                        );
                        if (
                                safe
                             && t2_type_kind(shadow->universe, arm_type)
                                == T2_TYPE_NIL
                        ) {
                                result = t2_join(shadow->universe, result, nil);
                                continue;
                        }
                        T2Type arm = infer_method_type(
                                shadow,
                                arm_type,
                                name,
                                safe,
                                site,
                                false
                        );
                        if (t2_type_kind(shadow->universe, arm) == T2_TYPE_ERROR) {
                                t2_solver_rollback(shadow->solver, coverage);
                                if (safe) return nil;
                                if (diagnose) add_diagnostic(
                                        shadow,
                                        site,
                                        TYPES2_DIAGNOSTIC_ERROR,
                                        "union-method-coverage",
                                        object,
                                        T2_TYPE_INVALID,
                                        "method `%s` must exist on every reachable union arm",
                                        name
                                );
                                return arm;
                        }
                        result = t2_join(shadow->universe, result, arm);
                }
                t2_solver_commit(shadow->solver, coverage);
                return result;
        }
        if (kind == T2_TYPE_DYNAMIC || kind == T2_TYPE_ERROR) return object;
        if (kind == T2_TYPE_NIL && safe) return nil;

        bool is_static = kind == T2_TYPE_TYPE_VALUE;
        T2Type receiver = is_static
                        ? t2_type_value_instance(shadow->universe, object)
                        : object;
        int class_id = -1;
        Types2Nominal *nominal = nominal_from_type(shadow, receiver);
        if (nominal != NULL) class_id = nominal->class_id;
        else {
                switch (t2_type_kind(shadow->universe, receiver)) {
                case T2_TYPE_STRING:
                case T2_TYPE_LITERAL_STRING: class_id = CLASS_STRING; break;
                case T2_TYPE_INT:
                case T2_TYPE_LITERAL_INT: class_id = CLASS_INT; break;
                case T2_TYPE_FLOAT: class_id = CLASS_FLOAT; break;
                case T2_TYPE_BOOL:
                case T2_TYPE_LITERAL_BOOL: class_id = CLASS_BOOL; break;
                case T2_TYPE_FUNCTION:
                case T2_TYPE_OVERLOAD: class_id = CLASS_FUNCTION; break;
                case T2_TYPE_TUPLE: class_id = CLASS_TUPLE; break;
                default: break;
                }
        }
        if (class_id >= 0) {
                (void)ensure_class_interface(shadow, class_id);
                Types2Member *member = find_member(
                        shadow,
                        class_id,
                        name,
                        TYPES2_MEMBER_METHOD,
                        is_static
                );
                if (member == NULL) {
                        member = find_member(
                                shadow,
                                class_id,
                                name,
                                TYPES2_MEMBER_GETTER,
                                is_static
                        );
                }
                if (member != NULL) {
                        return instantiate_member(
                                shadow,
                                member,
                                receiver,
                                site
                        );
                }
        }

        return infer_member_type(
                shadow,
                object,
                name,
                safe,
                site,
                diagnose
        );
}

static bool
check_membership(
        Types2Shadow *shadow,
        T2Type item,
        T2Type container,
        Expr const *site,
        bool diagnose
)
{
        container = resolved_operation_type(
                shadow,
                container,
                T2_PREFER_LOWER_BOUND
        );
        T2TypeKind kind = t2_type_kind(shadow->universe, container);
        if (kind == T2_TYPE_DYNAMIC || kind == T2_TYPE_ERROR) return true;
        if (kind == T2_TYPE_UNION) {
                T2SolverMark coverage = t2_solver_mark(shadow->solver);
                for (size_t i = 0; i < t2_type_arity(shadow->universe, container); ++i) {
                        if (!check_membership(
                                shadow,
                                item,
                                t2_type_child(shadow->universe, container, i),
                                site,
                                false
                        )) {
                                t2_solver_rollback(shadow->solver, coverage);
                                if (diagnose) add_diagnostic(
                                        shadow,
                                        site,
                                        TYPES2_DIAGNOSTIC_ERROR,
                                        "union-membership-coverage",
                                        item,
                                        container,
                                        "every reachable union arm must support membership"
                                );
                                return false;
                        }
                }
                t2_solver_commit(shadow->solver, coverage);
                return true;
        }

        Types2Nominal *nominal = nominal_from_type(shadow, container);
        if (nominal != NULL && nominal->class_id == CLASS_ARRAY) {
                return constrain_type_maybe_diagnose(
                        shadow,
                        site,
                        item,
                        t2_type_child(shadow->universe, container, 0),
                        diagnose,
                        "membership-type",
                        "array membership item has the wrong element type"
                );
        }
        if (nominal != NULL && nominal->class_id == CLASS_DICT) {
                return constrain_type_maybe_diagnose(
                        shadow,
                        site,
                        item,
                        t2_type_child(shadow->universe, container, 0),
                        diagnose,
                        "membership-type",
                        "dictionary membership uses the key type"
                );
        }
        if (kind == T2_TYPE_STRING || kind == T2_TYPE_LITERAL_STRING) {
                return constrain_type_maybe_diagnose(
                        shadow,
                        site,
                        item,
                        t2_primitive(shadow->universe, T2_TYPE_STRING),
                        diagnose,
                        "membership-type",
                        "string membership requires a String"
                );
        }

        T2SolverMark protocol = t2_solver_mark(shadow->solver);
        T2Type method = infer_method_type(
                shadow,
                container,
                "contains?",
                false,
                site,
                false
        );
        T2Type result = infer_call_types(
                shadow,
                method,
                &item,
                1,
                NULL,
                NULL,
                0,
                site,
                false
        );
        bool valid = result != T2_TYPE_INVALID
                  && t2_type_kind(shadow->universe, result) != T2_TYPE_ERROR
                  && constrain_type_maybe_diagnose(
                             shadow,
                             site,
                             result,
                             t2_primitive(shadow->universe, T2_TYPE_BOOL),
                             false,
                             "membership-result",
                             "membership protocol must return Bool"
                     )
                  && !t2_solver_failed(shadow->solver);
        if (valid) {
                t2_solver_commit(shadow->solver, protocol);
                return true;
        }
        t2_solver_rollback(shadow->solver, protocol);
        if (diagnose) add_diagnostic(
                shadow,
                site,
                TYPES2_DIAGNOSTIC_ERROR,
                "membership-contract",
                item,
                container,
                "container does not expose contains?(item) -> Bool"
        );
        return false;
}

static bool
check_subscript_write(
        Types2Shadow *shadow,
        T2Type container,
        T2Type index,
        T2Type value,
        Expr const *site,
        bool diagnose
)
{
        container = resolved_operation_type(
                shadow,
                container,
                T2_PREFER_LOWER_BOUND
        );
        T2TypeKind kind = t2_type_kind(shadow->universe, container);
        if (kind == T2_TYPE_DYNAMIC || kind == T2_TYPE_ERROR) return true;
        if (kind == T2_TYPE_UNION) {
                T2SolverMark coverage = t2_solver_mark(shadow->solver);
                for (size_t i = 0; i < t2_type_arity(shadow->universe, container); ++i) {
                        if (!check_subscript_write(
                                shadow,
                                t2_type_child(shadow->universe, container, i),
                                index,
                                value,
                                site,
                                false
                        )) {
                                t2_solver_rollback(shadow->solver, coverage);
                                if (diagnose) add_diagnostic(
                                        shadow,
                                        site,
                                        TYPES2_DIAGNOSTIC_ERROR,
                                        "union-subscript-write-coverage",
                                        container,
                                        value,
                                        "every reachable union arm must support this subscript write"
                                );
                                return false;
                        }
                }
                t2_solver_commit(shadow->solver, coverage);
                return true;
        }

        Types2Nominal *nominal = nominal_from_type(shadow, container);
        if (nominal != NULL && nominal->class_id == CLASS_ARRAY) {
                T2Type integer = t2_primitive(shadow->universe, T2_TYPE_INT);
                T2Relation integer_index = is_dynamic_type(shadow, index)
                                         ? T2_RELATION_YES
                                         : t2_consistent(
                                                 shadow->universe,
                                                 index,
                                                 integer
                                           );
                if (integer_index == T2_RELATION_NO) {
                        T2SolverMark protocol = t2_solver_mark(shadow->solver);
                        T2Type arguments[] = { index, value };
                        T2Type result = infer_subscript_protocol(
                                shadow,
                                container,
                                arguments,
                                2,
                                "[]=",
                                site
                        );
                        bool valid = result != T2_TYPE_INVALID
                                  && t2_type_kind(shadow->universe, result)
                                     != T2_TYPE_ERROR
                                  && !t2_solver_failed(shadow->solver);
                        if (valid) {
                                t2_solver_commit(shadow->solver, protocol);
                                return true;
                        }
                        t2_solver_rollback(shadow->solver, protocol);
                }
                return constrain_type_maybe_diagnose(
                        shadow,
                        site,
                        index,
                        integer,
                        diagnose,
                        "subscript-write-index",
                        "array write index must be an Int"
                ) && constrain_type_maybe_diagnose(
                        shadow,
                        site,
                        value,
                        t2_type_child(shadow->universe, container, 0),
                        diagnose,
                        "subscript-write-value",
                        "array write value has the wrong element type"
                );
        }
        if (nominal != NULL && nominal->class_id == CLASS_DICT) {
                return constrain_type_maybe_diagnose(
                        shadow,
                        site,
                        index,
                        t2_type_child(shadow->universe, container, 0),
                        diagnose,
                        "subscript-write-key",
                        "dictionary write key has the wrong type"
                ) && constrain_type_maybe_diagnose(
                        shadow,
                        site,
                        value,
                        t2_type_child(shadow->universe, container, 1),
                        diagnose,
                        "subscript-write-value",
                        "dictionary write value has the wrong type"
                );
        }
        if (kind == T2_TYPE_META) {
                return constrain_predicate(
                        shadow,
                        site,
                        (T2Predicate) {
                                .kind = T2_PREDICATE_SUBSCRIPT_WRITE,
                                .subtype = container,
                                .supertype = value,
                                .operand = index,
                                .name = "[]="
                        },
                        "subscript-write-contract",
                        "value must expose a compatible subscript write contract"
                );
        }
        if (
                kind == T2_TYPE_RECORD
             || kind == T2_TYPE_TYPE_VALUE
             || nominal != NULL
        ) {
                T2SolverMark protocol = t2_solver_mark(shadow->solver);
                T2Type arguments[] = { index, value };
                T2Type result = infer_subscript_protocol(
                        shadow,
                        container,
                        arguments,
                        2,
                        "[]=",
                        site
                );
                bool valid = result != T2_TYPE_INVALID
                          && t2_type_kind(shadow->universe, result) != T2_TYPE_ERROR
                          && !t2_solver_failed(shadow->solver);
                if (valid) {
                        t2_solver_commit(shadow->solver, protocol);
                        return true;
                }
                t2_solver_rollback(shadow->solver, protocol);
        }
        if (diagnose) add_diagnostic(
                shadow,
                site,
                TYPES2_DIAGNOSTIC_ERROR,
                "subscript-not-writable",
                container,
                value,
                "subscript target does not expose a compatible write contract"
        );
        return false;
}

static bool
check_member_write(
        Types2Shadow *shadow,
        T2Type object,
        char const *name,
        T2Type value,
        Expr const *site,
        bool diagnose
)
{
        object = resolved_operation_type(
                shadow,
                object,
                T2_PREFER_LOWER_BOUND
        );
        T2TypeKind kind = t2_type_kind(shadow->universe, object);
        if (kind == T2_TYPE_DYNAMIC || kind == T2_TYPE_ERROR) return true;
        if (kind == T2_TYPE_UNION) {
                for (size_t i = 0; i < t2_type_arity(shadow->universe, object); ++i) {
                        if (!check_member_write(
                                shadow,
                                t2_type_child(shadow->universe, object, i),
                                name,
                                value,
                                site,
                                false
                        )) {
                                if (diagnose) add_diagnostic(
                                        shadow,
                                        site,
                                        TYPES2_DIAGNOSTIC_ERROR,
                                        "union-write-coverage",
                                        object,
                                        value,
                                        "field `%s` must be writable on every reachable union arm",
                                        name
                                );
                                return false;
                        }
                }
                return true;
        }
        if (kind == T2_TYPE_TYPE_VALUE) {
                T2Type instance = t2_type_value_instance(
                        shadow->universe,
                        object
                );
                Types2Nominal *nominal = nominal_from_type(shadow, instance);
                int class_id = nominal == NULL ? -1 : nominal->class_id;
                if (class_id >= 0) {
                        (void)ensure_class_interface(shadow, class_id);
                        Types2Member *setter = find_member(
                                shadow,
                                class_id,
                                name,
                                TYPES2_MEMBER_SETTER,
                                true
                        );
                        if (setter != NULL) {
                                T2Type callable = instantiate_member(
                                        shadow,
                                        setter,
                                        instance,
                                        site
                                );
                                T2Type result = infer_call_types(
                                        shadow,
                                        callable,
                                        &value,
                                        1,
                                        NULL,
                                        NULL,
                                        0,
                                        site,
                                        diagnose
                                );
                                return t2_type_kind(shadow->universe, result)
                                    != T2_TYPE_ERROR;
                        }
                        Types2Member *field = find_member(
                                shadow,
                                class_id,
                                name,
                                TYPES2_MEMBER_FIELD,
                                true
                        );
                        if (field != NULL && field->writable) {
                                return constrain_type_maybe_diagnose(
                                        shadow,
                                        site,
                                        value,
                                        instantiate_member(
                                                shadow,
                                                field,
                                                instance,
                                                site
                                        ),
                                        diagnose,
                                        "static-field-write-type",
                                        "static field write has the wrong value type"
                                );
                        }
                }
                if (diagnose) add_diagnostic(
                        shadow,
                        site,
                        TYPES2_DIAGNOSTIC_ERROR,
                        "static-field-not-writable",
                        object,
                        value,
                        "static field `%s` is absent or readonly",
                        name
                );
                return false;
        }
        if (kind == T2_TYPE_META) {
                return constrain_predicate_maybe_diagnose(
                        shadow,
                        site,
                        (T2Predicate) {
                                .kind = T2_PREDICATE_MEMBER_WRITE,
                                .subtype = object,
                                .supertype = value,
                                .operand = t2_primitive(
                                        shadow->universe,
                                        T2_TYPE_NEVER
                                ),
                                .name = name
                        },
                        diagnose,
                        "field-write-requirement",
                        "value must provide a compatible writable field"
                );
        }
        if (kind == T2_TYPE_RECORD) {
                T2FieldCapability capability;
                T2Type field = t2_record_field_type(
                        shadow->universe,
                        object,
                        name,
                        NULL,
                        &capability
                );
                if (field != T2_TYPE_INVALID && capability == T2_FIELD_WRITABLE) {
                        return constrain_type_maybe_diagnose(
                                shadow,
                                site,
                                value,
                                field,
                                diagnose,
                                "field-write-type",
                                "field write has the wrong value type"
                        );
                }
        }
        if (kind == T2_TYPE_NOMINAL) {
                Types2Nominal *nominal = nominal_from_type(shadow, object);
                int class_id = nominal == NULL ? -1 : nominal->class_id;
                if (class_id >= 0) {
                        (void)ensure_class_interface(shadow, class_id);
                        nominal = find_class_nominal(shadow, class_id);
                }
                Types2Member *setter = nominal == NULL
                                     ? NULL
                                     : find_member(
                                             shadow,
                                             class_id,
                                             name,
                                             TYPES2_MEMBER_SETTER,
                                             false
                                       );
                if (setter != NULL) {
                        T2Type callable = instantiate_member(shadow, setter, object, site);
                        T2Type result = infer_call_types(
                                shadow,
                                callable,
                                &value,
                                1,
                                NULL,
                                NULL,
                                0,
                                site,
                                diagnose
                        );
                        return t2_type_kind(shadow->universe, result) != T2_TYPE_ERROR;
                }
                Types2Member *field = nominal == NULL
                                    ? NULL
                                    : find_member(
                                            shadow,
                                            class_id,
                                            name,
                                            TYPES2_MEMBER_FIELD,
                                            false
                                      );
                if (field != NULL && field->writable) {
                        return constrain_type_maybe_diagnose(
                                shadow,
                                site,
                                value,
                                instantiate_member(shadow, field, object, site),
                                diagnose,
                                "field-write-type",
                                "field write has the wrong value type"
                        );
                }
                Types2Member *missing_setter = find_missing_member(
                        shadow,
                        class_id,
                        TYPES2_MEMBER_SETTER
                );
                if (missing_setter != NULL) {
                        T2Type handler = instantiate_member(
                                shadow,
                                missing_setter,
                                object,
                                site
                        );
                        T2Type arguments[2] = {
                                t2_literal_string(shadow->universe, name),
                                value
                        };
                        T2Type result = infer_call_types(
                                shadow,
                                handler,
                                arguments,
                                2,
                                NULL,
                                NULL,
                                0,
                                site,
                                diagnose
                        );
                        return t2_type_kind(shadow->universe, result) != T2_TYPE_ERROR;
                }
                nominal = class_id < 0
                        ? NULL
                        : find_class_nominal(shadow, class_id);
                if (nominal != NULL && !nominal->complete) {
                        defer_node(shadow, TYPES2_DEFER_INCOMPLETE_INTERFACE, site, name);
                        return true;
                }
        }
        if (diagnose) add_diagnostic(
                shadow,
                site,
                TYPES2_DIAGNOSTIC_ERROR,
                "field-not-writable",
                object,
                value,
                "field `%s` is absent or readonly",
                name
        );
        return false;
}

static Expr const *
lvalue_annotation_expression(Expr const *target)
{
        if (target == NULL) return NULL;
        Expr const *annotation = target->constraint;
        /* Array-rest patterns can retain the pre-rewrite gather node in the
         * constraint slot.  It is pattern bookkeeping, not an annotation. */
        if (
                target->type == EXPRESSION_MATCH_REST
             && annotation != NULL
             && annotation->symbol == NULL
             && (
                        annotation->type == EXPRESSION_IDENTIFIER
                     || annotation->type == EXPRESSION_MATCH_REST
                )
             && annotation->identifier != NULL
             && target->identifier != NULL
             && (
                        strcmp(annotation->identifier, target->identifier) == 0
                     || (
                                strcmp(target->identifier, "_") == 0
                             && strcmp(annotation->identifier, "*") == 0
                        )
                )
        ) return NULL;
        return annotation;
}

static bool
dictionary_spread_types_x(
        Types2Shadow *shadow,
        T2Type spread,
        T2Type *key,
        T2Type *value,
        unsigned depth
)
{
        if (depth >= 64) return false;
        spread = resolved_operation_type(
                shadow,
                spread,
                T2_PREFER_LOWER_BOUND
        );
        T2TypeKind kind = t2_type_kind(shadow->universe, spread);
        if (kind == T2_TYPE_UNION) {
                for (size_t i = 0; i < t2_type_arity(shadow->universe, spread); ++i) {
                        T2Type arm_key = t2_primitive(
                                shadow->universe,
                                T2_TYPE_NEVER
                        );
                        T2Type arm_value = arm_key;
                        if (!dictionary_spread_types_x(
                                shadow,
                                t2_type_child(shadow->universe, spread, i),
                                &arm_key,
                                &arm_value,
                                depth + 1
                        )) return false;
                        *key = t2_join(shadow->universe, *key, arm_key);
                        *value = t2_join(shadow->universe, *value, arm_value);
                }
                return true;
        }
        if (kind == T2_TYPE_INTERSECTION) {
                bool represented = false;
                for (size_t i = 0; i < t2_type_arity(shadow->universe, spread); ++i) {
                        T2Type arm_key = t2_primitive(
                                shadow->universe,
                                T2_TYPE_NEVER
                        );
                        T2Type arm_value = arm_key;
                        if (!dictionary_spread_types_x(
                                shadow,
                                t2_type_child(shadow->universe, spread, i),
                                &arm_key,
                                &arm_value,
                                depth + 1
                        )) continue;
                        represented = true;
                        *key = t2_join(shadow->universe, *key, arm_key);
                        *value = t2_join(shadow->universe, *value, arm_value);
                }
                return represented;
        }
        if (kind == T2_TYPE_NOMINAL) {
                Types2Nominal *dict = ensure_nominal(
                        shadow,
                        CLASS_DICT,
                        "Dict",
                        2
                );
                T2Type projected = dict == NULL
                                 ? T2_TYPE_INVALID
                                 : t2_nominal_project(
                                         shadow->universe,
                                         spread,
                                         dict->symbol
                                   );
                if (
                        projected == T2_TYPE_INVALID
                     || t2_type_arity(shadow->universe, projected) != 2
                ) return false;
                *key = t2_join(
                        shadow->universe,
                        *key,
                        t2_type_child(shadow->universe, projected, 0)
                );
                *value = t2_join(
                        shadow->universe,
                        *value,
                        t2_type_child(shadow->universe, projected, 1)
                );
                return true;
        }
        if (kind == T2_TYPE_RECORD || kind == T2_TYPE_ROW) {
                size_t count = t2_record_field_count(
                        shadow->universe,
                        spread
                );
                for (size_t i = 0; i < count; ++i) {
                        T2FieldSpec field;
                        if (!t2_record_field(
                                shadow->universe,
                                spread,
                                i,
                                &field
                        )) return false;
                        *key = t2_join(
                                shadow->universe,
                                *key,
                                t2_primitive(shadow->universe, T2_TYPE_STRING)
                        );
                        *value = t2_join(
                                shadow->universe,
                                *value,
                                field.type
                        );
                }
                T2Type tail = t2_record_row_tail(
                        shadow->universe,
                        spread
                );
                T2TypeKind tail_kind = t2_type_kind(shadow->universe, tail);
                if (tail_kind == T2_TYPE_ROW_EMPTY) return true;
                return dictionary_spread_types_x(
                        shadow,
                        tail,
                        key,
                        value,
                        depth + 1
                );
        }
        if (kind == T2_TYPE_ROW_EMPTY || kind == T2_TYPE_NEVER) return true;
        if (
                kind == T2_TYPE_DYNAMIC
             || kind == T2_TYPE_ERROR
             || kind == T2_TYPE_ROW_ANY
        ) {
                *key = t2_join(
                        shadow->universe,
                        *key,
                        kind == T2_TYPE_ROW_ANY
                            ? t2_primitive(shadow->universe, T2_TYPE_STRING)
                            : t2_primitive(shadow->universe, T2_TYPE_DYNAMIC)
                );
                *value = t2_join(
                        shadow->universe,
                        *value,
                        t2_primitive(shadow->universe, T2_TYPE_DYNAMIC)
                );
                return true;
        }
        if (kind == T2_TYPE_META || kind == T2_TYPE_VARIABLE) {
                T2VariableKind variable_kind = t2_type_variable_kind(
                        shadow->universe,
                        spread
                );
                *key = t2_join(
                        shadow->universe,
                        *key,
                        variable_kind == T2_VARIABLE_ROW
                            ? t2_primitive(shadow->universe, T2_TYPE_STRING)
                            : t2_solver_new_meta(
                                    shadow->solver,
                                    T2_VARIABLE_FLEXIBLE,
                                    shadow->level,
                                    "dictionary spread key"
                              )
                );
                *value = t2_join(
                        shadow->universe,
                        *value,
                        t2_solver_new_meta(
                                shadow->solver,
                                T2_VARIABLE_FLEXIBLE,
                                shadow->level,
                                "dictionary spread value"
                        )
                );
                return true;
        }
        return false;
}

static bool
dictionary_spread_types(
        Types2Shadow *shadow,
        T2Type spread,
        T2Type *key,
        T2Type *value
)
{
        if (key == NULL || value == NULL) return false;
        T2Type never = t2_primitive(shadow->universe, T2_TYPE_NEVER);
        T2Type spread_key = never;
        T2Type spread_value = never;
        if (!dictionary_spread_types_x(
                shadow,
                spread,
                &spread_key,
                &spread_value,
                0
        )) return false;
        *key = spread_key;
        *value = spread_value;
        return true;
}

static bool contextual_fresh_literal(
        Types2Shadow *shadow,
        Expr const *source,
        T2Type expected
);

static bool
contextual_fresh_literal_x(
        Types2Shadow *shadow,
        Expr const *source,
        T2Type expected
)
{
        Expr const *expression = source == NULL ? NULL : unfurl(source);
        if (expression == NULL || expected == T2_TYPE_INVALID) return false;
        expected = resolved_type_head(
                shadow,
                expected,
                T2_PREFER_UPPER_BOUND
        );

        if (
                expression->type == EXPRESSION_TUPLE
             && tuple_is_record(expression)
             && t2_type_kind(shadow->universe, expected) == T2_TYPE_RECORD
        ) {
                size_t count = (size_t)vN(expression->es);
                T2FieldSpec *fields = count == 0
                                    ? NULL
                                    : calloc(count, sizeof *fields);
                if (count != 0 && fields == NULL) {
                        shadow->failed = true;
                        return false;
                }
                bool valid = true;
                for (size_t i = 0; i < count; ++i) {
                        char const *name = i < (size_t)vN(expression->names)
                                         ? v__(expression->names, (int)i)
                                         : NULL;
                        Expr const *item = v__(expression->es, (int)i);
                        T2Type actual = infer_expression(shadow, item);
                        T2Type wanted = name == NULL
                                      ? T2_TYPE_INVALID
                                      : t2_record_field_type(
                                              shadow->universe,
                                              expected,
                                              name,
                                              NULL,
                                              NULL
                                        );
                        if (wanted != T2_TYPE_INVALID) {
                                valid = contextual_fresh_literal(
                                                shadow,
                                                item,
                                                wanted
                                        ) || constrain_type_maybe_diagnose(
                                                shadow,
                                                item,
                                                actual,
                                                wanted,
                                                false,
                                                "contextual-field",
                                                "record literal field must satisfy its contextual type"
                                        );
                        }
                        fields[i] = (T2FieldSpec) {
                                .name = name,
                                .type = wanted == T2_TYPE_INVALID ? actual : wanted,
                                .presence = T2_PRESENCE_REQUIRED,
                                .capability = T2_FIELD_WRITABLE
                        };
                        valid &= name != NULL;
                        if (!valid) break;
                }
                T2Type contextual = valid
                                  ? t2_record(
                                          shadow->universe,
                                          fields,
                                          count,
                                          T2_TYPE_INVALID,
                                          T2_RECORD_EXACT
                                    )
                                  : T2_TYPE_INVALID;
                free(fields);
                return valid
                    && contextual != T2_TYPE_INVALID
                    && constrain_type_maybe_diagnose(
                            shadow,
                            expression,
                            contextual,
                            expected,
                            false,
                            "contextual-record",
                            "record literal must satisfy its contextual row"
                       );
        }

        Types2Nominal *nominal = nominal_from_type(shadow, expected);
        int class_id = nominal == NULL ? -1 : nominal->class_id;
        if (
                expression->type == EXPRESSION_ARRAY
             && class_id == CLASS_ARRAY
             && t2_type_arity(shadow->universe, expected) == 1
        ) {
                T2Type wanted = t2_type_child(shadow->universe, expected, 0);
                for (int i = 0; i < vN(expression->elements); ++i) {
                        Expr const *item = v__(expression->elements, i);
                        if (item != NULL && item->type == EXPRESSION_SPREAD) {
                                T2Type spread = infer_expression(shadow, item);
                                Types2Nominal *spread_nominal = nominal_from_type(
                                        shadow,
                                        spread
                                );
                                if (
                                        spread_nominal == NULL
                                     || spread_nominal->class_id != CLASS_ARRAY
                                     || !constrain_type_maybe_diagnose(
                                                shadow,
                                                item,
                                                t2_type_child(
                                                        shadow->universe,
                                                        spread,
                                                        0
                                                ),
                                                wanted,
                                                false,
                                                "contextual-array-spread",
                                                "spread element must satisfy the contextual array type"
                                        )
                                ) return false;
                                continue;
                        }
                        T2Type actual = infer_expression(shadow, item);
                        if (
                                !contextual_fresh_literal(shadow, item, wanted)
                             && !constrain_type_maybe_diagnose(
                                        shadow,
                                        item,
                                        actual,
                                        wanted,
                                        false,
                                        "contextual-array-element",
                                        "array element must satisfy its contextual type"
                                )
                        ) return false;
                }
                return true;
        }

        if (
                expression->type == EXPRESSION_DICT
             && class_id == CLASS_DICT
             && t2_type_arity(shadow->universe, expected) == 2
        ) {
                T2Type wanted_key = t2_type_child(shadow->universe, expected, 0);
                T2Type wanted_value = t2_type_child(shadow->universe, expected, 1);
                for (int i = 0; i < vN(expression->keys); ++i) {
                        Expr const *key_expression = v__(expression->keys, i);
                        if (
                                key_expression != NULL
                             && key_expression->type == EXPRESSION_SPLAT
                        ) {
                                T2Type spread = infer_expression(shadow, key_expression);
                                T2Type spread_key;
                                T2Type spread_value;
                                if (
                                        !dictionary_spread_types(
                                                shadow,
                                                spread,
                                                &spread_key,
                                                &spread_value
                                        )
                                     || !constrain_type_maybe_diagnose(
                                                shadow,
                                                key_expression,
                                                spread_key,
                                                wanted_key,
                                                false,
                                                "contextual-dictionary-spread-key",
                                                "spread key must satisfy the contextual dictionary type"
                                        )
                                     || !constrain_type_maybe_diagnose(
                                                shadow,
                                                key_expression,
                                                spread_value,
                                                wanted_value,
                                                false,
                                                "contextual-dictionary-spread-value",
                                                "spread value must satisfy the contextual dictionary type"
                                        )
                                ) return false;
                                continue;
                        }
                        Expr const *value_expression = v__(expression->values, i);
                        if (!constrain_type_maybe_diagnose(
                                shadow,
                                key_expression,
                                infer_expression(shadow, key_expression),
                                wanted_key,
                                false,
                                "contextual-dictionary-key",
                                "dictionary key must satisfy its contextual type"
                        )) return false;
                        T2Type actual_value = infer_expression(
                                shadow,
                                value_expression
                        );
                        if (
                                !contextual_fresh_literal(
                                        shadow,
                                        value_expression,
                                        wanted_value
                                )
                             && !constrain_type_maybe_diagnose(
                                        shadow,
                                        value_expression,
                                        actual_value,
                                        wanted_value,
                                        false,
                                        "contextual-dictionary-value",
                                        "dictionary value must satisfy its contextual type"
                                )
                        ) return false;
                }
                if (expression->dflt != NULL) {
                        T2Type default_value = infer_expression(
                                shadow,
                                expression->dflt
                        );
                        if (!constrain_type_maybe_diagnose(
                                shadow,
                                expression->dflt,
                                default_value,
                                wanted_value,
                                false,
                                "contextual-dictionary-default",
                                "dictionary default must satisfy its contextual value type"
                        )) {
                                T2SolverMark mark = t2_solver_mark(shadow->solver);
                                T2Type produced = infer_call_types(
                                        shadow,
                                        default_value,
                                        &wanted_key,
                                        1,
                                        NULL,
                                        NULL,
                                        0,
                                        expression->dflt,
                                        false
                                );
                                bool valid = produced != T2_TYPE_INVALID
                                          && t2_type_kind(
                                                     shadow->universe,
                                                     produced
                                             ) != T2_TYPE_ERROR
                                          && constrain_type_maybe_diagnose(
                                                     shadow,
                                                     expression->dflt,
                                                     produced,
                                                     wanted_value,
                                                     false,
                                                     "contextual-dictionary-default-result",
                                                     "dictionary default function must produce the contextual value type"
                                             )
                                          && !t2_solver_failed(shadow->solver);
                                if (valid) t2_solver_commit(shadow->solver, mark);
                                else t2_solver_rollback(shadow->solver, mark);
                                if (!valid) return false;
                        }
                }
                return true;
        }

        return false;
}

static bool
contextual_fresh_literal(
        Types2Shadow *shadow,
        Expr const *source,
        T2Type expected
)
{
        T2SolverMark mark = t2_solver_mark(shadow->solver);
        bool valid = contextual_fresh_literal_x(shadow, source, expected)
                  && !t2_solver_failed(shadow->solver);
        if (valid) t2_solver_commit(shadow->solver, mark);
        else t2_solver_rollback(shadow->solver, mark);
        return valid;
}

static bool assign_lvalue_x(
        Types2Shadow *shadow,
        Expr const *target,
        T2Type value,
        bool declaration,
        bool honor_annotation
);

static bool
assign_lvalue(
        Types2Shadow *shadow,
        Expr const *target,
        T2Type value,
        bool declaration
)
{
        return assign_lvalue_x(shadow, target, value, declaration, true);
}

static T2Type
implicit_member_receiver(Types2Shadow *shadow, Symbol const *member)
{
        if (member == NULL || !SymbolIsMember(member)) return T2_TYPE_INVALID;

        T2Type receiver = T2_TYPE_INVALID;
        if (
                shadow->member_class_id >= 0
             && shadow->member_receiver != T2_TYPE_INVALID
        ) {
                receiver = shadow->member_receiver;
        } else {
                for (size_t i = shadow->function_count; i != 0; --i) {
                        Expr const *function = shadow->functions[i - 1].function;
                        if (function == NULL || function->class == NULL) continue;
                        Symbol const *receiver_symbol = function->self;
                        if (
                                function->mtype == MT_2OP
                             && vN(function->param_symbols) != 0
                        ) receiver_symbol = v__(function->param_symbols, 0);
                        Types2Binding *binding = find_binding(
                                shadow,
                                receiver_symbol
                        );
                        if (binding == NULL || !binding->initialized) continue;
                        receiver = binding->refinement == T2_TYPE_INVALID
                                 ? binding->type
                                 : binding->refinement;
                        break;
                }
        }
        if (receiver == T2_TYPE_INVALID) return receiver;
        if (SymbolIsStatic(member)) {
                receiver = t2_type_value(
                        shadow->universe,
                        receiver,
                        t2_primitive(shadow->universe, T2_TYPE_DYNAMIC)
                );
        }
        return receiver;
}

static bool
array_destructure_element_x(
        Types2Shadow *shadow,
        T2Type subject,
        T2Type *element,
        unsigned depth
)
{
        if (depth >= 64 || element == NULL) return false;
        T2TypeKind original_kind = t2_type_kind(shadow->universe, subject);
        if (original_kind == T2_TYPE_META || original_kind == T2_TYPE_VARIABLE) {
                T2Type inferred = t2_solver_new_meta(
                        shadow->solver,
                        T2_VARIABLE_FLEXIBLE,
                        shadow->level,
                        "array destructuring element"
                );
                T2Type array = nominal_application(
                        shadow,
                        CLASS_ARRAY,
                        "Array",
                        &inferred,
                        1,
                        NULL
                );
                if (
                        array == T2_TYPE_INVALID
                     || !constrain_type_maybe_diagnose(
                                shadow,
                                NULL,
                                subject,
                                array,
                                false,
                                "array-destructuring-shape",
                                "array destructuring requires an Array value"
                        )
                ) return false;
                *element = inferred;
                return true;
        }

        subject = resolved_type_head(
                shadow,
                subject,
                T2_PREFER_LOWER_BOUND
        );
        T2TypeKind kind = t2_type_kind(shadow->universe, subject);
        if (kind == T2_TYPE_UNION) {
                T2Type joined = t2_primitive(shadow->universe, T2_TYPE_NEVER);
                for (size_t i = 0; i < t2_type_arity(shadow->universe, subject); ++i) {
                        T2Type arm = T2_TYPE_INVALID;
                        if (!array_destructure_element_x(
                                shadow,
                                t2_type_child(shadow->universe, subject, i),
                                &arm,
                                depth + 1
                        )) return false;
                        joined = t2_join(shadow->universe, joined, arm);
                }
                *element = joined;
                return true;
        }
        if (kind == T2_TYPE_INTERSECTION) {
                bool found = false;
                T2Type met = t2_primitive(shadow->universe, T2_TYPE_ANY);
                for (size_t i = 0; i < t2_type_arity(shadow->universe, subject); ++i) {
                        T2SolverMark trial = t2_solver_mark(shadow->solver);
                        T2Type arm = T2_TYPE_INVALID;
                        if (array_destructure_element_x(
                                shadow,
                                t2_type_child(shadow->universe, subject, i),
                                &arm,
                                depth + 1
                        )) {
                                t2_solver_commit(shadow->solver, trial);
                                met = found ? t2_meet(shadow->universe, met, arm) : arm;
                                found = true;
                        } else {
                                t2_solver_rollback(shadow->solver, trial);
                        }
                }
                if (found) *element = met;
                return found;
        }
        if (kind == T2_TYPE_DYNAMIC || kind == T2_TYPE_ERROR) {
                *element = t2_primitive(shadow->universe, T2_TYPE_DYNAMIC);
                return true;
        }
        if (kind != T2_TYPE_NOMINAL) return false;
        Types2Nominal *array_nominal = ensure_nominal(
                shadow,
                CLASS_ARRAY,
                "Array",
                1
        );
        if (array_nominal == NULL) return false;
        T2Type projected = t2_nominal_project(
                shadow->universe,
                subject,
                array_nominal->symbol
        );
        if (
                projected == T2_TYPE_INVALID
             || t2_type_arity(shadow->universe, projected) != 1
        ) return false;
        *element = t2_type_child(shadow->universe, projected, 0);
        return true;
}

static bool
assign_lvalue_x(
        Types2Shadow *shadow,
        Expr const *target,
        T2Type value,
        bool declaration,
        bool honor_annotation
)
{
        if (target == NULL) return false;
        switch (target->type) {
        case EXPRESSION_IDENTIFIER:
        case EXPRESSION_MATCH_NOT_NIL:
        case EXPRESSION_MATCH_REST:
        case EXPRESSION_RESOURCE_BINDING:
        case EXPRESSION_ALIAS_PATTERN:
        case EXPRESSION_TAG_PATTERN:
        case EXPRESSION_TAG_PATTERN_CALL:
        {
                T2Type member_receiver = target->type == EXPRESSION_IDENTIFIER
                                       ? implicit_member_receiver(
                                               shadow,
                                               target->symbol
                                         )
                                       : T2_TYPE_INVALID;
                if (member_receiver != T2_TYPE_INVALID) {
                        bool valid = check_member_write(
                                shadow,
                                member_receiver,
                                target->identifier,
                                value,
                                target,
                                true
                        );
                        Types2Binding *refined = find_binding(shadow, target->symbol);
                        if (refined != NULL && refined->member) {
                                refined->refinement = T2_TYPE_INVALID;
                        }
                        set_node_type(
                                shadow,
                                target,
                                valid
                                    ? value
                                    : t2_primitive(
                                            shadow->universe,
                                            T2_TYPE_ERROR
                                      )
                        );
                        return valid;
                }
                Symbol const *binding_symbol = target->symbol;
                Types2Binding *binding = ensure_binding(shadow, binding_symbol);
                if (binding == NULL) return false;
                if (!declaration && binding->initialized && !binding->mutable) {
                        add_diagnostic(
                                shadow,
                                target,
                                TYPES2_DIAGNOSTIC_ERROR,
                                "assign-constant",
                                value,
                                binding->type,
                                "cannot assign to constant `%s`",
                                target->identifier
                        );
                        set_node_type(
                                shadow,
                                target,
                                t2_primitive(shadow->universe, T2_TYPE_ERROR)
                        );
                        return false;
                }
                Expr const *annotation_expression = honor_annotation
                                                  ? lvalue_annotation_expression(
                                                            target
                                                    )
                                                  : NULL;
                T2Type annotation = annotation_expression == NULL
                                  ? T2_TYPE_INVALID
                                  : node_type(shadow, annotation_expression);
                if (
                        annotation_expression != NULL
                     && annotation == T2_TYPE_INVALID
                ) annotation = lower_type(shadow, annotation_expression);
                binding = find_binding(shadow, binding_symbol);
                if (binding == NULL) {
                        shadow->failed = true;
                        return false;
                }
                bool was_initialized = binding->initialized;
                bool was_forward = binding->forward;
                bool is_mutable = binding->mutable;
                bool fresh_weak = declaration
                               && !was_initialized
                               && is_mutable
                               && annotation == T2_TYPE_INVALID;
                T2Type expected = annotation != T2_TYPE_INVALID
                                ? annotation
                                : fresh_weak
                                  ? t2_solver_new_meta(
                                          shadow->solver,
                                          T2_VARIABLE_WEAK,
                                          shadow->level,
                                          target->identifier == NULL
                                              ? "mutable binding"
                                              : target->identifier
                                    )
                                : was_initialized
                                  ? binding->type
                                  : value;
                bool valid = constrain_type(
                        shadow,
                        target,
                        value,
                        expected,
                        "assignment-type",
                        "assigned value does not satisfy the writable target type"
                );
                /* Constraint discharge can populate class interfaces, which
                 * recursively infers member functions and grows the binding
                 * vector.  Reacquire the lexical slot before committing the
                 * write. */
                binding = find_binding(shadow, binding_symbol);
                if (binding == NULL) {
                        shadow->failed = true;
                        return false;
                }
                binding->type = valid
                              ? declaration && was_forward
                                && annotation == T2_TYPE_INVALID
                                && !is_mutable
                                ? value
                                : expected
                              : t2_primitive(shadow->universe, T2_TYPE_ERROR);
                /* The storage type retains every write as a lower bound, while
                 * the current flow path knows the value just written.  Calls
                 * and aliasing boundaries clear this refinement for captured
                 * or global mutable bindings. */
                binding->refinement = valid && is_mutable
                                    ? resolved_type_head(
                                              shadow,
                                              value,
                                              T2_PREFER_LOWER_BOUND
                                      )
                                    : T2_TYPE_INVALID;
                binding->initialized = true;
                if (declaration) binding->forward = false;
                set_node_type(shadow, target, binding->type);
                return valid;
        }
        case EXPRESSION_TUPLE:
        case EXPRESSION_LIST:
        {
                size_t count = (size_t)vN(target->es);
                if (
                        declaration
                     && target->type == EXPRESSION_TUPLE
                     && tuple_is_record(target)
                     && tuple_is_pure_record(target)
                ) {
                        bool valid = infer_pattern(shadow, target, value);
                        set_node_type(
                                shadow,
                                target,
                                valid
                                    ? value
                                    : t2_primitive(
                                            shadow->universe,
                                            T2_TYPE_ERROR
                                      )
                        );
                        return valid;
                }
                if (target->type == EXPRESSION_LIST && count == 1) {
                        Expr const *item = v__(target->es, 0);
                        bool valid = declaration
                                   ? infer_pattern(shadow, item, value)
                                   : item->type == EXPRESSION_MATCH_ANY
                                     ? true
                                     : assign_lvalue(shadow, item, value, false);
                        set_node_type(shadow, target, valid
                                ? value
                                : t2_primitive(shadow->universe, T2_TYPE_ERROR));
                        return valid;
                }
                T2Type recovered = resolved_type_head(
                        shadow,
                        value,
                        T2_PREFER_LOWER_BOUND
                );
                T2TypeKind recovered_kind = t2_type_kind(
                        shadow->universe,
                        recovered
                );
                if (
                        recovered_kind == T2_TYPE_DYNAMIC
                     || recovered_kind == T2_TYPE_ERROR
                ) {
                        T2Type dynamic = t2_primitive(
                                shadow->universe,
                                T2_TYPE_DYNAMIC
                        );
                        bool valid = true;
                        for (size_t i = 0; i < count; ++i) {
                                Expr const *item = v__(target->es, (int)i);
                                valid &= declaration
                                       ? infer_pattern(shadow, item, dynamic)
                                       : item->type == EXPRESSION_MATCH_ANY
                                         ? true
                                         : assign_lvalue(
                                                 shadow,
                                                 item,
                                                 dynamic,
                                                 false
                                           );
                        }
                        set_node_type(shadow, target, dynamic);
                        return valid;
                }
                T2Type *items = count == 0 ? NULL : malloc(count * sizeof *items);
                if (count != 0 && items == NULL) {
                        shadow->failed = true;
                        return false;
                }
                for (size_t i = 0; i < count; ++i) {
                        items[i] = t2_solver_new_meta(
                                shadow->solver,
                                T2_VARIABLE_FLEXIBLE,
                                shadow->level,
                                "destructured tuple item"
                        );
                }
                T2Type tuple = t2_tuple(shadow->universe, items, count);
                bool valid = constrain_type(
                        shadow,
                        target,
                        value,
                        tuple,
                        "tuple-arity",
                        "tuple destructuring requires the exact positional arity"
                );
                if (valid) {
                        for (size_t i = 0; i < count; ++i) {
                                Expr const *item = v__(target->es, (int)i);
                                valid &= declaration
                                       ? infer_pattern(shadow, item, items[i])
                                       : item->type == EXPRESSION_MATCH_ANY
                                         ? true
                                         : assign_lvalue(
                                                 shadow,
                                                 item,
                                                 items[i],
                                                 false
                                           );
                        }
                }
                free(items);
                set_node_type(
                        shadow,
                        target,
                        valid ? tuple : t2_primitive(shadow->universe, T2_TYPE_ERROR)
                );
                return valid;
        }
        case EXPRESSION_ARRAY:
        {
                if (declaration) {
                        bool valid = infer_pattern(shadow, target, value);
                        set_node_type(
                                shadow,
                                target,
                                valid
                                    ? value
                                    : t2_primitive(shadow->universe, T2_TYPE_ERROR)
                        );
                        return valid;
                }

                T2SolverMark shape = t2_solver_mark(shadow->solver);
                T2Type element = T2_TYPE_INVALID;
                if (!array_destructure_element_x(
                        shadow,
                        value,
                        &element,
                        0
                )) {
                        t2_solver_rollback(shadow->solver, shape);
                        add_diagnostic(
                                shadow,
                                target,
                                TYPES2_DIAGNOSTIC_ERROR,
                                "invalid-assignment-target",
                                value,
                                T2_TYPE_INVALID,
                                "array destructuring assignment requires an Array on every reachable path"
                        );
                        set_node_type(
                                shadow,
                                target,
                                t2_primitive(shadow->universe, T2_TYPE_ERROR)
                        );
                        return false;
                }
                t2_solver_commit(shadow->solver, shape);

                bool valid = true;
                for (int i = 0; i < vN(target->elements); ++i) {
                        Expr const *item = v__(target->elements, i);
                        if (item == NULL || item->type == EXPRESSION_MATCH_ANY) {
                                continue;
                        }
                        T2Type assigned = element;
                        if (item->type == EXPRESSION_MATCH_REST) {
                                assigned = nominal_application(
                                        shadow,
                                        CLASS_ARRAY,
                                        "Array",
                                        &element,
                                        1,
                                        item
                                );
                        }
                        valid &= assign_lvalue_x(
                                shadow,
                                item,
                                assigned,
                                false,
                                true
                        );
                }
                set_node_type(
                        shadow,
                        target,
                        valid
                            ? value
                            : t2_primitive(shadow->universe, T2_TYPE_ERROR)
                );
                return valid;
        }
        case EXPRESSION_SUBSCRIPT:
        {
                T2Type container = infer_expression(shadow, target->container);
                T2Type index = infer_expression(shadow, target->subscript);
                return check_subscript_write(
                        shadow,
                        container,
                        index,
                        value,
                        target,
                        true
                );
        }
        case EXPRESSION_MEMBER_ACCESS:
        case EXPRESSION_SELF_ACCESS:
        {
                T2Type object = infer_expression(shadow, target->object);
                return check_member_write(
                        shadow,
                        object,
                        target->member->identifier,
                        value,
                        target,
                        true
                );
        }
        default:
                add_diagnostic(
                        shadow,
                        target,
                        TYPES2_DIAGNOSTIC_ERROR,
                        "invalid-assignment-target",
                        value,
                        T2_TYPE_INVALID,
                        "expression is not a writable target"
                );
                return false;
        }
}

static T2Type
without_nil(Types2Shadow *shadow, T2Type type)
{
        if (t2_type_kind(shadow->universe, type) == T2_TYPE_NIL) {
                return t2_primitive(shadow->universe, T2_TYPE_NEVER);
        }
        if (t2_type_kind(shadow->universe, type) != T2_TYPE_UNION) return type;

        T2Type result = t2_primitive(shadow->universe, T2_TYPE_NEVER);
        for (size_t i = 0; i < t2_type_arity(shadow->universe, type); ++i) {
                T2Type arm = t2_type_child(shadow->universe, type, i);
                if (t2_type_kind(shadow->universe, arm) != T2_TYPE_NIL) {
                        result = t2_join(shadow->universe, result, arm);
                }
        }
        return result;
}

static T2Type
binding_effective_type(Types2Binding const *binding)
{
        return binding->refinement == T2_TYPE_INVALID
             ? binding->type
             : binding->refinement;
}

static T2Type *
snapshot_refinements(Types2Shadow *shadow, size_t count)
{
        T2Type *snapshot = count == 0 ? NULL : malloc(count * sizeof *snapshot);
        if (count != 0 && snapshot == NULL) {
                shadow->failed = true;
                return NULL;
        }
        for (size_t i = 0; i < count; ++i) {
                snapshot[i] = shadow->bindings[i].refinement;
        }
        return snapshot;
}

static T2Type *
snapshot_effective_types(Types2Shadow *shadow, size_t count)
{
        T2Type *snapshot = count == 0 ? NULL : malloc(count * sizeof *snapshot);
        if (count != 0 && snapshot == NULL) {
                shadow->failed = true;
                return NULL;
        }
        for (size_t i = 0; i < count; ++i) {
                snapshot[i] = binding_effective_type(&shadow->bindings[i]);
        }
        return snapshot;
}

static void
restore_refinements(
        Types2Shadow *shadow,
        T2Type const *snapshot,
        size_t count
)
{
        for (size_t i = 0; i < count; ++i) {
                shadow->bindings[i].refinement = snapshot[i];
        }
        for (size_t i = count; i < shadow->binding_count; ++i) {
                if (!shadow->bindings[i].persistent) {
                        shadow->bindings[i].active = false;
                }
        }
}

static void
merge_branch_refinements(
        Types2Shadow *shadow,
        T2Type const *then_types,
        bool then_falls_through,
        T2Type const *else_types,
        bool else_falls_through,
        size_t count
)
{
        for (size_t i = 0; i < count; ++i) {
                T2Type merged;
                if (then_falls_through && else_falls_through) {
                        merged = t2_join(
                                shadow->universe,
                                then_types[i],
                                else_types[i]
                        );
                } else if (then_falls_through) {
                        merged = then_types[i];
                } else if (else_falls_through) {
                        merged = else_types[i];
                } else {
                        merged = shadow->bindings[i].type;
                }
                shadow->bindings[i].refinement = merged == shadow->bindings[i].type
                                               ? T2_TYPE_INVALID
                                               : merged;
        }
}

static T2Type
narrow_type_to(Types2Shadow *shadow, T2Type current, T2Type wanted)
{
        T2TypeKind kind = t2_type_kind(shadow->universe, current);
        if (
                kind == T2_TYPE_DYNAMIC
             || kind == T2_TYPE_UNKNOWN
             || kind == T2_TYPE_ANY
             || kind == T2_TYPE_META
        ) return wanted;
        if (kind == T2_TYPE_UNION) {
                T2Type result = t2_primitive(shadow->universe, T2_TYPE_NEVER);
                for (size_t i = 0; i < t2_type_arity(shadow->universe, current); ++i) {
                        T2Type arm = t2_type_child(shadow->universe, current, i);
                        if (t2_consistent(shadow->universe, arm, wanted) == T2_RELATION_NO) {
                                continue;
                        }
                        T2Relation arm_is_wanted = t2_subtype(
                                shadow->universe,
                                arm,
                                wanted
                        );
                        T2Relation wanted_is_arm = t2_subtype(
                                shadow->universe,
                                wanted,
                                arm
                        );
                        T2Type narrowed = arm_is_wanted == T2_RELATION_YES
                                        ? arm
                                        : wanted_is_arm == T2_RELATION_YES
                                          ? wanted
                                          : type_contains_dynamic(shadow, wanted)
                                            ? arm
                                            : t2_meet(shadow->universe, arm, wanted);
                        result = t2_join(shadow->universe, result, narrowed);
                }
                return result;
        }
        if (t2_subtype(shadow->universe, current, wanted) == T2_RELATION_YES) {
                return current;
        }
        if (t2_subtype(shadow->universe, wanted, current) == T2_RELATION_YES) {
                return wanted;
        }
        if (
                type_contains_dynamic(shadow, wanted)
             && t2_consistent(shadow->universe, current, wanted) != T2_RELATION_NO
        ) return current;
        return t2_meet(shadow->universe, current, wanted);
}

static T2Type
exclude_type(Types2Shadow *shadow, T2Type current, T2Type excluded)
{
        if (t2_type_kind(shadow->universe, current) == T2_TYPE_UNION) {
                T2Type result = t2_primitive(shadow->universe, T2_TYPE_NEVER);
                for (size_t i = 0; i < t2_type_arity(shadow->universe, current); ++i) {
                        T2Type arm = t2_type_child(shadow->universe, current, i);
                        if (t2_subtype(
                                shadow->universe,
                                arm,
                                excluded
                        ) != T2_RELATION_YES) {
                                result = t2_join(shadow->universe, result, arm);
                        }
                }
                return result;
        }
        return t2_subtype(shadow->universe, current, excluded) == T2_RELATION_YES
             ? t2_primitive(shadow->universe, T2_TYPE_NEVER)
             : current;
}

static T2Type
condition_test_type(Types2Shadow *shadow, Expr const *source)
{
        Expr const *name = type_reference_leaf(source);
        T2Type primitive = name == NULL
                         ? T2_TYPE_INVALID
                         : primitive_named(shadow, name->identifier);
        if (primitive != T2_TYPE_INVALID) return primitive;
        Types2Nominal *nominal = name == NULL
                               ? NULL
                               : ensure_symbol_nominal(
                                       shadow,
                                       name->symbol,
                                       name->identifier
                                 );
        if (nominal == NULL) return T2_TYPE_INVALID;
        T2Type *arguments = nominal->arity == 0
                          ? NULL
                          : malloc(nominal->arity * sizeof *arguments);
        if (nominal->arity != 0 && arguments == NULL) {
                shadow->failed = true;
                return T2_TYPE_INVALID;
        }
        for (size_t i = 0; i < nominal->arity; ++i) {
                arguments[i] = t2_primitive(shadow->universe, T2_TYPE_DYNAMIC);
        }
        T2Type result = t2_nominal(
                shadow->universe,
                nominal->symbol,
                arguments,
                nominal->arity
        );
        free(arguments);
        return result;
}

static Types2Binding *
member_refinement_binding(Types2Shadow *shadow, Symbol const *symbol, Expr const *site)
{
        if (!SymbolIsMember(symbol)) return NULL;
        T2Type receiver = implicit_member_receiver(shadow, symbol);
        if (receiver == T2_TYPE_INVALID) return NULL;
        Types2Binding *binding = ensure_binding(shadow, symbol);
        if (binding == NULL) return NULL;
        if (!binding->initialized) {
                T2Type type = infer_member_type(
                        shadow,
                        receiver,
                        symbol->identifier,
                        false,
                        site,
                        false
                );
                binding = find_binding(shadow, symbol);
                if (
                        binding == NULL
                     || type == T2_TYPE_INVALID
                     || t2_type_kind(shadow->universe, type) == T2_TYPE_ERROR
                ) return NULL;
                binding->type = type;
                binding->refinement = T2_TYPE_INVALID;
                binding->mutable = true;
                binding->initialized = true;
                binding->forward = false;
                binding->member = true;
        }
        return binding->member ? binding : NULL;
}

static void
refine_binding(
        Types2Shadow *shadow,
        Symbol const *symbol,
        Expr const *site,
        T2Type wanted,
        bool include
)
{
        Types2Binding *binding = find_binding(shadow, symbol);
        if (binding == NULL || !binding->initialized) {
                binding = member_refinement_binding(shadow, symbol, site);
        }
        if (binding == NULL || !binding->initialized || binding->scheme != NULL) return;
        T2Type current = binding_effective_type(binding);
        T2Type refined = include
                       ? narrow_type_to(shadow, current, wanted)
                       : exclude_type(shadow, current, wanted);
        binding->refinement = refined == binding->type ? T2_TYPE_INVALID : refined;
}

static void
apply_condition_refinements(
        Types2Shadow *shadow,
        Expr const *source,
        bool truth
)
{
        Expr const *condition = source == NULL ? NULL : unfurl(source);
        if (condition == NULL) return;
        if (condition->type == EXPRESSION_PREFIX_BANG) {
                apply_condition_refinements(shadow, condition->operand, !truth);
                return;
        }
        if (condition->type == EXPRESSION_AND && truth) {
                apply_condition_refinements(shadow, condition->left, true);
                apply_condition_refinements(shadow, condition->right, true);
                return;
        }
        if (condition->type == EXPRESSION_OR && !truth) {
                apply_condition_refinements(shadow, condition->left, false);
                apply_condition_refinements(shadow, condition->right, false);
                return;
        }
        if (
                condition->type == EXPRESSION_DBL_EQ
             || condition->type == EXPRESSION_NOT_EQ
        ) {
                Expr const *identifier = NULL;
                if (
                        condition->left != NULL
                     && condition->left->type == EXPRESSION_IDENTIFIER
                     && condition->right != NULL
                     && condition->right->type == EXPRESSION_NIL
                ) identifier = condition->left;
                else if (
                        condition->right != NULL
                     && condition->right->type == EXPRESSION_IDENTIFIER
                     && condition->left != NULL
                     && condition->left->type == EXPRESSION_NIL
                ) identifier = condition->right;
                if (identifier != NULL) {
                        bool is_nil = condition->type == EXPRESSION_DBL_EQ
                                    ? truth
                                    : !truth;
                        refine_binding(
                                shadow,
                                identifier->symbol,
                                identifier,
                                t2_primitive(shadow->universe, T2_TYPE_NIL),
                                is_nil
                        );
                }
                return;
        }
        if (
                condition->type == EXPRESSION_CHECK_MATCH
             && condition->left != NULL
             && condition->left->type == EXPRESSION_IDENTIFIER
        ) {
                T2Type wanted = condition_test_type(shadow, condition->right);
                if (wanted != T2_TYPE_INVALID) {
                        refine_binding(
                                shadow,
                                condition->left->symbol,
                                condition->left,
                                wanted,
                                truth
                        );
                }
                return;
        }
        if (condition->type == EXPRESSION_IDENTIFIER && truth) {
                refine_binding(
                        shadow,
                        condition->symbol,
                        condition,
                        t2_primitive(shadow->universe, T2_TYPE_NIL),
                        false
                );
        }
}

static void
invalidate_unstable_refinements(Types2Shadow *shadow)
{
        for (size_t i = 0; i < shadow->binding_count; ++i) {
                Types2Binding *binding = &shadow->bindings[i];
                if (
                        binding->active
                     && binding->mutable
                     && binding->symbol != NULL
                     && (
                                binding->member
                             || SymbolIsCaptured(binding->symbol)
                             || SymbolIsGlobal(binding->symbol)
                        )
                ) binding->refinement = T2_TYPE_INVALID;
        }
}

static T2Type
infer_slice_type(
        Types2Shadow *shadow,
        T2Type container,
        T2Type const bounds[3],
        Expr const *site,
        bool diagnose
)
{
        container = resolved_operation_type(
                shadow,
                container,
                T2_PREFER_LOWER_BOUND
        );
        T2TypeKind kind = t2_type_kind(shadow->universe, container);
        if (kind == T2_TYPE_ERROR || kind == T2_TYPE_DYNAMIC) return container;
        if (kind == T2_TYPE_UNION) {
                T2SolverMark mark = t2_solver_mark(shadow->solver);
                T2Type result = t2_primitive(shadow->universe, T2_TYPE_NEVER);
                for (size_t i = 0; i < t2_type_arity(shadow->universe, container); ++i) {
                        T2Type arm = infer_slice_type(
                                shadow,
                                t2_type_child(shadow->universe, container, i),
                                bounds,
                                site,
                                false
                        );
                        if (
                                arm == T2_TYPE_INVALID
                             || t2_type_kind(shadow->universe, arm) == T2_TYPE_ERROR
                             || t2_solver_failed(shadow->solver)
                        ) {
                                t2_solver_rollback(shadow->solver, mark);
                                if (diagnose) add_diagnostic(
                                        shadow,
                                        site,
                                        TYPES2_DIAGNOSTIC_ERROR,
                                        "union-slice-coverage",
                                        container,
                                        T2_TYPE_INVALID,
                                        "every reachable union arm must support slicing"
                                );
                                return t2_primitive(shadow->universe, T2_TYPE_ERROR);
                        }
                        result = t2_join(shadow->universe, result, arm);
                }
                t2_solver_commit(shadow->solver, mark);
                return result;
        }

        T2Type integer_or_nil = t2_union(
                shadow->universe,
                (T2Type[]) {
                        t2_primitive(shadow->universe, T2_TYPE_INT),
                        t2_primitive(shadow->universe, T2_TYPE_NIL)
                },
                2
        );
        for (size_t i = 0; i < 3; ++i) {
                if (!constrain_type(
                        shadow,
                        site,
                        bounds[i],
                        integer_or_nil,
                        "slice-bound",
                        "slice bounds must be Int or nil"
                )) return t2_primitive(shadow->universe, T2_TYPE_ERROR);
        }

        if (kind == T2_TYPE_STRING || kind == T2_TYPE_LITERAL_STRING) {
                return t2_primitive(shadow->universe, T2_TYPE_STRING);
        }
        if (kind == T2_TYPE_TUPLE) return container;
        Types2Nominal *nominal = nominal_from_type(shadow, container);
        if (
                nominal != NULL
             && (
                        nominal->class_id == CLASS_ARRAY
                     || nominal->class_id == CLASS_BLOB
                )
        ) return container;

        T2SolverMark mark = t2_solver_mark(shadow->solver);
        T2Type method = infer_member_type(
                shadow,
                container,
                "[;;]",
                false,
                site,
                false
        );
        T2Type result = infer_call_types(
                shadow,
                method,
                bounds,
                3,
                NULL,
                NULL,
                0,
                site,
                false
        );
        if (
                result != T2_TYPE_INVALID
             && t2_type_kind(shadow->universe, result) != T2_TYPE_ERROR
             && !t2_solver_failed(shadow->solver)
        ) {
                t2_solver_commit(shadow->solver, mark);
                return result;
        }
        t2_solver_rollback(shadow->solver, mark);
        if (diagnose) add_diagnostic(
                shadow,
                site,
                TYPES2_DIAGNOSTIC_ERROR,
                "not-sliceable",
                container,
                T2_TYPE_INVALID,
                "value does not expose the three-bound slice contract"
        );
        return t2_primitive(shadow->universe, T2_TYPE_ERROR);
}

static T2Type
infer_count_type(
        Types2Shadow *shadow,
        T2Type operand,
        Expr const *site,
        bool diagnose
)
{
        operand = resolved_operation_type(
                shadow,
                operand,
                T2_PREFER_LOWER_BOUND
        );
        T2TypeKind kind = t2_type_kind(shadow->universe, operand);
        if (kind == T2_TYPE_ERROR || kind == T2_TYPE_DYNAMIC) return operand;
        if (kind == T2_TYPE_UNION) {
                T2SolverMark mark = t2_solver_mark(shadow->solver);
                T2Type result = t2_primitive(shadow->universe, T2_TYPE_NEVER);
                for (size_t i = 0; i < t2_type_arity(shadow->universe, operand); ++i) {
                        T2Type arm = infer_count_type(
                                shadow,
                                t2_type_child(shadow->universe, operand, i),
                                site,
                                false
                        );
                        if (
                                t2_type_kind(shadow->universe, arm) == T2_TYPE_ERROR
                             || t2_solver_failed(shadow->solver)
                        ) {
                                t2_solver_rollback(shadow->solver, mark);
                                if (diagnose) add_diagnostic(
                                        shadow,
                                        site,
                                        TYPES2_DIAGNOSTIC_ERROR,
                                        "union-count-coverage",
                                        operand,
                                        T2_TYPE_INVALID,
                                        "every reachable union arm must support prefix #"
                                );
                                return t2_primitive(shadow->universe, T2_TYPE_ERROR);
                        }
                        result = t2_join(shadow->universe, result, arm);
                }
                t2_solver_commit(shadow->solver, mark);
                return result;
        }
        if (
                kind == T2_TYPE_STRING
             || kind == T2_TYPE_LITERAL_STRING
             || kind == T2_TYPE_TUPLE
             || kind == T2_TYPE_RECORD
        ) return t2_primitive(shadow->universe, T2_TYPE_INT);

        Types2Nominal *nominal = nominal_from_type(shadow, operand);
        if (
                nominal != NULL
             && (
                        nominal->class_id == CLASS_ARRAY
                     || nominal->class_id == CLASS_DICT
                     || nominal->class_id == CLASS_BLOB
                )
        ) return t2_primitive(shadow->universe, T2_TYPE_INT);

        if (kind == T2_TYPE_META) {
                T2Type result = t2_solver_new_meta(
                        shadow->solver,
                        T2_VARIABLE_FLEXIBLE,
                        shadow->level,
                        "count result"
                );
                bool valid = constrain_predicate_maybe_diagnose(
                        shadow,
                        site,
                        (T2Predicate) {
                                .kind = T2_PREDICATE_OPERATOR,
                                .subtype = operand,
                                .supertype = result,
                                .operand = t2_primitive(
                                        shadow->universe,
                                        T2_TYPE_NEVER
                                ),
                                .name = "#"
                        },
                        diagnose,
                        "count-requirement",
                        "value must expose a compatible prefix # contract"
                );
                return valid
                     ? result
                     : t2_primitive(shadow->universe, T2_TYPE_ERROR);
        }

        T2SolverMark mark = t2_solver_mark(shadow->solver);
        T2Type method = infer_member_type(
                shadow,
                operand,
                "#",
                false,
                site,
                false
        );
        T2Type result = infer_call_types(
                shadow,
                method,
                NULL,
                0,
                NULL,
                NULL,
                0,
                site,
                false
        );
        if (
                result != T2_TYPE_INVALID
             && t2_type_kind(shadow->universe, result) != T2_TYPE_ERROR
             && !t2_solver_failed(shadow->solver)
        ) {
                t2_solver_commit(shadow->solver, mark);
                return result;
        }
        t2_solver_rollback(shadow->solver, mark);
        if (diagnose) add_diagnostic(
                shadow,
                site,
                TYPES2_DIAGNOSTIC_ERROR,
                "count-contract",
                operand,
                T2_TYPE_INVALID,
                "prefix # requires a sized value or a zero-argument # method"
        );
        return t2_primitive(shadow->universe, T2_TYPE_ERROR);
}

static T2Type
infer_prefix_minus_type(
        Types2Shadow *shadow,
        T2Type operand,
        Expr const *site,
        bool diagnose
)
{
        operand = resolved_operation_type(
                shadow,
                operand,
                T2_PREFER_LOWER_BOUND
        );
        T2TypeKind kind = t2_type_kind(shadow->universe, operand);
        if (kind == T2_TYPE_ERROR) return operand;
        if (kind == T2_TYPE_DYNAMIC) {
                defer_node(shadow, TYPES2_DEFER_DYNAMIC_OPERAND, site, NULL);
                return operand;
        }
        if (kind == T2_TYPE_UNION) {
                T2SolverMark mark = t2_solver_mark(shadow->solver);
                T2Type result = t2_primitive(shadow->universe, T2_TYPE_NEVER);
                for (size_t i = 0; i < t2_type_arity(shadow->universe, operand); ++i) {
                        T2Type arm = infer_prefix_minus_type(
                                shadow,
                                t2_type_child(shadow->universe, operand, i),
                                site,
                                false
                        );
                        if (
                                arm == T2_TYPE_INVALID
                             || t2_type_kind(shadow->universe, arm) == T2_TYPE_ERROR
                             || t2_solver_failed(shadow->solver)
                        ) {
                                t2_solver_rollback(shadow->solver, mark);
                                if (diagnose) add_diagnostic(
                                        shadow,
                                        site,
                                        TYPES2_DIAGNOSTIC_ERROR,
                                        "union-unary-operator-coverage",
                                        operand,
                                        T2_TYPE_INVALID,
                                        "every reachable union arm must support prefix minus"
                                );
                                return t2_primitive(
                                        shadow->universe,
                                        T2_TYPE_ERROR
                                );
                        }
                        result = t2_join(shadow->universe, result, arm);
                }
                t2_solver_commit(shadow->solver, mark);
                return result;
        }

        T2TypeKind relaxed = t2_type_kind(
                shadow->universe,
                relax_literal(shadow, operand)
        );
        if (relaxed == T2_TYPE_INT) {
                return t2_primitive(shadow->universe, T2_TYPE_INT);
        }
        if (relaxed == T2_TYPE_FLOAT) {
                return t2_primitive(shadow->universe, T2_TYPE_FLOAT);
        }

        T2SolverMark member_mark = t2_solver_mark(shadow->solver);
        T2Type method = infer_member_type(
                shadow,
                operand,
                "-",
                false,
                site,
                false
        );
        T2Type result = infer_call_types(
                shadow,
                method,
                NULL,
                0,
                NULL,
                NULL,
                0,
                site,
                false
        );
        if (
                result != T2_TYPE_INVALID
             && t2_type_kind(shadow->universe, result) != T2_TYPE_ERROR
             && !t2_solver_failed(shadow->solver)
        ) {
                t2_solver_commit(shadow->solver, member_mark);
                return result;
        }
        t2_solver_rollback(shadow->solver, member_mark);

        result = infer_registered_operator_call(
                shadow,
                "-",
                &operand,
                1,
                site,
                diagnose
        );
        if (result != T2_TYPE_INVALID) return result;
        if (diagnose) add_diagnostic(
                shadow,
                site,
                TYPES2_DIAGNOSTIC_ERROR,
                "unary-operator",
                operand,
                T2_TYPE_INVALID,
                "prefix minus requires a numeric operand or unary `-` contract"
        );
        return t2_primitive(shadow->universe, T2_TYPE_ERROR);
}

static uint8_t
named_binary_operation(char const *name)
{
        if (name == NULL) return EXPRESSION_MAX_TYPE;
        if (strcmp(name, "+") == 0) return EXPRESSION_PLUS;
        if (strcmp(name, "-") == 0) return EXPRESSION_MINUS;
        if (strcmp(name, "*") == 0) return EXPRESSION_STAR;
        if (strcmp(name, "/") == 0) return EXPRESSION_DIV;
        if (strcmp(name, "%") == 0) return EXPRESSION_PERCENT;
        if (strcmp(name, "&") == 0) return EXPRESSION_BIT_AND;
        if (strcmp(name, "|") == 0) return EXPRESSION_BIT_OR;
        if (strcmp(name, "^") == 0) return EXPRESSION_XOR;
        if (strcmp(name, "<<") == 0) return EXPRESSION_SHL;
        if (strcmp(name, ">>") == 0) return EXPRESSION_SHR;
        if (strcmp(name, "<") == 0) return EXPRESSION_LT;
        if (strcmp(name, "<=") == 0) return EXPRESSION_LEQ;
        if (strcmp(name, ">") == 0) return EXPRESSION_GT;
        if (strcmp(name, ">=") == 0) return EXPRESSION_GEQ;
        if (strcmp(name, "<=>") == 0) return EXPRESSION_CMP;
        if (strcmp(name, "==") == 0) return EXPRESSION_DBL_EQ;
        if (strcmp(name, "!=") == 0) return EXPRESSION_NOT_EQ;
        return EXPRESSION_MAX_TYPE;
}

static T2Type infer_function_expression(Types2Shadow *shadow, Expr const *function);

static void
promote_generator_frame(
        Types2Shadow *shadow,
        Types2FunctionFrame *frame,
        Expr const *site
)
{
        if (frame == NULL || frame->generator || frame->effectful) return;
        if (t2_type_kind(shadow->universe, frame->yields) == T2_TYPE_NEVER) {
                frame->yields = t2_solver_new_meta(
                        shadow->solver,
                        T2_VARIABLE_FLEXIBLE,
                        frame->level,
                        source_provenance(shadow, site, "implicit generator yield")
                );
                frame->sends = t2_solver_new_meta(
                        shadow->solver,
                        T2_VARIABLE_FLEXIBLE,
                        frame->level,
                        source_provenance(shadow, site, "implicit generator send")
                );
        }
        frame->effectful = true;
}

static bool
append_call_argument_type(
        Types2Shadow *shadow,
        T2Type **arguments,
        size_t *count,
        size_t *capacity,
        T2Type type
)
{
        if (*count == SIZE_MAX || !shadow_reserve(
                shadow,
                (void **)arguments,
                capacity,
                *count + 1,
                sizeof **arguments
        )) return false;
        (*arguments)[(*count)++] = type;
        return true;
}

static bool
expand_fixed_tuple_call_splats(
        Types2Shadow *shadow,
        ExprVec const *expressions,
        T2Type const *source_types,
        size_t source_count,
        T2Type **expanded,
        size_t *expanded_count
)
{
        *expanded = NULL;
        *expanded_count = 0;
        size_t capacity = 0;
        for (size_t i = 0; i < source_count; ++i) {
                Expr const *argument = expressions == NULL
                                     ? NULL
                                     : v__(*expressions, (int)i);
                T2Type type = source_types[i];
                T2Type resolved = resolved_type_head(
                        shadow,
                        type,
                        T2_PREFER_LOWER_BOUND
                );
                if (
                        argument != NULL
                     && (
                                argument->type == EXPRESSION_SPREAD
                             || argument->type == EXPRESSION_SPLAT
                        )
                     && t2_type_kind(shadow->universe, resolved) == T2_TYPE_TUPLE
                ) {
                        size_t arity = t2_type_arity(shadow->universe, resolved);
                        for (size_t j = 0; j < arity; ++j) {
                                if (!append_call_argument_type(
                                        shadow,
                                        expanded,
                                        expanded_count,
                                        &capacity,
                                        t2_type_child(shadow->universe, resolved, j)
                                )) {
                                        free(*expanded);
                                        *expanded = NULL;
                                        *expanded_count = 0;
                                        return false;
                                }
                        }
                        continue;
                }
                if (
                        argument != NULL
                     && (
                                argument->type == EXPRESSION_SPREAD
                             || argument->type == EXPRESSION_SPLAT
                        )
                ) {
                        T2Type element = iterated_type(
                                shadow,
                                resolved,
                                argument
                        );
                        T2Type expansion = t2_type_kind(
                                                   shadow->universe,
                                                   element
                                           ) == T2_TYPE_ERROR
                                         ? element
                                         : t2_pack_expansion(
                                                 shadow->universe,
                                                 element
                                           );
                        if (
                                expansion == T2_TYPE_INVALID
                             || !append_call_argument_type(
                                        shadow,
                                        expanded,
                                        expanded_count,
                                        &capacity,
                                        expansion
                                )
                        ) {
                                free(*expanded);
                                *expanded = NULL;
                                *expanded_count = 0;
                                return false;
                        }
                        continue;
                }
                if (!append_call_argument_type(
                        shadow,
                        expanded,
                        expanded_count,
                        &capacity,
                        type
                )) {
                        free(*expanded);
                        *expanded = NULL;
                        *expanded_count = 0;
                        return false;
                }
        }
        return true;
}

static bool
propagate_call_effect(
        Types2Shadow *shadow,
        Types2CallEffect const *effect,
        Expr const *site
)
{
        if (
                effect == NULL
             || !effect->active
             || shadow->function_count == 0
        ) return true;

        Types2FunctionFrame *frame = &shadow->functions[
                shadow->function_count - 1
        ];
        promote_generator_frame(shadow, frame, site);
        bool yields = constrain_type(
                shadow,
                site,
                effect->yields,
                frame->yields,
                "yield-call-type",
                "called coroutine may yield a value outside this function's generator contract"
        );
        bool sends = constrain_type(
                shadow,
                site,
                frame->sends,
                effect->sends,
                "send-call-type",
                "this function's resume value is not accepted by the called coroutine"
        );
        return yields && sends;
}

static bool
append_or_replace_record_field(
        Types2Shadow *shadow,
        T2FieldSpec **fields,
        size_t *count,
        size_t *capacity,
        T2FieldSpec field
)
{
        for (size_t i = 0; i < *count; ++i) {
                if (strcmp((*fields)[i].name, field.name) == 0) {
                        (*fields)[i] = field;
                        return true;
                }
        }
        if (*count == SIZE_MAX || !shadow_reserve(
                shadow,
                (void **)fields,
                capacity,
                *count + 1,
                sizeof **fields
        )) return false;
        (*fields)[(*count)++] = field;
        return true;
}

static T2Type
overlay_record_types_x(
        Types2Shadow *shadow,
        T2Type base,
        T2Type overlay,
        unsigned depth
)
{
        if (depth >= 64) return T2_TYPE_INVALID;
        base = resolved_type_head(shadow, base, T2_PREFER_LOWER_BOUND);
        overlay = resolved_type_head(shadow, overlay, T2_PREFER_LOWER_BOUND);
        T2TypeKind base_kind = t2_type_kind(shadow->universe, base);
        T2TypeKind overlay_kind = t2_type_kind(shadow->universe, overlay);
        if (base_kind == T2_TYPE_ERROR || overlay_kind == T2_TYPE_ERROR) {
                return t2_primitive(shadow->universe, T2_TYPE_ERROR);
        }
        if (base_kind == T2_TYPE_DYNAMIC || overlay_kind == T2_TYPE_DYNAMIC) {
                return t2_primitive(shadow->universe, T2_TYPE_DYNAMIC);
        }

        if (
                overlay_kind == T2_TYPE_META
             && t2_type_variable_kind(shadow->universe, overlay)
                    != T2_VARIABLE_ROW
             && t2_type_variable_kind(shadow->universe, overlay)
                    != T2_VARIABLE_PACK
        ) {
                T2Type row = t2_solver_new_meta(
                        shadow->solver,
                        T2_VARIABLE_ROW,
                        shadow->level,
                        "record spread row"
                );
                T2Type shape = t2_record(
                        shadow->universe,
                        NULL,
                        0,
                        row,
                        T2_RECORD_OPEN
                );
                if (
                        row == T2_TYPE_INVALID
                     || shape == T2_TYPE_INVALID
                     || !constrain_type_maybe_diagnose(
                                shadow,
                                NULL,
                                overlay,
                                shape,
                                false,
                                "record-spread-shape",
                                "spread value must retain its structural row"
                        )
                ) return T2_TYPE_INVALID;
                overlay = shape;
                overlay_kind = T2_TYPE_RECORD;
        }

        if (base_kind == T2_TYPE_UNION || overlay_kind == T2_TYPE_UNION) {
                T2Type union_type = base_kind == T2_TYPE_UNION ? base : overlay;
                T2Type other = base_kind == T2_TYPE_UNION ? overlay : base;
                size_t count = t2_type_arity(shadow->universe, union_type);
                if (count > SIZE_MAX / sizeof(T2Type)) return T2_TYPE_INVALID;
                T2Type *arms = count == 0 ? NULL : malloc(count * sizeof *arms);
                if (count != 0 && arms == NULL) {
                        shadow->failed = true;
                        return T2_TYPE_INVALID;
                }
                for (size_t i = 0; i < count; ++i) {
                        T2Type arm = t2_type_child(shadow->universe, union_type, i);
                        arms[i] = base_kind == T2_TYPE_UNION
                                ? overlay_record_types_x(
                                        shadow,
                                        arm,
                                        other,
                                        depth + 1
                                  )
                                : overlay_record_types_x(
                                        shadow,
                                        other,
                                        arm,
                                        depth + 1
                                  );
                        if (arms[i] == T2_TYPE_INVALID) {
                                free(arms);
                                return T2_TYPE_INVALID;
                        }
                }
                T2Type result = t2_union(shadow->universe, arms, count);
                free(arms);
                return result;
        }

        if (base_kind != T2_TYPE_RECORD || overlay_kind != T2_TYPE_RECORD) {
                return T2_TYPE_INVALID;
        }

        size_t base_count = t2_record_field_count(shadow->universe, base);
        size_t overlay_count = t2_record_field_count(shadow->universe, overlay);
        if (base_count > SIZE_MAX - overlay_count) return T2_TYPE_INVALID;
        T2FieldSpec *fields = NULL;
        size_t count = 0;
        size_t capacity = 0;
        if (base_count + overlay_count != 0 && !shadow_reserve(
                shadow,
                (void **)&fields,
                &capacity,
                base_count + overlay_count,
                sizeof *fields
        )) return T2_TYPE_INVALID;

        bool valid = true;
        for (size_t i = 0; valid && i < base_count; ++i) {
                T2FieldSpec field;
                valid = t2_record_field(shadow->universe, base, i, &field);
                if (valid) {
                        field.capability = T2_FIELD_WRITABLE;
                        valid = append_or_replace_record_field(
                                shadow,
                                &fields,
                                &count,
                                &capacity,
                                field
                        );
                }
        }
        for (size_t i = 0; valid && i < overlay_count; ++i) {
                T2FieldSpec field;
                valid = t2_record_field(shadow->universe, overlay, i, &field);
                if (valid) {
                        field.capability = T2_FIELD_WRITABLE;
                        valid = append_or_replace_record_field(
                                shadow,
                                &fields,
                                &count,
                                &capacity,
                                field
                        );
                }
        }

        T2RecordExactness base_exactness = T2_RECORD_OPEN;
        T2RecordExactness overlay_exactness = T2_RECORD_OPEN;
        valid = valid
             && t2_record_exactness(shadow->universe, base, &base_exactness)
             && t2_record_exactness(
                        shadow->universe,
                        overlay,
                        &overlay_exactness
                );
        T2RecordExactness exactness = base_exactness == T2_RECORD_EXACT
                                  && overlay_exactness == T2_RECORD_EXACT
                                   ? T2_RECORD_EXACT
                                   : T2_RECORD_OPEN;
        T2Type tail = T2_TYPE_INVALID;
        if (valid && exactness == T2_RECORD_OPEN) {
                T2Type base_tail = t2_record_row_tail(shadow->universe, base);
                T2Type overlay_tail = t2_record_row_tail(
                        shadow->universe,
                        overlay
                );
                if (base_exactness == T2_RECORD_EXACT) tail = overlay_tail;
                else if (overlay_exactness == T2_RECORD_EXACT) tail = base_tail;
                else if (base_tail == overlay_tail) tail = base_tail;
                else tail = t2_intersection(
                        shadow->universe,
                        (T2Type[]){ base_tail, overlay_tail },
                        2
                );
                valid = tail != T2_TYPE_INVALID
                     && t2_type_kind(shadow->universe, tail) != T2_TYPE_NEVER;
        }
        T2Type result = valid
                      ? t2_record(
                                shadow->universe,
                                fields,
                                count,
                                tail,
                                exactness
                        )
                      : T2_TYPE_INVALID;
        free(fields);
        return result;
}

static T2Type
infer_record_literal(Types2Shadow *shadow, Expr const *expression)
{
        T2Type result = t2_record(
                shadow->universe,
                NULL,
                0,
                T2_TYPE_INVALID,
                T2_RECORD_EXACT
        );
        size_t count = (size_t)vN(expression->es);
        for (size_t i = 0; i < count; ++i) {
                Expr const *item = v__(expression->es, (int)i);
                Expr const *condition = i < (size_t)vN(expression->tconds)
                                      ? v__(expression->tconds, (int)i)
                                      : NULL;
                if (condition != NULL) (void)infer_expression(shadow, condition);
                bool optional = i < (size_t)vN(expression->required)
                             && !v__(expression->required, (int)i);
                bool spread = item != NULL && item->type == EXPRESSION_SPREAD;
                T2Type previous = result;
                if (spread) {
                        T2Type source = resolved_type_head(
                                shadow,
                                infer_expression(shadow, item),
                                T2_PREFER_LOWER_BOUND
                        );
                        if (optional) source = without_nil(shadow, source);
                        result = overlay_record_types_x(
                                shadow,
                                result,
                                source,
                                0
                        );
                } else {
                        char const *name = i < (size_t)vN(expression->names)
                                         ? v__(expression->names, (int)i)
                                         : NULL;
                        T2FieldSpec field = {
                                .name = name,
                                .type = relax_literal(
                                        shadow,
                                        infer_expression(shadow, item)
                                ),
                                .presence = optional || condition != NULL
                                          ? T2_PRESENCE_OPTIONAL
                                          : T2_PRESENCE_REQUIRED,
                                .capability = T2_FIELD_WRITABLE
                        };
                        T2Type one = name == NULL
                                   ? T2_TYPE_INVALID
                                   : t2_record(
                                           shadow->universe,
                                           &field,
                                           1,
                                           T2_TYPE_INVALID,
                                           T2_RECORD_EXACT
                                     );
                        result = one == T2_TYPE_INVALID
                               ? T2_TYPE_INVALID
                               : overlay_record_types_x(
                                       shadow,
                                       result,
                                       one,
                                       0
                                 );
                }
                if (result == T2_TYPE_INVALID) {
                        add_diagnostic(
                                shadow,
                                item == NULL ? expression : item,
                                TYPES2_DIAGNOSTIC_ERROR,
                                spread ? "record-spread" : "record-field",
                                previous,
                                T2_TYPE_INVALID,
                                spread
                                    ? "record spread requires a record value or Dynamic"
                                    : "record literal field could not be represented"
                        );
                        return t2_primitive(shadow->universe, T2_TYPE_ERROR);
                }
                if (spread && (condition != NULL || optional)) {
                        result = t2_join(shadow->universe, previous, result);
                }
        }
        return result;
}

static T2Type
infer_mixed_tuple(Types2Shadow *shadow, Expr const *expression)
{
        size_t count = (size_t)vN(expression->es);
        if (count > SIZE_MAX / sizeof(T2Type)) return T2_TYPE_INVALID;
        T2Type *items = count == 0 ? NULL : malloc(count * sizeof *items);
        T2FieldSpec *fields = count == 0
                            ? NULL
                            : malloc(count * sizeof *fields);
        if (count != 0 && (items == NULL || fields == NULL)) {
                free(items);
                free(fields);
                shadow->failed = true;
                return T2_TYPE_INVALID;
        }
        size_t field_count = 0;
        for (size_t i = 0; i < count; ++i) {
                Expr const *item = v__(expression->es, (int)i);
                if (item != NULL && item->type == EXPRESSION_SPREAD) {
                        free(items);
                        free(fields);
                        defer_node(shadow, TYPES2_DEFER_TUPLE_SPREAD, expression, NULL);
                        return t2_primitive(shadow->universe, T2_TYPE_DYNAMIC);
                }
                items[i] = infer_expression(shadow, item);
                char const *name = i < (size_t)vN(expression->names)
                                 ? v__(expression->names, (int)i)
                                 : NULL;
                if (name != NULL) {
                        fields[field_count++] = (T2FieldSpec) {
                                .name = name,
                                .type = relax_literal(shadow, items[i]),
                                .presence = i < (size_t)vN(expression->required)
                                         && !v__(expression->required, (int)i)
                                          ? T2_PRESENCE_OPTIONAL
                                          : T2_PRESENCE_REQUIRED,
                                .capability = T2_FIELD_WRITABLE
                        };
                }
                if (i < (size_t)vN(expression->tconds)) {
                        (void)infer_expression(
                                shadow,
                                v__(expression->tconds, (int)i)
                        );
                }
        }
        T2Type tuple = t2_tuple(shadow->universe, items, count);
        T2Type record = t2_record(
                shadow->universe,
                fields,
                field_count,
                T2_TYPE_INVALID,
                T2_RECORD_OPEN
        );
        free(items);
        free(fields);
        if (tuple == T2_TYPE_INVALID || record == T2_TYPE_INVALID) {
                return T2_TYPE_INVALID;
        }
        return t2_intersection(
                shadow->universe,
                (T2Type[]){ tuple, record },
                2
        );
}

typedef enum types2_tag_presence {
        TYPES2_TAG_NEVER,
        TYPES2_TAG_ALWAYS,
        TYPES2_TAG_MAYBE,
        TYPES2_TAG_IMPOSSIBLE
} Types2TagPresence;

static Types2TagPresence
tag_presence_x(Types2Shadow *shadow, T2Type type, unsigned depth)
{
        if (type == T2_TYPE_INVALID || depth > 128) return TYPES2_TAG_MAYBE;
        type = resolved_type_head(shadow, type, T2_PREFER_LOWER_BOUND);
        T2TypeKind kind = t2_type_kind(shadow->universe, type);
        if (kind == T2_TYPE_NEVER) return TYPES2_TAG_IMPOSSIBLE;
        if (kind == T2_TYPE_ERROR) return TYPES2_TAG_MAYBE;
        if (
                kind == T2_TYPE_DYNAMIC
             || kind == T2_TYPE_UNKNOWN
             || kind == T2_TYPE_ANY
             || kind == T2_TYPE_OBJECT
             || kind == T2_TYPE_COMPUTED
             || kind == T2_TYPE_VARIABLE
             || kind == T2_TYPE_META
        ) return TYPES2_TAG_MAYBE;
        if (kind == T2_TYPE_NOMINAL) {
                Types2Nominal *nominal = nominal_from_type(shadow, type);
                return nominal != NULL && nominal->tag_id > 0
                     ? TYPES2_TAG_ALWAYS
                     : TYPES2_TAG_NEVER;
        }
        if (kind == T2_TYPE_UNION) {
                bool always = false;
                bool never = false;
                for (size_t i = 0; i < t2_type_arity(shadow->universe, type); ++i) {
                        Types2TagPresence arm = tag_presence_x(
                                shadow,
                                t2_type_child(shadow->universe, type, i),
                                depth + 1
                        );
                        if (arm == TYPES2_TAG_MAYBE) return TYPES2_TAG_MAYBE;
                        always |= arm == TYPES2_TAG_ALWAYS;
                        never |= arm == TYPES2_TAG_NEVER;
                }
                if (always && never) return TYPES2_TAG_MAYBE;
                if (always) return TYPES2_TAG_ALWAYS;
                if (never) return TYPES2_TAG_NEVER;
                return TYPES2_TAG_IMPOSSIBLE;
        }
        if (kind == T2_TYPE_INTERSECTION) {
                bool always = false;
                bool never = false;
                bool maybe = false;
                for (size_t i = 0; i < t2_type_arity(shadow->universe, type); ++i) {
                        Types2TagPresence arm = tag_presence_x(
                                shadow,
                                t2_type_child(shadow->universe, type, i),
                                depth + 1
                        );
                        always |= arm == TYPES2_TAG_ALWAYS;
                        never |= arm == TYPES2_TAG_NEVER;
                        maybe |= arm == TYPES2_TAG_MAYBE;
                }
                if (always && never) return TYPES2_TAG_IMPOSSIBLE;
                if (always) return TYPES2_TAG_ALWAYS;
                if (never) return TYPES2_TAG_NEVER;
                return maybe ? TYPES2_TAG_MAYBE : TYPES2_TAG_IMPOSSIBLE;
        }
        if (
                (kind == T2_TYPE_REFINEMENT || kind == T2_TYPE_RECURSIVE)
             && t2_type_arity(shadow->universe, type) != 0
        ) return tag_presence_x(
                shadow,
                t2_type_child(shadow->universe, type, 0),
                depth + 1
        );
        return TYPES2_TAG_NEVER;
}

static T2Type
infer_tag_value_type(Types2Shadow *shadow, T2Type operand, Expr const *site)
{
        if (t2_type_kind(shadow->universe, operand) == T2_TYPE_ERROR) {
                return operand;
        }
        Types2TagPresence presence = tag_presence_x(shadow, operand, 0);
        if (presence == TYPES2_TAG_IMPOSSIBLE) {
                return t2_primitive(shadow->universe, T2_TYPE_NEVER);
        }
        T2Type nil = t2_primitive(shadow->universe, T2_TYPE_NIL);
        if (presence == TYPES2_TAG_NEVER) return nil;
        T2Type tag = nominal_application(
                shadow,
                CLASS_TAG,
                "Tag",
                NULL,
                0,
                site
        );
        return presence == TYPES2_TAG_ALWAYS
             ? tag
             : t2_join(shadow->universe, tag, nil);
}

static void register_declaration(Types2Shadow *shadow, Stmt const *statement);
static bool is_named_binding_target(Expr const *target);

static bool
same_symbol(Symbol const *candidate, Symbol const *symbol, bool home)
{
        if (candidate == symbol) return true;
        if (
                candidate == NULL
             || symbol == NULL
             || candidate->identifier == NULL
             || symbol->identifier == NULL
             || strcmp(candidate->identifier, symbol->identifier) != 0
        ) return false;
        return home || candidate->mod == symbol->mod;
}

static bool
statement_defines_symbol(
        Stmt const *statement,
        Symbol const *symbol,
        bool home
)
{
        switch (statement->type) {
        case STATEMENT_FUNCTION_DEFINITION:
        case STATEMENT_PATTERN_DEFINITION:
        case STATEMENT_OPERATOR_DEFINITION:
                return statement->target != NULL
                    && same_symbol(statement->target->symbol, symbol, home);
        case STATEMENT_DEFINITION:
                return is_named_binding_target(statement->target)
                    && same_symbol(statement->target->symbol, symbol, home);
        case STATEMENT_CLASS_DEFINITION:
                return same_symbol(statement->class.var, symbol, home);
        case STATEMENT_TAG_DEFINITION:
                return same_symbol(statement->tag.var, symbol, home);
        default:
                return false;
        }
}

static Symbol const *
statement_target_symbol(Stmt const *statement)
{
        switch (statement->type) {
        case STATEMENT_CLASS_DEFINITION:
                return statement->class.var;
        case STATEMENT_TAG_DEFINITION:
                return statement->tag.var;
        default:
                return statement->target == NULL ? NULL : statement->target->symbol;
        }
}

static void
import_definitions_in(
        Types2Shadow *shadow,
        Stmt const *statement,
        Symbol const *symbol,
        bool home,
        Symbol const **definition
)
{
        if (statement == NULL || shadow->failed) return;
        if (
                statement->type == STATEMENT_BLOCK
             || statement->type == STATEMENT_MULTI
        ) {
                for (int i = 0; i < vN(statement->statements); ++i) {
                        import_definitions_in(
                                shadow,
                                v__(statement->statements, i),
                                symbol,
                                home,
                                definition
                        );
                }
                return;
        }
        if (!statement_defines_symbol(statement, symbol, home)) return;
        if (*definition == NULL) *definition = statement_target_symbol(statement);
        register_declaration(shadow, statement);
        if (statement->type != STATEMENT_CLASS_DEFINITION) {
                (void)infer_statement(shadow, statement);
        }
        Types2Binding *binding = find_binding(shadow, statement_target_symbol(statement));
        if (binding != NULL) binding->persistent = true;
}

static bool
module_is_current(Types2Shadow const *shadow, Module const *module)
{
        return module != NULL
            && (
                       (
                                module->name != NULL
                             && strcmp(module->name, shadow->unit) == 0
                       )
                    || (
                                module->path != NULL
                             && strcmp(module->path, shadow->path) == 0
                       )
               );
}

static void
import_program(
        Types2Shadow *shadow,
        Stmt **program,
        Symbol const *symbol,
        bool home,
        Symbol const **definition
)
{
        if (program == NULL) return;
        for (size_t i = 0; program[i] != NULL; ++i) {
                import_definitions_in(shadow, program[i], symbol, home, definition);
        }
}

static Symbol const *
import_external_binding(Types2Shadow *shadow, Symbol const *symbol)
{
        if (symbol == NULL || shadow->ty == NULL) return NULL;
        Module const *home = symbol->mod;
        if (module_is_current(shadow, home)) return NULL;

        bool previous = shadow->importing;
        shadow->importing = true;
        Symbol const *definition = NULL;
        if (home != NULL) {
                import_program(shadow, home->prog, symbol, true, &definition);
        }
        if (definition == NULL) {
                ModuleVector const *modules = TyActiveModules(shadow->ty);
                for (int i = 0; i < vN(*modules); ++i) {
                        Module const *module = v__(*modules, i);
                        if (module == home || module_is_current(shadow, module)) {
                                continue;
                        }
                        import_program(shadow, module->prog, symbol, false, &definition);
                }
        }
        bool found = definition != NULL;
        shadow->importing = previous;
        if (shadow->trace_deferred && shadow->log != NULL && !shadow->failed) {
                log_prefix(shadow, "import");
                fputs(",\"name\":", shadow->log);
                json_string(shadow->log, symbol->identifier);
                fputs(",\"module\":", shadow->log);
                if (home == NULL) fputs("null", shadow->log);
                else json_string(shadow->log, home->name);
                fprintf(
                        shadow->log,
                        ",\"module_program\":%s,\"found\":%s",
                        home != NULL && home->prog != NULL ? "true" : "false",
                        found ? "true" : "false"
                );
                log_end(shadow);
        }
        return definition;
}

static bool
scheme_parameters_erased(Types2Shadow *shadow, T2Scheme const *scheme)
{
        T2Type callable = t2_scheme_body(scheme);
        if (t2_type_kind(shadow->universe, callable) != T2_TYPE_FUNCTION) return false;
        size_t count = t2_callable_parameter_count(shadow->universe, callable);
        for (size_t i = 0; i < count; ++i) {
                T2ParameterSpec parameter;
                if (!t2_callable_parameter(shadow->universe, callable, i, &parameter)) {
                        return false;
                }
                if (t2_type_kind(shadow->universe, parameter.type) != T2_TYPE_DYNAMIC) {
                        return false;
                }
        }
        return count != 0;
}

static bool
statement_defines_operator(Stmt const *statement, char const *name)
{
        if (statement->type != STATEMENT_OPERATOR_DEFINITION) return false;
        char const *target = statement->target == NULL
                           ? NULL
                           : statement->target->identifier;
        char const *function = statement->value == NULL
                             ? NULL
                             : statement->value->name;
        return (target != NULL && strcmp(target, name) == 0)
            || (function != NULL && strcmp(function, name) == 0);
}

static bool
import_operator_in(Types2Shadow *shadow, Stmt const *statement, char const *name)
{
        if (statement == NULL || shadow->failed) return false;
        if (
                statement->type == STATEMENT_BLOCK
             || statement->type == STATEMENT_MULTI
        ) {
                bool found = false;
                for (int i = 0; i < vN(statement->statements); ++i) {
                        found |= import_operator_in(
                                shadow,
                                v__(statement->statements, i),
                                name
                        );
                }
                return found;
        }
        if (!statement_defines_operator(statement, name)) return false;
        size_t mark = shadow->operator_count;
        register_declaration(shadow, statement);
        (void)infer_statement(shadow, statement);
        size_t kept = mark;
        for (size_t i = mark; i < shadow->operator_count; ++i) {
                Types2Operator candidate = shadow->operators[i];
                if (scheme_parameters_erased(shadow, candidate.scheme)) {
                        t2_scheme_free(candidate.scheme);
                        continue;
                }
                shadow->operators[kept++] = candidate;
        }
        shadow->operator_count = kept;
        return kept != mark;
}

static bool
import_operator_definitions(Types2Shadow *shadow, char const *name)
{
        if (shadow->ty == NULL || name == NULL) return false;
        for (size_t i = 0; i < shadow->imported_operator_count; ++i) {
                if (strcmp(shadow->imported_operators[i], name) == 0) return false;
        }
        if (!shadow_reserve(
                shadow,
                (void **)&shadow->imported_operators,
                &shadow->imported_operator_capacity,
                shadow->imported_operator_count + 1,
                sizeof *shadow->imported_operators
        )) return false;
        shadow->imported_operators[shadow->imported_operator_count++] = name;

        bool previous = shadow->importing;
        shadow->importing = true;
        bool found = false;
        ModuleVector const *modules = TyActiveModules(shadow->ty);
        for (int i = 0; i < vN(*modules); ++i) {
                Module const *module = v__(*modules, i);
                if (module_is_current(shadow, module) || module->prog == NULL) {
                        continue;
                }
                for (size_t j = 0; module->prog[j] != NULL; ++j) {
                        found |= import_operator_in(shadow, module->prog[j], name);
                }
        }
        shadow->importing = previous;
        return found;
}

static Types2Binding *
ensure_resolved_binding(Types2Shadow *shadow, Symbol const *symbol)
{
        Types2Binding *binding = ensure_binding(shadow, symbol);
        if (binding == NULL || binding->initialized || binding->imported) {
                return binding;
        }
        binding->imported = true;
        binding->persistent = true;
        Symbol const *definition = import_external_binding(shadow, symbol);
        binding = find_binding(shadow, symbol);
        if (binding == NULL || binding->initialized) return binding;
        Types2Binding *source = definition == NULL || definition == symbol
                              ? NULL
                              : find_binding(shadow, definition);
        if (source != NULL && source->initialized) {
                binding->alias = definition;
                binding->type = source->type;
                binding->mutable = source->mutable;
                binding->initialized = true;
                return binding;
        }
        T2Type literal = literal_symbol_type(shadow, symbol);
        if (literal != T2_TYPE_INVALID) {
                binding->type = literal;
                binding->mutable = false;
                binding->initialized = true;
        }
        return binding;
}

static bool
spread_in_arguments(ExprVec const *arguments)
{
        for (int i = 0; i < vN(*arguments); ++i) {
                Expr const *argument = v__(*arguments, i);
                if (argument != NULL && argument->type == EXPRESSION_SPREAD) return true;
        }
        return false;
}

static bool
tag_symbol_expression(Expr const *expression)
{
        Expr const *unfurled = expression == NULL ? NULL : unfurl(expression);
        return unfurled != NULL
            && (
                       unfurled->type == EXPRESSION_TAG
                    || (
                               unfurled->type == EXPRESSION_IDENTIFIER
                            && SymbolIsTag(unfurled->symbol)
                       )
               );
}

static T2Type
infer_tag_value(Types2Shadow *shadow, Expr const *expression, T2Type payload)
{
        Types2Nominal *nominal = ensure_tag_nominal(
                shadow,
                expression->symbol == NULL ? -1 : expression->symbol->tag,
                expression->identifier
        );
        if (nominal == NULL) {
                defer_node(shadow, TYPES2_DEFER_UNRESOLVED_TAG, expression, expression->identifier);
                return t2_primitive(shadow->universe, T2_TYPE_DYNAMIC);
        }
        return t2_nominal(shadow->universe, nominal->symbol, &payload, 1);
}

static T2Type
infer_tag_call(Types2Shadow *shadow, Expr const *expression)
{
        size_t count = (size_t)vN(expression->args);
        T2Type payload;
        if (count == 0) {
                payload = t2_primitive(shadow->universe, T2_TYPE_NIL);
        } else if (count == 1) {
                payload = infer_expression(shadow, v__(expression->args, 0));
        } else {
                T2Type *items = malloc(count * sizeof *items);
                if (items == NULL) {
                        shadow->failed = true;
                        return T2_TYPE_INVALID;
                }
                for (size_t i = 0; i < count; ++i) {
                        items[i] = infer_expression(shadow, v__(expression->args, (int)i));
                }
                payload = t2_tuple(shadow->universe, items, count);
                free(items);
        }
        return infer_tag_value(shadow, unfurl(expression->function), payload);
}

static T2Type
tag_type_value(Types2Shadow *shadow, Expr const *expression)
{
        T2Type dynamic = t2_primitive(shadow->universe, T2_TYPE_DYNAMIC);
        T2Type instance = infer_tag_value(shadow, expression, dynamic);
        if (t2_type_kind(shadow->universe, instance) != T2_TYPE_NOMINAL) return instance;
        T2ParameterSpec parameter = {
                .name = "value",
                .type = dynamic,
                .kind = T2_PARAMETER_POSITIONAL_ONLY,
                .required = true
        };
        T2Type constructor = t2_callable(
                shadow->universe,
                &parameter,
                1,
                instance,
                t2_primitive(shadow->universe, T2_TYPE_NEVER),
                t2_primitive(shadow->universe, T2_TYPE_NIL)
        );
        if (constructor == T2_TYPE_INVALID) return instance;
        T2Type value = t2_type_value(shadow->universe, instance, constructor);
        return value == T2_TYPE_INVALID ? instance : value;
}

static T2Type
infer_receiver(Types2Shadow *shadow, Expr const *object)
{
        T2Type type = infer_expression(shadow, object);
        if (!tag_symbol_expression(object)) return type;
        return tag_type_value(shadow, unfurl(object));
}

static T2Type
infer_expression(Types2Shadow *shadow, Expr const *source)
{
        Expr const *expression = source == NULL ? NULL : unfurl(source);
        if (expression == NULL) return t2_primitive(shadow->universe, T2_TYPE_NIL);
        if (IsStmt(expression)) {
                return infer_statement(shadow, (Stmt const *)expression).value;
        }
        T2Type cached = node_type(shadow, expression);
        if (cached != T2_TYPE_INVALID) return cached;

        T2Type result = T2_TYPE_INVALID;
        switch (expression->type) {
        case EXPRESSION_INTEGER:
                result = t2_literal_int(shadow->universe, expression->integer);
                break;
        case EXPRESSION_BOOLEAN:
                result = t2_literal_bool(shadow->universe, expression->boolean);
                break;
        case EXPRESSION_STRING:
                result = t2_literal_string(shadow->universe, expression->string);
                break;
        case EXPRESSION_SPECIAL_STRING:
        {
                T2Type payload = t2_primitive(shadow->universe, T2_TYPE_NEVER);
                T2Type string = t2_primitive(shadow->universe, T2_TYPE_STRING);
                for (int i = 0; i < vN(expression->expressions); ++i) {
                        payload = t2_join(
                                shadow->universe,
                                payload,
                                infer_expression(
                                        shadow,
                                        v__(expression->expressions, i)
                                )
                        );
                        Expr const *format = i < vN(expression->fmts)
                                           ? *v_(expression->fmts, i)
                                           : NULL;
                        if (format != NULL) {
                                (void)constrain_type(
                                        shadow,
                                        format,
                                        infer_expression(shadow, format),
                                        string,
                                        "special-string-format",
                                        "an interpolation format must be a String"
                                );
                        }
                        Expr const *formatter = i < vN(expression->fmtfs)
                                              ? *v_(expression->fmtfs, i)
                                              : NULL;
                        if (formatter != NULL) {
                                (void)infer_expression(shadow, formatter);
                        }
                }
                if (expression->lang == NULL) {
                        result = string;
                        break;
                }

                T2Type element = string;
                if (vN(expression->expressions) != 0) {
                        T2Type interpolation = t2_tuple(
                                shadow->universe,
                                (T2Type[]) {
                                        payload,
                                        t2_union(
                                                shadow->universe,
                                                (T2Type[]) {
                                                        string,
                                                        t2_primitive(
                                                                shadow->universe,
                                                                T2_TYPE_NIL
                                                        )
                                                },
                                                2
                                        ),
                                        t2_primitive(shadow->universe, T2_TYPE_INT)
                                },
                                3
                        );
                        element = t2_join(
                                shadow->universe,
                                element,
                                interpolation
                        );
                }
                T2Type parts = nominal_application(
                        shadow,
                        CLASS_ARRAY,
                        "Array",
                        &element,
                        1,
                        expression
                );
                T2Type handler = infer_expression(shadow, expression->lang);
                result = infer_runtime_call_types(
                        shadow,
                        handler,
                        &parts,
                        1,
                        NULL,
                        NULL,
                        0,
                        expression,
                        true
                );
                break;
        }
        case EXPRESSION_REGEX:
        case EXPRESSION_DYNAMIC_REGEX:
        {
                if (expression->type == EXPRESSION_DYNAMIC_REGEX) {
                        for (int i = 0; i < vN(expression->expressions); ++i) {
                                (void)infer_expression(
                                        shadow,
                                        v__(expression->expressions, i)
                                );
                        }
                }
                bool detailed = expression->type == EXPRESSION_REGEX
                              ? expression->regex != NULL
                             && expression->regex->detailed
                              : expression->re_flags != NULL
                             && strchr(expression->re_flags, 'v') != NULL;
                int class_id = detailed ? CLASS_REGEXV : CLASS_REGEX;
                Types2Nominal *nominal = ensure_nominal(
                        shadow,
                        class_id,
                        detailed ? "RegexV" : "Regex",
                        0
                );
                if (nominal == NULL) {
                        defer_node(
                                shadow,
                                TYPES2_DEFER_UNRESOLVED_NOMINAL,
                                expression,
                                detailed ? "RegexV" : "Regex"
                        );
                        result = t2_primitive(shadow->universe, T2_TYPE_DYNAMIC);
                        break;
                }
                T2Type base = t2_nominal(
                        shadow->universe,
                        nominal->symbol,
                        NULL,
                        0
                );
                T2Type captures = expression->type == EXPRESSION_REGEX
                                && expression->regex != NULL
                                ? t2_literal_int(
                                        shadow->universe,
                                        expression->regex->ncap
                                  )
                                : t2_primitive(
                                        shadow->universe,
                                        T2_TYPE_UNKNOWN
                                  );
                result = t2_refinement(shadow->universe, base, captures);
                break;
        }
        case EXPRESSION_REAL:
                result = t2_primitive(shadow->universe, T2_TYPE_FLOAT);
                break;
        case EXPRESSION_NIL:
        case EXPRESSION_NONE:
                result = t2_primitive(shadow->universe, T2_TYPE_NIL);
                break;
        case EXPRESSION_MATCH_ANY:
                /* The resolver also uses MATCH_ANY for an underscore value in
                 * expanded templates.  In expression position it is Ty's
                 * quiet Dynamic escape hatch; pattern position is handled by
                 * infer_pattern and remains an irrefutable wildcard. */
                result = t2_primitive(shadow->universe, T2_TYPE_DYNAMIC);
                break;
        case EXPRESSION_IDENTIFIER:
        case EXPRESSION_SELF:
        case EXPRESSION_SUPER:
        {
                /* Name resolution represents an implicit `self.member` access
                 * as an identifier whose symbol carries SYM_MEMBER.  Treating
                 * that symbol as an ordinary lexical binding loses the class
                 * scheme (and, in particular, receiver type arguments). */
                if (
                        expression->type == EXPRESSION_IDENTIFIER
                     && SymbolIsTag(expression->symbol)
                ) {
                        result = infer_tag_value(
                                shadow,
                                expression,
                                t2_primitive(shadow->universe, T2_TYPE_NEVER)
                        );
                        break;
                }
                T2Type member_receiver = expression->type == EXPRESSION_IDENTIFIER
                                       ? implicit_member_receiver(
                                               shadow,
                                               expression->symbol
                                         )
                                       : T2_TYPE_INVALID;
                if (member_receiver != T2_TYPE_INVALID) {
                        result = infer_member_type(
                                shadow,
                                member_receiver,
                                expression->identifier,
                                false,
                                expression,
                                true
                        );
                        Types2Binding *refined = member_refinement_binding(
                                shadow,
                                expression->symbol,
                                expression
                        );
                        if (refined != NULL && refined->refinement != T2_TYPE_INVALID) {
                                result = refined->refinement;
                        }
                        break;
                }
                Types2Binding *binding = ensure_resolved_binding(
                        shadow,
                        expression->symbol
                );
                if (binding != NULL && !binding->initialized) {
                        binding->type = t2_primitive(
                                shadow->universe,
                                T2_TYPE_DYNAMIC
                        );
                        binding->initialized = true;
                        defer_symbol(
                                shadow,
                                TYPES2_DEFER_UNRESOLVED_BINDING,
                                expression,
                                expression->symbol
                        );
                }
                result = instantiate_binding(shadow, binding, expression);
                if (result == T2_TYPE_INVALID) {
                        result = t2_primitive(shadow->universe, T2_TYPE_DYNAMIC);
                }
                break;
        }
        case EXPRESSION_SPREAD:
        case EXPRESSION_SPLAT:
                result = infer_expression(shadow, expression->value);
                break;
        case EXPRESSION_ARRAY:
        {
                T2Type element = t2_primitive(shadow->universe, T2_TYPE_NEVER);
                for (int i = 0; i < vN(expression->elements); ++i) {
                        Expr const *element_expression = v__(expression->elements, i);
                        T2Type item = relax_literal(
                                shadow,
                                infer_expression(shadow, element_expression)
                        );
                        if (
                                element_expression != NULL
                             && element_expression->type == EXPRESSION_SPREAD
                        ) {
                                item = iterated_type(
                                        shadow,
                                        item,
                                        element_expression
                                );
                        }
                        element = t2_join(shadow->universe, element, item);
                        if (i < vN(expression->aconds) && v__(expression->aconds, i) != NULL) {
                                (void)infer_expression(
                                        shadow,
                                        v__(expression->aconds, i)
                                );
                        }
                }
                if (t2_type_kind(shadow->universe, element) == T2_TYPE_NEVER) {
                        element = t2_solver_new_meta(
                                shadow->solver,
                                T2_VARIABLE_WEAK,
                                shadow->level,
                                "empty array element"
                        );
                }
                result = nominal_application(
                        shadow,
                        CLASS_ARRAY,
                        "Array",
                        &element,
                        1,
                        expression
                );
                break;
        }
        case EXPRESSION_ARRAY_COMPR:
        {
                size_t binding_mark = shadow->binding_count;
                for (int i = 0; i < vN(expression->compr); ++i) {
                        ComprPart const *part = v_(expression->compr, i);
                        T2Type collection = infer_expression(shadow, part->iter);
                        (void)assign_lvalue(
                                shadow,
                                part->pattern,
                                iterated_type(shadow, collection, part->iter),
                                true
                        );
                        (void)infer_statement(shadow, part->where);
                        (void)infer_expression(shadow, part->_while);
                        (void)infer_expression(shadow, part->_if);
                }
                T2Type element = t2_primitive(shadow->universe, T2_TYPE_NEVER);
                for (int i = 0; i < vN(expression->elements); ++i) {
                        element = t2_join(
                                shadow->universe,
                                element,
                                relax_literal(
                                        shadow,
                                        infer_expression(shadow, v__(expression->elements, i))
                                )
                        );
                        if (i < vN(expression->aconds)) {
                                (void)infer_expression(shadow, v__(expression->aconds, i));
                        }
                }
                if (t2_type_kind(shadow->universe, element) == T2_TYPE_NEVER) {
                        element = t2_solver_new_meta(
                                shadow->solver,
                                T2_VARIABLE_WEAK,
                                shadow->level,
                                "empty array comprehension element"
                        );
                }
                for (size_t i = binding_mark; i < shadow->binding_count; ++i) {
                        if (!shadow->bindings[i].persistent) {
                                shadow->bindings[i].active = false;
                        }
                }
                result = nominal_application(
                        shadow,
                        CLASS_ARRAY,
                        "Array",
                        &element,
                        1,
                        expression
                );
                break;
        }
        case EXPRESSION_DICT:
        {
                T2Type key = t2_primitive(shadow->universe, T2_TYPE_NEVER);
                T2Type value = t2_primitive(shadow->universe, T2_TYPE_NEVER);
                for (int i = 0; i < vN(expression->keys); ++i) {
                        Expr const *key_expression = v__(expression->keys, i);
                        if (
                                key_expression != NULL
                             && key_expression->type == EXPRESSION_SPLAT
                        ) {
                                T2Type spread = resolved_type_head(
                                        shadow,
                                        infer_expression(shadow, key_expression),
                                        T2_PREFER_LOWER_BOUND
                                );
                                T2Type spread_key;
                                T2Type spread_value;
                                if (dictionary_spread_types(
                                        shadow,
                                        spread,
                                        &spread_key,
                                        &spread_value
                                )) {
                                        key = t2_join(
                                                shadow->universe,
                                                key,
                                                spread_key
                                        );
                                        value = t2_join(
                                                shadow->universe,
                                                value,
                                                spread_value
                                        );
                                } else {
                                        add_diagnostic(
                                                shadow,
                                                key_expression,
                                                TYPES2_DIAGNOSTIC_ERROR,
                                                "dictionary-spread",
                                                spread,
                                                T2_TYPE_INVALID,
                                                "dictionary spread requires a dictionary or structural record value"
                                        );
                                        key = t2_primitive(shadow->universe, T2_TYPE_ERROR);
                                        value = key;
                                }
                                continue;
                        }
                        key = t2_join(
                                shadow->universe,
                                key,
                                relax_literal(
                                        shadow,
                                        infer_expression(shadow, key_expression)
                                )
                        );
                        Expr const *value_expression = i < vN(expression->values)
                                                     ? v__(expression->values, i)
                                                     : NULL;
                        value = t2_join(
                                shadow->universe,
                                value,
                                relax_literal(
                                        shadow,
                                        infer_expression(shadow, value_expression)
                                )
                        );
                }
                if (t2_type_kind(shadow->universe, key) == T2_TYPE_NEVER) {
                        key = t2_solver_new_meta(
                                shadow->solver,
                                T2_VARIABLE_WEAK,
                                shadow->level,
                                "empty dictionary key"
                        );
                        value = t2_solver_new_meta(
                                shadow->solver,
                                T2_VARIABLE_WEAK,
                                shadow->level,
                                "empty dictionary value"
                        );
                }
                if (expression->dflt != NULL) {
                        T2Type fallback = infer_expression(shadow, expression->dflt);
                        T2Type produced = T2_TYPE_INVALID;
                        T2TypeKind fallback_kind = t2_type_kind(
                                shadow->universe,
                                fallback
                        );
                        if (
                                fallback_kind == T2_TYPE_FUNCTION
                             || fallback_kind == T2_TYPE_OVERLOAD
                             || fallback_kind == T2_TYPE_INTERSECTION
                        ) {
                                T2SolverMark mark = t2_solver_mark(shadow->solver);
                                produced = infer_call_types(
                                        shadow,
                                        fallback,
                                        &key,
                                        1,
                                        NULL,
                                        NULL,
                                        0,
                                        expression->dflt,
                                        false
                                );
                                if (
                                        produced != T2_TYPE_INVALID
                                     && t2_type_kind(shadow->universe, produced)
                                        != T2_TYPE_ERROR
                                     && !t2_solver_failed(shadow->solver)
                                ) t2_solver_commit(shadow->solver, mark);
                                else {
                                        t2_solver_rollback(shadow->solver, mark);
                                        produced = T2_TYPE_INVALID;
                                }
                        }
                        value = t2_join(
                                shadow->universe,
                                value,
                                produced == T2_TYPE_INVALID ? fallback : produced
                        );
                }
                result = nominal_application(
                        shadow,
                        CLASS_DICT,
                        "Dict",
                        (T2Type[]){ key, value },
                        2,
                        expression
                );
                break;
        }
        case EXPRESSION_DICT_COMPR:
        {
                size_t binding_mark = shadow->binding_count;
                for (int i = 0; i < vN(expression->dcompr); ++i) {
                        ComprPart const *part = v_(expression->dcompr, i);
                        T2Type collection = infer_expression(shadow, part->iter);
                        (void)assign_lvalue(
                                shadow,
                                part->pattern,
                                iterated_type(shadow, collection, part->iter),
                                true
                        );
                        (void)infer_statement(shadow, part->where);
                        (void)infer_expression(shadow, part->_while);
                        (void)infer_expression(shadow, part->_if);
                }
                T2Type key = t2_primitive(shadow->universe, T2_TYPE_NEVER);
                T2Type value = t2_primitive(shadow->universe, T2_TYPE_NEVER);
                for (int i = 0; i < vN(expression->keys); ++i) {
                        key = t2_join(
                                shadow->universe,
                                key,
                                relax_literal(
                                        shadow,
                                        infer_expression(shadow, v__(expression->keys, i))
                                )
                        );
                        value = t2_join(
                                shadow->universe,
                                value,
                                relax_literal(
                                        shadow,
                                        infer_expression(shadow, v__(expression->values, i))
                                )
                        );
                }
                if (t2_type_kind(shadow->universe, key) == T2_TYPE_NEVER) {
                        key = t2_solver_new_meta(
                                shadow->solver,
                                T2_VARIABLE_WEAK,
                                shadow->level,
                                "empty dictionary comprehension key"
                        );
                        value = t2_solver_new_meta(
                                shadow->solver,
                                T2_VARIABLE_WEAK,
                                shadow->level,
                                "empty dictionary comprehension value"
                        );
                }
                if (expression->dflt != NULL) {
                        T2Type fallback = infer_expression(shadow, expression->dflt);
                        T2Type produced = T2_TYPE_INVALID;
                        T2TypeKind fallback_kind = t2_type_kind(
                                shadow->universe,
                                fallback
                        );
                        if (
                                fallback_kind == T2_TYPE_FUNCTION
                             || fallback_kind == T2_TYPE_OVERLOAD
                             || fallback_kind == T2_TYPE_INTERSECTION
                        ) {
                                T2SolverMark mark = t2_solver_mark(shadow->solver);
                                produced = infer_call_types(
                                        shadow,
                                        fallback,
                                        &key,
                                        1,
                                        NULL,
                                        NULL,
                                        0,
                                        expression->dflt,
                                        false
                                );
                                if (
                                        produced != T2_TYPE_INVALID
                                     && t2_type_kind(shadow->universe, produced)
                                        != T2_TYPE_ERROR
                                     && !t2_solver_failed(shadow->solver)
                                ) t2_solver_commit(shadow->solver, mark);
                                else {
                                        t2_solver_rollback(shadow->solver, mark);
                                        produced = T2_TYPE_INVALID;
                                }
                        }
                        value = t2_join(
                                shadow->universe,
                                value,
                                produced == T2_TYPE_INVALID ? fallback : produced
                        );
                }
                for (size_t i = binding_mark; i < shadow->binding_count; ++i) {
                        if (!shadow->bindings[i].persistent) {
                                shadow->bindings[i].active = false;
                        }
                }
                result = nominal_application(
                        shadow,
                        CLASS_DICT,
                        "Dict",
                        (T2Type[]) { key, value },
                        2,
                        expression
                );
                break;
        }
        case EXPRESSION_TUPLE:
        case EXPRESSION_LIST:
        {
                size_t count = (size_t)vN(expression->es);
                if (expression->type == EXPRESSION_TUPLE && tuple_is_record(expression)) {
                        result = tuple_is_pure_record(expression)
                               ? infer_record_literal(shadow, expression)
                               : infer_mixed_tuple(shadow, expression);
                } else {
                        T2Type *items = count == 0 ? NULL : malloc(count * sizeof *items);
                        if (count != 0 && items == NULL) {
                                shadow->failed = true;
                                break;
                        }
                        for (size_t i = 0; i < count; ++i) {
                                items[i] = infer_expression(
                                        shadow,
                                        v__(expression->es, (int)i)
                                );
                        }
                        result = t2_tuple(shadow->universe, items, count);
                        free(items);
                }
                break;
        }
        case EXPRESSION_TAG:
                result = infer_tag_value(
                        shadow,
                        expression,
                        t2_primitive(shadow->universe, T2_TYPE_NEVER)
                );
                break;
        case EXPRESSION_TAG_APPLICATION:
        {
                T2Type payload = infer_expression(shadow, expression->tagged);
                Types2Nominal *nominal = ensure_tag_nominal(
                        shadow,
                        expression->symbol == NULL ? -1 : expression->symbol->tag,
                        expression->identifier
                );
                if (nominal == NULL) {
                        defer_node(shadow, TYPES2_DEFER_UNRESOLVED_TAG, expression, expression->identifier);
                        result = t2_primitive(shadow->universe, T2_TYPE_DYNAMIC);
                } else {
                        result = t2_nominal(
                                shadow->universe,
                                nominal->symbol,
                                &payload,
                                1
                        );
                }
                break;
        }
        case EXPRESSION_MATCH:
        {
                T2Type subject = infer_expression(shadow, expression->subject);
                T2Type remaining = subject;
                result = t2_primitive(shadow->universe, T2_TYPE_NEVER);
                for (int i = 0; i < vN(expression->patterns); ++i) {
                        size_t binding_mark = shadow->binding_count;
                        Expr const *pattern = v__(expression->patterns, i);
                        bool covered = t2_type_kind(
                                               shadow->universe,
                                               remaining
                                       ) == T2_TYPE_NEVER;
                        if (covered) {
                                add_diagnostic(
                                        shadow,
                                        pattern,
                                        TYPES2_DIAGNOSTIC_WARNING,
                                        "unreachable-pattern",
                                        subject,
                                        T2_TYPE_INVALID,
                                        "previous match arms already cover the subject type"
                                );
                        }
                        bool reachable = infer_refutable_pattern(
                                shadow,
                                pattern,
                                covered ? subject : remaining
                        );
                        T2Type arm = infer_expression(
                                shadow,
                                v__(expression->thens, i)
                        );
                        if (reachable && !covered) {
                                result = t2_join(
                                        shadow->universe,
                                        result,
                                        arm
                                );
                                bool certain = false;
                                T2Type coverage = pattern_coverage(
                                        shadow,
                                        pattern,
                                        remaining,
                                        &certain
                                );
                                if (certain) {
                                        remaining = subtract_pattern_coverage(
                                                shadow,
                                                remaining,
                                                coverage,
                                                pattern_is_catch_all(pattern)
                                        );
                                }
                        }
                        for (size_t j = binding_mark; j < shadow->binding_count; ++j) {
                                if (!shadow->bindings[j].persistent) {
                                        shadow->bindings[j].active = false;
                                }
                        }
                }
                if (
                        t2_type_kind(shadow->universe, remaining) != T2_TYPE_NEVER
                     && match_domain_is_closed(shadow, subject)
                ) add_diagnostic(
                        shadow,
                        expression,
                        TYPES2_DIAGNOSTIC_WARNING,
                        "non-exhaustive-match",
                        remaining,
                        T2_TYPE_INVALID,
                        "match expression does not cover every reachable closed-domain value"
                );
                break;
        }
        case EXPRESSION_COMPILE_TIME:
                /* The legacy compile-time broker has already run.  Consuming its
                 * legacy Type would couple the solvers, so unresolved snapshots
                 * remain explicitly deferred until the native broker lands. */
                defer_node(shadow, TYPES2_DEFER_COMPILE_TIME, expression, NULL);
                result = t2_primitive(shadow->universe, T2_TYPE_DYNAMIC);
                break;
        case EXPRESSION_CONDITIONAL:
        {
                (void)infer_expression(shadow, expression->cond);
                size_t binding_mark = shadow->binding_count;
                T2Type *before = snapshot_refinements(shadow, binding_mark);
                if (binding_mark != 0 && before == NULL) break;
                apply_condition_refinements(shadow, expression->cond, true);
                T2Type then_type = infer_expression(shadow, expression->then);
                T2Type *then_bindings = snapshot_effective_types(
                        shadow,
                        binding_mark
                );
                restore_refinements(shadow, before, binding_mark);
                apply_condition_refinements(shadow, expression->cond, false);
                T2Type else_type = expression->_else == NULL
                                 ? t2_primitive(shadow->universe, T2_TYPE_NIL)
                                 : infer_expression(shadow, expression->_else);
                T2Type *else_bindings = snapshot_effective_types(
                        shadow,
                        binding_mark
                );
                restore_refinements(shadow, before, binding_mark);
                if (
                        (binding_mark == 0 || then_bindings != NULL)
                     && (binding_mark == 0 || else_bindings != NULL)
                ) merge_branch_refinements(
                        shadow,
                        then_bindings,
                        true,
                        else_bindings,
                        true,
                        binding_mark
                );
                free(before);
                free(then_bindings);
                free(else_bindings);
                result = t2_join(shadow->universe, then_type, else_type);
                break;
        }
        case EXPRESSION_FUNCTION_CALL:
        {
                size_t positional_count = (size_t)vN(expression->args);
                size_t keyword_count = (size_t)vN(expression->kwargs);
                if (
                        keyword_count == 0
                     && tag_symbol_expression(expression->function)
                     && !spread_in_arguments(&expression->args)
                ) {
                        result = infer_tag_call(shadow, expression);
                        break;
                }
                T2Type *arguments = positional_count == 0
                                  ? NULL
                                  : malloc(positional_count * sizeof *arguments);
                T2Type *keyword_arguments = keyword_count == 0
                                          ? NULL
                                          : malloc(keyword_count * sizeof *keyword_arguments);
                if (
                        (positional_count != 0 && arguments == NULL)
                     || (keyword_count != 0 && keyword_arguments == NULL)
                ) {
                        free(arguments);
                        free(keyword_arguments);
                        shadow->failed = true;
                        break;
                }
                T2SolverMark argument_scope = t2_solver_mark(shadow->solver);
                for (size_t i = 0; i < positional_count; ++i) {
                        arguments[i] = infer_expression(
                                shadow,
                                v__(expression->args, (int)i)
                        );
                }
                for (size_t i = 0; i < keyword_count; ++i) {
                        keyword_arguments[i] = infer_expression(
                                shadow,
                                v__(expression->kwargs, (int)i)
                        );
                }
                /* Instantiate the callee only after independently checking its
                 * arguments.  This gives a failed call one precise obligation
                 * boundary without rolling back types cached for argument
                 * subexpressions. */
                T2SolverMark invocation = t2_solver_mark(shadow->solver);
                T2Type callee = infer_expression(shadow, expression->function);
                T2TypeKind callee_kind = t2_type_kind(
                        shadow->universe,
                        callee
                );
                if (
                        callee_kind == T2_TYPE_DYNAMIC
                     || callee_kind == T2_TYPE_ERROR
                ) {
                        default_dynamic_callback_arguments(
                                shadow,
                                &expression->args,
                                arguments,
                                positional_count
                        );
                        default_dynamic_callback_arguments(
                                shadow,
                                &expression->kwargs,
                                keyword_arguments,
                                keyword_count
                        );
                }
                T2Type *expanded_arguments = NULL;
                size_t expanded_count = 0;
                if (!expand_fixed_tuple_call_splats(
                        shadow,
                        &expression->args,
                        arguments,
                        positional_count,
                        &expanded_arguments,
                        &expanded_count
                )) {
                        result = T2_TYPE_INVALID;
                } else {
                        result = infer_runtime_call_types(
                                shadow,
                                callee,
                                expanded_arguments,
                                expanded_count,
                                keyword_arguments,
                                (char const *const *)vv(expression->kws),
                                keyword_count,
                                expression,
                                true
                        );
                }
                if (
                        result == T2_TYPE_INVALID
                     || t2_type_kind(shadow->universe, result) == T2_TYPE_ERROR
                     || t2_solver_failed(shadow->solver)
                ) {
                        if (!t2_solver_cancel_obligations_since(
                                shadow->solver,
                                invocation
                        )) shadow->failed = true;
                }
                t2_solver_commit(shadow->solver, invocation);
                if (
                        result == T2_TYPE_INVALID
                     || t2_type_kind(shadow->universe, result) == T2_TYPE_ERROR
                     || t2_solver_failed(shadow->solver)
                ) {
                        if (!t2_solver_cancel_obligations_since(
                                shadow->solver,
                                argument_scope
                        )) shadow->failed = true;
                }
                t2_solver_commit(shadow->solver, argument_scope);
                invalidate_unstable_refinements(shadow);
                free(expanded_arguments);
                free(arguments);
                free(keyword_arguments);
                break;
        }
        case EXPRESSION_OPERATOR:
                /* Operator values are open-world overload sets.  The native
                 * class-operator registry supplies their final scheme later in
                 * this pass; keeping this as an explicit deferred boundary is
                 * preferable to borrowing the mutable legacy overload graph. */
                defer_node(shadow, TYPES2_DEFER_OPERATOR_VALUE, expression, expression->op.id);
                result = t2_primitive(shadow->universe, T2_TYPE_DYNAMIC);
                break;
        case EXPRESSION_USER_OP:
        {
                (void)infer_expression(shadow, expression->sc);
                T2Type left = infer_expression(shadow, expression->left);
                T2Type right = infer_expression(shadow, expression->right);
                uint8_t operation = named_binary_operation(expression->op_name);
                if (operation != EXPRESSION_MAX_TYPE) {
                        result = infer_binary_pair(
                                shadow,
                                operation,
                                left,
                                right,
                                expression,
                                true
                        );
                        break;
                }
                result = infer_registered_operator(
                        shadow,
                        expression->op_name,
                        left,
                        right,
                        expression,
                        false
                );
                if (result != T2_TYPE_INVALID) {
                        if (t2_type_kind(shadow->universe, result) == T2_TYPE_ERROR) {
                                add_diagnostic(
                                        shadow,
                                        expression,
                                        TYPES2_DIAGNOSTIC_ERROR,
                                        "unsupported-user-operator",
                                        left,
                                        right,
                                        "operator `%s` has no unique applicable binary contract",
                                        expression->op_name == NULL
                                            ? "<operator>"
                                            : expression->op_name
                                );
                        }
                        invalidate_unstable_refinements(shadow);
                        break;
                }
                T2Type method = infer_method_type(
                        shadow,
                        left,
                        expression->op_name,
                        false,
                        expression,
                        false
                );
                result = infer_runtime_call_types(
                        shadow,
                        method,
                        &right,
                        1,
                        NULL,
                        NULL,
                        0,
                        expression,
                        false
                );
                invalidate_unstable_refinements(shadow);
                if (t2_type_kind(shadow->universe, result) == T2_TYPE_ERROR) {
                        add_diagnostic(
                                shadow,
                                expression,
                                TYPES2_DIAGNOSTIC_ERROR,
                                "unsupported-user-operator",
                                left,
                                right,
                                "operator `%s` has no applicable binary contract",
                                expression->op_name == NULL ? "<operator>" : expression->op_name
                        );
                }
                break;
        }
        case EXPRESSION_PLUS:
        case EXPRESSION_MINUS:
        case EXPRESSION_STAR:
        case EXPRESSION_DIV:
        case EXPRESSION_PERCENT:
        case EXPRESSION_BIT_AND:
        case EXPRESSION_BIT_OR:
        case EXPRESSION_XOR:
        case EXPRESSION_SHL:
        case EXPRESSION_SHR:
        case EXPRESSION_LT:
        case EXPRESSION_LEQ:
        case EXPRESSION_GT:
        case EXPRESSION_GEQ:
        case EXPRESSION_CMP:
        case EXPRESSION_DBL_EQ:
        case EXPRESSION_NOT_EQ:
        case EXPRESSION_CHECK_MATCH:
                result = infer_binary_pair(
                        shadow,
                        expression->type,
                        infer_expression(shadow, expression->left),
                        infer_expression(shadow, expression->right),
                        expression,
                        true
                );
                invalidate_unstable_refinements(shadow);
                break;
        case EXPRESSION_UNARY_OP:
        {
                T2Type operand = infer_expression(shadow, expression->operand);
                T2Type method = infer_member_type(
                        shadow,
                        operand,
                        expression->uop,
                        false,
                        expression,
                        false
                );
                result = infer_call_types(
                        shadow,
                        method,
                        NULL,
                        0,
                        NULL,
                        NULL,
                        0,
                        expression,
                        false
                );
                invalidate_unstable_refinements(shadow);
                if (t2_type_kind(shadow->universe, result) == T2_TYPE_ERROR) {
                        add_diagnostic(
                                shadow,
                                expression,
                                TYPES2_DIAGNOSTIC_ERROR,
                                "unsupported-unary-operator",
                                operand,
                                T2_TYPE_INVALID,
                                "unary operator `%s` has no zero-argument contract",
                                expression->uop == NULL ? "<operator>" : expression->uop
                        );
                }
                break;
        }
        case EXPRESSION_AND:
        case EXPRESSION_OR:
        case EXPRESSION_KW_AND:
        case EXPRESSION_KW_OR:
        {
                T2Type left = infer_expression(shadow, expression->left);
                size_t binding_mark = shadow->binding_count;
                T2Type *before = snapshot_refinements(shadow, binding_mark);
                if (binding_mark != 0 && before == NULL) break;
                bool right_condition = expression->type == EXPRESSION_AND
                                    || expression->type == EXPRESSION_KW_AND;
                apply_condition_refinements(
                        shadow,
                        expression->left,
                        right_condition
                );
                T2Type right = expression->right == NULL
                             ? t2_primitive(shadow->universe, T2_TYPE_NIL)
                             : infer_expression(shadow, expression->right);
                T2Type *right_bindings = snapshot_effective_types(
                        shadow,
                        binding_mark
                );
                restore_refinements(shadow, before, binding_mark);
                T2Type *skipped_bindings = snapshot_effective_types(
                        shadow,
                        binding_mark
                );
                if (
                        (binding_mark == 0 || right_bindings != NULL)
                     && (binding_mark == 0 || skipped_bindings != NULL)
                ) merge_branch_refinements(
                        shadow,
                        right_bindings,
                        true,
                        skipped_bindings,
                        true,
                        binding_mark
                );
                free(before);
                free(right_bindings);
                free(skipped_bindings);
                result = t2_join(shadow->universe, left, right);
                break;
        }
        case EXPRESSION_WTF:
        {
                T2Type left = resolved_type_head(
                        shadow,
                        infer_expression(shadow, expression->left),
                        T2_PREFER_LOWER_BOUND
                );
                T2Type right = infer_expression(shadow, expression->right);
                result = t2_join(
                        shadow->universe,
                        without_nil(shadow, left),
                        right
                );
                break;
        }
        case EXPRESSION_SUBSCRIPT:
                result = infer_subscript_type(
                        shadow,
                        infer_expression(shadow, expression->container),
                        infer_expression(shadow, expression->subscript),
                        expression->subscript,
                        expression,
                        true
                );
                break;
        case EXPRESSION_SLICE:
        {
                T2Type nil = t2_primitive(shadow->universe, T2_TYPE_NIL);
                T2Type bounds[3] = {
                        expression->slice.i == NULL
                            ? nil
                            : infer_expression(shadow, expression->slice.i),
                        expression->slice.j == NULL
                            ? nil
                            : infer_expression(shadow, expression->slice.j),
                        expression->slice.k == NULL
                            ? nil
                            : infer_expression(shadow, expression->slice.k)
                };
                result = infer_slice_type(
                        shadow,
                        infer_expression(shadow, expression->slice.e),
                        bounds,
                        expression,
                        true
                );
                break;
        }
        case EXPRESSION_MEMBER_ACCESS:
        case EXPRESSION_SELF_ACCESS:
                result = infer_member_type(
                        shadow,
                        infer_receiver(shadow, expression->object),
                        expression->member->identifier,
                        expression->maybe,
                        expression,
                        true
                );
                break;
        case EXPRESSION_DYN_MEMBER_ACCESS:
        {
                T2Type object = infer_expression(shadow, expression->object);
                (void)constrain_type(
                        shadow,
                        expression->member,
                        infer_expression(shadow, expression->member),
                        t2_primitive(shadow->universe, T2_TYPE_STRING),
                        "dynamic-member-name",
                        "a dynamic member name must be a String"
                );
                if (t2_type_kind(shadow->universe, object) == T2_TYPE_ERROR) {
                        result = object;
                } else {
                        defer_node(shadow, TYPES2_DEFER_DYNAMIC_MEMBER_NAME, expression, NULL);
                        result = t2_primitive(shadow->universe, T2_TYPE_DYNAMIC);
                        if (expression->maybe) {
                                result = t2_join(
                                        shadow->universe,
                                        result,
                                        t2_primitive(shadow->universe, T2_TYPE_NIL)
                                );
                        }
                }
                break;
        }
        case EXPRESSION_METHOD_CALL:
        {
                T2Type method = infer_method_type(
                        shadow,
                        infer_receiver(shadow, expression->object),
                        expression->method->identifier,
                        expression->maybe,
                        expression,
                        true
                );
                size_t count = (size_t)vN(expression->method_args);
                size_t kwcount = (size_t)vN(expression->method_kwargs);
                T2Type *arguments = count == 0 ? NULL : malloc(count * sizeof *arguments);
                T2Type *kwargs = kwcount == 0 ? NULL : malloc(kwcount * sizeof *kwargs);
                if ((count && arguments == NULL) || (kwcount && kwargs == NULL)) {
                        free(arguments);
                        free(kwargs);
                        shadow->failed = true;
                        break;
                }
                T2SolverMark argument_scope = t2_solver_mark(shadow->solver);
                for (size_t i = 0; i < count; ++i) {
                        arguments[i] = infer_expression(
                                shadow,
                                v__(expression->method_args, (int)i)
                        );
                }
                for (size_t i = 0; i < kwcount; ++i) {
                        kwargs[i] = infer_expression(
                                shadow,
                                v__(expression->method_kwargs, (int)i)
                        );
                }
                T2TypeKind method_kind = t2_type_kind(
                        shadow->universe,
                        method
                );
                if (
                        method_kind == T2_TYPE_DYNAMIC
                     || method_kind == T2_TYPE_ERROR
                ) {
                        default_dynamic_callback_arguments(
                                shadow,
                                &expression->method_args,
                                arguments,
                                count
                        );
                        default_dynamic_callback_arguments(
                                shadow,
                                &expression->method_kwargs,
                                kwargs,
                                kwcount
                        );
                }
                T2Type *expanded_arguments = NULL;
                size_t expanded_count = 0;
                if (!expand_fixed_tuple_call_splats(
                        shadow,
                        &expression->method_args,
                        arguments,
                        count,
                        &expanded_arguments,
                        &expanded_count
                )) {
                        result = T2_TYPE_INVALID;
                } else {
                        result = infer_runtime_call_types(
                                shadow,
                                method,
                                expanded_arguments,
                                expanded_count,
                                kwargs,
                                (char const *const *)vv(expression->method_kws),
                                kwcount,
                                expression,
                                true
                        );
                }
                if (
                        result == T2_TYPE_INVALID
                     || t2_type_kind(shadow->universe, result) == T2_TYPE_ERROR
                     || t2_solver_failed(shadow->solver)
                ) {
                        if (!t2_solver_cancel_obligations_since(
                                shadow->solver,
                                argument_scope
                        )) shadow->failed = true;
                }
                t2_solver_commit(shadow->solver, argument_scope);
                invalidate_unstable_refinements(shadow);
                free(expanded_arguments);
                free(arguments);
                free(kwargs);
                break;
        }
        case EXPRESSION_DYN_METHOD_CALL:
        {
                T2Type object = infer_expression(shadow, expression->object);
                (void)constrain_type(
                        shadow,
                        expression->method,
                        infer_expression(shadow, expression->method),
                        t2_primitive(shadow->universe, T2_TYPE_STRING),
                        "dynamic-method-name",
                        "a dynamic method name must be a String"
                );
                for (int i = 0; i < vN(expression->method_args); ++i) {
                        (void)infer_expression(shadow, v__(expression->method_args, i));
                        if (i < vN(expression->mconds)) {
                                (void)infer_expression(shadow, v__(expression->mconds, i));
                        }
                }
                for (int i = 0; i < vN(expression->method_kwargs); ++i) {
                        (void)infer_expression(shadow, v__(expression->method_kwargs, i));
                }
                if (t2_type_kind(shadow->universe, object) == T2_TYPE_ERROR) {
                        result = object;
                } else {
                        defer_node(shadow, TYPES2_DEFER_DYNAMIC_METHOD_NAME, expression, NULL);
                        result = t2_primitive(shadow->universe, T2_TYPE_DYNAMIC);
                        if (expression->maybe) {
                                result = t2_join(
                                        shadow->universe,
                                        result,
                                        t2_primitive(shadow->universe, T2_TYPE_NIL)
                                );
                        }
                }
                invalidate_unstable_refinements(shadow);
                break;
        }
        case EXPRESSION_EQ:
        case EXPRESSION_MAYBE_EQ:
        {
                T2SolverMark assignment = t2_solver_mark(shadow->solver);
                T2Type value = infer_expression(shadow, expression->value);
                bool valid = assign_lvalue(shadow, expression->target, value, false);
                if (
                        !valid
                     && !t2_solver_cancel_obligations_since(
                            shadow->solver,
                            assignment
                        )
                ) shadow->failed = true;
                t2_solver_commit(shadow->solver, assignment);
                result = valid ? value : t2_primitive(shadow->universe, T2_TYPE_ERROR);
                break;
        }
        case EXPRESSION_PLUS_EQ:
        case EXPRESSION_STAR_EQ:
        case EXPRESSION_DIV_EQ:
        case EXPRESSION_MOD_EQ:
        case EXPRESSION_MINUS_EQ:
        case EXPRESSION_AND_EQ:
        case EXPRESSION_OR_EQ:
        case EXPRESSION_XOR_EQ:
        case EXPRESSION_SHL_EQ:
        case EXPRESSION_SHR_EQ:
        {
                T2SolverMark assignment = t2_solver_mark(shadow->solver);
                uint8_t operation = EXPRESSION_PLUS;
                switch (expression->type) {
                case EXPRESSION_STAR_EQ: operation = EXPRESSION_STAR; break;
                case EXPRESSION_DIV_EQ: operation = EXPRESSION_DIV; break;
                case EXPRESSION_MOD_EQ: operation = EXPRESSION_PERCENT; break;
                case EXPRESSION_MINUS_EQ: operation = EXPRESSION_MINUS; break;
                case EXPRESSION_AND_EQ: operation = EXPRESSION_BIT_AND; break;
                case EXPRESSION_OR_EQ: operation = EXPRESSION_BIT_OR; break;
                case EXPRESSION_XOR_EQ: operation = EXPRESSION_XOR; break;
                case EXPRESSION_SHL_EQ: operation = EXPRESSION_SHL; break;
                case EXPRESSION_SHR_EQ: operation = EXPRESSION_SHR; break;
                default: break;
                }
                T2Type combined = infer_binary_pair(
                        shadow,
                        operation,
                        infer_expression(shadow, expression->target),
                        infer_expression(shadow, expression->value),
                        expression,
                        true
                );
                bool valid = assign_lvalue(shadow, expression->target, combined, false);
                if (
                        !valid
                     && !t2_solver_cancel_obligations_since(
                            shadow->solver,
                            assignment
                        )
                ) shadow->failed = true;
                t2_solver_commit(shadow->solver, assignment);
                result = valid ? combined : t2_primitive(shadow->universe, T2_TYPE_ERROR);
                break;
        }
        case EXPRESSION_PREFIX_MINUS:
                result = infer_prefix_minus_type(
                        shadow,
                        infer_expression(shadow, expression->operand),
                        expression,
                        true
                );
                break;
        case EXPRESSION_PREFIX_BANG:
        case EXPRESSION_PREFIX_QUESTION:
                (void)infer_expression(shadow, expression->operand);
                result = t2_primitive(shadow->universe, T2_TYPE_BOOL);
                break;
        case EXPRESSION_PREFIX_HASH:
                result = infer_count_type(
                        shadow,
                        infer_expression(shadow, expression->operand),
                        expression,
                        true
                );
                break;
        case EXPRESSION_ENTER:
        {
                T2Type operand = infer_expression(shadow, expression->operand);
                T2SolverMark mark = t2_solver_mark(shadow->solver);
                T2Type method = infer_member_type(
                        shadow,
                        operand,
                        "__enter__",
                        false,
                        expression,
                        false
                );
                T2Type entered = infer_call_types(
                        shadow,
                        method,
                        NULL,
                        0,
                        NULL,
                        NULL,
                        0,
                        expression,
                        false
                );
                if (
                        entered != T2_TYPE_INVALID
                     && t2_type_kind(shadow->universe, entered) != T2_TYPE_ERROR
                     && !t2_solver_failed(shadow->solver)
                ) {
                        t2_solver_commit(shadow->solver, mark);
                        result = entered;
                } else {
                        /* ENTER deliberately falls back to the original value
                         * when no __enter__ hook exists at runtime. */
                        t2_solver_rollback(shadow->solver, mark);
                        result = operand;
                }
                break;
        }
        case EXPRESSION_PREFIX_AT:
                result = infer_tag_value_type(
                        shadow,
                        infer_expression(shadow, expression->operand),
                        expression
                );
                break;
        case EXPRESSION_PREFIX_INC:
        case EXPRESSION_PREFIX_DEC:
        case EXPRESSION_POSTFIX_INC:
        case EXPRESSION_POSTFIX_DEC:
        {
                T2Type operand = infer_expression(shadow, expression->operand);
                T2Type updated = infer_binary_pair(
                        shadow,
                        expression->type == EXPRESSION_PREFIX_DEC
                             || expression->type == EXPRESSION_POSTFIX_DEC
                            ? EXPRESSION_MINUS
                            : EXPRESSION_PLUS,
                        operand,
                        t2_literal_int(shadow->universe, 1),
                        expression,
                        true
                );
                (void)assign_lvalue(shadow, expression->operand, updated, false);
                result = operand;
                break;
        }
        case EXPRESSION_DOT_DOT:
        case EXPRESSION_DOT_DOT_DOT:
        {
                T2Type integer = t2_primitive(shadow->universe, T2_TYPE_INT);
                bool valid = true;
                if (expression->left != NULL) valid &= constrain_type(
                        shadow,
                        expression->left,
                        infer_expression(shadow, expression->left),
                        integer,
                        "range-endpoint",
                        "range start must be Int"
                );
                if (expression->right != NULL) valid &= constrain_type(
                        shadow,
                        expression->right,
                        infer_expression(shadow, expression->right),
                        integer,
                        "range-endpoint",
                        "range end must be Int"
                );
                int class_id = expression->type == EXPRESSION_DOT_DOT
                             ? CLASS_RANGE
                             : CLASS_INC_RANGE;
                result = valid
                       ? nominal_application(
                               shadow,
                               class_id,
                               expression->type == EXPRESSION_DOT_DOT ? "Range" : "IncRange",
                               NULL,
                               0,
                               expression
                         )
                       : t2_primitive(shadow->universe, T2_TYPE_ERROR);
                break;
        }
        case EXPRESSION_IN:
        case EXPRESSION_NOT_IN:
        {
                T2Type item = infer_expression(shadow, expression->left);
                T2Type container = infer_expression(shadow, expression->right);
                bool valid = check_membership(
                        shadow,
                        item,
                        container,
                        expression,
                        true
                );
                result = valid
                       ? t2_primitive(shadow->universe, T2_TYPE_BOOL)
                       : t2_primitive(shadow->universe, T2_TYPE_ERROR);
                break;
        }
        case EXPRESSION_CAST:
                (void)infer_expression(shadow, expression->left);
                result = lower_type(shadow, expression->right);
                break;
        case EXPRESSION_FUNCTION:
        case EXPRESSION_IMPLICIT_FUNCTION:
        case EXPRESSION_GENERATOR:
        case EXPRESSION_MULTI_FUNCTION:
                result = infer_function_expression(shadow, expression);
                break;
        case EXPRESSION_WITH:
        {
                size_t binding_mark = shadow->binding_count;
                for (int i = 0; i < vN(expression->with.defs); ++i) {
                        (void)infer_statement(shadow, v__(expression->with.defs, i));
                }
                result = infer_statement(shadow, expression->with.block).value;
                for (size_t i = binding_mark; i < shadow->binding_count; ++i) {
                        if (!shadow->bindings[i].persistent) {
                                shadow->bindings[i].active = false;
                        }
                }
                break;
        }
        case EXPRESSION_STATEMENT:
                result = infer_statement(shadow, expression->statement).value;
                break;
        case EXPRESSION_THROW:
                (void)infer_expression(shadow, expression->throw);
                result = t2_primitive(shadow->universe, T2_TYPE_NEVER);
                break;
        case EXPRESSION_YIELD:
        {
                T2Type yielded = t2_primitive(shadow->universe, T2_TYPE_NIL);
                bool delegated = false;
                if (vN(expression->es) == 1) {
                        Expr const *item = v__(expression->es, 0);
                        delegated = item != NULL
                                 && item->type == EXPRESSION_SPREAD;
                        if (delegated) {
                                T2Type source = infer_expression(shadow, item->value);
                                yielded = iterated_type(shadow, source, item);
                        } else {
                                yielded = infer_expression(shadow, item);
                        }
                } else if (vN(expression->es) > 1) {
                        size_t count = (size_t)vN(expression->es);
                        T2Type *items = malloc(count * sizeof *items);
                        if (items == NULL) {
                                shadow->failed = true;
                                break;
                        }
                        for (size_t i = 0; i < count; ++i) {
                                items[i] = infer_expression(
                                        shadow,
                                        v__(expression->es, (int)i)
                                );
                        }
                        yielded = t2_tuple(shadow->universe, items, count);
                        free(items);
                }
                if (shadow->function_count != 0) {
                        size_t frame_index = shadow->function_count - 1;
                        Types2FunctionFrame *frame = &shadow->functions[frame_index];
                        promote_generator_frame(shadow, frame, expression);
                        T2Type yields = frame->yields;
                        T2Type sends = frame->sends;
                        (void)constrain_type(
                                shadow,
                                expression,
                                yielded,
                                yields,
                                "yield-type",
                                "yielded value has the wrong generator element type"
                        );
                        invalidate_unstable_refinements(shadow);
                        result = delegated
                               ? t2_primitive(shadow->universe, T2_TYPE_NIL)
                               : sends;
                } else {
                        add_diagnostic(
                                shadow,
                                expression,
                                TYPES2_DIAGNOSTIC_ERROR,
                                "yield-context",
                                yielded,
                                T2_TYPE_INVALID,
                                "yield is only valid inside a generator"
                        );
                        result = t2_primitive(shadow->universe, T2_TYPE_ERROR);
                }
                break;
        }
        case EXPRESSION_DEFINED:
                result = t2_primitive(shadow->universe, T2_TYPE_BOOL);
                break;
        case EXPRESSION_IFDEF:
                if (expression->symbol != NULL) {
                        Types2Binding *binding = ensure_binding(shadow, expression->symbol);
                        if (binding != NULL && binding->initialized) {
                                (void)instantiate_binding(shadow, binding, expression);
                        }
                }
                defer_node(shadow, TYPES2_DEFER_IFDEF, expression, expression->identifier);
                result = t2_primitive(shadow->universe, T2_TYPE_DYNAMIC);
                break;
        case EXPRESSION_TEMPLATE:
                for (int i = 0; i < vN(expression->template.holes); ++i) {
                        Expr const *hole = v__(expression->template.holes, i);
                        if (i < vN(expression->template.ctxs)
                         && v__(expression->template.ctxs, i) == CTX_TYPE) {
                                (void)lower_type(shadow, hole);
                        } else {
                                (void)infer_expression(shadow, hole);
                        }
                }
                for (int i = 0; i < vN(expression->template.exprs); ++i) {
                        (void)infer_expression(shadow, v__(expression->template.exprs, i));
                }
                defer_node(shadow, TYPES2_DEFER_TEMPLATE, expression, NULL);
                result = t2_primitive(shadow->universe, T2_TYPE_DYNAMIC);
                break;
        case EXPRESSION_TEMPLATE_XHOLE:
                result = infer_expression(shadow, expression->hole.expr);
                break;
        case EXPRESSION_TEMPLATE_HOLE:
        case EXPRESSION_TEMPLATE_VHOLE:
        case EXPRESSION_TEMPLATE_THOLE:
                defer_node(shadow, TYPES2_DEFER_TEMPLATE_HOLE, expression, NULL);
                result = t2_primitive(shadow->universe, T2_TYPE_DYNAMIC);
                break;
        case EXPRESSION_PACK_UNION:
        case EXPRESSION_PACK_INTERSECT:
                (void)infer_expression(shadow, expression->operand);
                defer_node(shadow, TYPES2_DEFER_PACK_FOLD, expression, NULL);
                result = t2_primitive(shadow->universe, T2_TYPE_DYNAMIC);
                break;
        case EXPRESSION_TYPE_OF:
        {
                T2Type instance = infer_expression(shadow, expression->operand);
                T2Type dynamic = t2_primitive(
                        shadow->universe,
                        T2_TYPE_DYNAMIC
                );
                result = t2_type_value(
                        shadow->universe,
                        instance,
                        dynamic
                );
                break;
        }
        case EXPRESSION_TYPE:
        {
                T2Type instance = lower_type(shadow, expression->constraint);
                T2Type dynamic = t2_primitive(
                        shadow->universe,
                        T2_TYPE_DYNAMIC
                );
                result = t2_type_value(
                        shadow->universe,
                        instance,
                        dynamic
                );
                break;
        }
        case EXPRESSION_TYPE_UNION:
        {
                /* A union syntax node can survive macro expansion in an
                 * expression position.  It denotes the corresponding native
                 * type value here just as an explicit `type` expression does;
                 * it is not a runtime value union to be inferred arm by arm. */
                T2Type instance = lower_type(shadow, expression);
                T2Type dynamic = t2_primitive(
                        shadow->universe,
                        T2_TYPE_DYNAMIC
                );
                result = t2_type_value(
                        shadow->universe,
                        instance,
                        dynamic
                );
                break;
        }
        case EXPRESSION_RESOURCE_BINDING:
        case EXPRESSION_MATCH_NOT_NIL:
        case EXPRESSION_MATCH_REST:
        {
                Types2Binding *binding = ensure_binding(shadow, expression->symbol);
                if (binding == NULL) {
                        result = t2_primitive(shadow->universe, T2_TYPE_ERROR);
                } else {
                        if (!binding->initialized) {
                                binding->type = t2_solver_new_meta(
                                        shadow->solver,
                                        T2_VARIABLE_FLEXIBLE,
                                        shadow->level,
                                        "pattern binding"
                                );
                                binding->initialized = true;
                        }
                        result = instantiate_binding(shadow, binding, expression);
                }
                break;
        }
        case EXPRESSION_MUST_EQUAL:
        {
                Types2Binding *binding = ensure_binding(shadow, expression->symbol);
                result = binding == NULL || !binding->initialized
                       ? t2_primitive(shadow->universe, T2_TYPE_ERROR)
                       : instantiate_binding(shadow, binding, expression);
                break;
        }
        case EXPRESSION_RESOLVED:
                result = infer_expression(shadow, expression->value);
                break;
        case EXPRESSION_MODULE:
        case EXPRESSION_NAMESPACE:
                result = nominal_application(
                        shadow,
                        CLASS_MODULE,
                        "Module",
                        NULL,
                        0,
                        expression
                );
                break;
        case EXPRESSION_TRACE:
        case EXPRESSION_CTX_INFO:
                defer_node(shadow, TYPES2_DEFER_RUNTIME_CONTEXT, expression, NULL);
                result = t2_primitive(shadow->universe, T2_TYPE_DYNAMIC);
                break;
        case EXPRESSION_VALUE:
                defer_node(shadow, TYPES2_DEFER_RUNTIME_VALUE, expression, NULL);
                result = t2_primitive(shadow->universe, T2_TYPE_DYNAMIC);
                break;
        case EXPRESSION_ERROR:
                add_diagnostic(
                        shadow,
                        expression,
                        TYPES2_DIAGNOSTIC_ERROR,
                        "source-error",
                        T2_TYPE_INVALID,
                        T2_TYPE_INVALID,
                        "%s",
                        expression->string == NULL ? "invalid source expression" : expression->string
                );
                result = t2_primitive(shadow->universe, T2_TYPE_ERROR);
                break;
        case EXPRESSION_MACRO_INVOCATION:
        case EXPRESSION_FUN_MACRO_INVOCATION:
        case EXPRESSION_PLACEHOLDER:
        case EXPRESSION_TICK:
        case EXPRESSION_PTR:
        case EXPRESSION_KEEP_LOC:
        case EXPRESSION_MAX_TYPE:
                add_diagnostic(
                        shadow,
                        expression,
                        TYPES2_DIAGNOSTIC_ERROR,
                        "unexpanded-expression",
                        T2_TYPE_INVALID,
                        T2_TYPE_INVALID,
                        "internal expression `%s` reached types2 before expansion completed",
                        construct_name(expression->type)
                );
                result = t2_primitive(shadow->universe, T2_TYPE_ERROR);
                break;
        case EXPRESSION_UNSAFE:
        case EXPRESSION_EVAL:
                if (expression->operand != NULL) (void)infer_expression(shadow, expression->operand);
                defer_node(shadow, TYPES2_DEFER_UNSAFE_EVAL, expression, NULL);
                result = t2_primitive(shadow->universe, T2_TYPE_DYNAMIC);
                break;
        default:
                shadow->unsupported_nodes += 1;
                shadow->unsupported_constructs[expression->type] += 1;
                result = t2_primitive(shadow->universe, T2_TYPE_DYNAMIC);
                break;
        }

        if (result == T2_TYPE_INVALID && !shadow->failed) {
                result = t2_primitive(shadow->universe, T2_TYPE_ERROR);
        }
        set_node_type(shadow, expression, result);
        return result;
}

static Types2Flow
flow_fallthrough(Types2Shadow *shadow, T2Type value)
{
        return (Types2Flow) {
                .outcomes = TYPES2_FLOW_FALLS_THROUGH,
                .value = value == T2_TYPE_INVALID
                       ? t2_primitive(shadow->universe, T2_TYPE_NIL)
                       : value,
                .returns = t2_primitive(shadow->universe, T2_TYPE_NEVER)
        };
}

static Types2Flow
flow_join(Types2Shadow *shadow, Types2Flow left, Types2Flow right)
{
        T2Type never = t2_primitive(shadow->universe, T2_TYPE_NEVER);
        return (Types2Flow) {
                .outcomes = left.outcomes | right.outcomes,
                .value = t2_join(
                        shadow->universe,
                        left.value == T2_TYPE_INVALID ? never : left.value,
                        right.value == T2_TYPE_INVALID ? never : right.value
                ),
                .returns = t2_join(
                        shadow->universe,
                        left.returns == T2_TYPE_INVALID ? never : left.returns,
                        right.returns == T2_TYPE_INVALID ? never : right.returns
                )
        };
}

static bool
expression_is_expansive(Expr const *source)
{
        Expr const *expression = source == NULL ? NULL : unfurl(source);
        if (expression == NULL) return false;
        switch (expression->type) {
        case EXPRESSION_FUNCTION:
        case EXPRESSION_IMPLICIT_FUNCTION:
        case EXPRESSION_GENERATOR:
        case EXPRESSION_MULTI_FUNCTION:
        case EXPRESSION_INTEGER:
        case EXPRESSION_BOOLEAN:
        case EXPRESSION_STRING:
        case EXPRESSION_REAL:
        case EXPRESSION_NIL:
        case EXPRESSION_NONE:
        case EXPRESSION_IDENTIFIER:
                return false;
        case EXPRESSION_TUPLE:
        case EXPRESSION_LIST:
                for (int i = 0; i < vN(expression->es); ++i) {
                        if (expression_is_expansive(v__(expression->es, i))) return true;
                }
                return false;
        default:
                return true;
        }
}

static bool
is_named_binding_target(Expr const *target)
{
        return target != NULL
            && target->symbol != NULL
            && (
                       target->type == EXPRESSION_IDENTIFIER
                    || target->type == EXPRESSION_RESOURCE_BINDING
               );
}

static T2Type *
environment_types(
        Types2Shadow *shadow,
        Symbol const *excluded,
        size_t *count
)
{
        *count = 0;
        if (shadow->binding_count == 0) return NULL;
        T2Type *environment = malloc(shadow->binding_count * sizeof *environment);
        if (environment == NULL) {
                shadow->failed = true;
                return NULL;
        }
        for (size_t i = 0; i < shadow->binding_count; ++i) {
                Types2Binding const *binding = &shadow->bindings[i];
                if (
                        binding->symbol == excluded
                     || !binding->active
                     || !binding->initialized
                     || binding->type == T2_TYPE_INVALID
                ) continue;
                environment[(*count)++] = binding->type;
        }
        return environment;
}

static bool
generalize_binding(
        Types2Shadow *shadow,
        Types2Binding *binding,
        T2Type type,
        T2Type const *environment,
        size_t environment_count,
        uint32_t binding_level,
        bool expansive,
        T2SolverMark scope
)
{
        if (binding == NULL || type == T2_TYPE_INVALID) {
                t2_solver_commit(shadow->solver, scope);
                return false;
        }
        if (shadow->failed) {
                t2_solver_commit(shadow->solver, scope);
                return false;
        }
        Symbol const *symbol = binding->symbol;
        T2Scheme *scheme = t2_solver_generalize_scoped(
                shadow->solver,
                type,
                environment,
                environment_count,
                binding_level,
                expansive,
                scope
        );
        t2_solver_commit(shadow->solver, scope);
        if (scheme == NULL) {
                if (!t2_solver_failed(shadow->solver)) shadow->failed = true;
                return false;
        }
        binding = find_binding(shadow, symbol);
        if (binding == NULL) {
                t2_scheme_free(scheme);
                shadow->failed = true;
                return false;
        }
        t2_scheme_free(binding->scheme);
        binding->scheme = scheme;
        binding->type = type;
        binding->initialized = true;
        return true;
}

static bool
is_callable_set(Types2Shadow *shadow, T2Type type)
{
        T2TypeKind kind = t2_type_kind(shadow->universe, type);
        return kind == T2_TYPE_FUNCTION || kind == T2_TYPE_OVERLOAD;
}

static bool
push_function_frame(Types2Shadow *shadow, Types2FunctionFrame frame)
{
        if (!shadow_reserve(
                shadow,
                (void **)&shadow->functions,
                &shadow->function_capacity,
                shadow->function_count + 1,
                sizeof *shadow->functions
        )) return false;
        shadow->functions[shadow->function_count++] = frame;
        return true;
}

static T2Type
function_return_values(Types2Shadow *shadow, ExprVec const *returns)
{
        size_t count = (size_t)vN(*returns);
        if (count == 0) return t2_primitive(shadow->universe, T2_TYPE_NIL);
        if (count == 1) return infer_expression(shadow, v__(*returns, 0));
        T2Type *items = malloc(count * sizeof *items);
        if (items == NULL) {
                shadow->failed = true;
                return T2_TYPE_INVALID;
        }
        for (size_t i = 0; i < count; ++i) {
                items[i] = infer_expression(shadow, v__(*returns, (int)i));
        }
        T2Type result = t2_tuple(shadow->universe, items, count);
        free(items);
        return result;
}

static T2Type
iterated_type_x(
        Types2Shadow *shadow,
        T2Type source,
        Expr const *site,
        bool diagnose,
        unsigned depth
)
{
        if (depth > 64) {
                if (diagnose) add_diagnostic(
                        shadow,
                        site,
                        TYPES2_DIAGNOSTIC_ERROR,
                        "iteration-complexity",
                        source,
                        T2_TYPE_INVALID,
                        "iteration protocol is recursively defined"
                );
                return t2_primitive(shadow->universe, T2_TYPE_ERROR);
        }
        source = resolved_operation_type(
                shadow,
                source,
                T2_PREFER_LOWER_BOUND
        );
        T2TypeKind kind = t2_type_kind(shadow->universe, source);
        if (kind == T2_TYPE_DYNAMIC || kind == T2_TYPE_ERROR) return source;
        if (kind == T2_TYPE_UNION) {
                T2SolverMark coverage = t2_solver_mark(shadow->solver);
                T2Type result = t2_primitive(shadow->universe, T2_TYPE_NEVER);
                for (size_t i = 0; i < t2_type_arity(shadow->universe, source); ++i) {
                        T2Type item = iterated_type_x(
                                shadow,
                                t2_type_child(shadow->universe, source, i),
                                site,
                                false,
                                depth + 1
                        );
                        if (t2_type_kind(shadow->universe, item) == T2_TYPE_ERROR) {
                                t2_solver_rollback(shadow->solver, coverage);
                                if (diagnose) add_diagnostic(
                                        shadow,
                                        site,
                                        TYPES2_DIAGNOSTIC_ERROR,
                                        "union-iteration-coverage",
                                        source,
                                        T2_TYPE_INVALID,
                                        "every reachable union arm must be iterable"
                                );
                                return item;
                        }
                        result = t2_join(shadow->universe, result, item);
                }
                t2_solver_commit(shadow->solver, coverage);
                return result;
        }
        Types2Nominal *nominal = nominal_from_type(shadow, source);
        if (nominal != NULL) {
                if (
                        nominal->class_id == CLASS_ARRAY
                     || nominal->class_id == CLASS_ITERABLE
                     || nominal->class_id == CLASS_ITER
                ) return t2_type_child(shadow->universe, source, 0);
                if (nominal->class_id == CLASS_DICT) {
                        return t2_tuple(
                                shadow->universe,
                                (T2Type[]) {
                                        t2_type_child(shadow->universe, source, 0),
                                        t2_type_child(shadow->universe, source, 1)
                                },
                                2
                        );
                }
                if (nominal->class_id == CLASS_GENERATOR) {
                        T2Type send = t2_type_child(shadow->universe, source, 1);
                        if (t2_subtype(
                                shadow->universe,
                                t2_primitive(shadow->universe, T2_TYPE_NIL),
                                send
                        ) == T2_RELATION_NO) {
                                if (diagnose) add_diagnostic(
                                        shadow,
                                        site,
                                        TYPES2_DIAGNOSTIC_ERROR,
                                        "generator-not-iterable",
                                        source,
                                        T2_TYPE_INVALID,
                                        "a generator requiring a non-nil send value cannot be used as an iterator"
                                );
                                return t2_primitive(shadow->universe, T2_TYPE_ERROR);
                        }
                        return t2_type_child(shadow->universe, source, 0);
                }
        }
        if (kind == T2_TYPE_STRING || kind == T2_TYPE_LITERAL_STRING) {
                return t2_primitive(shadow->universe, T2_TYPE_STRING);
        }
        if (kind == T2_TYPE_TUPLE) {
                T2Type result = t2_primitive(shadow->universe, T2_TYPE_NEVER);
                for (size_t i = 0; i < t2_type_arity(shadow->universe, source); ++i) {
                        result = t2_join(
                                shadow->universe,
                                result,
                                t2_type_child(shadow->universe, source, i)
                        );
                }
                return result;
        }
        if (kind == T2_TYPE_VARIADIC_TUPLE) {
                size_t prefix = t2_type_arity(shadow->universe, source) - 1;
                T2Type result = t2_primitive(shadow->universe, T2_TYPE_NEVER);
                for (size_t i = 0; i < prefix; ++i) {
                        result = t2_join(
                                shadow->universe,
                                result,
                                t2_type_child(shadow->universe, source, i)
                        );
                }
                return t2_join(
                        shadow->universe,
                        result,
                        t2_pack_fold_union(
                                shadow->universe,
                                t2_type_child(shadow->universe, source, prefix)
                        )
                );
        }
        if (kind == T2_TYPE_NOMINAL) {
                T2SolverMark protocol = t2_solver_mark(shadow->solver);
                T2Type method = infer_method_type(
                        shadow,
                        source,
                        "__iter__",
                        false,
                        site,
                        false
                );
                T2Type iterator = infer_call_types(
                        shadow,
                        method,
                        NULL,
                        0,
                        NULL,
                        NULL,
                        0,
                        site,
                        false
                );
                if (
                        iterator != T2_TYPE_INVALID
                     && iterator != source
                     && t2_type_kind(shadow->universe, iterator) != T2_TYPE_ERROR
                     && !t2_solver_failed(shadow->solver)
                ) {
                        T2Type element = iterated_type_x(
                                shadow,
                                iterator,
                                site,
                                false,
                                depth + 1
                        );
                        if (
                                t2_type_kind(shadow->universe, element)
                                != T2_TYPE_ERROR
                             && !t2_solver_failed(shadow->solver)
                        ) {
                                t2_solver_commit(shadow->solver, protocol);
                                return element;
                        }
                }
                t2_solver_rollback(shadow->solver, protocol);
        }
        if (kind == T2_TYPE_NOMINAL || kind == T2_TYPE_META) {
                T2SolverMark mark = t2_solver_mark(shadow->solver);
                T2Type element = t2_solver_new_meta(
                        shadow->solver,
                        T2_VARIABLE_FLEXIBLE,
                        shadow->level,
                        "iterable element"
                );
                T2Type iterable = nominal_application(
                        shadow,
                        CLASS_ITERABLE,
                        "Iterable",
                        &element,
                        1,
                        site
                );
                T2Relation relation = t2_solver_constrain_subtype(
                        shadow->solver,
                        source,
                        iterable,
                        "iteration requires Iterable[element]"
                );
                if (relation != T2_RELATION_NO && !t2_solver_failed(shadow->solver)) {
                        t2_solver_commit(shadow->solver, mark);
                        return element;
                }
                t2_solver_rollback(shadow->solver, mark);
        }
        if (diagnose) add_diagnostic(
                shadow,
                site,
                TYPES2_DIAGNOSTIC_ERROR,
                "not-iterable",
                source,
                T2_TYPE_INVALID,
                "value does not expose an iterable element type"
        );
        return t2_primitive(shadow->universe, T2_TYPE_ERROR);
}

static T2Type
iterated_type(Types2Shadow *shadow, T2Type source, Expr const *site)
{
        return iterated_type_x(shadow, source, site, true, 0);
}

static void
bind_capture(Types2Shadow *shadow, Symbol const *symbol)
{
        if (symbol == NULL) return;
        Types2Binding *binding = ensure_binding(shadow, symbol);
        if (binding == NULL) return;
        binding->type = t2_primitive(shadow->universe, T2_TYPE_STRING);
        binding->refinement = T2_TYPE_INVALID;
        binding->mutable = false;
        binding->initialized = true;
        binding->forward = false;
}

static void
bind_regex_captures(Types2Shadow *shadow, Expr const *pattern)
{
        Symbol const *match = pattern->match_symbol;
        Regex const *regex = pattern->regex;
        bind_capture(shadow, match);
        if (
                match == NULL
             || match->scope == NULL
             || regex == NULL
             || shadow->ty == NULL
        ) return;
        for (uint32_t i = 1; i <= regex->ncap; ++i) {
                char name[16];
                snprintf(name, sizeof name, "$%" PRIu32, i);
                bind_capture(
                        shadow,
                        scope_local_lookup(shadow->ty, match->scope, name)
                );
        }
        uint32_t named = 0;
        uint32_t entry_size = 0;
        PCRE2_SPTR table = NULL;
        if (
                regex->pcre2 == NULL
             || pcre2_pattern_info(regex->pcre2, PCRE2_INFO_NAMECOUNT, &named) != 0
             || pcre2_pattern_info(regex->pcre2, PCRE2_INFO_NAMEENTRYSIZE, &entry_size) != 0
             || pcre2_pattern_info(regex->pcre2, PCRE2_INFO_NAMETABLE, &table) != 0
        ) return;
        for (uint32_t i = 0; i < named; ++i) {
                char const *entry = (char const *)table + (size_t)i * entry_size + 2;
                bind_capture(
                        shadow,
                        scope_local_lookup(shadow->ty, match->scope, entry)
                );
        }
}

static bool
pattern_types_overlap(Types2Shadow *shadow, T2Type left, T2Type right)
{
        T2TypeKind left_kind = t2_type_kind(shadow->universe, left);
        T2TypeKind right_kind = t2_type_kind(shadow->universe, right);
        if (
                left_kind == T2_TYPE_DYNAMIC
             || left_kind == T2_TYPE_UNKNOWN
             || left_kind == T2_TYPE_ANY
             || left_kind == T2_TYPE_META
             || right_kind == T2_TYPE_DYNAMIC
             || right_kind == T2_TYPE_UNKNOWN
             || right_kind == T2_TYPE_ANY
             || right_kind == T2_TYPE_META
        ) return true;
        return t2_type_kind(
                shadow->universe,
                t2_meet(shadow->universe, left, right)
        ) != T2_TYPE_NEVER;
}

static bool
nominal_is_tag(Types2Shadow *shadow, Types2Nominal const *nominal)
{
        (void)shadow;
        return nominal != NULL && nominal->tag_id > 0;
}

static T2Type
tag_pattern_payload(
        Types2Shadow *shadow,
        T2Type subject,
        int wanted_tag,
        bool any_tag,
        bool *reachable
)
{
        *reachable = false;
        T2TypeKind kind = t2_type_kind(shadow->universe, subject);
        if (
                kind == T2_TYPE_DYNAMIC
             || kind == T2_TYPE_UNKNOWN
             || kind == T2_TYPE_ANY
             || kind == T2_TYPE_OBJECT
             || kind == T2_TYPE_META
        ) {
                *reachable = true;
                if (kind == T2_TYPE_DYNAMIC || kind == T2_TYPE_META) {
                        return t2_primitive(
                                shadow->universe,
                                T2_TYPE_DYNAMIC
                        );
                }
                return t2_solver_new_meta(
                        shadow->solver,
                        T2_VARIABLE_FLEXIBLE,
                        shadow->level,
                        "matched tag payload"
                );
        }
        if (kind == T2_TYPE_UNION) {
                T2Type result = t2_primitive(shadow->universe, T2_TYPE_NEVER);
                for (size_t i = 0; i < t2_type_arity(shadow->universe, subject); ++i) {
                        bool arm_reachable = false;
                        T2Type payload = tag_pattern_payload(
                                shadow,
                                t2_type_child(shadow->universe, subject, i),
                                wanted_tag,
                                any_tag,
                                &arm_reachable
                        );
                        if (arm_reachable) {
                                *reachable = true;
                                result = t2_join(shadow->universe, result, payload);
                        }
                }
                return result;
        }
        if (kind != T2_TYPE_NOMINAL) {
                return t2_primitive(shadow->universe, T2_TYPE_NEVER);
        }
        Types2Nominal *nominal = nominal_from_type(shadow, subject);
        if (
                nominal == NULL
             || (!any_tag && nominal->tag_id != wanted_tag)
             || (any_tag && !nominal_is_tag(shadow, nominal))
        ) return t2_primitive(shadow->universe, T2_TYPE_NEVER);
        *reachable = true;
        return t2_type_arity(shadow->universe, subject) == 0
             ? t2_primitive(shadow->universe, T2_TYPE_NEVER)
             : t2_type_child(shadow->universe, subject, 0);
}

static bool
tuple_pattern_items(
        Types2Shadow *shadow,
        T2Type subject,
        T2Type *items,
        size_t count
)
{
        subject = resolved_operation_type(
                shadow,
                subject,
                T2_PREFER_LOWER_BOUND
        );
        /* Call-local pack constraints can turn a variadic tuple into an exact
         * tuple.  Rebuild the composite after solving the pack before deciding
         * arity; looking only through the outer constructor leaves a solved
         * PackMeta hidden in the tail and spuriously rejects destructuring. */
        T2Type zonked = t2_solver_zonk(
                shadow->solver,
                subject,
                T2_PREFER_LOWER_BOUND
        );
        if (zonked != T2_TYPE_INVALID) subject = zonked;
        T2TypeKind kind = t2_type_kind(shadow->universe, subject);
        if (kind == T2_TYPE_UNION) {
                bool reachable = false;
                for (size_t i = 0; i < t2_type_arity(shadow->universe, subject); ++i) {
                        reachable |= tuple_pattern_items(
                                shadow,
                                t2_type_child(shadow->universe, subject, i),
                                items,
                                count
                        );
                }
                return reachable;
        }
        if (kind == T2_TYPE_TUPLE) {
                if (t2_type_arity(shadow->universe, subject) != count) return false;
                for (size_t i = 0; i < count; ++i) {
                        items[i] = t2_join(
                                shadow->universe,
                                items[i],
                                t2_type_child(shadow->universe, subject, i)
                        );
                }
                return true;
        }
        if (kind == T2_TYPE_META || kind == T2_TYPE_VARIABLE) {
                if (shadow->refutable_pattern_depth != 0) {
                        /* A refutable pattern does not prove that an open
                         * subject has this tuple shape.  Fresh item metas here
                         * are therefore disconnected from the subject: if the
                         * enclosing callback is later committed to Dynamic,
                         * member/subscript predicates on those items can never
                         * wake.  The payload of a successful runtime match is
                         * gradual until a concrete subject shape is known. */
                        T2Type dynamic = t2_primitive(
                                shadow->universe,
                                T2_TYPE_DYNAMIC
                        );
                        for (size_t i = 0; i < count; ++i) {
                                items[i] = t2_join(
                                        shadow->universe,
                                        items[i],
                                        dynamic
                                );
                        }
                        return true;
                }
                T2SolverMark mark = t2_solver_mark(shadow->solver);
                T2Type *shape_items = count == 0
                                         ? NULL
                                         : malloc(count * sizeof *shape_items);
                if (count != 0 && shape_items == NULL) {
                        shadow->failed = true;
                        t2_solver_rollback(shadow->solver, mark);
                        return false;
                }
                for (size_t i = 0; i < count; ++i) {
                        shape_items[i] = t2_solver_new_meta(
                                shadow->solver,
                                T2_VARIABLE_FLEXIBLE,
                                shadow->level,
                                "tuple pattern item"
                        );
                }
                T2Type shape = t2_tuple(shadow->universe, shape_items, count);
                T2Relation relation = t2_solver_constrain_subtype(
                        shadow->solver,
                        subject,
                        shape,
                        "tuple pattern shape"
                );
                if (relation == T2_RELATION_NO || t2_solver_failed(shadow->solver)) {
                        free(shape_items);
                        t2_solver_rollback(shadow->solver, mark);
                        return false;
                }
                for (size_t i = 0; i < count; ++i) {
                        items[i] = t2_join(
                                shadow->universe,
                                items[i],
                                shape_items[i]
                        );
                }
                free(shape_items);
                t2_solver_commit(shadow->solver, mark);
                return true;
        }
        if (
                kind == T2_TYPE_DYNAMIC
             || kind == T2_TYPE_UNKNOWN
             || kind == T2_TYPE_ANY
             || kind == T2_TYPE_ERROR
        ) {
                for (size_t i = 0; i < count; ++i) {
                        T2Type item = kind == T2_TYPE_DYNAMIC || kind == T2_TYPE_ERROR
                                    ? t2_primitive(
                                            shadow->universe,
                                            T2_TYPE_DYNAMIC
                                      )
                                    : t2_solver_new_meta(
                                            shadow->solver,
                                            T2_VARIABLE_FLEXIBLE,
                                            shadow->level,
                                            "tuple pattern item"
                                      );
                        items[i] = t2_join(shadow->universe, items[i], item);
                }
                return true;
        }
        return false;
}

static bool
nominal_pattern_arguments_x(
        Types2Shadow *shadow,
        T2Type subject,
        Types2Nominal const *wanted,
        T2Type *arguments,
        size_t arity,
        char const *description,
        unsigned depth
)
{
        if (wanted == NULL || depth >= 64) return false;
        subject = resolved_type_head(
                shadow,
                subject,
                T2_PREFER_LOWER_BOUND
        );
        T2TypeKind kind = t2_type_kind(shadow->universe, subject);
        if (kind == T2_TYPE_UNION || kind == T2_TYPE_INTERSECTION) {
                bool reachable = false;
                for (size_t i = 0; i < t2_type_arity(shadow->universe, subject); ++i) {
                        reachable |= nominal_pattern_arguments_x(
                                shadow,
                                t2_type_child(shadow->universe, subject, i),
                                wanted,
                                arguments,
                                arity,
                                description,
                                depth + 1
                        );
                }
                return reachable;
        }
        if (
                kind == T2_TYPE_DYNAMIC
             || kind == T2_TYPE_UNKNOWN
             || kind == T2_TYPE_ANY
             || kind == T2_TYPE_OBJECT
             || kind == T2_TYPE_ERROR
             || kind == T2_TYPE_META
             || kind == T2_TYPE_VARIABLE
        ) {
                for (size_t i = 0; i < arity; ++i) {
                        T2Type argument = kind == T2_TYPE_DYNAMIC
                                       || kind == T2_TYPE_ERROR
                                        ? t2_primitive(
                                                shadow->universe,
                                                T2_TYPE_DYNAMIC
                                          )
                                        : t2_solver_new_meta(
                                                shadow->solver,
                                                T2_VARIABLE_FLEXIBLE,
                                                shadow->level,
                                                description
                                          );
                        arguments[i] = t2_join(
                                shadow->universe,
                                arguments[i],
                                argument
                        );
                }
                if (
                        kind == T2_TYPE_META
                     && shadow->refutable_pattern_depth == 0
                ) {
                        T2Type shape = t2_nominal(
                                shadow->universe,
                                wanted->symbol,
                                arguments,
                                arity
                        );
                        if (
                                shape == T2_TYPE_INVALID
                             || t2_solver_constrain_subtype(
                                        shadow->solver,
                                        subject,
                                        shape,
                                        description
                                ) == T2_RELATION_NO
                             || t2_solver_failed(shadow->solver)
                        ) return false;
                }
                return true;
        }
        if (kind != T2_TYPE_NOMINAL) return false;

        T2Type projected = t2_nominal_project(
                shadow->universe,
                subject,
                wanted->symbol
        );
        if (
                projected == T2_TYPE_INVALID
             || t2_type_arity(shadow->universe, projected) != arity
        ) return false;
        for (size_t i = 0; i < arity; ++i) {
                arguments[i] = t2_join(
                        shadow->universe,
                        arguments[i],
                        t2_type_child(shadow->universe, projected, i)
                );
        }
        return true;
}

static bool
nominal_pattern_arguments(
        Types2Shadow *shadow,
        T2Type subject,
        int class_id,
        char const *name,
        T2Type *arguments,
        size_t arity,
        char const *description
)
{
        Types2Nominal *wanted = ensure_nominal(
                shadow,
                class_id,
                name,
                arity
        );
        if (wanted == NULL) return false;
        T2Type never = t2_primitive(shadow->universe, T2_TYPE_NEVER);
        for (size_t i = 0; i < arity; ++i) arguments[i] = never;
        return nominal_pattern_arguments_x(
                shadow,
                subject,
                wanted,
                arguments,
                arity,
                description,
                0
        );
}

static T2Type
record_pattern_field_type(
        Types2Shadow *shadow,
        T2Type subject,
        char const *name,
        bool optional,
        bool *reachable,
        unsigned depth
)
{
        *reachable = false;
        if (depth >= 64) return T2_TYPE_INVALID;
        subject = resolved_operation_type(
                shadow,
                subject,
                T2_PREFER_LOWER_BOUND
        );
        T2TypeKind kind = t2_type_kind(shadow->universe, subject);
        T2Type nil = t2_primitive(shadow->universe, T2_TYPE_NIL);
        if (kind == T2_TYPE_UNION || kind == T2_TYPE_INTERSECTION) {
                T2Type result = t2_primitive(
                        shadow->universe,
                        T2_TYPE_NEVER
                );
                bool any = false;
                for (size_t i = 0; i < t2_type_arity(shadow->universe, subject); ++i) {
                        bool arm_reachable = false;
                        T2Type arm = record_pattern_field_type(
                                shadow,
                                t2_type_child(shadow->universe, subject, i),
                                name,
                                optional,
                                &arm_reachable,
                                depth + 1
                        );
                        if (!arm_reachable) continue;
                        any = true;
                        result = t2_join(shadow->universe, result, arm);
                }
                *reachable = any;
                return result;
        }
        if (kind == T2_TYPE_RECORD) {
                T2Presence presence = T2_PRESENCE_UNKNOWN;
                T2Type field = t2_record_field_type(
                        shadow->universe,
                        subject,
                        name,
                        &presence,
                        NULL
                );
                if (field != T2_TYPE_INVALID) {
                        if (presence == T2_PRESENCE_ABSENT) {
                                *reachable = optional;
                                return nil;
                        }
                        *reachable = true;
                        if (
                                optional
                             || presence != T2_PRESENCE_REQUIRED
                        ) field = t2_join(shadow->universe, field, nil);
                        return field;
                }
                T2Type tail = t2_record_row_tail(shadow->universe, subject);
                T2TypeKind tail_kind = t2_type_kind(shadow->universe, tail);
                if (tail_kind != T2_TYPE_ROW_EMPTY) {
                        *reachable = true;
                        T2Type unknown = t2_solver_new_meta(
                                shadow->solver,
                                T2_VARIABLE_FLEXIBLE,
                                shadow->level,
                                "record pattern row field"
                        );
                        return optional
                             ? t2_join(shadow->universe, unknown, nil)
                             : unknown;
                }
                *reachable = optional;
                return nil;
        }
        if (
                kind == T2_TYPE_DYNAMIC
             || kind == T2_TYPE_ERROR
        ) {
                *reachable = true;
                return t2_primitive(shadow->universe, T2_TYPE_DYNAMIC);
        }
        if (
                kind == T2_TYPE_UNKNOWN
             || kind == T2_TYPE_ANY
             || kind == T2_TYPE_OBJECT
             || kind == T2_TYPE_META
             || kind == T2_TYPE_VARIABLE
        ) {
                *reachable = true;
                T2Type field = t2_solver_new_meta(
                        shadow->solver,
                        T2_VARIABLE_FLEXIBLE,
                        shadow->level,
                        "record pattern field"
                );
                return optional
                     ? t2_join(shadow->universe, field, nil)
                     : field;
        }
        return T2_TYPE_INVALID;
}

static bool
record_pattern_items(
        Types2Shadow *shadow,
        Expr const *pattern,
        T2Type subject,
        T2Type *items
)
{
        T2TypeKind kind = t2_type_kind(shadow->universe, subject);
        size_t count = (size_t)vN(pattern->es);
        if (kind == T2_TYPE_UNION) {
                bool reachable = false;
                if (count > SIZE_MAX / sizeof(T2Type)) return false;
                T2Type *arm_items = count == 0
                                  ? NULL
                                  : malloc(count * sizeof *arm_items);
                if (count != 0 && arm_items == NULL) {
                        shadow->failed = true;
                        return false;
                }
                T2Type never = t2_primitive(shadow->universe, T2_TYPE_NEVER);
                for (size_t i = 0; i < t2_type_arity(shadow->universe, subject); ++i) {
                        for (size_t j = 0; j < count; ++j) arm_items[j] = never;
                        if (!record_pattern_items(
                                shadow,
                                pattern,
                                t2_type_child(shadow->universe, subject, i),
                                arm_items
                        )) continue;
                        reachable = true;
                        for (size_t j = 0; j < count; ++j) {
                                items[j] = t2_join(
                                        shadow->universe,
                                        items[j],
                                        arm_items[j]
                                );
                        }
                }
                free(arm_items);
                return reachable;
        }

        for (size_t i = 0; i < count; ++i) {
                Expr const *item = v__(pattern->es, (int)i);
                char const *name = i < (size_t)vN(pattern->names)
                                 ? v__(pattern->names, (int)i)
                                 : NULL;
                if (
                        item != NULL
                     && (
                                item->type == EXPRESSION_MATCH_REST
                             || item->type == EXPRESSION_SPREAD
                        )
                ) {
                        items[i] = subject;
                        continue;
                }
                if (name == NULL || strcmp(name, "*") == 0) return false;
                bool optional = i < (size_t)vN(pattern->required)
                             && !v__(pattern->required, (int)i);
                bool field_reachable = false;
                T2Type field = record_pattern_field_type(
                        shadow,
                        subject,
                        name,
                        optional,
                        &field_reachable,
                        0
                );
                if (!field_reachable || field == T2_TYPE_INVALID) return false;
                items[i] = field;
        }
        return true;
}

static Expr const *
pattern_constraint_source(Expr const *constraint)
{
        if (
                constraint != NULL
             && constraint->type == EXPRESSION_TYPE
             && constraint->constraint != NULL
        ) return constraint->constraint;
        return constraint;
}

static bool
pattern_constraint_is_class(Expr const *constraint)
{
        Expr const *source = pattern_constraint_source(constraint);
        Expr const *name = type_reference_leaf(source);
        return name != NULL
            && name->type == EXPRESSION_IDENTIFIER
            && name->symbol != NULL
            && !SymbolIsMember(name->symbol)
            && (
                       name->symbol->class != -1
                    || SymbolIsTypeAlias(name->symbol)
                    || SymbolIsTypeVar(name->symbol)
               );
}

static bool
infer_pattern(Types2Shadow *shadow, Expr const *pattern, T2Type subject)
{
        if (pattern == NULL) return true;
        subject = resolved_type_head(
                shadow,
                subject,
                T2_PREFER_LOWER_BOUND
        );
        switch (pattern->type) {
        case EXPRESSION_MATCH_ANY:
                return true;
        case EXPRESSION_IDENTIFIER:
        case EXPRESSION_MATCH_REST:
        case EXPRESSION_RESOURCE_BINDING:
        {
                Expr const *constraint = pattern->constraint;
                if (!pattern_constraint_is_class(constraint)) {
                        bool valid = assign_lvalue_x(
                                shadow,
                                pattern,
                                subject,
                                true,
                                false
                        );
                        if (constraint != NULL) {
                                (void)infer_expression(
                                        shadow,
                                        pattern_constraint_source(constraint)
                                );
                        }
                        return valid;
                }
                T2Type annotation = lower_type(shadow, constraint);
                T2Type narrowed = narrow_type_to(shadow, subject, annotation);
                if (t2_type_kind(shadow->universe, narrowed) == T2_TYPE_NEVER) {
                        add_diagnostic(
                                shadow,
                                pattern,
                                TYPES2_DIAGNOSTIC_WARNING,
                                "unreachable-pattern",
                                subject,
                                annotation,
                                "annotated pattern cannot match the subject type"
                        );
                        return false;
                }
                return assign_lvalue(shadow, pattern, narrowed, true);
        }
        case EXPRESSION_MATCH_NOT_NIL:
        {
                T2Type narrowed = without_nil(shadow, subject);
                if (t2_type_kind(shadow->universe, narrowed) == T2_TYPE_NEVER) {
                        add_diagnostic(
                                shadow,
                                pattern,
                                TYPES2_DIAGNOSTIC_WARNING,
                                "unreachable-pattern",
                                subject,
                                T2_TYPE_INVALID,
                                "not-nil pattern cannot match this subject"
                        );
                        return false;
                }
                return assign_lvalue(shadow, pattern, narrowed, true);
        }
        case EXPRESSION_ALIAS_PATTERN:
        {
                bool valid = assign_lvalue(shadow, pattern, subject, true);
                return infer_pattern(shadow, pattern->aliased, subject) && valid;
        }
        case EXPRESSION_INTEGER:
        case EXPRESSION_STRING:
        case EXPRESSION_BOOLEAN:
        case EXPRESSION_NIL:
        {
                T2Type pattern_type = infer_expression(shadow, pattern);
                if (pattern_types_overlap(shadow, pattern_type, subject)) return true;
                add_diagnostic(
                        shadow,
                        pattern,
                        TYPES2_DIAGNOSTIC_WARNING,
                        "unreachable-pattern",
                        pattern_type,
                        subject,
                        "literal pattern cannot match the subject type"
                );
                return false;
        }
        case EXPRESSION_TUPLE:
        case EXPRESSION_LIST:
        {
                size_t count = (size_t)vN(pattern->es);
                if (pattern->type == EXPRESSION_LIST && count == 1) {
                        return infer_pattern(shadow, v__(pattern->es, 0), subject);
                }
                T2Type *items = count == 0 ? NULL : malloc(count * sizeof *items);
                if (count != 0 && items == NULL) {
                        shadow->failed = true;
                        return false;
                }
                T2Type never = t2_primitive(shadow->universe, T2_TYPE_NEVER);
                for (size_t i = 0; i < count; ++i) items[i] = never;
                bool record = pattern->type == EXPRESSION_TUPLE
                           && tuple_is_record(pattern)
                           && tuple_is_pure_record(pattern);
                bool reachable = record
                               ? record_pattern_items(
                                       shadow,
                                       pattern,
                                       subject,
                                       items
                                 )
                               : tuple_pattern_items(
                                       shadow,
                                       subject,
                                       items,
                                       count
                                 );
                if (!reachable) {
                        add_diagnostic(
                                shadow,
                                pattern,
                                TYPES2_DIAGNOSTIC_WARNING,
                                "unreachable-pattern",
                                subject,
                                T2_TYPE_INVALID,
                                record
                                    ? "record pattern cannot match the subject's field shape"
                                    : "tuple pattern cannot match the subject's positional shape"
                        );
                } else {
                        for (size_t i = 0; i < count; ++i) {
                                Expr const *item = v__(pattern->es, (int)i);
                                if (
                                        record
                                     && item != NULL
                                     && item->type == EXPRESSION_SPREAD
                                ) item = item->value;
                                reachable &= infer_pattern(
                                        shadow,
                                        item,
                                        items[i]
                                );
                        }
                }
                free(items);
                return reachable;
        }
        case EXPRESSION_ARRAY:
        {
                T2Type element;
                if (!nominal_pattern_arguments(
                        shadow,
                        subject,
                        CLASS_ARRAY,
                        "Array",
                        &element,
                        1,
                        "array pattern element"
                )) {
                        add_diagnostic(
                                shadow,
                                pattern,
                                TYPES2_DIAGNOSTIC_WARNING,
                                "unreachable-pattern",
                                subject,
                                T2_TYPE_INVALID,
                                "array pattern cannot match the subject type"
                        );
                        return false;
                }
                bool valid = true;
                for (int i = 0; i < vN(pattern->elements); ++i) {
                        Expr const *item = v__(pattern->elements, i);
                        if (item->type == EXPRESSION_MATCH_REST) {
                                T2Type array = nominal_application(
                                        shadow,
                                        CLASS_ARRAY,
                                        "Array",
                                        &element,
                                        1,
                                        item
                                );
                                valid &= infer_pattern(shadow, item, array);
                        } else {
                                valid &= infer_pattern(shadow, item, element);
                        }
                }
                return valid;
        }
        case EXPRESSION_DICT:
        {
                T2Type arguments[2];
                if (!nominal_pattern_arguments(
                        shadow,
                        subject,
                        CLASS_DICT,
                        "Dict",
                        arguments,
                        2,
                        "dictionary pattern argument"
                )) {
                        add_diagnostic(
                                shadow,
                                pattern,
                                TYPES2_DIAGNOSTIC_WARNING,
                                "unreachable-pattern",
                                subject,
                                T2_TYPE_INVALID,
                                "dictionary pattern cannot match the subject type"
                        );
                        return false;
                }
                T2Type key = arguments[0];
                T2Type value = arguments[1];
                bool valid = true;
                for (int i = 0; i < vN(pattern->keys); ++i) {
                        T2Type actual_key = infer_expression(shadow, v__(pattern->keys, i));
                        valid &= constrain_type(
                                shadow,
                                v__(pattern->keys, i),
                                actual_key,
                                key,
                                "dictionary-pattern-key",
                                "dictionary pattern key has the wrong type"
                        );
                        if (v__(pattern->values, i) != NULL) {
                                valid &= infer_pattern(
                                        shadow,
                                        v__(pattern->values, i),
                                        t2_join(
                                                shadow->universe,
                                                value,
                                                t2_primitive(shadow->universe, T2_TYPE_NIL)
                                        )
                                );
                        }
                }
                return valid;
        }
        case EXPRESSION_TAG_APPLICATION:
        {
                bool reachable;
                int tag_id = pattern->symbol == NULL ? -1 : pattern->symbol->tag;
                T2Type payload = tag_pattern_payload(
                        shadow,
                        subject,
                        tag_id,
                        false,
                        &reachable
                );
                if (!reachable) {
                        add_diagnostic(
                                shadow,
                                pattern,
                                TYPES2_DIAGNOSTIC_WARNING,
                                "unreachable-pattern",
                                subject,
                                T2_TYPE_INVALID,
                                "tag pattern cannot match the subject type"
                        );
                        (void)infer_pattern(
                                shadow,
                                pattern->tagged,
                                t2_primitive(shadow->universe, T2_TYPE_DYNAMIC)
                        );
                        return false;
                }
                return infer_pattern(shadow, pattern->tagged, payload);
        }
        case EXPRESSION_TAG_PATTERN:
        case EXPRESSION_TAG_PATTERN_CALL:
        {
                bool reachable;
                T2Type payload = tag_pattern_payload(
                        shadow,
                        subject,
                        -1,
                        true,
                        &reachable
                );
                T2Type tag = nominal_application(
                        shadow,
                        CLASS_TAG,
                        "Tag",
                        NULL,
                        0,
                        pattern
                );
                bool valid = assign_lvalue(shadow, pattern, tag, true);
                if (!reachable) {
                        add_diagnostic(
                                shadow,
                                pattern,
                                TYPES2_DIAGNOSTIC_WARNING,
                                "unreachable-pattern",
                                subject,
                                T2_TYPE_INVALID,
                                "tag-binding pattern cannot match the subject type"
                        );
                        (void)infer_pattern(
                                shadow,
                                pattern->tagged,
                                t2_primitive(shadow->universe, T2_TYPE_DYNAMIC)
                        );
                        return false;
                }
                return infer_pattern(shadow, pattern->tagged, payload) && valid;
        }
        case EXPRESSION_OBJECT_PATTERN:
        {
                int class_id = type_symbol_class_id(shadow, pattern->symbol);
                if (class_id < 0) {
                        T2SolverMark trial = t2_solver_mark(shadow->solver);
                        Types2Binding *binding = ensure_resolved_binding(
                                shadow,
                                pattern->symbol
                        );
                        T2Type matcher = instantiate_binding(
                                shadow,
                                binding,
                                pattern
                        );
                        if (matcher == T2_TYPE_INVALID) {
                                defer_symbol(
                                        shadow,
                                        TYPES2_DEFER_UNRESOLVED_MATCHER,
                                        pattern,
                                        pattern->symbol
                                );
                                matcher = t2_primitive(
                                        shadow->universe,
                                        T2_TYPE_DYNAMIC
                                );
                        }
                        T2Type payload = infer_call_types(
                                shadow,
                                matcher,
                                &subject,
                                1,
                                NULL,
                                NULL,
                                0,
                                pattern,
                                false
                        );
                        payload = without_nil(shadow, payload);
                        if (t2_type_kind(shadow->universe, payload) == T2_TYPE_ERROR
                         || t2_type_kind(shadow->universe, payload) == T2_TYPE_NEVER) {
                                t2_solver_rollback(shadow->solver, trial);
                                add_diagnostic(
                                        shadow,
                                        pattern,
                                        TYPES2_DIAGNOSTIC_WARNING,
                                        "unreachable-pattern",
                                        subject,
                                        matcher,
                                        "pattern matcher cannot accept the subject type"
                                );
                                return false;
                        }
                        t2_solver_commit(shadow->solver, trial);
                        return infer_pattern(shadow, pattern->tagged, payload);
                }
                Types2Nominal *nominal = ensure_nominal(
                        shadow,
                        class_id,
                        pattern->identifier,
                        0
                );
                T2Type expected = primitive_class_type(shadow, class_id);
                if (expected == T2_TYPE_INVALID && nominal != NULL) {
                        T2Type *arguments = nominal->arity == 0
                                          ? NULL
                                          : malloc(nominal->arity * sizeof *arguments);
                        if (nominal->arity != 0 && arguments == NULL) {
                                shadow->failed = true;
                                return false;
                        }
                        for (size_t i = 0; i < nominal->arity; ++i) {
                                arguments[i] = t2_solver_new_meta(
                                        shadow->solver,
                                        T2_VARIABLE_FLEXIBLE,
                                        shadow->level,
                                        "object pattern argument"
                                );
                        }
                        expected = t2_nominal(
                                shadow->universe,
                                nominal->symbol,
                                arguments,
                                nominal->arity
                        );
                        free(arguments);
                }
                bool reachable = expected != T2_TYPE_INVALID
                              && pattern_types_overlap(shadow, subject, expected);
                if (!reachable) {
                        add_diagnostic(
                                shadow,
                                pattern,
                                TYPES2_DIAGNOSTIC_WARNING,
                                "unreachable-pattern",
                                subject,
                                T2_TYPE_INVALID,
                                "object pattern cannot match the subject type"
                        );
                        return false;
                }
                T2Type matched_subject = narrow_type_to(
                        shadow,
                        subject,
                        expected
                );
                /* Named field extraction is checked by member inference; until
                 * positional constructor fields are indexed, keep their payload
                 * variables independent instead of copying legacy field types. */
                if (pattern->tagged != NULL && pattern->tagged->type == EXPRESSION_TUPLE) {
                        bool valid = true;
                        for (int i = 0; i < vN(pattern->tagged->es); ++i) {
                                T2Type field = t2_type_kind(
                                                       shadow->universe,
                                                       matched_subject
                                               ) == T2_TYPE_DYNAMIC
                                             ? t2_primitive(
                                                     shadow->universe,
                                                     T2_TYPE_DYNAMIC
                                               )
                                             : t2_solver_new_meta(
                                                     shadow->solver,
                                                     T2_VARIABLE_FLEXIBLE,
                                                     shadow->level,
                                                     "object pattern field"
                                               );
                                if (i < vN(pattern->tagged->names)
                                 && v__(pattern->tagged->names, i) != NULL) {
                                        char const *name = v__(
                                                pattern->tagged->names,
                                                i
                                        );
                                        bool structurally_reachable = false;
                                        T2Type structural =
                                                record_pattern_field_type(
                                                        shadow,
                                                        matched_subject,
                                                        name,
                                                        false,
                                                        &structurally_reachable,
                                                        0
                                                );
                                        field = structurally_reachable
                                              ? structural
                                              : infer_member_type(
                                                        shadow,
                                                        matched_subject,
                                                        name,
                                                        false,
                                                        v__(pattern->tagged->es, i),
                                                        false
                                                );
                                        if (
                                                t2_type_kind(
                                                        shadow->universe,
                                                        field
                                                ) == T2_TYPE_ERROR
                                        ) valid = false;
                                }
                                valid &= infer_pattern(
                                        shadow,
                                        v__(pattern->tagged->es, i),
                                        field
                                );
                        }
                        return valid;
                }
                return infer_pattern(
                        shadow,
                        pattern->tagged,
                        t2_type_kind(shadow->universe, matched_subject) == T2_TYPE_DYNAMIC
                            ? t2_primitive(shadow->universe, T2_TYPE_DYNAMIC)
                            : t2_solver_new_meta(
                                    shadow->solver,
                                    T2_VARIABLE_FLEXIBLE,
                                    shadow->level,
                                    "object pattern field"
                              )
                );
        }
        case EXPRESSION_VIEW_PATTERN:
        case EXPRESSION_NOT_NIL_VIEW_PATTERN:
        {
                T2SolverMark view_scope = t2_solver_mark(shadow->solver);
                T2Type function = infer_expression(shadow, pattern->left);
                T2Type input = pattern->type == EXPRESSION_NOT_NIL_VIEW_PATTERN
                             ? without_nil(shadow, subject)
                             : subject;
                if (t2_type_kind(shadow->universe, input) == T2_TYPE_NEVER) {
                        if (!t2_solver_cancel_obligations_since(
                                shadow->solver,
                                view_scope
                        )) shadow->failed = true;
                        t2_solver_commit(shadow->solver, view_scope);
                        return false;
                }
                T2Type viewed = infer_call_types(
                        shadow,
                        function,
                        &input,
                        1,
                        NULL,
                        NULL,
                        0,
                        pattern,
                        true
                );
                if (
                        viewed == T2_TYPE_INVALID
                     || t2_type_kind(shadow->universe, viewed) == T2_TYPE_ERROR
                     || t2_solver_failed(shadow->solver)
                ) {
                        if (!t2_solver_cancel_obligations_since(
                                shadow->solver,
                                view_scope
                        )) shadow->failed = true;
                }
                t2_solver_commit(shadow->solver, view_scope);
                return infer_pattern(shadow, pattern->right, viewed);
        }
        case EXPRESSION_REF_PATTERN:
        case EXPRESSION_REF_MAYBE_PATTERN:
                return assign_lvalue(shadow, pattern->target, subject, false);
        case EXPRESSION_MUST_EQUAL:
        {
                T2Type existing = literal_symbol_type(
                        shadow,
                        pattern->symbol
                );
                if (existing == T2_TYPE_INVALID) {
                        Types2Binding *binding = ensure_resolved_binding(
                                shadow,
                                pattern->symbol
                        );
                        existing = instantiate_binding(shadow, binding, pattern);
                }
                if (existing == T2_TYPE_INVALID) {
                        /* A non-literal imported constant can still participate
                         * in runtime equality matching.  With no native scheme
                         * available, its reachability is unknown rather than
                         * disproven. */
                        defer_symbol(
                                shadow,
                                TYPES2_DEFER_UNRESOLVED_BINDING,
                                pattern,
                                pattern->symbol
                        );
                        return true;
                }
                if (existing != T2_TYPE_INVALID
                 && pattern_types_overlap(shadow, existing, subject)) return true;
                add_diagnostic(
                        shadow,
                        pattern,
                        TYPES2_DIAGNOSTIC_WARNING,
                        "unreachable-pattern",
                        existing,
                        subject,
                        "existing value pattern cannot match the subject type"
                );
                return false;
        }
        case EXPRESSION_CHECK_MATCH:
                return infer_pattern(shadow, pattern->left, subject)
                    && pattern_types_overlap(
                            shadow,
                            infer_expression(shadow, pattern->right),
                            subject
                       );
        case EXPRESSION_DOT_DOT:
        case EXPRESSION_DOT_DOT_DOT:
                (void)infer_expression(shadow, pattern->left);
                (void)infer_expression(shadow, pattern->right);
                return pattern_types_overlap(
                        shadow,
                        subject,
                        t2_primitive(shadow->universe, T2_TYPE_INT)
                );
        case EXPRESSION_CHOICE_PATTERN:
        case EXPRESSION_OR_LIST:
        {
                bool valid = true;
                for (int i = 0; i < vN(pattern->es); ++i) {
                        valid &= infer_pattern(shadow, v__(pattern->es, i), subject);
                }
                return valid;
        }
        case EXPRESSION_REGEX:
                bind_regex_captures(shadow, pattern);
                return pattern_types_overlap(
                        shadow,
                        subject,
                        t2_primitive(shadow->universe, T2_TYPE_STRING)
                );
        case EXPRESSION_KW_AND:
        {
                bool valid = infer_pattern(shadow, pattern->left, subject);
                for (int i = 0; i < vN(pattern->p_cond); ++i) {
                        struct condpart const *part = v__(pattern->p_cond, i);
                        T2Type value = infer_expression(shadow, part->e);
                        if (part->target != NULL) {
                                valid &= infer_pattern(shadow, part->target, value);
                        }
                }
                return valid;
        }
        default:
                defer_node(shadow, TYPES2_DEFER_UNSUPPORTED_PATTERN, pattern, NULL);
                return true;
        }
}

static bool
infer_refutable_pattern(
        Types2Shadow *shadow,
        Expr const *pattern,
        T2Type subject
)
{
        shadow->refutable_pattern_depth += 1;
        bool reachable = infer_pattern(shadow, pattern, subject);
        shadow->refutable_pattern_depth -= 1;
        return reachable;
}

static bool
pattern_payload_is_irrefutable(Expr const *pattern)
{
        if (pattern == NULL) return true;
        switch (pattern->type) {
        case EXPRESSION_MATCH_ANY:
                return true;
        case EXPRESSION_IDENTIFIER:
        case EXPRESSION_MATCH_REST:
        case EXPRESSION_RESOURCE_BINDING:
                return lvalue_annotation_expression(pattern) == NULL;
        case EXPRESSION_ALIAS_PATTERN:
                return pattern->constraint == NULL
                    && pattern_payload_is_irrefutable(pattern->aliased);
        case EXPRESSION_LIST:
        case EXPRESSION_TUPLE:
                for (int i = 0; i < vN(pattern->es); ++i) {
                        Expr const *item = v__(pattern->es, i);
                        if (item != NULL && item->type == EXPRESSION_SPREAD) {
                                item = item->value;
                        }
                        if (!pattern_payload_is_irrefutable(item)) return false;
                }
                return true;
        case EXPRESSION_CHOICE_PATTERN:
        case EXPRESSION_OR_LIST:
                for (int i = 0; i < vN(pattern->es); ++i) {
                        if (pattern_payload_is_irrefutable(v__(pattern->es, i))) {
                                return true;
                        }
                }
                return false;
        default:
                return false;
        }
}

static T2Type
tuple_pattern_coverage_x(
        Types2Shadow *shadow,
        Expr const *pattern,
        T2Type subject,
        unsigned depth
)
{
        T2Type never = t2_primitive(shadow->universe, T2_TYPE_NEVER);
        if (pattern == NULL || depth >= 64) return never;
        subject = resolved_type_head(
                shadow,
                subject,
                T2_PREFER_LOWER_BOUND
        );
        T2TypeKind kind = t2_type_kind(shadow->universe, subject);
        if (kind == T2_TYPE_UNION) {
                T2Type result = never;
                for (size_t i = 0; i < t2_type_arity(shadow->universe, subject); ++i) {
                        result = t2_join(
                                shadow->universe,
                                result,
                                tuple_pattern_coverage_x(
                                        shadow,
                                        pattern,
                                        t2_type_child(shadow->universe, subject, i),
                                        depth + 1
                                )
                        );
                }
                return result;
        }
        if (kind == T2_TYPE_INTERSECTION) {
                for (size_t i = 0; i < t2_type_arity(shadow->universe, subject); ++i) {
                        if (
                                t2_type_kind(
                                        shadow->universe,
                                        tuple_pattern_coverage_x(
                                                shadow,
                                                pattern,
                                                t2_type_child(
                                                        shadow->universe,
                                                        subject,
                                                        i
                                                ),
                                                depth + 1
                                        )
                                ) != T2_TYPE_NEVER
                        ) return subject;
                }
                return never;
        }
        if (kind != T2_TYPE_TUPLE) return never;
        return t2_type_arity(shadow->universe, subject)
                    == (size_t)vN(pattern->es)
             ? subject
             : never;
}

static T2Type
nominal_pattern_coverage_x(
        Types2Shadow *shadow,
        T2Type subject,
        uint64_t wanted_symbol,
        int wanted_tag,
        bool any_tag,
        unsigned depth
)
{
        T2Type never = t2_primitive(shadow->universe, T2_TYPE_NEVER);
        if (depth >= 64) return never;
        subject = resolved_type_head(
                shadow,
                subject,
                T2_PREFER_LOWER_BOUND
        );
        T2TypeKind kind = t2_type_kind(shadow->universe, subject);
        if (kind == T2_TYPE_UNION) {
                T2Type result = never;
                for (size_t i = 0; i < t2_type_arity(shadow->universe, subject); ++i) {
                        result = t2_join(
                                shadow->universe,
                                result,
                                nominal_pattern_coverage_x(
                                        shadow,
                                        t2_type_child(shadow->universe, subject, i),
                                        wanted_symbol,
                                        wanted_tag,
                                        any_tag,
                                        depth + 1
                                )
                        );
                }
                return result;
        }
        if (kind != T2_TYPE_NOMINAL) return never;
        Types2Nominal *nominal = nominal_from_type(shadow, subject);
        if (any_tag) return nominal_is_tag(shadow, nominal) ? subject : never;
        if (wanted_tag >= 0) {
                return nominal != NULL && nominal->tag_id == wanted_tag
                     ? subject
                     : never;
        }
        return t2_nominal_project(
                shadow->universe,
                subject,
                wanted_symbol
        ) != T2_TYPE_INVALID ? subject : never;
}

static T2Type
pattern_coverage(
        Types2Shadow *shadow,
        Expr const *pattern,
        T2Type subject,
        bool *certain
)
{
        T2Type never = t2_primitive(shadow->universe, T2_TYPE_NEVER);
        if (certain != NULL) *certain = false;
        if (pattern == NULL) return never;
        switch (pattern->type) {
        case EXPRESSION_MATCH_ANY:
                if (certain != NULL) *certain = true;
                return subject;
        case EXPRESSION_IDENTIFIER:
        case EXPRESSION_MATCH_REST:
        case EXPRESSION_RESOURCE_BINDING:
        {
                Expr const *constraint = lvalue_annotation_expression(pattern);
                if (constraint == NULL) {
                        if (certain != NULL) *certain = true;
                        return subject;
                }
                if (!pattern_constraint_is_class(pattern->constraint)) return never;
                T2Type annotation = lower_type(shadow, pattern->constraint);
                if (certain != NULL) *certain = true;
                return narrow_type_to(shadow, subject, annotation);
        }
        case EXPRESSION_MATCH_NOT_NIL:
                if (certain != NULL) *certain = true;
                return without_nil(shadow, subject);
        case EXPRESSION_ALIAS_PATTERN:
                return pattern_coverage(
                        shadow,
                        pattern->aliased,
                        subject,
                        certain
                );
        case EXPRESSION_INTEGER:
        case EXPRESSION_STRING:
        case EXPRESSION_BOOLEAN:
        case EXPRESSION_NIL:
        {
                T2Type literal = infer_expression(shadow, pattern);
                if (certain != NULL) *certain = true;
                return narrow_type_to(shadow, subject, literal);
        }
        case EXPRESSION_MUST_EQUAL:
        {
                T2Type literal = literal_symbol_type(shadow, pattern->symbol);
                if (literal == T2_TYPE_INVALID) return never;
                if (certain != NULL) *certain = true;
                return narrow_type_to(shadow, subject, literal);
        }
        case EXPRESSION_TUPLE:
        case EXPRESSION_LIST:
                if (pattern->type == EXPRESSION_LIST && vN(pattern->es) == 1) {
                        return pattern_coverage(
                                shadow,
                                v__(pattern->es, 0),
                                subject,
                                certain
                        );
                }
                if (
                        (pattern->type == EXPRESSION_TUPLE
                      && tuple_is_record(pattern))
                     || !pattern_payload_is_irrefutable(pattern)
                ) return never;
                if (certain != NULL) *certain = true;
                return tuple_pattern_coverage_x(
                        shadow,
                        pattern,
                        subject,
                        0
                );
        case EXPRESSION_TAG_APPLICATION:
        {
                if (!pattern_payload_is_irrefutable(pattern->tagged)) return never;
                if (certain != NULL) *certain = true;
                return nominal_pattern_coverage_x(
                        shadow,
                        subject,
                        0,
                        pattern->symbol == NULL ? -1 : pattern->symbol->tag,
                        false,
                        0
                );
        }
        case EXPRESSION_TAG_PATTERN:
        case EXPRESSION_TAG_PATTERN_CALL:
                if (!pattern_payload_is_irrefutable(pattern->tagged)) return never;
                if (certain != NULL) *certain = true;
                return nominal_pattern_coverage_x(
                        shadow,
                        subject,
                        0,
                        -1,
                        true,
                        0
                );
        case EXPRESSION_OBJECT_PATTERN:
        {
                int class_id = type_symbol_class_id(shadow, pattern->symbol);
                if (class_id < 0
                 || !pattern_payload_is_irrefutable(pattern->tagged)) return never;
                Types2Nominal *nominal = ensure_nominal(
                        shadow,
                        class_id,
                        pattern->identifier,
                        0
                );
                if (nominal == NULL) return never;
                if (certain != NULL) *certain = true;
                return nominal_pattern_coverage_x(
                        shadow,
                        subject,
                        nominal->symbol,
                        -1,
                        false,
                        0
                );
        }
        case EXPRESSION_CHOICE_PATTERN:
        case EXPRESSION_OR_LIST:
        {
                T2Type result = never;
                bool all_certain = true;
                for (int i = 0; i < vN(pattern->es); ++i) {
                        bool arm_certain = false;
                        result = t2_join(
                                shadow->universe,
                                result,
                                pattern_coverage(
                                        shadow,
                                        v__(pattern->es, i),
                                        subject,
                                        &arm_certain
                                )
                        );
                        all_certain &= arm_certain;
                }
                if (certain != NULL) *certain = all_certain;
                return result;
        }
        default:
                return never;
        }
}

static T2Type
subtract_pattern_coverage(
        Types2Shadow *shadow,
        T2Type subject,
        T2Type coverage,
        bool covers_open_domain
)
{
        T2TypeKind subject_kind = t2_type_kind(shadow->universe, subject);
        T2TypeKind coverage_kind = t2_type_kind(shadow->universe, coverage);
        if (coverage_kind == T2_TYPE_NEVER) return subject;
        if (
                subject_kind == T2_TYPE_DYNAMIC
             || subject_kind == T2_TYPE_UNKNOWN
             || subject_kind == T2_TYPE_ANY
             || subject_kind == T2_TYPE_OBJECT
             || subject_kind == T2_TYPE_META
             || subject_kind == T2_TYPE_VARIABLE
             || subject_kind == T2_TYPE_ERROR
        ) {
                /* An open or gradual domain cannot be represented as
                 * `Dynamic except Int` (and a metavariable's lower bound is
                 * not its complete runtime domain).  Only a syntactic
                 * catch-all is therefore allowed to consume such an arm. */
                return covers_open_domain
                     ? t2_primitive(shadow->universe, T2_TYPE_NEVER)
                     : subject;
        }
        if (subject_kind == T2_TYPE_UNION) {
                T2Type result = t2_primitive(shadow->universe, T2_TYPE_NEVER);
                for (size_t i = 0; i < t2_type_arity(shadow->universe, subject); ++i) {
                        result = t2_join(
                                shadow->universe,
                                result,
                                subtract_pattern_coverage(
                                        shadow,
                                        t2_type_child(shadow->universe, subject, i),
                                        coverage,
                                        covers_open_domain
                                )
                        );
                }
                return result;
        }
        if (coverage_kind == T2_TYPE_UNION) {
                T2Type result = subject;
                for (size_t i = 0; i < t2_type_arity(shadow->universe, coverage); ++i) {
                        result = subtract_pattern_coverage(
                                shadow,
                                result,
                                t2_type_child(shadow->universe, coverage, i),
                                covers_open_domain
                        );
                }
                return result;
        }
        if (subject_kind == T2_TYPE_BOOL
         && coverage_kind == T2_TYPE_LITERAL_BOOL) {
                return t2_literal_bool(
                        shadow->universe,
                        t2_type_payload(shadow->universe, coverage) == 0
                );
        }
        return exclude_type(shadow, subject, coverage);
}

static bool
match_domain_is_closed(Types2Shadow *shadow, T2Type subject)
{
        subject = resolved_type_head(
                shadow,
                subject,
                T2_PREFER_LOWER_BOUND
        );
        T2TypeKind kind = t2_type_kind(shadow->universe, subject);
        if (kind == T2_TYPE_UNION) {
                for (size_t i = 0; i < t2_type_arity(shadow->universe, subject); ++i) {
                        T2TypeKind arm = t2_type_kind(
                                shadow->universe,
                                t2_type_child(shadow->universe, subject, i)
                        );
                        if (
                                arm == T2_TYPE_DYNAMIC
                             || arm == T2_TYPE_UNKNOWN
                             || arm == T2_TYPE_ANY
                             || arm == T2_TYPE_OBJECT
                             || arm == T2_TYPE_META
                             || arm == T2_TYPE_VARIABLE
                             || arm == T2_TYPE_ERROR
                        ) return false;
                }
                return true;
        }
        if (
                kind == T2_TYPE_BOOL
             || kind == T2_TYPE_LITERAL_BOOL
             || kind == T2_TYPE_LITERAL_INT
             || kind == T2_TYPE_LITERAL_STRING
             || kind == T2_TYPE_NIL
        ) return true;
        if (kind == T2_TYPE_NOMINAL) {
                return nominal_is_tag(shadow, nominal_from_type(shadow, subject));
        }
        return false;
}

static bool
pattern_is_catch_all(Expr const *pattern)
{
        if (pattern == NULL) return false;
        switch (pattern->type) {
        case EXPRESSION_MATCH_ANY:
                return true;
        case EXPRESSION_IDENTIFIER:
        case EXPRESSION_MATCH_REST:
        case EXPRESSION_RESOURCE_BINDING:
                return lvalue_annotation_expression(pattern) == NULL;
        case EXPRESSION_ALIAS_PATTERN:
                return pattern->constraint == NULL
                    && pattern_is_catch_all(pattern->aliased);
        case EXPRESSION_CHOICE_PATTERN:
        case EXPRESSION_OR_LIST:
                for (int i = 0; i < vN(pattern->es); ++i) {
                        if (pattern_is_catch_all(v__(pattern->es, i))) return true;
                }
                return false;
        default:
                return false;
        }
}

static void
apply_function_bounds(Types2Shadow *shadow, Expr const *function)
{
        for (int i = 0; i < vN(function->type_bounds); ++i) {
                TypeBound const *bound = v_(function->type_bounds, i);
                if (bound->var == NULL || bound->bound == NULL) continue;
                if (
                        bound->var->type == EXPRESSION_IDENTIFIER
                     || bound->var->type == EXPRESSION_FUNCTION_TYPE
                ) {
                        T2Type subtype = lower_type(shadow, bound->var);
                        T2Type supertype = lower_type(shadow, bound->bound);
                        if (shadow_reserve(
                                shadow,
                                (void **)&shadow->upper_assumptions,
                                &shadow->upper_assumption_capacity,
                                shadow->upper_assumption_count + 1,
                                sizeof *shadow->upper_assumptions
                        )) {
                                shadow->upper_assumptions[
                                        shadow->upper_assumption_count++
                                ] = (Types2UpperAssumption) {
                                        .subtype = subtype,
                                        .supertype = supertype
                                };
                        }
                        (void)constrain_type(
                                shadow,
                                bound->var,
                                subtype,
                                supertype,
                                "generic-bound",
                                "declared generic subtype bound is not satisfiable"
                        );
                        continue;
                }
                switch (bound->var->type) {
                case EXPRESSION_PLUS:
                case EXPRESSION_MINUS:
                case EXPRESSION_STAR:
                case EXPRESSION_DIV:
                case EXPRESSION_PERCENT:
                case EXPRESSION_CMP:
                case EXPRESSION_XOR:
                case EXPRESSION_SHL:
                case EXPRESSION_SHR:
                case EXPRESSION_LT:
                case EXPRESSION_GT:
                case EXPRESSION_LEQ:
                case EXPRESSION_GEQ:
                case EXPRESSION_DBL_EQ:
                case EXPRESSION_NOT_EQ:
                case EXPRESSION_CHECK_MATCH:
                case EXPRESSION_USER_OP:
                {
                        char const *name = bound->var->type == EXPRESSION_USER_OP
                                           ? bound->var->op_name
                                           : binary_operation_name(bound->var->type);
                        (void)constrain_predicate(
                                shadow,
                                bound->var,
                                (T2Predicate) {
                                        .kind = T2_PREDICATE_OPERATOR,
                                        .subtype = lower_type(
                                                shadow,
                                                bound->var->left
                                        ),
                                        .supertype = lower_type(shadow, bound->bound),
                                        .operand = lower_type(
                                                shadow,
                                                bound->var->right
                                        ),
                                        .name = name
                                },
                                "generic-operator-bound",
                                "declared generic operator bound is not satisfiable"
                        );
                        break;
                }
                default:
                        defer_node(shadow, TYPES2_DEFER_UNSUPPORTED_BOUND, bound->var, NULL);
                        break;
                }
        }
}

static T2Type
replace_callable_channels(
        Types2Shadow *shadow,
        T2Type callable,
        T2Type result,
        T2Type yields,
        T2Type sends
)
{
        if (t2_type_kind(shadow->universe, callable) != T2_TYPE_FUNCTION) {
                return T2_TYPE_INVALID;
        }
        size_t count = t2_callable_parameter_count(shadow->universe, callable);
        T2ParameterSpec *parameters = count == 0
                                    ? NULL
                                    : malloc(count * sizeof *parameters);
        if (count != 0 && parameters == NULL) {
                shadow->failed = true;
                return T2_TYPE_INVALID;
        }
        for (size_t i = 0; i < count; ++i) {
                if (!t2_callable_parameter(
                        shadow->universe,
                        callable,
                        i,
                        &parameters[i]
                )) {
                        free(parameters);
                        return T2_TYPE_INVALID;
                }
        }
        T2Type replacement = t2_effectful_callable(
                shadow->universe,
                parameters,
                count,
                result,
                yields,
                sends
        );
        free(parameters);
        return replacement;
}

static T2Type
infer_single_function(Types2Shadow *shadow, Expr const *function)
{
        uint32_t outer_level = shadow->level;
        size_t binding_mark = shadow->binding_count;
        size_t assumption_mark = shadow->upper_assumption_count;
        shadow->level = outer_level + 1;
        size_t type_mark = push_type_variables(shadow);
        size_t type_argument_count = (size_t)vN(function->type_params);
        T2Type *type_arguments = type_argument_count == 0
                               ? NULL
                               : malloc(type_argument_count * sizeof *type_arguments);
        if (type_argument_count != 0 && type_arguments == NULL) {
                shadow->failed = true;
                goto Failure;
        }

        for (size_t i = 0; i < type_argument_count; ++i) {
                Expr const *parameter = v__(function->type_params, i);
                T2VariableKind kind = parameter->symbol != NULL
                                   && (parameter->symbol->flags & SYM_PARAM_PACK)
                                    ? T2_VARIABLE_PACK
                                    : T2_VARIABLE_FLEXIBLE;
                T2Type variable = t2_solver_new_meta(
                        shadow->solver,
                        kind,
                        shadow->level,
                        parameter->identifier == NULL
                            ? "explicit type parameter"
                            : parameter->identifier
                );
                if (
                        variable == T2_TYPE_INVALID
                     || !add_type_variable(shadow, parameter->symbol, variable)
                ) goto Failure;
                type_arguments[i] = variable;
        }

        T2Type declared_callable = T2_TYPE_INVALID;
        Types2Operator *operator = find_operator_declaration(shadow, function);
        if (
                operator != NULL
             && t2_scheme_quantifier_count(operator->scheme) == type_argument_count
        ) declared_callable = t2_scheme_apply(
                operator->scheme,
                shadow->solver,
                type_arguments,
                type_argument_count,
                "class operator signature"
        );
        free(type_arguments);
        type_arguments = NULL;

        size_t parameter_count = (size_t)vN(function->params);
        T2ParameterSpec *parameters = parameter_count == 0
                                    ? NULL
                                    : calloc(parameter_count, sizeof *parameters);
        if (parameter_count != 0 && parameters == NULL) {
                shadow->failed = true;
                goto Failure;
        }

        for (size_t i = 0; i < parameter_count; ++i) {
                Expr const *annotation = declared_parameter_annotation(function, i);
                T2Type parameter_type;
                T2ParameterSpec declared_parameter;
                bool has_declared_parameter = declared_callable != T2_TYPE_INVALID
                                           && t2_callable_parameter(
                                                   shadow->universe,
                                                   declared_callable,
                                                   i,
                                                   &declared_parameter
                                              );
                if (has_declared_parameter) {
                        parameter_type = declared_parameter.type;
                } else if (annotation == NULL) {
                        parameter_type = t2_solver_new_meta(
                                shadow->solver,
                                T2_VARIABLE_FLEXIBLE,
                                shadow->level,
                                v__(function->params, (int)i)
                        );
                } else {
                        parameter_type = i == 0
                                      && function->mtype == MT_2OP
                                      && annotation->type == EXPRESSION_TYPE
                                      && annotation->constraint == NULL
                                       ? declared_function_receiver(shadow, function)
                                       : lower_type(shadow, annotation);
                }
                T2ParameterKind kind = T2_PARAMETER_POSITIONAL_OR_KEYWORD;
                if ((int)i == function->rest) kind = T2_PARAMETER_POSITIONAL_REST;
                if ((int)i == function->ikwargs) kind = T2_PARAMETER_KEYWORD_REST;
                if (
                        function->rest >= 0
                     && (int)i > function->rest
                     && kind == T2_PARAMETER_POSITIONAL_OR_KEYWORD
                ) kind = T2_PARAMETER_KEYWORD_ONLY;
                if (
                        is_pack_type(shadow, parameter_type)
                     && kind != T2_PARAMETER_KEYWORD_REST
                ) kind = T2_PARAMETER_PACK;
                bool required = kind != T2_PARAMETER_POSITIONAL_REST
                             && kind != T2_PARAMETER_KEYWORD_REST
                             && kind != T2_PARAMETER_PACK
                             && (
                                        i >= (size_t)vN(function->dflts)
                                     || v__(function->dflts, (int)i) == NULL
                                )
                             && !type_admits_nil(shadow, parameter_type);
                if (has_declared_parameter) {
                        kind = declared_parameter.kind;
                        required = declared_parameter.required;
                }
                parameters[i] = (T2ParameterSpec) {
                        .name = v__(function->params, (int)i),
                        .type = parameter_type,
                        .kind = kind,
                        .required = required
                };

                if (i < (size_t)vN(function->param_symbols)) {
                        Types2Binding *binding = ensure_binding(
                                shadow,
                                v__(function->param_symbols, (int)i)
                        );
                        if (binding != NULL) {
                                T2Type local_type = parameter_type;
                                if (kind == T2_PARAMETER_POSITIONAL_REST) {
                                        local_type = nominal_application(
                                                shadow,
                                                CLASS_ARRAY,
                                                "Array",
                                                &parameter_type,
                                                1,
                                                function
                                        );
                                } else if (kind == T2_PARAMETER_PACK) {
                                        T2Type element = t2_pack_fold_union(
                                                shadow->universe,
                                                parameter_type
                                        );
                                        local_type = nominal_application(
                                                shadow,
                                                CLASS_ARRAY,
                                                "Array",
                                                &element,
                                                1,
                                                function
                                        );
                                } else if (kind == T2_PARAMETER_KEYWORD_REST) {
                                        local_type = nominal_application(
                                                shadow,
                                                CLASS_DICT,
                                                "Dict",
                                                (T2Type[]) {
                                                        t2_primitive(
                                                                shadow->universe,
                                                                T2_TYPE_STRING
                                                        ),
                                                        parameter_type
                                                },
                                                2,
                                                function
                                        );
                                }
                                binding->type = local_type;
                                binding->initialized = true;
                        }
                }
        }

        bool generator = function->type == EXPRESSION_GENERATOR || function->star;
        T2Type yields = !generator
                      ? t2_primitive(shadow->universe, T2_TYPE_NEVER)
                      : function->return_type != NULL
                        ? T2_TYPE_INVALID
                        : t2_solver_new_meta(
                                shadow->solver,
                                T2_VARIABLE_FLEXIBLE,
                                shadow->level,
                                "generator yield"
                          );
        T2Type sends = !generator
                    ? t2_primitive(shadow->universe, T2_TYPE_NIL)
                    : function->return_type != NULL
                      ? T2_TYPE_INVALID
                      : t2_solver_new_meta(
                              shadow->solver,
                              T2_VARIABLE_FLEXIBLE,
                              shadow->level,
                              "generator send"
                        );
        T2Type result;
        if (generator && function->return_type != NULL) {
                result = lower_type(shadow, function->return_type);
                if (!callable_channels_from_result(
                        shadow,
                        result,
                        &yields,
                        &sends
                )) {
                        add_diagnostic(
                                shadow,
                                function->return_type,
                                TYPES2_DIAGNOSTIC_ERROR,
                                "generator-result",
                                result,
                                T2_TYPE_INVALID,
                                "a generator's declared result must expose an iterable yield type"
                        );
                        yields = t2_primitive(shadow->universe, T2_TYPE_DYNAMIC);
                        sends = t2_primitive(shadow->universe, T2_TYPE_DYNAMIC);
                }
        } else if (generator) {
                result = nominal_application(
                        shadow,
                        CLASS_GENERATOR,
                        "Generator",
                        (T2Type[]) { yields, sends },
                        2,
                        function
                );
        } else if (
                declared_callable != T2_TYPE_INVALID
             && t2_type_kind(shadow->universe, declared_callable) == T2_TYPE_FUNCTION
        ) {
                result = t2_callable_result(shadow->universe, declared_callable);
                yields = t2_callable_yield(shadow->universe, declared_callable);
                sends = t2_callable_send(shadow->universe, declared_callable);
        } else {
                result = function->return_type == NULL
                       ? t2_solver_new_meta(
                               shadow->solver,
                               T2_VARIABLE_FLEXIBLE,
                               shadow->level,
                               "function result"
                         )
                       : lower_type(shadow, function->return_type);
        }
        if (!generator && function->return_type != NULL) {
                (void)callable_channels_from_result(
                        shadow,
                        result,
                        &yields,
                        &sends
                );
        }
        if (
                result == T2_TYPE_INVALID
             || yields == T2_TYPE_INVALID
             || sends == T2_TYPE_INVALID
        ) {
                free(parameters);
                goto Failure;
        }
        T2Type callable = t2_callable(
                shadow->universe,
                parameters,
                parameter_count,
                result,
                yields,
                sends
        );
        free(parameters);
        if (callable == T2_TYPE_INVALID) goto Failure;

        Types2Binding *self_binding = ensure_binding(shadow, function->self);
        if (self_binding != NULL && function->class != NULL) {
                T2Type receiver = T2_TYPE_INVALID;
                if (
                        shadow->member_receiver != T2_TYPE_INVALID
                     && shadow->member_class_id == function->class->i
                ) {
                        receiver = shadow->member_receiver;
                } else {
                        Types2Nominal *nominal = ensure_nominal(
                                shadow,
                                function->class->i,
                                function->class->name,
                                0
                        );
                        T2Type *arguments = nominal == NULL || nominal->arity == 0
                                          ? NULL
                                          : malloc(nominal->arity * sizeof *arguments);
                        if (nominal != NULL && nominal->arity != 0 && arguments == NULL) {
                                shadow->failed = true;
                                goto Failure;
                        }
                        for (size_t i = 0; nominal != NULL && i < nominal->arity; ++i) {
                                T2Type argument = T2_TYPE_INVALID;
                                if (
                                        function->class->def != NULL
                                     && i < (size_t)vN(function->class->def->class.type_params)
                                ) {
                                        Expr const *parameter = v__(
                                                function->class->def->class.type_params,
                                                (int)i
                                        );
                                        argument = find_type_variable(
                                                shadow,
                                                parameter->symbol
                                        );
                                }
                                arguments[i] = argument != T2_TYPE_INVALID
                                             ? argument
                                             : t2_solver_new_meta(
                                                     shadow->solver,
                                                     T2_VARIABLE_FLEXIBLE,
                                                     shadow->level,
                                                     "receiver type argument"
                                               );
                        }
                        receiver = nominal == NULL
                                 ? t2_primitive(shadow->universe, T2_TYPE_DYNAMIC)
                                 : t2_nominal(
                                           shadow->universe,
                                           nominal->symbol,
                                           arguments,
                                           nominal->arity
                                   );
                        free(arguments);
                }

                T2Type self_type = receiver;
                if (
                        function->fn_symbol != NULL
                     && SymbolIsStatic(function->fn_symbol)
                     && receiver != T2_TYPE_INVALID
                ) {
                        T2Type constructor = T2_TYPE_INVALID;
                        Types2Member const *initializer = find_direct_member(
                                shadow,
                                function->class->i,
                                "init",
                                TYPES2_MEMBER_METHOD,
                                false
                        );
                        if (initializer != NULL && initializer->scheme != NULL) {
                                Types2Member snapshot = *initializer;
                                constructor = instantiate_member(
                                        shadow,
                                        &snapshot,
                                        receiver,
                                        function
                                );
                                constructor = callable_set_result(
                                        shadow,
                                        constructor,
                                        receiver
                                );
                        }
                        if (constructor == T2_TYPE_INVALID) {
                                constructor = t2_callable(
                                        shadow->universe,
                                        NULL,
                                        0,
                                        receiver,
                                        t2_primitive(
                                                shadow->universe,
                                                T2_TYPE_NEVER
                                        ),
                                        t2_primitive(
                                                shadow->universe,
                                                T2_TYPE_NIL
                                        )
                                );
                        }
                        self_type = t2_type_value(
                                shadow->universe,
                                receiver,
                                constructor
                        );
                }
                self_binding->type = self_type;
                self_binding->initialized = true;
        }

        Symbol const *recursive_symbol = function->fn_symbol;
        Types2Binding *recursive = ensure_binding(shadow, recursive_symbol);
        if (recursive != NULL) {
                recursive->type = callable;
                recursive->initialized = true;
        }

        apply_function_bounds(shadow, function);

        /* The parameter array has been released, so validate defaults using the
         * stable callable protocol rather than retaining an auxiliary copy. */
        for (size_t i = 0; i < parameter_count; ++i) {
                if (i >= (size_t)vN(function->dflts)) break;
                Expr const *value = v__(function->dflts, (int)i);
                if (value == NULL) continue;
                if (
                        function->mtype == MT_DFL
                     && value->type == EXPRESSION_NIL
                     && value->start.s == NULL
                ) continue;
                T2ParameterSpec parameter;
                if (t2_callable_parameter(shadow->universe, callable, i, &parameter)) {
                        (void)constrain_type(
                                shadow,
                                value,
                                infer_expression(shadow, value),
                                parameter.type,
                                "default-argument",
                                "default argument does not satisfy its parameter type"
                        );
                }
        }

        if (!push_function_frame(shadow, (Types2FunctionFrame) {
                .function = function,
                .result = generator
                        ? t2_primitive(shadow->universe, T2_TYPE_DYNAMIC)
                        : result,
                .yields = yields,
                .sends = sends,
                .level = shadow->level,
                .generator = generator,
                .effectful = false,
                .inferred_result = !generator
                                && function->return_type == NULL
                                && declared_callable == T2_TYPE_INVALID
        })) goto Failure;

        Types2Flow body = function->body == NULL
                        ? (Types2Flow) {
                                .outcomes = 0,
                                .value = t2_primitive(shadow->universe, T2_TYPE_NEVER),
                                .returns = t2_primitive(shadow->universe, T2_TYPE_NEVER)
                          }
                        : infer_statement(shadow, function->body);
        Types2FunctionFrame frame = shadow->functions[--shadow->function_count];
        if (
                !frame.generator
             && function->body != NULL
             && (body.outcomes & TYPES2_FLOW_FALLS_THROUGH)
        ) {
                if (
                        frame.inferred_result
                     && is_dynamic_type(shadow, body.value)
                ) default_dynamic_callable_metas(shadow, frame.result, 0);
                (void)constrain_type(
                        shadow,
                        function,
                        body.value,
                        frame.result,
                        "function-fallthrough",
                        "fallthrough value does not satisfy the function result type"
                );
        }
        if (frame.effectful && !generator) {
                T2Type replacement = replace_callable_channels(
                        shadow,
                        callable,
                        result,
                        frame.yields,
                        frame.sends
                );
                if (replacement != T2_TYPE_INVALID) {
                        callable = replacement;
                        recursive = find_binding(shadow, recursive_symbol);
                        if (recursive != NULL) recursive->type = callable;
                }
        }

        for (size_t i = binding_mark; i < shadow->binding_count; ++i) {
                if (!shadow->bindings[i].persistent) {
                        shadow->bindings[i].active = false;
                }
        }
        shadow->upper_assumption_count = assumption_mark;
        pop_type_variables(shadow, type_mark);
        shadow->level = outer_level;
        return callable;

Failure:
        free(type_arguments);
        for (size_t i = binding_mark; i < shadow->binding_count; ++i) {
                if (!shadow->bindings[i].persistent) {
                        shadow->bindings[i].active = false;
                }
        }
        shadow->upper_assumption_count = assumption_mark;
        pop_type_variables(shadow, type_mark);
        shadow->level = outer_level;
        return t2_primitive(shadow->universe, T2_TYPE_ERROR);
}

static T2Type
infer_function_expression(Types2Shadow *shadow, Expr const *function)
{
        T2Type cached = node_type(shadow, function);
        if (cached != T2_TYPE_INVALID) return cached;
        if (function->type != EXPRESSION_MULTI_FUNCTION) {
                T2Type result = infer_single_function(shadow, function);
                if (
                        function->type == EXPRESSION_GENERATOR
                     && t2_type_kind(shadow->universe, result) == T2_TYPE_FUNCTION
                ) {
                        result = t2_callable_result(shadow->universe, result);
                }
                set_node_type(shadow, function, result);
                return result;
        }

        size_t count = (size_t)vN(function->functions);
        T2Type *candidates = NULL;
        size_t capacity = 0;
        size_t used = 0;
        for (size_t i = 0; i < count; ++i) {
                Expr const *entry = v__(function->functions, (int)i);
                Expr const *candidate = entry;
                if (entry != NULL && IsStmt(entry)) {
                        Stmt const *definition = (Stmt const *)entry;
                        candidate = definition->value;
                }
                if (candidate == NULL) continue;
                T2Type type = infer_function_expression(shadow, candidate);
                if (t2_type_kind(shadow->universe, type) == T2_TYPE_OVERLOAD) {
                        size_t arms = t2_type_arity(shadow->universe, type);
                        if (used > SIZE_MAX - arms) {
                                free(candidates);
                                shadow->failed = true;
                                return T2_TYPE_INVALID;
                        }
                        if (!shadow_reserve(
                                shadow,
                                (void **)&candidates,
                                &capacity,
                                used + arms,
                                sizeof *candidates
                        )) {
                                free(candidates);
                                return T2_TYPE_INVALID;
                        }
                        for (size_t j = 0; j < arms; ++j) {
                                candidates[used++] = t2_type_child(shadow->universe, type, j);
                        }
                } else {
                        if (!shadow_reserve(
                                shadow,
                                (void **)&candidates,
                                &capacity,
                                used + 1,
                                sizeof *candidates
                        )) {
                                free(candidates);
                                return T2_TYPE_INVALID;
                        }
                        candidates[used++] = type;
                }
        }
        T2Type result = t2_overload(shadow->universe, candidates, used);
        free(candidates);
        Types2Binding *binding = ensure_binding(shadow, function->fn_symbol);
        if (binding != NULL) {
                binding->type = result;
                binding->initialized = true;
        }
        set_node_type(shadow, function, result);
        return result;
}

static bool
function_has_body(Expr const *function)
{
        if (function == NULL) return false;
        if (function->type != EXPRESSION_MULTI_FUNCTION) return function->body != NULL;
        for (int i = 0; i < vN(function->functions); ++i) {
                Expr const *entry = v__(function->functions, i);
                if (entry != NULL && IsStmt(entry)) entry = ((Stmt const *)entry)->value;
                if (function_has_body(entry)) return true;
        }
        return false;
}

static T2Scheme *
generalize_member_scheme(
        Types2Shadow *shadow,
        T2Type type,
        T2Type const *environment,
        size_t environment_count,
        T2Quantifier const *class_quantifiers,
        size_t class_arity,
        uint32_t class_level,
        T2SolverMark scope
)
{
        if (shadow->failed) {
                t2_solver_commit(shadow->solver, scope);
                return NULL;
        }
        T2Type generalization_root = type;
        if (class_arity != 0) {
                if (class_arity == SIZE_MAX) {
                        shadow->failed = true;
                        t2_solver_commit(shadow->solver, scope);
                        return NULL;
                }
                T2Type *roots = malloc((class_arity + 1) * sizeof *roots);
                if (roots == NULL) {
                        shadow->failed = true;
                        t2_solver_commit(shadow->solver, scope);
                        return NULL;
                }
                roots[0] = type;
                for (size_t i = 0; i < class_arity; ++i) {
                        roots[i + 1] = t2_variable(
                                shadow->universe,
                                class_quantifiers[i].kind,
                                class_quantifiers[i].id
                        );
                }
                generalization_root = t2_tuple(
                        shadow->universe,
                        roots,
                        class_arity + 1
                );
                free(roots);
        }
        T2Scheme *inner = t2_solver_generalize_scoped(
                shadow->solver,
                generalization_root,
                environment,
                environment_count,
                class_level,
                false,
                scope
        );
        t2_solver_commit(shadow->solver, scope);
        if (inner == NULL) return NULL;
        if (class_arity != 0) {
                T2Type body = t2_scheme_body(inner);
                T2Type callable = t2_type_kind(shadow->universe, body)
                                == T2_TYPE_TUPLE
                               && t2_type_arity(shadow->universe, body)
                                  == class_arity + 1
                                ? t2_type_child(shadow->universe, body, 0)
                                : T2_TYPE_INVALID;
                T2Scheme *trimmed = callable == T2_TYPE_INVALID
                                  ? NULL
                                  : scheme_with_body(shadow, inner, callable);
                t2_scheme_free(inner);
                inner = trimmed;
                if (inner == NULL) return NULL;
        }
        T2Scheme *result = prepend_scheme_quantifiers(
                shadow,
                class_quantifiers,
                class_arity,
                inner,
                T2_TYPE_INVALID
        );
        t2_scheme_free(inner);
        return result;
}

static void
infer_member_functions(
        Types2Shadow *shadow,
        int class_id,
        ExprVec const *functions,
        Types2MemberKind kind,
        bool is_static,
        T2Quantifier const *class_quantifiers,
        size_t class_arity,
        uint32_t class_level
)
{
        for (int i = 0; i < vN(*functions); ++i) {
                Expr const *function = v__(*functions, i);
                size_t binding_mark = shadow->binding_count;
                size_t environment_count = 0;
                T2Type *environment = environment_types(
                        shadow,
                        NULL,
                        &environment_count
                );
                size_t pending_before = t2_solver_pending_obligations(shadow->solver);
                T2SolverMark scope = t2_solver_mark(shadow->solver);
                T2Type type = infer_function_expression(shadow, function);
                size_t pending_inferred = t2_solver_pending_obligations(shadow->solver);
                /* A multi-function creates a synthetic recursive binding after
                 * its individual arms have left scope.  Class members are not
                 * lexical bindings in the surrounding class definition, so do
                 * not let that implementation detail enter the member scheme's
                 * generalization environment or escape into later members. */
                for (size_t j = binding_mark; j < shadow->binding_count; ++j) {
                        if (!shadow->bindings[j].persistent) {
                                shadow->bindings[j].active = false;
                        }
                }
                T2Scheme *scheme = generalize_member_scheme(
                        shadow,
                        type,
                        environment,
                        environment_count,
                        class_quantifiers,
                        class_arity,
                        class_level,
                        scope
                );
                free(environment);
                if (shadow->log != NULL && !shadow->failed) {
                        log_prefix(shadow, "member_scheme");
                        fprintf(shadow->log, ",\"class_id\":%d,\"member\":", class_id);
                        json_string(
                                shadow->log,
                                function->name == NULL ? "<member>" : function->name
                        );
                        fprintf(
                                shadow->log,
                                ",\"line\":%u,\"pending_before\":%zu"
                                ",\"pending_inferred\":%zu,\"pending_after\":%zu"
                                ",\"quantifiers\":%zu,\"predicates\":%zu",
                                function->start.line + 1,
                                pending_before,
                                pending_inferred,
                                t2_solver_pending_obligations(shadow->solver),
                                t2_scheme_quantifier_count(scheme),
                                t2_scheme_predicate_count(scheme)
                        );
                        fputs(",\"type\":", shadow->log);
                        if (scheme == NULL) {
                                fputs("null", shadow->log);
                        } else {
                                char *scheme_type = t2_type_string(
                                        shadow->universe,
                                        t2_scheme_body(scheme)
                                );
                                if (scheme_type == NULL) fputs("null", shadow->log);
                                else {
                                        json_string(shadow->log, scheme_type);
                                        free(scheme_type);
                                }
                        }
                        log_end(shadow);
                }
                if (scheme == NULL) {
                        if (!t2_solver_failed(shadow->solver)) shadow->failed = true;
                        return;
                }
                (void)add_member(
                        shadow,
                        class_id,
                        function->name == NULL ? "<member>" : function->name,
                        kind,
                        is_static,
                        !function_has_body(function),
                        kind == TYPES2_MEMBER_SETTER,
                        class_arity,
                        scheme,
                        function
                );
        }
}

static void
infer_member_fields(
        Types2Shadow *shadow,
        int class_id,
        ExprVec const *fields,
        bool is_static,
        T2Quantifier const *class_quantifiers,
        size_t class_arity
)
{
        for (int i = 0; i < vN(*fields); ++i) {
                Expr const *field = v__(*fields, i);
                Expr const *identifier = field != NULL && field->type == EXPRESSION_EQ
                                       ? field->target
                                       : field;
                if (identifier == NULL || identifier->identifier == NULL) continue;
                T2Type type = identifier->constraint == NULL
                            ? t2_primitive(shadow->universe, T2_TYPE_DYNAMIC)
                            : lower_type(shadow, identifier->constraint);
                if (field->type == EXPRESSION_EQ && field->value != NULL) {
                        (void)constrain_type(
                                shadow,
                                field->value,
                                infer_expression(shadow, field->value),
                                type,
                                "field-default",
                                "field initializer does not satisfy its declared type"
                        );
                }
                T2Scheme *scheme = prepend_scheme_quantifiers(
                        shadow,
                        class_quantifiers,
                        class_arity,
                        NULL,
                        type
                );
                if (scheme == NULL) return;
                (void)add_member(
                        shadow,
                        class_id,
                        identifier->identifier,
                        TYPES2_MEMBER_FIELD,
                        is_static,
                        false,
                        true,
                        class_arity,
                        scheme,
                        identifier
                );
        }
}

static T2Type
class_receiver_type(
        Types2Shadow *shadow,
        int class_id,
        T2Type const *arguments,
        size_t arity,
        Expr const *site
)
{
        T2Type primitive = primitive_class_type(shadow, class_id);
        if (primitive != T2_TYPE_INVALID) {
                if (arity != 0) {
                        add_diagnostic(
                                shadow,
                                site,
                                TYPES2_DIAGNOSTIC_ERROR,
                                "class-arity",
                                primitive,
                                T2_TYPE_INVALID,
                                "primitive class receiver cannot have generic arguments"
                        );
                        return t2_primitive(shadow->universe, T2_TYPE_ERROR);
                }
                return primitive;
        }
        Types2Nominal *nominal = ensure_nominal(shadow, class_id, NULL, arity);
        if (nominal == NULL || nominal->arity != arity) {
                add_diagnostic(
                        shadow,
                        site,
                        TYPES2_DIAGNOSTIC_ERROR,
                        "class-arity",
                        T2_TYPE_INVALID,
                        T2_TYPE_INVALID,
                        "class receiver has inconsistent generic arity"
                );
                return t2_primitive(shadow->universe, T2_TYPE_ERROR);
        }
        return t2_nominal(shadow->universe, nominal->symbol, arguments, arity);
}

static bool
member_contract_compatible(
        Types2Shadow *shadow,
        Types2Member const *actual_member,
        T2Type actual_receiver,
        Types2Member const *expected_member,
        T2Type expected_receiver,
        Expr const *site,
        char const *code,
        char const *description
)
{
        if (actual_member == NULL || expected_member == NULL) return false;
        /* Instantiating the first side may discover inherited interfaces and
         * reallocate the member table before the second side is examined. */
        Types2Member actual_snapshot = *actual_member;
        Types2Member expected_snapshot = *expected_member;
        actual_member = &actual_snapshot;
        expected_member = &expected_snapshot;
        T2SolverMark mark = t2_solver_mark(shadow->solver);
        T2Type actual = instantiate_member(
                shadow,
                actual_member,
                actual_receiver,
                site
        );
        T2Type expected = instantiate_member(
                shadow,
                expected_member,
                expected_receiver,
                site
        );
        T2Relation relation;
        if (
                actual_member->kind == TYPES2_MEMBER_FIELD
             && (actual_member->writable || expected_member->writable)
        ) {
                relation = t2_solver_unify(
                        shadow->solver,
                        actual,
                        expected,
                        description
                );
        } else if (
                type_contains_dynamic(shadow, actual)
             || type_contains_dynamic(shadow, expected)
        ) {
                default_dynamic_callable_metas(shadow, actual, 0);
                default_dynamic_callable_metas(shadow, expected, 0);
                relation = t2_consistent(shadow->universe, actual, expected);
        } else {
                relation = t2_solver_constrain_subtype(
                        shadow->solver,
                        actual,
                        expected,
                        source_provenance(shadow, site, description)
                );
        }

        bool compatible = relation != T2_RELATION_NO
                       && relation != T2_RELATION_COMPLEXITY
                       && !t2_solver_failed(shadow->solver);
        char *explanation = compatible
                          ? NULL
                          : t2_solver_explain_since(shadow->solver, mark);
        /* Contract checking proves a relation between immutable schemes.  Its
         * fresh instantiation metas and obligations are never part of program
         * inference, even when the proof succeeds. */
        t2_solver_rollback(shadow->solver, mark);
        if (compatible) return true;

        add_diagnostic(
                shadow,
                site,
                TYPES2_DIAGNOSTIC_ERROR,
                code,
                actual,
                expected,
                "%s%s%s",
                description,
                explanation == NULL || *explanation == '\0' ? "" : ": ",
                explanation == NULL ? "" : explanation
        );
        free(explanation);
        return false;
}

static void
validate_class_contracts(
        Types2Shadow *shadow,
        Stmt const *statement,
        int class_id,
        T2Type receiver
)
{
        ClassDefinition const *definition = &statement->class;

        if (definition->super != NULL) {
                T2Type supertype = lower_type(shadow, definition->super);
                Types2Nominal *super_nominal = nominal_from_type(shadow, supertype);
                if (super_nominal != NULL) {
                        int super_class_id = super_nominal->class_id;
                        size_t member_count = shadow->member_count;
                        for (size_t i = 0; i < member_count; ++i) {
                                Types2Member actual = shadow->members[i];
                                if (actual.class_id != class_id) continue;
                                /* Initializers describe the class value's
                                 * construction protocol, not an operation on
                                 * an instance.  Likewise, private members are
                                 * class-mangled by the compiler and therefore
                                 * do not override a same-spelled private member
                                 * in a superclass. */
                                if (
                                        (
                                                actual.kind == TYPES2_MEMBER_METHOD
                                             && strcmp(actual.name, "init") == 0
                                        )
                                     || IsPrivateMember(actual.name)
                                ) continue;
                                Types2Member const *expected = find_direct_member(
                                        shadow,
                                        super_class_id,
                                        actual.name,
                                        actual.kind,
                                        actual.is_static
                                );
                                if (expected == NULL) continue;
                                (void)member_contract_compatible(
                                        shadow,
                                        &actual,
                                        receiver,
                                        expected,
                                        supertype,
                                        actual.declaration,
                                        "invalid-override",
                                        "override does not satisfy the inherited member contract"
                                );
                        }
                }
        }

        for (int ti = 0; ti < vN(definition->traits); ++ti) {
                Expr const *trait_expression = v__(definition->traits, ti);
                T2Type trait = lower_type(shadow, trait_expression);
                Types2Nominal *trait_nominal = nominal_from_type(shadow, trait);
                if (trait_nominal == NULL) continue;
                int trait_class_id = trait_nominal->class_id;
                size_t count = shadow->member_count;
                for (size_t i = 0; i < count; ++i) {
                        Types2Member expected = shadow->members[i];
                        if (
                                expected.class_id != trait_class_id
                             || expected.is_static
                             || IsPrivateMember(expected.name)
                        ) continue;
                        Types2Member const *actual = find_member(
                                shadow,
                                class_id,
                                expected.name,
                                expected.kind,
                                false
                        );
                        bool inherited_default = actual != NULL
                                              && actual->class_id == expected.class_id
                                              && actual->kind == expected.kind
                                              && actual->is_static == expected.is_static
                                              && strcmp(actual->name, expected.name) == 0;
                        if (inherited_default) {
                                if (expected.required) actual = NULL;
                                else continue;
                        }
                        if (actual == NULL) {
                                if (expected.required) {
                                        add_diagnostic(
                                                shadow,
                                                trait_expression,
                                                TYPES2_DIAGNOSTIC_ERROR,
                                                "missing-trait-member",
                                                receiver,
                                                trait,
                                                "class `%s` does not implement required trait member `%s`",
                                                definition->name,
                                                expected.name
                                        );
                                }
                                continue;
                        }
                        (void)member_contract_compatible(
                                shadow,
                                actual,
                                receiver,
                                &expected,
                                trait,
                                actual->declaration,
                                "invalid-trait-member",
                                "member does not satisfy the declared trait contract"
                        );
                }
        }
}

static void
remember_class_contract(
        Types2Shadow *shadow,
        Stmt const *statement,
        int class_id,
        T2Type receiver
)
{
        for (size_t i = 0; i < shadow->class_contract_count; ++i) {
                if (shadow->class_contracts[i].statement == statement) {
                        shadow->class_contracts[i].class_id = class_id;
                        shadow->class_contracts[i].receiver = receiver;
                        return;
                }
        }
        if (!shadow_reserve(
                shadow,
                (void **)&shadow->class_contracts,
                &shadow->class_contract_capacity,
                shadow->class_contract_count + 1,
                sizeof *shadow->class_contracts
        )) return;
        shadow->class_contracts[shadow->class_contract_count++] =
                (Types2ClassContract) {
                        .statement = statement,
                        .class_id = class_id,
                        .receiver = receiver
                };
}

static void
validate_pending_class_contracts(Types2Shadow *shadow)
{
        if (shadow->class_contracts_validated || shadow->failed) return;
        shadow->class_contracts_validated = true;
        for (size_t i = 0; i < shadow->class_contract_count; ++i) {
                Types2ClassContract contract = shadow->class_contracts[i];
                Stmt const *statement = contract.statement;
                if (statement == NULL) continue;
                ClassDefinition const *definition = &statement->class;
                size_t mark = push_type_variables(shadow);
                size_t arity = t2_type_kind(shadow->universe, contract.receiver)
                             == T2_TYPE_NOMINAL
                             ? t2_type_arity(shadow->universe, contract.receiver)
                             : 0;
                size_t declared_arity = (size_t)vN(definition->type_params);
                for (size_t j = 0; j < arity && j < declared_arity; ++j) {
                        Expr const *parameter = v__(definition->type_params, (int)j);
                        (void)add_type_variable(
                                shadow,
                                parameter == NULL ? NULL : parameter->symbol,
                                t2_type_child(shadow->universe, contract.receiver, j)
                        );
                }
                validate_class_contracts(
                        shadow,
                        statement,
                        contract.class_id,
                        contract.receiver
                );
                pop_type_variables(shadow, mark);
        }
}

static T2Type
callable_set_result(
        Types2Shadow *shadow,
        T2Type callable,
        T2Type result
)
{
        T2TypeKind kind = t2_type_kind(shadow->universe, callable);
        if (kind == T2_TYPE_FUNCTION) {
                size_t count = t2_callable_parameter_count(
                        shadow->universe,
                        callable
                );
                T2ParameterSpec *parameters = count == 0
                                            ? NULL
                                            : malloc(count * sizeof *parameters);
                if (count != 0 && parameters == NULL) {
                        shadow->failed = true;
                        return T2_TYPE_INVALID;
                }
                for (size_t i = 0; i < count; ++i) {
                        if (!t2_callable_parameter(
                                shadow->universe,
                                callable,
                                i,
                                &parameters[i]
                        )) {
                                free(parameters);
                                return T2_TYPE_INVALID;
                        }
                }
                T2Type replaced = t2_callable_is_effectful(
                                          shadow->universe,
                                          callable
                                  )
                                ? t2_effectful_callable(
                                          shadow->universe,
                                          parameters,
                                          count,
                                          result,
                                          t2_callable_yield(shadow->universe, callable),
                                          t2_callable_send(shadow->universe, callable)
                                  )
                                : t2_callable(
                        shadow->universe,
                        parameters,
                        count,
                        result,
                        t2_callable_yield(shadow->universe, callable),
                        t2_callable_send(shadow->universe, callable)
                                  );
                free(parameters);
                return replaced;
        }
        if (kind == T2_TYPE_OVERLOAD || kind == T2_TYPE_INTERSECTION) {
                size_t count = t2_type_arity(shadow->universe, callable);
                T2Type *candidates = count == 0
                                   ? NULL
                                   : malloc(count * sizeof *candidates);
                if (count != 0 && candidates == NULL) {
                        shadow->failed = true;
                        return T2_TYPE_INVALID;
                }
                for (size_t i = 0; i < count; ++i) {
                        candidates[i] = callable_set_result(
                                shadow,
                                t2_type_child(shadow->universe, callable, i),
                                result
                        );
                        if (candidates[i] == T2_TYPE_INVALID) {
                                free(candidates);
                                return T2_TYPE_INVALID;
                        }
                }
                T2Type replaced = kind == T2_TYPE_OVERLOAD
                                ? t2_overload(shadow->universe, candidates, count)
                                : t2_intersection(shadow->universe, candidates, count);
                free(candidates);
                return replaced;
        }
        return T2_TYPE_INVALID;
}

static T2Scheme *
scheme_with_body(
        Types2Shadow *shadow,
        T2Scheme const *source,
        T2Type body
)
{
        size_t quantifier_count = t2_scheme_quantifier_count(source);
        size_t predicate_count = t2_scheme_predicate_count(source);
        T2Quantifier *quantifiers = quantifier_count == 0
                                  ? NULL
                                  : malloc(quantifier_count * sizeof *quantifiers);
        T2Predicate *predicates = predicate_count == 0
                                ? NULL
                                : malloc(predicate_count * sizeof *predicates);
        if (
                (quantifier_count != 0 && quantifiers == NULL)
             || (predicate_count != 0 && predicates == NULL)
        ) {
                free(quantifiers);
                free(predicates);
                shadow->failed = true;
                return NULL;
        }
        for (size_t i = 0; i < quantifier_count; ++i) {
                if (!t2_scheme_quantifier(source, i, &quantifiers[i])) {
                        free(quantifiers);
                        free(predicates);
                        return NULL;
                }
        }
        for (size_t i = 0; i < predicate_count; ++i) {
                if (!t2_scheme_predicate(source, i, &predicates[i])) {
                        free(quantifiers);
                        free(predicates);
                        return NULL;
                }
        }
        T2Scheme *scheme = t2_scheme_new(
                shadow->universe,
                quantifiers,
                quantifier_count,
                body,
                predicates,
                predicate_count
        );
        free(quantifiers);
        free(predicates);
        return scheme;
}

static T2Type
constructor_receiver_for_scheme(
        Types2Shadow *shadow,
        int class_id,
        T2Scheme const *scheme,
        size_t class_arity
)
{
        T2Type primitive = primitive_class_type(shadow, class_id);
        if (primitive != T2_TYPE_INVALID) return primitive;
        Types2Nominal *nominal = find_class_nominal(shadow, class_id);
        if (nominal == NULL || nominal->arity != class_arity) {
                return T2_TYPE_INVALID;
        }
        T2Type *arguments = class_arity == 0
                          ? NULL
                          : malloc(class_arity * sizeof *arguments);
        if (class_arity != 0 && arguments == NULL) {
                shadow->failed = true;
                return T2_TYPE_INVALID;
        }
        for (size_t i = 0; i < class_arity; ++i) {
                T2Quantifier quantifier;
                if (!t2_scheme_quantifier(scheme, i, &quantifier)) {
                        free(arguments);
                        return T2_TYPE_INVALID;
                }
                arguments[i] = t2_variable(
                        shadow->universe,
                        quantifier.kind,
                        quantifier.id
                );
        }
        T2Type receiver = t2_nominal(
                shadow->universe,
                nominal->symbol,
                arguments,
                class_arity
        );
        free(arguments);
        return receiver;
}

static Types2Member const *
find_constructor_initializer(Types2Shadow *shadow, int class_id)
{
        int current = class_id;
        for (unsigned depth = 0; current >= 0 && depth < 256; ++depth) {
                (void)ensure_class_interface(shadow, current);
                Types2Member const *initializer = find_direct_member(
                        shadow,
                        current,
                        "init",
                        TYPES2_MEMBER_METHOD,
                        false
                );
                if (initializer != NULL) return initializer;
                if (shadow->ty == NULL) return NULL;
                Class *class = class_get(shadow->ty, current);
                if (
                        class == NULL
                     || class->super == NULL
                     || class->super->i == current
                ) return NULL;
                current = class->super->i;
        }
        return NULL;
}

static void
install_class_constructor(
        Types2Shadow *shadow,
        ClassDefinition const *definition,
        int class_id,
        T2Type fallback_receiver,
        T2Quantifier const *fallback_quantifiers,
        size_t class_arity
)
{
        if (definition == NULL || definition->var == NULL || definition->is_trait) {
                return;
        }

        Types2Member const *initializer = find_constructor_initializer(
                shadow,
                class_id
        );
        T2Scheme *constructor = NULL;
        T2Type instance = fallback_receiver;
        if (initializer != NULL && initializer->scheme != NULL) {
                T2Type receiver = constructor_receiver_for_scheme(
                        shadow,
                        class_id,
                        initializer->scheme,
                        initializer->class_arity
                );
                instance = receiver;
                T2Type body = callable_set_result(
                        shadow,
                        t2_scheme_body(initializer->scheme),
                        receiver
                );
                if (body != T2_TYPE_INVALID) {
                        constructor = scheme_with_body(
                                shadow,
                                initializer->scheme,
                                body
                        );
                }
        } else {
                T2Type body = t2_callable(
                        shadow->universe,
                        NULL,
                        0,
                        fallback_receiver,
                        t2_primitive(shadow->universe, T2_TYPE_NEVER),
                        t2_primitive(shadow->universe, T2_TYPE_NIL)
                );
                constructor = t2_scheme_new(
                        shadow->universe,
                        fallback_quantifiers,
                        class_arity,
                        body,
                        NULL,
                        0
                );
        }
        if (constructor == NULL) return;

        T2Type value_body = t2_type_value(
                shadow->universe,
                instance,
                t2_scheme_body(constructor)
        );
        T2Scheme *class_value = value_body == T2_TYPE_INVALID
                              ? NULL
                              : scheme_with_body(
                                      shadow,
                                      constructor,
                                      value_body
                                );
        t2_scheme_free(constructor);
        constructor = class_value;
        if (constructor == NULL) return;

        Types2Binding *binding = ensure_binding(shadow, definition->var);
        if (binding == NULL) {
                t2_scheme_free(constructor);
                return;
        }
        t2_scheme_free(binding->scheme);
        binding->scheme = constructor;
        binding->type = t2_scheme_body(constructor);
        binding->refinement = T2_TYPE_INVALID;
        binding->mutable = false;
        binding->initialized = true;
        binding->forward = false;
}

static T2Type
infer_class_definition(Types2Shadow *shadow, Stmt const *statement)
{
        ClassDefinition const *definition = &statement->class;
        bool is_tag = statement->type == STATEMENT_TAG_DEFINITION;
        int tag_id = is_tag ? definition->symbol : -1;
        Class *runtime_class = is_tag && shadow->ty != NULL
                             ? tags_get_class(shadow->ty, tag_id)
                             : NULL;
        int class_id = is_tag
                     ? (runtime_class == NULL ? CLASS_TAG : runtime_class->i)
                     : definition->symbol;
        size_t declared_arity = (size_t)vN(definition->type_params);
        if (is_tag && declared_arity > 1) {
                add_diagnostic(
                        shadow,
                        (Expr const *)statement,
                        TYPES2_DIAGNOSTIC_ERROR,
                        "tag-arity",
                        T2_TYPE_INVALID,
                        T2_TYPE_INVALID,
                        "tag `%s` declares %zu payload type parameters; exactly one is supported",
                        definition->name,
                        declared_arity
                );
        }
        size_t arity = is_tag ? 1 : declared_arity;
        bool implicit_tag_payload = is_tag && declared_arity == 0;
        uint32_t outer_level = shadow->level;
        shadow->level = outer_level + 1;
        uint32_t class_level = shadow->level;
        size_t type_mark = push_type_variables(shadow);
        T2Quantifier *quantifiers = arity == 0
                                  ? NULL
                                  : malloc(arity * sizeof *quantifiers);
        T2Type *arguments = arity == 0 ? NULL : malloc(arity * sizeof *arguments);
        if (arity != 0 && (quantifiers == NULL || arguments == NULL)) {
                free(quantifiers);
                free(arguments);
                shadow->failed = true;
                goto Done;
        }
        for (size_t i = 0; i < arity; ++i) {
                Expr const *parameter = implicit_tag_payload
                                      ? NULL
                                      : i < declared_arity
                                        ? v__(definition->type_params, (int)i)
                                        : NULL;
                T2VariableKind kind = parameter != NULL
                                   && parameter->symbol != NULL
                                   && SymbolIsParamPack(parameter->symbol)
                                    ? T2_VARIABLE_PACK
                                    : T2_VARIABLE_QUANTIFIED;
                uint32_t id = shadow->next_quantified_id++;
                arguments[i] = t2_variable(shadow->universe, kind, id);
                quantifiers[i] = (T2Quantifier) { .id = id, .kind = kind };
                if (parameter != NULL) {
                        (void)add_type_variable(shadow, parameter->symbol, arguments[i]);
                }
        }
        T2Type receiver;
        if (is_tag) {
                Types2Nominal *nominal = ensure_tag_nominal(
                        shadow,
                        tag_id,
                        definition->name
                );
                receiver = nominal == NULL
                         ? t2_primitive(shadow->universe, T2_TYPE_ERROR)
                         : apply_nominal(
                                 shadow,
                                 nominal,
                                 arguments,
                                 arity,
                                 (Expr const *)statement
                           );
        } else {
                receiver = class_receiver_type(
                        shadow,
                        class_id,
                        arguments,
                        arity,
                        (Expr const *)statement
                );
        }

        int previous_member_class = shadow->member_class_id;
        T2Type previous_member_receiver = shadow->member_receiver;
        shadow->member_class_id = class_id;
        shadow->member_receiver = receiver;

        if (!is_tag) {
                (void)ensure_class_interface(shadow, class_id);
                install_class_constructor(
                        shadow,
                        definition,
                        class_id,
                        receiver,
                        quantifiers,
                        arity
                );
        }

        infer_member_fields(
                shadow,
                class_id,
                &definition->fields,
                false,
                quantifiers,
                arity
        );
        infer_member_fields(
                shadow,
                class_id,
                &definition->s_fields,
                true,
                quantifiers,
                arity
        );
        infer_member_functions(
                shadow,
                class_id,
                &definition->methods,
                TYPES2_MEMBER_METHOD,
                false,
                quantifiers,
                arity,
                class_level
        );
        infer_member_functions(
                shadow,
                class_id,
                &definition->getters,
                TYPES2_MEMBER_GETTER,
                false,
                quantifiers,
                arity,
                class_level
        );
        infer_member_functions(
                shadow,
                class_id,
                &definition->setters,
                TYPES2_MEMBER_SETTER,
                false,
                quantifiers,
                arity,
                class_level
        );
        infer_member_functions(
                shadow,
                class_id,
                &definition->s_methods,
                TYPES2_MEMBER_METHOD,
                true,
                quantifiers,
                arity,
                class_level
        );
        infer_member_functions(
                shadow,
                class_id,
                &definition->s_getters,
                TYPES2_MEMBER_GETTER,
                true,
                quantifiers,
                arity,
                class_level
        );
        infer_member_functions(
                shadow,
                class_id,
                &definition->s_setters,
                TYPES2_MEMBER_SETTER,
                true,
                quantifiers,
                arity,
                class_level
        );
        if (!is_tag) install_class_constructor(
                shadow,
                definition,
                class_id,
                receiver,
                quantifiers,
                arity
        );
        remember_class_contract(shadow, statement, class_id, receiver);
        Types2Nominal *completed = is_tag
                                 ? find_tag_nominal(shadow, tag_id)
                                 : find_class_nominal(shadow, class_id);
        if (completed != NULL) completed->complete = true;
        Types2Nominal *class_nominal = find_class_nominal(shadow, class_id);
        if (class_nominal != NULL) class_nominal->complete = true;
        shadow->member_class_id = previous_member_class;
        shadow->member_receiver = previous_member_receiver;
        free(quantifiers);
        free(arguments);
        pop_type_variables(shadow, type_mark);
        shadow->level = outer_level;
        return receiver;

Done:
        pop_type_variables(shadow, type_mark);
        shadow->level = outer_level;
        return t2_primitive(shadow->universe, T2_TYPE_ERROR);
}

static Types2Flow
infer_statement(Types2Shadow *shadow, Stmt const *statement)
{
        T2Type nil = t2_primitive(shadow->universe, T2_TYPE_NIL);
        T2Type never = t2_primitive(shadow->universe, T2_TYPE_NEVER);
        if (statement == NULL) return flow_fallthrough(shadow, nil);

        Types2Flow result = flow_fallthrough(shadow, nil);
        switch (statement->type) {
        case STATEMENT_NULL:
        case STATEMENT_IMPORT:
        case STATEMENT_USE:
        case STATEMENT_EXPORT:
        case STATEMENT_DROP:
        case STATEMENT_CLEANUP:
                break;

        case STATEMENT_EXPRESSION:
                result.value = infer_expression(shadow, statement->expression);
                if (t2_type_kind(shadow->universe, result.value) == T2_TYPE_NEVER) {
                        result.outcomes = TYPES2_FLOW_THROWS;
                }
                break;

        case STATEMENT_BLOCK:
        case STATEMENT_MULTI:
        {
                result = flow_fallthrough(shadow, nil);
                result.returns = never;
                for (int i = 0; i < vN(statement->statements); ++i) {
                        if ((result.outcomes & TYPES2_FLOW_FALLS_THROUGH) == 0) break;
                        Types2Flow next = infer_statement(
                                shadow,
                                v__(statement->statements, i)
                        );
                        unsigned prior_terminal = result.outcomes
                                                & ~TYPES2_FLOW_FALLS_THROUGH;
                        T2Type prior_returns = result.returns;
                        result = next;
                        result.outcomes |= prior_terminal;
                        result.returns = t2_join(
                                shadow->universe,
                                prior_returns,
                                next.returns
                        );
                }
                break;
        }

        case STATEMENT_DEFINITION:
        {
                Symbol const *target_symbol = is_named_binding_target(
                                                   statement->target
                                               )
                                            ? statement->target->symbol
                                            : NULL;
                size_t environment_count = 0;
                T2Type *environment = environment_types(
                        shadow,
                        target_symbol,
                        &environment_count
                );
                T2SolverMark scope = t2_solver_mark(shadow->solver);
                T2Type value = infer_expression(shadow, statement->value);
                bool declared_mutable = !statement->cnst
                                     && (
                                                !is_named_binding_target(
                                                        statement->target
                                                 )
                                             || !SymbolIsConst(statement->target->symbol)
                                        );
                T2Type stored = declared_mutable ? relax_literal(shadow, value) : value;
                Expr const *annotation_expression = is_named_binding_target(
                                                            statement->target
                                                    )
                                                  ? lvalue_annotation_expression(
                                                            statement->target
                                                    )
                                                  : NULL;
                if (annotation_expression != NULL) {
                        T2Type contextual = node_type(
                                shadow,
                                annotation_expression
                        );
                        if (contextual == T2_TYPE_INVALID) {
                                contextual = lower_type(
                                        shadow,
                                        annotation_expression
                                );
                        }
                        if (contextual_fresh_literal(
                                shadow,
                                statement->value,
                                contextual
                        )) stored = contextual;
                }
                bool valid = assign_lvalue(shadow, statement->target, stored, true);
                if (
                        valid
                     && is_named_binding_target(statement->target)
                ) {
                        Types2Binding *binding = find_binding(
                                shadow,
                                statement->target->symbol
                        );
                        if (binding != NULL) {
                                binding->mutable = declared_mutable;
                                if (!binding->mutable) {
                                        (void)generalize_binding(
                                                shadow,
                                                binding,
                                                binding->type,
                                                environment,
                                                environment_count,
                                                shadow->level,
                                                expression_is_expansive(statement->value),
                                                scope
                                        );
                                } else {
                                        t2_solver_commit(shadow->solver, scope);
                                }
                        } else {
                                t2_solver_commit(shadow->solver, scope);
                        }
                } else {
                        if (!valid) {
                                (void)t2_solver_cancel_obligations_since(
                                        shadow->solver,
                                        scope
                                );
                        }
                        t2_solver_commit(shadow->solver, scope);
                }
                result.value = valid
                             ? value
                             : t2_primitive(shadow->universe, T2_TYPE_ERROR);
                free(environment);
                break;
        }

        case STATEMENT_FUNCTION_DEFINITION:
        case STATEMENT_OPERATOR_DEFINITION:
        case STATEMENT_PATTERN_DEFINITION:
        {
                Symbol const *target_symbol = statement->target == NULL
                                           ? NULL
                                           : statement->target->symbol;
                size_t environment_count = 0;
                T2Type *environment = environment_types(
                        shadow,
                        target_symbol,
                        &environment_count
                );
                size_t pending_before = t2_solver_pending_obligations(
                        shadow->solver
                );
                T2SolverMark scope = t2_solver_mark(shadow->solver);
                Types2Binding *binding = statement->target == NULL
                                       ? NULL
                                       : find_binding(
                                               shadow,
                                               statement->target->symbol
                                         );
                T2Type previous = T2_TYPE_INVALID;
                bool append_overload = binding != NULL
                                    && binding->initialized
                                    && !binding->forward;
                if (append_overload) {
                        previous = instantiate_binding(
                                shadow,
                                binding,
                                statement->target
                        );
                        append_overload = is_callable_set(shadow, previous);
                }
                T2Type value = infer_function_expression(shadow, statement->value);
                size_t pending_inferred = t2_solver_pending_obligations(
                        shadow->solver
                );
                append_overload &= is_callable_set(shadow, value);
                bool valid;
                T2Type stored = value;
                if (append_overload) {
                        /* Function inference creates parameter, self, and
                         * recursive bindings, so the vector pointer captured
                         * before inference is no longer stable. */
                        binding = find_binding(shadow, target_symbol);
                        append_overload = binding != NULL;
                }
                if (append_overload) {
                        stored = t2_overload(
                                shadow->universe,
                                (T2Type[]) { previous, value },
                                2
                        );
                        valid = stored != T2_TYPE_INVALID;
                        if (valid) {
                                binding->type = stored;
                                binding->initialized = true;
                                binding->forward = false;
                                set_node_type(shadow, statement->target, stored);
                        }
                } else {
                        valid = assign_lvalue(
                                shadow,
                                statement->target,
                                value,
                                true
                        );
                }
                if (
                        valid
                     && is_named_binding_target(statement->target)
                ) {
                        Types2Binding *binding = find_binding(
                                shadow,
                                statement->target->symbol
                        );
                        if (binding != NULL) {
                                binding->mutable = false;
                                bool generalized = generalize_binding(
                                        shadow,
                                        binding,
                                        stored,
                                        environment,
                                        environment_count,
                                        shadow->level,
                                        false,
                                        scope
                                );
                                if (shadow->log != NULL && !shadow->failed) {
                                        log_prefix(shadow, "binding_scheme");
                                        fputs(",\"binding\":", shadow->log);
                                        json_string(
                                                shadow->log,
                                                statement->target->identifier == NULL
                                                    ? "<function>"
                                                    : statement->target->identifier
                                        );
                                        fprintf(
                                                shadow->log,
                                                ",\"line\":%u,\"pending_before\":%zu"
                                                ",\"pending_inferred\":%zu"
                                                ",\"pending_after\":%zu"
                                                ",\"quantifiers\":%zu,\"predicates\":%zu",
                                                statement->start.line + 1,
                                                pending_before,
                                                pending_inferred,
                                                t2_solver_pending_obligations(
                                                        shadow->solver
                                                ),
                                                generalized
                                                    ? t2_scheme_quantifier_count(
                                                            binding->scheme
                                                      )
                                                    : 0,
                                                generalized
                                                    ? t2_scheme_predicate_count(
                                                            binding->scheme
                                                      )
                                                    : 0
                                        );
                                        fputs(",\"type\":", shadow->log);
                                        if (!generalized) fputs("null", shadow->log);
                                        else log_native_type(
                                                shadow,
                                                t2_scheme_body(binding->scheme)
                                        );
                                        log_end(shadow);
                                }
                                if (
                                        generalized
                                     && statement->type == STATEMENT_OPERATOR_DEFINITION
                                ) replace_operator_expression_scheme(
                                        shadow,
                                        statement->value,
                                        binding->scheme
                                );
                        } else {
                                t2_solver_commit(shadow->solver, scope);
                        }
                } else {
                        if (!valid) {
                                (void)t2_solver_cancel_obligations_since(
                                        shadow->solver,
                                        scope
                                );
                        }
                        t2_solver_commit(shadow->solver, scope);
                }
                result.value = stored;
                free(environment);
                break;
        }

        case STATEMENT_RETURN:
        case STATEMENT_GENERATOR_RETURN:
        {
                T2Type value = function_return_values(shadow, &statement->returns);
                bool generator_return = statement->type == STATEMENT_GENERATOR_RETURN;
                if (shadow->function_count == 0) {
                        add_diagnostic(
                                shadow,
                                (Expr const *)statement,
                                TYPES2_DIAGNOSTIC_ERROR,
                                "return-context",
                                value,
                                T2_TYPE_INVALID,
                                "return is only valid inside a function"
                        );
                } else {
                        Types2FunctionFrame *frame = &shadow->functions[
                                shadow->function_count - 1
                        ];
                        if (
                                !generator_return
                             && frame->inferred_result
                             && is_dynamic_type(shadow, value)
                        ) default_dynamic_callable_metas(
                                shadow,
                                frame->result,
                                0
                        );
                        if (!generator_return) {
                                (void)constrain_type(
                                        shadow,
                                        (Expr const *)statement,
                                        value,
                                        frame->result,
                                        "return-type",
                                        "returned value does not satisfy the function result type"
                                );
                        }
                }
                result = (Types2Flow) {
                        .outcomes = TYPES2_FLOW_RETURNS,
                        .value = never,
                        .returns = generator_return ? never : value
                };
                break;
        }

        case STATEMENT_IF:
        case STATEMENT_IF_LET:
        {
                size_t part_count = (size_t)vN(statement->_if.parts);
                T2Type *conditions = part_count == 0
                                   ? NULL
                                   : malloc(part_count * sizeof *conditions);
                if (part_count != 0 && conditions == NULL) {
                        shadow->failed = true;
                        break;
                }
                for (size_t i = 0; i < part_count; ++i) {
                        struct condpart const *part = v__(
                                statement->_if.parts,
                                (int)i
                        );
                        conditions[i] = infer_expression(shadow, part->e);
                }
                size_t binding_mark = shadow->binding_count;
                T2Type *before = snapshot_refinements(shadow, binding_mark);
                if (binding_mark != 0 && before == NULL) {
                        free(conditions);
                        break;
                }
                bool negated = statement->_if.neg;
                for (size_t i = 0; i < part_count; ++i) {
                        struct condpart const *part = v__(
                                statement->_if.parts,
                                (int)i
                        );
                        apply_condition_refinements(shadow, part->e, !negated);
                        if (part->target != NULL && !negated) {
                                (void)infer_refutable_pattern(
                                        shadow,
                                        part->target,
                                        conditions[i]
                                );
                        }
                }
                Types2Flow then_flow = infer_statement(shadow, statement->_if.then);
                T2Type *then_bindings = snapshot_effective_types(
                        shadow,
                        binding_mark
                );
                restore_refinements(shadow, before, binding_mark);
                if (part_count == 1) {
                        apply_condition_refinements(
                                shadow,
                                v__(statement->_if.parts, 0)->e,
                                negated
                        );
                }
                Types2Flow else_flow = statement->_if._else == NULL
                                     ? flow_fallthrough(shadow, nil)
                                     : infer_statement(shadow, statement->_if._else);
                T2Type *else_bindings = snapshot_effective_types(
                        shadow,
                        binding_mark
                );
                restore_refinements(shadow, before, binding_mark);
                if (
                        (binding_mark == 0 || then_bindings != NULL)
                     && (binding_mark == 0 || else_bindings != NULL)
                ) merge_branch_refinements(
                        shadow,
                        then_bindings,
                        (then_flow.outcomes & TYPES2_FLOW_FALLS_THROUGH) != 0,
                        else_bindings,
                        (else_flow.outcomes & TYPES2_FLOW_FALLS_THROUGH) != 0,
                        binding_mark
                );
                for (size_t i = 0; negated && i < part_count; ++i) {
                        struct condpart const *part = v__(
                                statement->_if.parts,
                                (int)i
                        );
                        if (part->target != NULL) {
                                (void)infer_refutable_pattern(
                                        shadow,
                                        part->target,
                                        conditions[i]
                                );
                        }
                }
                free(conditions);
                free(before);
                free(then_bindings);
                free(else_bindings);
                result = flow_join(shadow, then_flow, else_flow);
                break;
        }

        case STATEMENT_FOR_LOOP:
        {
                (void)infer_statement(shadow, statement->for_loop.init);
                if (statement->for_loop.cond != NULL) {
                        (void)infer_expression(shadow, statement->for_loop.cond);
                }
                Types2Flow body = infer_statement(shadow, statement->for_loop.body);
                if (statement->for_loop.next != NULL) {
                        (void)infer_expression(shadow, statement->for_loop.next);
                }
                result = (Types2Flow) {
                        .outcomes = TYPES2_FLOW_FALLS_THROUGH
                                  | (body.outcomes & (TYPES2_FLOW_RETURNS | TYPES2_FLOW_THROWS)),
                        .value = nil,
                        .returns = body.returns
                };
                break;
        }

        case STATEMENT_EACH_LOOP:
        {
                T2Type collection = infer_expression(shadow, statement->each.array);
                T2Type element = iterated_type(
                        shadow,
                        collection,
                        statement->each.array
                );
                if (
                        statement->each.target != NULL
                     && statement->each.target->type == EXPRESSION_LIST
                     && vN(statement->each.target->es) > 1
                     && !(
                                t2_type_kind(shadow->universe, element) == T2_TYPE_TUPLE
                             && t2_type_arity(shadow->universe, element)
                                == (size_t)vN(statement->each.target->es)
                        )
                ) {
                        size_t count = (size_t)vN(statement->each.target->es);
                        T2Type *items = malloc(count * sizeof *items);
                        if (items == NULL) {
                                shadow->failed = true;
                                break;
                        }
                        items[0] = element;
                        items[1] = t2_primitive(shadow->universe, T2_TYPE_INT);
                        for (size_t i = 2; i < count; ++i) {
                                items[i] = t2_primitive(
                                        shadow->universe,
                                        T2_TYPE_DYNAMIC
                                );
                        }
                        element = t2_tuple(shadow->universe, items, count);
                        free(items);
                }
                (void)assign_lvalue(shadow, statement->each.target, element, true);
                if (statement->each._if != NULL) {
                        (void)infer_expression(shadow, statement->each._if);
                }
                if (statement->each._while != NULL) {
                        (void)infer_expression(shadow, statement->each._while);
                }
                Types2Flow body = infer_statement(shadow, statement->each.body);
                result = (Types2Flow) {
                        .outcomes = TYPES2_FLOW_FALLS_THROUGH
                                  | (body.outcomes & (TYPES2_FLOW_RETURNS | TYPES2_FLOW_THROWS)),
                        .value = nil,
                        .returns = body.returns
                };
                break;
        }

        case STATEMENT_WHILE:
        {
                for (int i = 0; i < vN(statement->_while.parts); ++i) {
                        struct condpart const *part = v__(statement->_while.parts, i);
                        T2Type condition = infer_expression(shadow, part->e);
                        if (part->target != NULL) {
                                (void)infer_refutable_pattern(
                                        shadow,
                                        part->target,
                                        condition
                                );
                        }
                }
                Types2Flow body = infer_statement(shadow, statement->_while.block);
                result = (Types2Flow) {
                        .outcomes = TYPES2_FLOW_FALLS_THROUGH
                                  | (body.outcomes & (TYPES2_FLOW_RETURNS | TYPES2_FLOW_THROWS)),
                        .value = nil,
                        .returns = body.returns
                };
                break;
        }

        case STATEMENT_MATCH:
        case STATEMENT_WHILE_MATCH:
        {
                T2Type subject = infer_expression(shadow, statement->match.e);
                T2Type remaining = subject;
                result = statement->type == STATEMENT_WHILE_MATCH
                       ? flow_fallthrough(shadow, nil)
                       : (Types2Flow) {
                               .outcomes = 0,
                               .value = never,
                               .returns = never
                         };
                for (int i = 0; i < vN(statement->match.patterns); ++i) {
                        size_t binding_mark = shadow->binding_count;
                        Expr const *pattern = v__(statement->match.patterns, i);
                        bool covered = t2_type_kind(
                                               shadow->universe,
                                               remaining
                                       ) == T2_TYPE_NEVER;
                        if (covered) {
                                add_diagnostic(
                                        shadow,
                                        pattern,
                                        TYPES2_DIAGNOSTIC_WARNING,
                                        "unreachable-pattern",
                                        subject,
                                        T2_TYPE_INVALID,
                                        "previous match arms already cover the subject type"
                                );
                        }
                        bool reachable = infer_refutable_pattern(
                                shadow,
                                pattern,
                                covered ? subject : remaining
                        );
                        bool guarded = i < vN(statement->match.conds)
                                    && v__(statement->match.conds, i) != NULL;
                        if (guarded) {
                                Expr const *condition = v__(statement->match.conds, i);
                                (void)infer_expression(shadow, condition);
                        }
                        Types2Flow arm = infer_statement(
                                shadow,
                                v__(statement->match.statements, i)
                        );
                        if (reachable && !covered) {
                                result = flow_join(shadow, result, arm);
                                if (!guarded) {
                                        bool certain = false;
                                        T2Type coverage = pattern_coverage(
                                                shadow,
                                                pattern,
                                                remaining,
                                                &certain
                                        );
                                        if (certain) {
                                                remaining = subtract_pattern_coverage(
                                                        shadow,
                                                        remaining,
                                                        coverage,
                                                        pattern_is_catch_all(pattern)
                                                );
                                        }
                                }
                        }
                        for (size_t j = binding_mark; j < shadow->binding_count; ++j) {
                                if (!shadow->bindings[j].persistent) {
                                        shadow->bindings[j].active = false;
                                }
                        }
                }
                if (
                        statement->type == STATEMENT_MATCH
                     && t2_type_kind(shadow->universe, remaining) != T2_TYPE_NEVER
                ) {
                        if (match_domain_is_closed(shadow, subject)) {
                                add_diagnostic(
                                        shadow,
                                        (Expr const *)statement,
                                        TYPES2_DIAGNOSTIC_WARNING,
                                        "non-exhaustive-match",
                                        remaining,
                                        T2_TYPE_INVALID,
                                        "match does not cover every reachable closed-domain value"
                                );
                        }
                        result = flow_join(shadow, result, (Types2Flow) {
                                .outcomes = TYPES2_FLOW_THROWS,
                                .value = never,
                                .returns = never
                        });
                }
                if (statement->type == STATEMENT_WHILE_MATCH) {
                        result.outcomes |= TYPES2_FLOW_FALLS_THROUGH;
                        result.value = nil;
                }
                break;
        }

        case STATEMENT_TRY:
        case STATEMENT_TRY_CLEAN:
        {
                result = infer_statement(shadow, statement->try.s);
                for (int i = 0; i < vN(statement->try.handlers); ++i) {
                        T2Type thrown = t2_primitive(shadow->universe, T2_TYPE_DYNAMIC);
                        if (i < vN(statement->try.patterns)) {
                                (void)infer_refutable_pattern(
                                        shadow,
                                        v__(statement->try.patterns, i),
                                        thrown
                                );
                        }
                        result = flow_join(
                                shadow,
                                result,
                                infer_statement(shadow, v__(statement->try.handlers, i))
                        );
                }
                if (statement->try.finally != NULL) {
                        Types2Flow final = infer_statement(shadow, statement->try.finally);
                        result.returns = t2_join(
                                shadow->universe,
                                result.returns,
                                final.returns
                        );
                        result.outcomes |= final.outcomes & ~TYPES2_FLOW_FALLS_THROUGH;
                        if ((final.outcomes & TYPES2_FLOW_FALLS_THROUGH) == 0) {
                                result.outcomes = final.outcomes;
                                result.value = final.value;
                        }
                }
                break;
        }

        case STATEMENT_BREAK:
                if (statement->expression != NULL) {
                        result.value = infer_expression(shadow, statement->expression);
                } else result.value = nil;
                result.outcomes = TYPES2_FLOW_BREAKS;
                result.returns = never;
                break;
        case STATEMENT_CONTINUE:
        case STATEMENT_NEXT:
                result = (Types2Flow) {
                        .outcomes = TYPES2_FLOW_CONTINUES,
                        .value = never,
                        .returns = never
                };
                break;
        case STATEMENT_HALT:
                result = (Types2Flow) {
                        .outcomes = TYPES2_FLOW_THROWS,
                        .value = never,
                        .returns = never
                };
                break;

        case STATEMENT_DEFER:
                if (statement->expression != NULL) {
                        (void)infer_expression(shadow, statement->expression);
                }
                break;

        case STATEMENT_TYPE_DEFINITION:
        {
                register_type_alias(shadow, &statement->class);
                Types2Alias *alias = find_alias(
                        shadow,
                        statement->class.var
                );
                result.value = resolve_alias(
                        shadow,
                        alias,
                        (Expr const *)statement
                );
                break;
        }
        case STATEMENT_CLASS_DEFINITION:
        case STATEMENT_TAG_DEFINITION:
                result.value = infer_class_definition(shadow, statement);
                break;
        case STATEMENT_MACRO_DEFINITION:
        case STATEMENT_FUN_MACRO_DEFINITION:
                defer_node(
                        shadow,
                        TYPES2_DEFER_MACRO_DEFINITION,
                        (Expr const *)statement,
                        NULL
                );
                break;
        case STATEMENT_SET_TYPE:
                defer_node(
                        shadow,
                        TYPES2_DEFER_SET_TYPE,
                        (Expr const *)statement,
                        NULL
                );
                break;

        default:
                shadow->unsupported_nodes += 1;
                shadow->unsupported_constructs[statement->type] += 1;
                break;
        }

        set_node_type(shadow, (Expr const *)statement, result.value);
        return result;
}

static Expr *
observe_expression(Expr *expr, Scope *scope, void *user)
{
        Types2Shadow *shadow = ((Types2Walk *)user)->shadow;
        (void)scope;

        shadow->role_visits[0] += 1;
        (void)remember_node(shadow, expr, expr->type, TYPES2_ROLE_EXPRESSION);

        return expr;
}

static Expr *
observe_type(Expr *expr, Scope *scope, void *user)
{
        Types2Shadow *shadow = ((Types2Walk *)user)->shadow;
        (void)scope;

        shadow->role_visits[1] += 1;
        (void)remember_node(shadow, expr, expr->type, TYPES2_ROLE_TYPE);

        return expr;
}

static Expr *
observe_pattern(Expr *expr, Scope *scope, void *user)
{
        Types2Shadow *shadow = ((Types2Walk *)user)->shadow;
        (void)scope;

        shadow->role_visits[2] += 1;
        (void)remember_node(shadow, expr, expr->type, TYPES2_ROLE_PATTERN);

        return expr;
}

static Expr *
observe_lvalue(Expr *expr, bool declaration, Scope *scope, void *user)
{
        Types2Shadow *shadow = ((Types2Walk *)user)->shadow;
        (void)declaration;
        (void)scope;

        shadow->role_visits[3] += 1;
        (void)remember_node(shadow, expr, expr->type, TYPES2_ROLE_LVALUE);

        return expr;
}

static Stmt *
observe_statement(Stmt *stmt, Scope *scope, void *user)
{
        Types2Shadow *shadow = ((Types2Walk *)user)->shadow;
        (void)scope;

        shadow->role_visits[4] += 1;
        (void)remember_node(shadow, stmt, stmt->type, TYPES2_ROLE_STATEMENT);

        return stmt;
}

static void
register_forward_binding(Types2Shadow *shadow, Symbol const *symbol, bool mutable)
{
        Types2Binding *binding = ensure_binding(shadow, symbol);
        if (binding == NULL) return;
        binding->active = true;
        binding->mutable = mutable;
        if (binding->initialized) return;
        binding->type = t2_solver_new_meta(
                shadow->solver,
                mutable ? T2_VARIABLE_WEAK : T2_VARIABLE_FLEXIBLE,
                shadow->level,
                symbol->identifier == NULL ? "forward declaration" : symbol->identifier
        );
        binding->initialized = binding->type != T2_TYPE_INVALID;
        binding->forward = binding->initialized;
}

static void
register_type_alias(Types2Shadow *shadow, ClassDefinition const *definition)
{
        if (
                definition == NULL
             || definition->var == NULL
             || find_alias(shadow, definition->var) != NULL
        ) return;
        if (!shadow_reserve(
                shadow,
                (void **)&shadow->aliases,
                &shadow->alias_capacity,
                shadow->alias_count + 1,
                sizeof *shadow->aliases
        )) return;
        shadow->aliases[shadow->alias_count++] = (Types2Alias) {
                .symbol = definition->var,
                .definition = definition,
                .binder = t2_universe_fresh_recursive_binder(shadow->universe),
                .arity = (size_t)vN(definition->type_params),
                .state = TYPES2_ALIAS_UNRESOLVED
        };
}

static void
register_nominal_hierarchy(
        Types2Shadow *shadow,
        ClassDefinition const *definition,
        Types2Nominal const *nominal
)
{
        if (definition == NULL || nominal == NULL) return;
        uint64_t nominal_symbol = nominal->symbol;
        size_t arity = nominal->arity;
        size_t declared_arity = (size_t)vN(definition->type_params);
        size_t type_mark = push_type_variables(shadow);
        for (size_t i = 0; i < arity && i < declared_arity; ++i) {
                Expr const *parameter = v__(definition->type_params, (int)i);
                (void)add_type_variable(
                        shadow,
                        parameter->symbol,
                        t2_nominal_type_parameter(shadow->universe, (uint32_t)i)
                );
        }

        size_t count = (definition->super == NULL ? 0 : 1)
                     + (size_t)vN(definition->traits);
        for (size_t i = 0; i < count; ++i) {
                Expr const *declaration = i == 0 && definition->super != NULL
                                        ? definition->super
                                        : v__(
                                                definition->traits,
                                                (int)(i - (definition->super != NULL))
                                          );
                T2Type supertype = lower_type(shadow, declaration);
                if (t2_type_kind(shadow->universe, supertype) != T2_TYPE_NOMINAL) {
                        defer_node(shadow, TYPES2_DEFER_UNSUPPORTED_HIERARCHY, declaration, NULL);
                        continue;
                }
                if (!t2_nominal_add_super(
                        shadow->universe,
                        nominal_symbol,
                        supertype
                ) && t2_universe_ok(shadow->universe)) {
                        defer_node(shadow, TYPES2_DEFER_HIERARCHY_REJECTED, declaration, NULL);
                }
        }
        pop_type_variables(shadow, type_mark);
}

static void
install_declared_class_constructor(
        Types2Shadow *shadow,
        ClassDefinition const *definition,
        Types2Nominal const *nominal
)
{
        if (
                definition == NULL
             || nominal == NULL
             || definition->is_trait
             || definition->var == NULL
        ) return;

        size_t arity = nominal->arity;
        size_t declared_arity = (size_t)vN(definition->type_params);
        T2Quantifier *quantifiers = arity == 0
                                  ? NULL
                                  : malloc(arity * sizeof *quantifiers);
        T2Type *arguments = arity == 0
                          ? NULL
                          : malloc(arity * sizeof *arguments);
        if (arity != 0 && (quantifiers == NULL || arguments == NULL)) {
                free(quantifiers);
                free(arguments);
                shadow->failed = true;
                return;
        }

        size_t type_mark = push_type_variables(shadow);
        for (size_t i = 0; i < arity; ++i) {
                Expr const *parameter = i < declared_arity
                                      ? v__(definition->type_params, (int)i)
                                      : NULL;
                T2VariableKind kind = parameter != NULL
                                   && parameter->symbol != NULL
                                   && SymbolIsParamPack(parameter->symbol)
                                    ? T2_VARIABLE_PACK
                                    : T2_VARIABLE_QUANTIFIED;
                uint32_t id = shadow->next_quantified_id++;
                quantifiers[i] = (T2Quantifier) { .id = id, .kind = kind };
                arguments[i] = t2_variable(shadow->universe, kind, id);
                if (parameter != NULL) {
                        (void)add_type_variable(
                                shadow,
                                parameter->symbol,
                                arguments[i]
                        );
                }
        }

        T2Type receiver = primitive_class_type(shadow, nominal->class_id);
        if (receiver == T2_TYPE_INVALID) {
                receiver = t2_nominal(
                        shadow->universe,
                        nominal->symbol,
                        arguments,
                        arity
                );
        }
        install_class_constructor(
                shadow,
                definition,
                nominal->class_id,
                receiver,
                quantifiers,
                arity
        );
        pop_type_variables(shadow, type_mark);
        free(arguments);
        free(quantifiers);
}

static void
register_declaration(Types2Shadow *shadow, Stmt const *statement)
{
        if (statement == NULL || shadow->failed) return;
        switch (statement->type) {
        case STATEMENT_BLOCK:
        case STATEMENT_MULTI:
                for (int i = 0; i < vN(statement->statements); ++i) {
                        register_declaration(shadow, v__(statement->statements, i));
                }
                break;
        case STATEMENT_TYPE_DEFINITION:
                register_type_alias(shadow, &statement->class);
                break;
        case STATEMENT_CLASS_DEFINITION:
        {
                int class_id = statement->class.symbol;
                if (class_id < 0 && statement->class.var != NULL) {
                        class_id = statement->class.var->class;
                }
                Types2Nominal *nominal = ensure_nominal(
                        shadow,
                        class_id,
                        statement->class.name,
                        (size_t)vN(statement->class.type_params)
                );
                register_nominal_hierarchy(shadow, &statement->class, nominal);
                if (nominal != NULL) {
                        (void)ensure_class_interface(shadow, class_id);
                        nominal = find_class_nominal(shadow, class_id);
                        install_declared_class_constructor(
                                shadow,
                                &statement->class,
                                nominal
                        );
                }
                register_forward_binding(shadow, statement->class.var, false);
                break;
        }
        case STATEMENT_TAG_DEFINITION:
        {
                Types2Nominal *nominal = ensure_tag_nominal(
                        shadow,
                        statement->tag.symbol,
                        statement->tag.name
                );
                register_nominal_hierarchy(shadow, &statement->tag, nominal);
                register_forward_binding(shadow, statement->tag.var, false);
                break;
        }
        case STATEMENT_FUNCTION_DEFINITION:
        case STATEMENT_PATTERN_DEFINITION:
                register_forward_binding(
                        shadow,
                        statement->target == NULL ? NULL : statement->target->symbol,
                        false
                );
                break;
        case STATEMENT_OPERATOR_DEFINITION:
                register_forward_binding(
                        shadow,
                        statement->target == NULL ? NULL : statement->target->symbol,
                        false
                );
                register_operator_expression(shadow, statement->value);
                break;
        case STATEMENT_DEFINITION:
                if (is_named_binding_target(statement->target)) {
                        register_forward_binding(
                        shadow,
                        statement->target->symbol,
                        !statement->cnst
                     && !SymbolIsConst(statement->target->symbol)
                        );
                }
                break;
        default:
                break;
        }
}

static void
log_native_type(Types2Shadow *shadow, T2Type type)
{
        if (type == T2_TYPE_INVALID) {
                fputs("null", shadow->log);
                return;
        }
        T2Type zonked = t2_solver_zonk(
                shadow->solver,
                type,
                T2_PREFER_LOWER_BOUND
        );
        if (zonked == T2_TYPE_INVALID) zonked = type;
        char *text = t2_type_string(shadow->universe, zonked);
        if (text == NULL) fputs("null", shadow->log);
        else {
                json_string(shadow->log, text);
                free(text);
        }
}

static void
report_internal_failure(Types2Shadow *shadow)
{
        if (shadow == NULL) return;

        bool universe_failed = !t2_universe_ok(shadow->universe);
        bool solver_failed = t2_solver_failed(shadow->solver);
        if (universe_failed || solver_failed) shadow->failed = true;
        if (
                shadow->log == NULL
             || !shadow->failed
             || shadow->reported_failure
        ) return;

        shadow->reported_failure = true;
        log_prefix(shadow, "internal_error");
        fputs(",\"reason\":", shadow->log);
        json_string(
                shadow->log,
                solver_failed
                    ? "solver_failure"
                    : universe_failed
                      ? "type_universe_failure"
                      : "shadow_allocation_failure"
        );
        if (solver_failed) {
                fputs(",\"detail\":", shadow->log);
                json_string(shadow->log, t2_solver_error(shadow->solver));
        }
        log_end(shadow);
}

static T2Type
resolve_external_head(
        Types2Shadow *shadow,
        T2Type type,
        T2SolutionPreference preference
)
{
        for (unsigned depth = 0; depth < 64; ++depth) {
                if (t2_type_kind(shadow->universe, type) != T2_TYPE_META) {
                        return type;
                }
                T2Type solution = t2_solver_solution(
                        shadow->solver,
                        type,
                        preference
                );
                if (solution == T2_TYPE_INVALID || solution == type) return solution;
                type = solution;
        }
        return T2_TYPE_INVALID;
}

static T2Relation
discharge_translated_predicate(T2Solver *solver, T2Relation relation)
{
        if (relation == T2_RELATION_NO || relation == T2_RELATION_COMPLEXITY) {
                return relation;
        }
        /* Once an external protocol has been translated to ordinary solver
         * bounds/edges, the protocol obligation itself is complete.  A
         * deferred nested subtype relation has its own retained obligation or
         * metavariable watchers and must not keep duplicating the external
         * lookup on every wakeup. */
        return t2_solver_failed(solver) ? T2_RELATION_NO : T2_RELATION_YES;
}

static T2Relation
discharge_dynamic_predicate_result(
        Types2Shadow *shadow,
        T2Solver *solver,
        T2Type result,
        char const *provenance
)
{
        T2Type dynamic = t2_primitive(shadow->universe, T2_TYPE_DYNAMIC);
        T2Type resolved = resolve_external_head(
                shadow,
                result,
                T2_PREFER_UPPER_BOUND
        );
        if (
                t2_type_kind(shadow->universe, result) == T2_TYPE_META
             && resolved == result
        ) {
                return discharge_translated_predicate(
                        solver,
                        t2_solver_constrain_subtype(
                                solver,
                                dynamic,
                                result,
                                provenance
                        )
                );
        }
        if (resolved == T2_TYPE_INVALID) return T2_RELATION_DEFERRED;
        default_dynamic_callable_metas(shadow, resolved, 0);
        if (shadow->failed) return T2_RELATION_NO;
        return t2_consistent(shadow->universe, dynamic, resolved)
                    == T2_RELATION_NO
             ? T2_RELATION_NO
             : T2_RELATION_YES;
}

static T2Type
callable_keyword_parameter_type(
        Types2Shadow *shadow,
        T2Type callable,
        char const *name
)
{
        if (t2_type_kind(shadow->universe, callable) != T2_TYPE_FUNCTION) {
                return T2_TYPE_INVALID;
        }
        T2Type rest = T2_TYPE_INVALID;
        size_t count = t2_callable_parameter_count(shadow->universe, callable);
        for (size_t i = 0; i < count; ++i) {
                T2ParameterSpec parameter;
                if (!t2_callable_parameter(
                        shadow->universe,
                        callable,
                        i,
                        &parameter
                )) continue;
                if (parameter.kind == T2_PARAMETER_KEYWORD_REST) {
                        rest = parameter.type;
                        continue;
                }
                if (
                        parameter.name != NULL
                     && name != NULL
                     && strcmp(parameter.name, name) == 0
                     && (
                                parameter.kind == T2_PARAMETER_POSITIONAL_OR_KEYWORD
                             || parameter.kind == T2_PARAMETER_KEYWORD_ONLY
                        )
                ) return parameter.type;
        }
        return rest;
}

static T2Type
callable_keyword_value_union(Types2Shadow *shadow, T2Type callable)
{
        if (t2_type_kind(shadow->universe, callable) != T2_TYPE_FUNCTION) {
                return T2_TYPE_INVALID;
        }
        T2Type result = t2_primitive(shadow->universe, T2_TYPE_NEVER);
        size_t count = t2_callable_parameter_count(shadow->universe, callable);
        for (size_t i = 0; i < count; ++i) {
                T2ParameterSpec parameter;
                if (!t2_callable_parameter(
                        shadow->universe,
                        callable,
                        i,
                        &parameter
                )) continue;
                if (
                        parameter.kind == T2_PARAMETER_POSITIONAL_OR_KEYWORD
                     || parameter.kind == T2_PARAMETER_KEYWORD_ONLY
                     || parameter.kind == T2_PARAMETER_KEYWORD_REST
                ) result = t2_join(shadow->universe, result, parameter.type);
        }
        return result;
}

static T2Relation
resolve_keyword_spread(
        Types2Shadow *shadow,
        T2Solver *solver,
        T2Type spread,
        T2Type callable,
        char const *provenance,
        unsigned depth
)
{
        if (depth >= 64) return T2_RELATION_COMPLEXITY;
        T2TypeKind spread_kind = t2_type_kind(shadow->universe, spread);
        T2TypeKind callable_kind = t2_type_kind(shadow->universe, callable);
        if (spread_kind == T2_TYPE_DYNAMIC) return T2_RELATION_YES;
        if (
                spread_kind == T2_TYPE_META
             || spread_kind == T2_TYPE_VARIABLE
             || callable_kind == T2_TYPE_META
             || callable_kind == T2_TYPE_VARIABLE
        ) return T2_RELATION_DEFERRED;
        if (callable_kind != T2_TYPE_FUNCTION) return T2_RELATION_NO;

        if (spread_kind == T2_TYPE_UNION) {
                T2Relation relation = T2_RELATION_YES;
                size_t count = t2_type_arity(shadow->universe, spread);
                for (size_t i = 0; i < count; ++i) {
                        T2Relation arm = resolve_keyword_spread(
                                shadow,
                                solver,
                                t2_type_child(shadow->universe, spread, i),
                                callable,
                                provenance,
                                depth + 1
                        );
                        if (arm == T2_RELATION_NO || arm == T2_RELATION_COMPLEXITY) {
                                return arm;
                        }
                        if (arm == T2_RELATION_DEFERRED) relation = arm;
                }
                return relation;
        }

        if (spread_kind == T2_TYPE_RECORD || spread_kind == T2_TYPE_ROW) {
                size_t arity = t2_type_arity(shadow->universe, spread);
                if (arity == 0) return T2_RELATION_NO;
                for (size_t i = 0; i + 1 < arity; ++i) {
                        T2Type field = t2_type_child(shadow->universe, spread, i);
                        if (t2_type_kind(shadow->universe, field) != T2_TYPE_FIELD) {
                                return T2_RELATION_NO;
                        }
                        T2Type parameter = callable_keyword_parameter_type(
                                shadow,
                                callable,
                                t2_type_name(shadow->universe, field)
                        );
                        if (parameter == T2_TYPE_INVALID) return T2_RELATION_NO;
                        T2Relation relation = t2_solver_constrain_subtype(
                                solver,
                                t2_type_child(shadow->universe, field, 0),
                                parameter,
                                provenance
                        );
                        if (
                                relation == T2_RELATION_NO
                             || relation == T2_RELATION_COMPLEXITY
                             || t2_solver_failed(solver)
                        ) return relation;
                }
                T2Type tail = t2_type_child(shadow->universe, spread, arity - 1);
                T2TypeKind tail_kind = t2_type_kind(shadow->universe, tail);
                if (tail_kind == T2_TYPE_ROW_EMPTY) return T2_RELATION_YES;
                if (tail_kind == T2_TYPE_ROW) {
                        return resolve_keyword_spread(
                                shadow,
                                solver,
                                tail,
                                callable,
                                provenance,
                                depth + 1
                        );
                }
                if (
                        tail_kind == T2_TYPE_META
                     || tail_kind == T2_TYPE_VARIABLE
                ) return T2_RELATION_DEFERRED;
                return T2_RELATION_NO;
        }

        if (spread_kind == T2_TYPE_NOMINAL) {
                Types2Nominal *nominal = nominal_from_type(shadow, spread);
                if (
                        nominal == NULL
                     || nominal->class_id != CLASS_DICT
                     || t2_type_arity(shadow->universe, spread) != 2
                ) return T2_RELATION_NO;
                T2Relation keys = t2_solver_constrain_subtype(
                        solver,
                        t2_type_child(shadow->universe, spread, 0),
                        t2_primitive(shadow->universe, T2_TYPE_STRING),
                        provenance
                );
                if (
                        keys == T2_RELATION_NO
                     || keys == T2_RELATION_COMPLEXITY
                     || t2_solver_failed(solver)
                ) return keys;
                T2Type values = resolve_external_head(
                        shadow,
                        t2_type_child(shadow->universe, spread, 1),
                        T2_PREFER_LOWER_BOUND
                );
                T2TypeKind value_kind = t2_type_kind(
                        shadow->universe,
                        values
                );
                T2VariableKind value_variable =
                        value_kind == T2_TYPE_META
                     || value_kind == T2_TYPE_VARIABLE
                        ? t2_type_variable_kind(shadow->universe, values)
                        : T2_VARIABLE_RIGID;
                if (
                        value_kind == T2_TYPE_DYNAMIC
                     || value_variable == T2_VARIABLE_FLEXIBLE
                     || value_variable == T2_VARIABLE_WEAK
                ) {
                        /* `%kwargs` is represented as a homogeneous Dict until
                         * keyword-row inference is complete.  An unannotated
                         * value therefore has unknown names as well as unknown
                         * values and is a gradual runtime-checked forwarding
                         * boundary.  Concrete dictionary values still require
                         * an accepted keyword/rest contract below. */
                        defer_node(
                                shadow,
                                value_kind == T2_TYPE_DYNAMIC
                                        ? TYPES2_DEFER_DYNAMIC_KEYWORD_SPREAD
                                        : TYPES2_DEFER_KEYWORD_ROW,
                                NULL,
                                provenance
                        );
                        return T2_RELATION_YES;
                }
                /* An open keyword map may contain names not represented by a
                 * fixed parameter.  If the callee has a keyword-rest slot,
                 * those values flow there; using the union of every named
                 * parameter would lose that call-shape fact and leave a
                 * spurious disjunctive bound. */
                T2Type accepted = callable_keyword_parameter_type(
                        shadow,
                        callable,
                        NULL
                );
                if (accepted == T2_TYPE_INVALID) {
                        accepted = callable_keyword_value_union(shadow, callable);
                }
                if (
                        accepted == T2_TYPE_INVALID
                     || t2_type_kind(shadow->universe, accepted) == T2_TYPE_NEVER
                ) return T2_RELATION_NO;
                return discharge_translated_predicate(
                        solver,
                        t2_solver_constrain_subtype(
                                solver,
                                values,
                                accepted,
                                provenance
                        )
                );
        }

        return T2_RELATION_NO;
}

static T2Relation
resolve_external_predicate_x(
        void *context,
        T2Solver *solver,
        T2Predicate const *predicate
)
{
        Types2Shadow *shadow = context;
        if (
                shadow == NULL
             || solver != shadow->solver
             || predicate == NULL
        ) return T2_RELATION_NO;

        bool subscript = predicate->kind == T2_PREDICATE_SUBSCRIPT_READ
                      || predicate->kind == T2_PREDICATE_SUBSCRIPT_WRITE;
        bool member = predicate->kind == T2_PREDICATE_MEMBER_READ
                   || predicate->kind == T2_PREDICATE_MEMBER_WRITE;
        T2Type subject = subscript || member
                       ? resolve_external_head(
                               shadow,
                               predicate->subtype,
                               T2_PREFER_LOWER_BOUND
                         )
                       : t2_solver_zonk(
                               solver,
                               predicate->subtype,
                               T2_PREFER_LOWER_BOUND
                         );
        T2Type operand = subscript
                       ? resolve_external_head(
                               shadow,
                               predicate->operand,
                               T2_PREFER_LOWER_BOUND
                         )
                       : t2_solver_zonk(
                               solver,
                               predicate->operand,
                               T2_PREFER_LOWER_BOUND
                         );
        if (
                subject == T2_TYPE_INVALID
             || operand == T2_TYPE_INVALID
        ) return T2_RELATION_DEFERRED;
        if (is_dynamic_type(shadow, subject)) {
                switch (predicate->kind) {
                case T2_PREDICATE_OPERATOR:
                case T2_PREDICATE_SUBSCRIPT_READ:
                case T2_PREDICATE_MEMBER_READ:
                        return discharge_dynamic_predicate_result(
                                shadow,
                                solver,
                                predicate->supertype,
                                predicate->provenance
                        );
                case T2_PREDICATE_SUBTYPE:
                        break;
                case T2_PREDICATE_SUBSCRIPT_WRITE:
                case T2_PREDICATE_MEMBER_WRITE:
                case T2_PREDICATE_KEYWORD_SPREAD:
                        return T2_RELATION_YES;
                }
        }
        if (
                predicate->kind == T2_PREDICATE_OPERATOR
             && is_dynamic_type(shadow, operand)
        ) {
                return discharge_dynamic_predicate_result(
                        shadow,
                        solver,
                        predicate->supertype,
                        predicate->provenance
                );
        }
        if (
                predicate->kind == T2_PREDICATE_OPERATOR
             && (
                        operator_type_is_open(shadow, subject, 0)
                     || operator_type_is_open(shadow, operand, 0)
                )
        ) return T2_RELATION_DEFERRED;
        if (
                predicate->kind != T2_PREDICATE_OPERATOR
             && t2_type_kind(shadow->universe, subject) == T2_TYPE_META
        ) return T2_RELATION_DEFERRED;

        T2Type result = T2_TYPE_INVALID;
        switch (predicate->kind) {
        case T2_PREDICATE_OPERATOR:
        {
                if (
                        predicate->name != NULL
                     && strcmp(predicate->name, "#") == 0
                     && t2_type_kind(shadow->universe, operand)
                        == T2_TYPE_NEVER
                ) {
                        result = infer_count_type(
                                shadow,
                                subject,
                                NULL,
                                false
                        );
                } else {
                        uint8_t operation = named_binary_operation(
                                predicate->name
                        );
                        result = operation == EXPRESSION_MAX_TYPE
                               ? infer_registered_operator(
                                       shadow,
                                       predicate->name,
                                       subject,
                                       operand,
                                       NULL,
                                       false
                                 )
                               : infer_binary_pair(
                                       shadow,
                                       operation,
                                       subject,
                                       operand,
                                       NULL,
                                       false
                                 );
                }
                break;
        }
        case T2_PREDICATE_SUBSCRIPT_READ:
                result = infer_subscript_type(
                        shadow,
                        subject,
                        operand,
                        NULL,
                        NULL,
                        false
                );
                break;
        case T2_PREDICATE_SUBSCRIPT_WRITE:
        {
                T2Type value = resolve_external_head(
                        shadow,
                        predicate->supertype,
                        T2_PREFER_LOWER_BOUND
                );
                if (value == T2_TYPE_INVALID) return T2_RELATION_DEFERRED;
                return check_subscript_write(
                        shadow,
                        subject,
                        operand,
                        value,
                        NULL,
                        false
                ) ? T2_RELATION_YES : T2_RELATION_NO;
        }
        case T2_PREDICATE_MEMBER_READ:
        case T2_PREDICATE_MEMBER_WRITE:
        {
                if (predicate->name == NULL) return T2_RELATION_NO;
                bool write = predicate->kind == T2_PREDICATE_MEMBER_WRITE;
                if (t2_type_kind(shadow->universe, subject) == T2_TYPE_RECORD) {
                        T2FieldSpec requirement = {
                                .name = predicate->name,
                                .type = predicate->supertype,
                                .presence = T2_PRESENCE_REQUIRED,
                                .capability = write
                                            ? T2_FIELD_WRITABLE
                                            : T2_FIELD_READONLY
                        };
                        T2Type record = t2_record(
                                shadow->universe,
                                &requirement,
                                1,
                                t2_primitive(
                                        shadow->universe,
                                        T2_TYPE_ROW_ANY
                                ),
                                T2_RECORD_OPEN
                        );
                        if (record == T2_TYPE_INVALID) {
                                return T2_RELATION_COMPLEXITY;
                        }
                        return discharge_translated_predicate(
                                solver,
                                t2_solver_constrain_subtype(
                                        solver,
                                        subject,
                                        record,
                                        predicate->provenance
                                )
                        );
                }
                if (write) {
                        return check_member_write(
                                shadow,
                                subject,
                                predicate->name,
                                predicate->supertype,
                                NULL,
                                false
                        ) ? T2_RELATION_YES : T2_RELATION_NO;
                }
                result = infer_member_type(
                        shadow,
                        subject,
                        predicate->name,
                        false,
                        NULL,
                        false
                );
                break;
        }
        case T2_PREDICATE_KEYWORD_SPREAD:
                return resolve_keyword_spread(
                        shadow,
                        solver,
                        subject,
                        t2_solver_zonk(
                                solver,
                                predicate->supertype,
                                T2_PREFER_UPPER_BOUND
                        ),
                        predicate->provenance,
                        0
                );
        case T2_PREDICATE_SUBTYPE:
                return t2_solver_constrain_subtype(
                        solver,
                        predicate->subtype,
                        predicate->supertype,
                        predicate->provenance
                );
        }

        if (
                result == T2_TYPE_INVALID
             || t2_type_kind(shadow->universe, result) == T2_TYPE_ERROR
        ) return T2_RELATION_NO;
        if (is_dynamic_type(shadow, result)) return T2_RELATION_DEFERRED;
        return discharge_translated_predicate(
                solver,
                t2_solver_constrain_subtype(
                        solver,
                        result,
                        predicate->supertype,
                        predicate->provenance
                )
        );
}

static T2Relation
resolve_external_predicate(
        void *context,
        T2Solver *solver,
        T2Predicate const *predicate
)
{
        Types2Shadow *shadow = context;
        if (shadow == NULL) return T2_RELATION_NO;

        /* Predicate discharge may probe operator methods and callable
         * protocols.  Those probes are type-level evidence, not runtime
         * calls in the enclosing function, so their callable channels must
         * not escape into the active call-effect transaction. */
        Types2CallEffect *previous = shadow->call_effect_sink;
        shadow->call_effect_sink = NULL;
        T2Relation relation = resolve_external_predicate_x(
                context,
                solver,
                predicate
        );
        shadow->call_effect_sink = previous;
        return relation;
}

static void
destroy_shadow(Types2Shadow *shadow)
{
        if (shadow == NULL) {
                return;
        }

        for (size_t i = 0; i < shadow->binding_count; ++i) {
                t2_scheme_free(shadow->bindings[i].scheme);
        }
        for (size_t i = 0; i < shadow->alias_count; ++i) {
                t2_scheme_free(shadow->aliases[i].scheme);
        }
        for (size_t i = 0; i < shadow->member_count; ++i) {
                t2_scheme_free(shadow->members[i].scheme);
        }
        for (size_t i = 0; i < shadow->operator_count; ++i) {
                t2_scheme_free(shadow->operators[i].scheme);
        }
        for (size_t i = 0; i < shadow->diagnostic_count; ++i) {
                free(shadow->diagnostics[i].code);
                free(shadow->diagnostics[i].message);
                free(shadow->diagnostics[i].actual);
                free(shadow->diagnostics[i].expected);
        }
        for (size_t i = 0; i < shadow->provenance_count; ++i) {
                free(shadow->provenances[i]);
        }
        free(shadow->functions);
        free(shadow->class_contracts);
        free(shadow->operators);
        free(shadow->provenances);
        free(shadow->diagnostics);
        free(shadow->type_variables);
        free(shadow->upper_assumptions);
        free(shadow->members);
        free(shadow->nominals);
        free(shadow->aliases);
        free(shadow->bindings);
        free(shadow->imported_operators);
        free(shadow->nodes);
        t2_solver_free(shadow->solver);
        t2_universe_free(shadow->universe);
        if (shadow->close_log && shadow->log != NULL) {
                fclose(shadow->log);
        }
        free(shadow);
}


bool Types2Authoritative = false;
static bool types2_after_startup = false;

void
types2_startup_finished(void)
{
        types2_after_startup = true;
}

static bool
report_all_units(void)
{
        char const *value = getenv("TY_TYPES2_REPORT");
        return value != NULL && ascii_case_equal(value, "all");
}

static bool
entry_unit(Types2Shadow const *shadow)
{
        return strcmp(shadow->unit, "main") == 0
            || strcmp(shadow->unit, "(repl)") == 0;
}

static void
paint(FILE *out, char const *sgr)
{
        if (ColorStderr) fprintf(out, "\x1b[%sm", sgr);
}

static bool
primitive_type_word(char const *word, size_t length)
{
        static char const *const words[] = {
                "Int", "Float", "String", "Bool", "Dynamic", "Never", "Any",
                "Object", "Unknown", "Error", "nil", "true", "false"
        };
        for (size_t i = 0; i < sizeof words / sizeof words[0]; ++i) {
                if (strlen(words[i]) == length && memcmp(words[i], word, length) == 0) {
                        return true;
                }
        }
        return false;
}

static bool
structural_type_word(char const *word, size_t length)
{
        static char const *const words[] = { "var", "yields", "sends", "where" };
        for (size_t i = 0; i < sizeof words / sizeof words[0]; ++i) {
                if (strlen(words[i]) == length && memcmp(words[i], word, length) == 0) {
                        return true;
                }
        }
        return false;
}

static bool
type_word_char(unsigned char c, unsigned char next)
{
        return isalnum(c)
            || c == '_'
            || c == '?'
            || c == '!'
            || (c == '-' && isalnum(next));
}

static void
paint_type(FILE *out, char const *text)
{
        size_t i = 0;
        while (text[i] != '\0') {
                unsigned char c = (unsigned char)text[i];
                if (c == '$') {
                        size_t start = i++;
                        while (isalnum((unsigned char)text[i]) || text[i] == '_') ++i;
                        paint(out, "35");
                        fwrite(text + start, 1, i - start, out);
                        paint(out, "0");
                } else if (isalpha(c) || c == '_') {
                        size_t start = i;
                        while (type_word_char((unsigned char)text[i], (unsigned char)text[i + 1])) ++i;
                        size_t length = i - start;
                        if (primitive_type_word(text + start, length)) paint(out, "36");
                        else if (structural_type_word(text + start, length)) paint(out, "2");
                        else if (isupper(c)) paint(out, "33");
                        fwrite(text + start, 1, length, out);
                        paint(out, "0");
                } else if (isdigit(c)) {
                        size_t start = i;
                        while (isdigit((unsigned char)text[i]) || text[i] == '.') ++i;
                        paint(out, "32");
                        fwrite(text + start, 1, i - start, out);
                        paint(out, "0");
                } else if (c == '\'') {
                        size_t start = i++;
                        while (text[i] != '\0' && text[i] != '\'') ++i;
                        if (text[i] == '\'') ++i;
                        paint(out, "32");
                        fwrite(text + start, 1, i - start, out);
                        paint(out, "0");
                } else {
                        fputc(c, out);
                        ++i;
                }
        }
}

static void
print_source_excerpt(FILE *out, Types2Shadow const *shadow, Location location)
{
        if (shadow->source == NULL) return;
        char const *line = shadow->source;
        for (uint32_t n = 0; n < location.line && line != NULL; ++n) {
                line = strchr(line, '\n');
                if (line != NULL) ++line;
        }
        if (line == NULL) return;
        char const *end = strchr(line, '\n');
        size_t length = end == NULL ? strlen(line) : (size_t)(end - line);
        paint(out, "2");
        fprintf(out, "    %5u | ", location.line + 1);
        paint(out, "0");
        fwrite(line, 1, length, out);
        fputc('\n', out);
        paint(out, "2");
        fputs("          | ", out);
        paint(out, "0");
        for (uint32_t i = 0; i < location.col && i < length; ++i) {
                fputc(line[i] == '\t' ? '\t' : ' ', out);
        }
        paint(out, "1;31");
        fputs("^\n", out);
        paint(out, "0");
}

static int
compare_diagnostics(void const *left, void const *right)
{
        Types2Diagnostic const *a = *(Types2Diagnostic const *const *)left;
        Types2Diagnostic const *b = *(Types2Diagnostic const *const *)right;
        if (a->location.line != b->location.line) {
                return a->location.line < b->location.line ? -1 : 1;
        }
        if (a->location.col != b->location.col) {
                return a->location.col < b->location.col ? -1 : 1;
        }
        return strcmp(a->code, b->code);
}

static bool
same_diagnostic(Types2Diagnostic const *a, Types2Diagnostic const *b)
{
        return a->location.line == b->location.line
            && a->location.col == b->location.col
            && a->severity == b->severity
            && strcmp(a->code, b->code) == 0
            && strcmp(a->message, b->message) == 0;
}

static void
print_diagnostic(FILE *out, Types2Shadow const *shadow, Types2Diagnostic const *diagnostic)
{
        bool error = diagnostic->severity == TYPES2_DIAGNOSTIC_ERROR;
        char const *message = diagnostic->message;
        char const *newline = strchr(message, '\n');
        size_t headline = newline == NULL ? strlen(message) : (size_t)(newline - message);
        paint(out, error ? "1;31" : "1;33");
        fputs(error ? "error" : "warning", out);
        paint(out, "0");
        paint(out, "1");
        fputs(": ", out);
        fwrite(message, 1, headline, out);
        paint(out, "0");
        paint(out, "2");
        fprintf(out, "  [%s]\n", diagnostic->code);
        paint(out, "0");
        for (char const *rest = newline; rest != NULL && rest[1] != '\0';) {
                char const *next = strchr(rest + 1, '\n');
                size_t length = next == NULL ? strlen(rest + 1) : (size_t)(next - rest - 1);
                if (length != 0) {
                        paint(out, "2");
                        fputs("          note: ", out);
                        fwrite(rest + 1, 1, length, out);
                        fputc('\n', out);
                        paint(out, "0");
                }
                rest = next;
        }
        paint(out, "36");
        fputs("      --> ", out);
        paint(out, "0");
        fprintf(
                out,
                "%s:%u:%u\n",
                shadow->path,
                diagnostic->location.line + 1,
                diagnostic->location.col + 1
        );
        print_source_excerpt(out, shadow, diagnostic->location);
        if (diagnostic->actual != NULL) {
                paint(out, "2");
                fputs("          = actual:   ", out);
                paint(out, "0");
                paint_type(out, diagnostic->actual);
                fputc('\n', out);
        }
        if (diagnostic->expected != NULL) {
                paint(out, "2");
                fputs("          = expected: ", out);
                paint(out, "0");
                paint_type(out, diagnostic->expected);
                fputc('\n', out);
        }
}

static void
report_diagnostics(Types2Shadow *shadow, size_t errors, size_t warnings)
{
        if (shadow->diagnostic_count == 0) return;
        FILE *out = stderr;
        Types2Diagnostic const **ordered = malloc(
                shadow->diagnostic_count * sizeof *ordered
        );
        if (ordered == NULL) return;
        for (size_t i = 0; i < shadow->diagnostic_count; ++i) {
                ordered[i] = &shadow->diagnostics[i];
        }
        qsort(ordered, shadow->diagnostic_count, sizeof *ordered, compare_diagnostics);
        for (size_t i = 0; i < shadow->diagnostic_count; ++i) {
                if (i != 0 && same_diagnostic(ordered[i], ordered[i - 1])) continue;
                print_diagnostic(out, shadow, ordered[i]);
        }
        free(ordered);
        paint(out, "1");
        fputs("types2", out);
        paint(out, "0");
        fprintf(
                out,
                ": %s: %zu error%s, %zu warning%s\n",
                shadow->unit,
                errors,
                errors == 1 ? "" : "s",
                warnings,
                warnings == 1 ? "" : "s"
        );
        fflush(out);
}

Types2Shadow *
types2_shadow_begin(char const *unit, char const *path, char const *source)
{
        int saved_errno = errno;

        if (shadow_disabled()) {
                errno = saved_errno;
                return NULL;
        }

        Types2Shadow *shadow = calloc(1, sizeof *shadow);
        if (shadow == NULL) {
                errno = saved_errno;
                return NULL;
        }

        shadow->unit = unit == NULL ? "<unknown>" : unit;
        shadow->path = path == NULL ? "<unknown>" : path;
        shadow->source = source;
        shadow->next_node_id = 1;
        shadow->next_nominal_symbol = 1;
        shadow->next_quantified_id = UINT32_C(0x40000000);
        shadow->member_class_id = -1;
        shadow->log = open_shadow_log(&shadow->close_log);
        shadow->trace_nodes = shadow_option_enabled("TY_TYPES2_TRACE_NODES");
        shadow->trace_deferred = shadow_option_enabled("TY_TYPES2_TRACE_DEFERRED");
        shadow->universe = t2_universe_new();
        shadow->solver = t2_solver_new(shadow->universe);
        t2_solver_set_predicate_resolver(
                shadow->solver,
                resolve_external_predicate,
                shadow
        );
        shadow->failed = shadow->universe == NULL || shadow->solver == NULL;

        if (shadow->log != NULL) {
                log_prefix(shadow, "begin");
                log_end(shadow);
        }

        errno = saved_errno;
        return shadow;
}

void
types2_shadow_observe_statement(
        Ty *ty,
        Types2Shadow *shadow,
        Stmt const *stmt,
        Types2ShadowCheckpoint checkpoint,
        size_t index
)
{
        int saved_errno = errno;

        if (shadow == NULL || shadow->failed || stmt == NULL) {
                report_internal_failure(shadow);
                errno = saved_errno;
                return;
        }

        size_t before = shadow->node_count;
        Types2Walk walk = { .shadow = shadow };
        VisitorCtx visitor = visit_identity(ty);

        visitor.user = &walk;
        visitor.e_pre = observe_expression;
        visitor.t_pre = observe_type;
        visitor.p_pre = observe_pattern;
        visitor.l_pre = observe_lvalue;
        visitor.s_pre = observe_statement;

        /* A NULL scope keeps the shared visitor from allocating shadow scopes. */
        (void)visit_statement(ty, (Stmt *)stmt, NULL, &visitor);

        shadow->ty = ty;
        if (
                checkpoint == TYPES2_SHADOW_DECLARATION
             || checkpoint == TYPES2_SHADOW_CLASS_OPERATOR_DECLARATION
        ) {
                register_declaration(shadow, stmt);
        } else {
                (void)infer_statement(shadow, stmt);
        }

        if ((unsigned)checkpoint < TYPES2_SHADOW_CHECKPOINT_COUNT) {
                shadow->checkpoints[checkpoint] += 1;
        }

        report_internal_failure(shadow);

        if (shadow->log != NULL && !shadow->failed) {
                Types2Node *root = remember_node(
                        shadow,
                        stmt,
                        stmt->type,
                        TYPES2_ROLE_STATEMENT
                );

                log_prefix(shadow, "checkpoint");
                fputs(",\"checkpoint\":", shadow->log);
                json_string(shadow->log, checkpoint_name(checkpoint));
                fprintf(
                        shadow->log,
                        ",\"index\":%zu,\"node\":%" PRIu64
                        ",\"construct\":",
                        index,
                        root == NULL ? UINT64_C(0) : root->id
                );
                json_string(shadow->log, construct_name(stmt->type));
                fprintf(
                        shadow->log,
                        ",\"line\":%u,\"column\":%u"
                        ",\"new_nodes\":%zu,\"nodes\":%zu"
                        ",\"pending_obligations\":%zu",
                        stmt->start.line + 1,
                        stmt->start.col + 1,
                        shadow->node_count - before,
                        shadow->node_count,
                        t2_solver_pending_obligations(shadow->solver)
                );
                fputs(",\"types2_type\":", shadow->log);
                log_native_type(shadow, root == NULL ? T2_TYPE_INVALID : root->type);
                log_end(shadow);
        }

        errno = saved_errno;
}

static size_t
count_runtime_fact_nodes(Types2Shadow *shadow)
{
        size_t count = 0;
        for (size_t i = 0; i < shadow->node_capacity; ++i) {
                Types2Node const *node = &shadow->nodes[i];
                if (!node->inferred || node->type == T2_TYPE_INVALID) continue;
                T2Type zonked = t2_solver_zonk(
                        shadow->solver,
                        node->type,
                        T2_PREFER_LOWER_BOUND
                );
                T2RuntimeFacts facts;
                if (
                        zonked != T2_TYPE_INVALID
                     && t2_type_runtime_facts(shadow->universe, zonked, &facts)
                     && facts.exact
                ) count += 1;
        }
        return count;
}

static Expr const *
obligation_provenance_site(
        Types2Shadow *shadow,
        char const *provenance
)
{
        if (
                shadow == NULL
             || provenance == NULL
             || shadow->node_capacity == 0
        ) return NULL;

        char const *column_separator = strrchr(provenance, ':');
        if (column_separator == NULL) return NULL;
        char *end = NULL;
        unsigned long column = strtoul(column_separator + 1, &end, 10);
        if (end == column_separator + 1 || *end != '\0' || column == 0) {
                return NULL;
        }

        char const *line_separator = column_separator;
        while (line_separator != provenance && line_separator[-1] != ':') {
                --line_separator;
        }
        if (line_separator == provenance) return NULL;
        --line_separator;
        unsigned long line = strtoul(line_separator + 1, &end, 10);
        if (end != column_separator || line == 0) return NULL;

        for (size_t i = 0; i < shadow->node_capacity; ++i) {
                Types2Node const *node = &shadow->nodes[i];
                if (
                        node->syntax == NULL
                     || (node->roles & TYPES2_ROLE_STATEMENT)
                        == node->roles
                ) continue;
                Expr const *expression = node->syntax;
                if (
                        expression->start.line + 1 == line
                     && expression->start.col + 1 == column
                ) return expression;
        }
        return NULL;
}

static void
diagnose_unresolved_obligations(Types2Shadow *shadow)
{
        size_t pending = t2_solver_pending_obligations(shadow->solver);
        for (size_t i = 0; i < pending; ++i) {
                T2Predicate predicate;
                if (!t2_solver_pending_obligation(
                        shadow->solver,
                        i,
                        &predicate
                )) continue;
                add_diagnostic(
                        shadow,
                        obligation_provenance_site(
                                shadow,
                                predicate.provenance
                        ),
                        TYPES2_DIAGNOSTIC_ERROR,
                        "unresolved-constraint",
                        predicate.subtype,
                        predicate.supertype,
                        "the `%s%s%s` constraint remained unsolved at the end of the compilation unit%s%s",
                        predicate_kind_name(predicate.kind),
                        predicate.name == NULL ? "" : ":",
                        predicate.name == NULL ? "" : predicate.name,
                        predicate.provenance == NULL ? "" : " from ",
                        predicate.provenance == NULL ? "" : predicate.provenance
                );
        }
}

size_t
types2_shadow_finish(Types2Shadow *shadow)
{
        int saved_errno = errno;

        if (shadow == NULL) {
                errno = saved_errno;
                return 0;
        }

        validate_pending_class_contracts(shadow);
        diagnose_unresolved_obligations(shadow);
        report_internal_failure(shadow);

        size_t errors = 0;
        size_t warnings = 0;
        for (size_t i = 0; i < shadow->diagnostic_count; ++i) {
                errors += shadow->diagnostics[i].severity == TYPES2_DIAGNOSTIC_ERROR;
                warnings += shadow->diagnostics[i].severity == TYPES2_DIAGNOSTIC_WARNING;
        }
        bool reported = Types2Authoritative
                     && (types2_after_startup || report_all_units());
        if (reported) report_diagnostics(shadow, errors, warnings);
        size_t fatal = Types2Authoritative && entry_unit(shadow) ? errors : 0;

        if (shadow->log != NULL) {
                for (size_t i = 0; i < shadow->diagnostic_count; ++i) {
                        Types2Diagnostic const *diagnostic = &shadow->diagnostics[i];
                        log_prefix(shadow, "diagnostic");
                        fprintf(
                                shadow->log,
                                ",\"node\":%" PRIu64 ",\"line\":%u,\"column\":%u",
                                diagnostic->node,
                                diagnostic->location.line + 1,
                                diagnostic->location.col + 1
                        );
                        fputs(",\"severity\":", shadow->log);
                        json_string(
                                shadow->log,
                                diagnostic->severity == TYPES2_DIAGNOSTIC_ERROR
                                    ? "error"
                                    : diagnostic->severity == TYPES2_DIAGNOSTIC_WARNING
                                      ? "warning"
                                      : "note"
                        );
                        fputs(",\"code\":", shadow->log);
                        json_string(shadow->log, diagnostic->code);
                        fputs(",\"message\":", shadow->log);
                        json_string(shadow->log, diagnostic->message);
                        fputs(",\"actual\":", shadow->log);
                        if (diagnostic->actual == NULL) fputs("null", shadow->log);
                        else json_string(shadow->log, diagnostic->actual);
                        fputs(",\"expected\":", shadow->log);
                        if (diagnostic->expected == NULL) fputs("null", shadow->log);
                        else json_string(shadow->log, diagnostic->expected);
                        fputs(",\"actual_hash\":", shadow->log);
                        log_type_hash(shadow, diagnostic->actual, diagnostic->actual_hash);
                        fputs(",\"expected_hash\":", shadow->log);
                        log_type_hash(shadow, diagnostic->expected, diagnostic->expected_hash);
                        log_end(shadow);
                }

                size_t pending = t2_solver_pending_obligations(shadow->solver);
                for (size_t i = 0; i < pending; ++i) {
                        T2Predicate obligation;
                        if (!t2_solver_pending_obligation(
                                shadow->solver,
                                i,
                                &obligation
                        )) continue;
                        log_prefix(shadow, "pending_obligation");
                        fprintf(shadow->log, ",\"index\":%zu,\"kind\":", i);
                        json_string(
                                shadow->log,
                                predicate_kind_name(obligation.kind)
                        );
                        fputs(",\"name\":", shadow->log);
                        if (obligation.name == NULL) {
                                fputs("null", shadow->log);
                        } else {
                                json_string(shadow->log, obligation.name);
                        }
                        fputs(",\"subtype\":", shadow->log);
                        log_native_type(shadow, obligation.subtype);
                        fputs(",\"subtype_lower\":", shadow->log);
                        log_native_type(
                                shadow,
                                t2_solver_zonk(
                                        shadow->solver,
                                        obligation.subtype,
                                        T2_PREFER_LOWER_BOUND
                                )
                        );
                        fputs(",\"subtype_upper\":", shadow->log);
                        log_native_type(
                                shadow,
                                t2_solver_zonk(
                                        shadow->solver,
                                        obligation.subtype,
                                        T2_PREFER_UPPER_BOUND
                                )
                        );
                        fputs(",\"supertype\":", shadow->log);
                        log_native_type(shadow, obligation.supertype);
                        fputs(",\"supertype_lower\":", shadow->log);
                        log_native_type(
                                shadow,
                                t2_solver_zonk(
                                        shadow->solver,
                                        obligation.supertype,
                                        T2_PREFER_LOWER_BOUND
                                )
                        );
                        fputs(",\"supertype_upper\":", shadow->log);
                        log_native_type(
                                shadow,
                                t2_solver_zonk(
                                        shadow->solver,
                                        obligation.supertype,
                                        T2_PREFER_UPPER_BOUND
                                )
                        );
                        fputs(",\"operand\":", shadow->log);
                        if (obligation.operand == T2_TYPE_INVALID) {
                                fputs("null", shadow->log);
                        } else {
                                log_native_type(shadow, obligation.operand);
                        }
                        fputs(",\"provenance\":", shadow->log);
                        json_string(
                                shadow->log,
                                obligation.provenance == NULL
                                        ? "<unknown>"
                                        : obligation.provenance
                        );
                        log_end(shadow);
                }

                size_t runtime_fact_nodes = count_runtime_fact_nodes(shadow);
                log_prefix(shadow, "finish");
                fprintf(
                        shadow->log,
                        ",\"status\":\"%s\",\"nodes\":%zu"
                        ",\"inferred_nodes\":%" PRIu64
                        ",\"types2_errors\":%zu,\"types2_warnings\":%zu"
                        ",\"unsupported_nodes\":%" PRIu64
                        ",\"deferred_nodes\":%" PRIu64
                        ",\"pending_obligations\":%zu"
                        ",\"candidate_trials\":%" PRIu64
                        ",\"union_call_splits\":%" PRIu64
                        ",\"union_call_arms\":%" PRIu64
                        ",\"computed_type_terms\":%" PRIu64
                        ",\"materialized_computed_types\":%" PRIu64
                        ",\"runtime_fact_nodes\":%zu"
                        ",\"core_types\":%zu"
                        ",\"solver_metas\":%zu"
                        ",\"solver_edges\":%zu"
                        ",\"solver_work_steps\":%" PRIu64
                        ",\"class_contracts\":%zu"
                        ",\"declarations\":%" PRIu64
                        ",\"class_operator_declarations\":%" PRIu64
                        ",\"statements\":%" PRIu64
                        ",\"class_operators\":%" PRIu64
                        ",\"expression_visits\":%" PRIu64
                        ",\"type_visits\":%" PRIu64
                        ",\"pattern_visits\":%" PRIu64
                        ",\"lvalue_visits\":%" PRIu64
                        ",\"statement_visits\":%" PRIu64,
                        shadow->failed ? "internal_error" : "ok",
                        shadow->node_count,
                        shadow->inferred_nodes,
                        errors,
                        warnings,
                        shadow->unsupported_nodes,
                        shadow->deferred_nodes,
                        t2_solver_pending_obligations(shadow->solver),
                        shadow->candidate_trials,
                        shadow->union_call_splits,
                        shadow->union_call_arms,
                        shadow->computed_type_terms,
                        shadow->materialized_computed_types,
                        runtime_fact_nodes,
                        t2_universe_type_count(shadow->universe),
                        t2_solver_meta_count(shadow->solver),
                        t2_solver_edge_count(shadow->solver),
                        t2_solver_work_steps(shadow->solver),
                        shadow->class_contract_count,
                        shadow->checkpoints[TYPES2_SHADOW_DECLARATION],
                        shadow->checkpoints[TYPES2_SHADOW_CLASS_OPERATOR_DECLARATION],
                        shadow->checkpoints[TYPES2_SHADOW_STATEMENT],
                        shadow->checkpoints[TYPES2_SHADOW_CLASS_OPERATOR],
                        shadow->role_visits[0],
                        shadow->role_visits[1],
                        shadow->role_visits[2],
                        shadow->role_visits[3],
                        shadow->role_visits[4]
                );

                fputs(",\"constructs\":{", shadow->log);
                bool first = true;
                for (size_t i = 0; i < UINT8_MAX + 1; ++i) {
                        if (shadow->constructs[i] == 0) {
                                continue;
                        }
                        if (!first) {
                                fputc(',', shadow->log);
                        }
                        first = false;
                        json_string(shadow->log, construct_name((uint8_t)i));
                        fprintf(shadow->log, ":%" PRIu64, shadow->constructs[i]);
                }
                fputc('}', shadow->log);
                fputs(",\"unsupported_constructs\":{", shadow->log);
                first = true;
                for (size_t i = 0; i < UINT8_MAX + 1; ++i) {
                        if (shadow->unsupported_constructs[i] == 0) continue;
                        if (!first) fputc(',', shadow->log);
                        first = false;
                        json_string(shadow->log, construct_name((uint8_t)i));
                        fprintf(
                                shadow->log,
                                ":%" PRIu64,
                                shadow->unsupported_constructs[i]
                        );
                }
                fputc('}', shadow->log);
                fputs(",\"deferred_reasons\":{", shadow->log);
                first = true;
                for (size_t i = 0; i < TYPES2_DEFER_REASON_COUNT; ++i) {
                        if (shadow->deferred_reasons[i] == 0) continue;
                        if (!first) fputc(',', shadow->log);
                        first = false;
                        json_string(shadow->log, defer_reason_names[i]);
                        fprintf(
                                shadow->log,
                                ":%" PRIu64,
                                shadow->deferred_reasons[i]
                        );
                }
                fputc('}', shadow->log);
                fputs(",\"deferred_classes\":{", shadow->log);
                for (size_t i = 0; i < TYPES2_DEFER_CLASS_COUNT; ++i) {
                        if (i != 0) fputc(',', shadow->log);
                        json_string(shadow->log, defer_class_names[i]);
                        fprintf(
                                shadow->log,
                                ":%" PRIu64,
                                deferred_class_total(shadow, (Types2DeferClass)i)
                        );
                }
                fputc('}', shadow->log);
                log_end(shadow);
        }

        destroy_shadow(shadow);
        errno = saved_errno;
        return fatal;
}

void
types2_shadow_abort(Types2Shadow *shadow)
{
        int saved_errno = errno;

        if (shadow == NULL) {
                errno = saved_errno;
                return;
        }

        report_internal_failure(shadow);

        if (shadow->log != NULL) {
                log_prefix(shadow, "abort");
                fputs(",\"reason\":\"legacy_checker_error\"", shadow->log);
                log_end(shadow);
        }

        destroy_shadow(shadow);
        errno = saved_errno;
}

/* vim: set sts=8 sw=8 expandtab: */
