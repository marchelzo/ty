#ifndef TYPES2_H_INCLUDED
#define TYPES2_H_INCLUDED

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#include "types2_core.h"

typedef struct ty Ty;
typedef struct statement Stmt;
typedef struct expression Expr;
typedef struct value Value;
typedef struct class Class;
typedef struct types2_shadow Types2Shadow;

typedef enum types2_shadow_checkpoint {
        TYPES2_SHADOW_DECLARATION,
        TYPES2_SHADOW_CLASS_OPERATOR_DECLARATION,
        TYPES2_SHADOW_STATEMENT,
        TYPES2_SHADOW_CLASS_OPERATOR,
        TYPES2_SHADOW_CHECKPOINT_COUNT
} Types2ShadowCheckpoint;

extern uint32_t TYPES_OFF;

#define WITH_TYPES_OFF                                  \
        for (                                           \
                uint32_t _ctx_cond = (++TYPES_OFF, 1);  \
                _ctx_cond;                              \
                --_ctx_cond, --TYPES_OFF                \
        )

enum { TYPES2_TAG_SYMBOL_BASE = UINT64_C(1) << 32 };

inline static uint64_t
types2_class_symbol(int class_id)
{
        return (uint64_t)class_id + 1;
}

inline static uint64_t
types2_tag_symbol(int tag_id)
{
        return TYPES2_TAG_SYMBOL_BASE + (uint64_t)tag_id;
}

inline static int
types2_symbol_class(uint64_t symbol)
{
        return (symbol == 0 || symbol >= TYPES2_TAG_SYMBOL_BASE)
             ? -1
             : (int)(symbol - 1);
}

inline static int
types2_symbol_tag(uint64_t symbol)
{
        return (symbol < TYPES2_TAG_SYMBOL_BASE)
             ? -1
             : (int)(symbol - TYPES2_TAG_SYMBOL_BASE);
}

void
types2_startup_finished(void);

Types2Shadow *
types2_shadow_begin(char const *unit, char const *path, char const *source);

void
types2_shadow_observe_statement(
        Ty *ty,
        Types2Shadow *shadow,
        Stmt const *stmt,
        Types2ShadowCheckpoint checkpoint,
        size_t index
);

void
types2_shadow_finish(Ty *ty, Types2Shadow *shadow);

void
types2_shadow_abort(Types2Shadow *shadow);

T2Universe *
types2_universe(void);

T2Type
types2_primitive(T2TypeKind kind);

T2Type
types2_literal_int(int64_t z);

T2Type
types2_literal_bool(bool b);

T2Type
types2_literal_string(char const *s);

T2Type
types2_type_value(T2Type instance);

T2Type
types2_union(T2Type const *arms, size_t count);

T2Type
types2_object_type(Ty *ty, Class *class);

T2Type
types2_class_type(Ty *ty, Class *class);

T2Type
types2_class_instance(Ty *ty, int class_id, T2Type const *arguments, size_t count);

T2Type
types2_tag_instance(Ty *ty, int tag_id, T2Type payload);

void
types2_check_expression(Ty *ty, Expr *expression);

T2Type
types2_resolve(Ty *ty, Expr *type_expression);

T2Type
types2_infer(Ty *ty, Expr *expression);

bool
types2_check(Ty *ty, T2Type type, Value const *value);

char *
types2_show(Ty *ty, T2Type type);

Value
types2_to_ty(Ty *ty, T2Type type);

T2Type
types2_from_ty(Ty *ty, Value const *value);

Class *
types2_class_of(Ty *ty, T2Type type);

bool
types2_is_nil(T2Type type);

bool
types2_is_callable(T2Type type);

T2Type
types2_callable_result(T2Type type);

bool
types2_subtype(T2Type subtype, T2Type supertype);

T2Type
types2_substitute(T2Type type, uint32_t const *ids, T2Type const *replacements, size_t count);

T2Type
types2_member_type(Ty *ty, T2Type receiver, T2Type member);

Expr const *
types2_find_member(Ty *ty, T2Type type, char const *name);

void
types2_completions(Ty *ty, T2Type type, char const *prefix, void *out);

#endif

/* vim: set sts=8 sw=8 expandtab: */
