#ifndef T2_H_INCLUDED
#define T2_H_INCLUDED

#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>

#include "types2_core.h"

typedef struct ty Ty;
typedef struct statement Stmt;
typedef struct expression Expr;
typedef struct value Value;
typedef struct class Class;
typedef struct module Module;
typedef struct t2_checker T2Checker;

typedef enum t2_checkpoint {
        T2_CHECKPOINT_DECLARATION,
        T2_CHECKPOINT_CLASS_OPERATOR_DECLARATION,
        T2_CHECKPOINT_STATEMENT,
        T2_CHECKPOINT_CLASS_OPERATOR,
        T2_CHECKPOINT_COUNT
} T2Checkpoint;

extern uint32_t TYPES_OFF;

#define WITH_TYPES_OFF                                  \
        for (                                           \
                uint32_t _ctx_cond = (++TYPES_OFF, 1);  \
                _ctx_cond;                              \
                --_ctx_cond, --TYPES_OFF                \
        )

enum { T2_TAG_SYMBOL_BASE = UINT64_C(1) << 32 };

inline static uint64_t
t2_class_symbol(int class_id)
{
        return (uint64_t)class_id + 1;
}

inline static uint64_t
t2_tag_symbol(int tag_id)
{
        return T2_TAG_SYMBOL_BASE + (uint64_t)tag_id;
}

inline static int
t2_symbol_class(uint64_t symbol)
{
        return (symbol == 0 || symbol >= T2_TAG_SYMBOL_BASE)
             ? -1
             : (int)(symbol - 1);
}

inline static int
t2_symbol_tag(uint64_t symbol)
{
        return (symbol < T2_TAG_SYMBOL_BASE)
             ? -1
             : (int)(symbol - T2_TAG_SYMBOL_BASE);
}

void
t2_startup_finished(void);

T2Checker *
t2_checker_begin(Ty *ty, Module const *module);

void
t2_checker_observe(
        Ty *ty,
        T2Checker *checker,
        Stmt const *stmt,
        T2Checkpoint checkpoint,
        size_t index
);

void
t2_checker_finish(Ty *ty, T2Checker *checker);

void
t2_checker_abort(T2Checker *checker);

T2Universe *
t2_global_universe(void);







T2Type
t2_object_type(Ty *ty, Class *class);

T2Type
t2_class_template(Ty *ty, Class *class);

T2Type
t2_class_parameter(Ty *ty, Class *class, size_t index);

T2Type
t2_class_type(Ty *ty, Class *class);

T2Type
t2_class_instance(Ty *ty, int class_id, T2Type const *arguments, size_t count);

T2Type
t2_tag_instance(Ty *ty, int tag_id, T2Type payload);

void
t2_check_expression(Ty *ty, Expr *expression);

T2Type
t2_resolve(Ty *ty, Expr *type_expression);

T2Type
t2_infer(Ty *ty, Expr *expression);

T2Type
t2_resolve_in_class(Ty *ty, Class *class, Expr *type_expression);

bool
t2_check(Ty *ty, T2Type type, Value const *value);

typedef struct t2_render {
        bool color;
        unsigned width;
        unsigned column;
        unsigned hang;
} T2Render;

char *
t2_render(Ty *ty, T2Type type, T2Render render);

char *
t2_show(Ty *ty, T2Type type);

Value
t2_to_ty(Ty *ty, T2Type type);

T2Type
t2_from_ty(Ty *ty, Value const *value);

Class *
t2_class_of(Ty *ty, T2Type type);

bool
t2_is_nil(T2Type type);

bool
t2_is_callable(T2Type type);

T2Type
t2_callable_result_type(T2Type type);


T2Type
t2_substitute(T2Type type, uint32_t const *ids, T2Type const *replacements, size_t count);

T2Type
t2_member_type(Ty *ty, T2Type receiver, T2Type member);

Expr const *
t2_find_member(Ty *ty, T2Type type, char const *name);

void
t2_completions(Ty *ty, T2Type type, char const *prefix, void *out);

#endif

/* vim: set sts=8 sw=8 expandtab: */
