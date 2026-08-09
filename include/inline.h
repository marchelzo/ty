#ifndef INLINE_H_INCLUDED
#define INLINE_H_INCLUDED

#include "ty.h"

enum {
        TY_INLINE_MAX_INSNS = 24,
        TY_INLINE_MAX_STACK = 8,
        TY_INLINE_MAX_ARGS = 64,
        TY_INLINE_MAX_BYTES = 96,
        TY_INLINE_MAX_COST = 64,
};

typedef enum {
        TY_INLINE_METHOD,
        TY_INLINE_OPERATOR,
} TyInlineKind;

typedef enum {
        TY_INLINE_LOCAL,
        TY_INLINE_FIELD,
        TY_INLINE_INTEGER,
        TY_INLINE_ADD,
        TY_INLINE_SUB,
        TY_INLINE_MUL,
} TyInlineOp;

typedef struct {
        u8 op;
        i16 local;
        i32 member;
        imax integer;
} TyInlineInsn;

typedef struct {
        u8 count;
        u8 max_stack;
        u8 argc;
        i8 self_local;
        TyInlineInsn insns[TY_INLINE_MAX_INSNS];
} TyInlinePlan;

typedef struct TyInlineTarget TyInlineTarget;

bool
ty_inline_analyze(Value const *callee, TyInlineKind kind, int argc, TyInlinePlan *plan);

TyInlineTarget *
ty_inline_method_target(Class const *class, int member, Value const *callee);

TyInlineTarget *
ty_inline_getter_target(Class const *class, int member, Value const *callee);

TyInlineTarget *
ty_inline_operator_target(Class const *left, Class const *right, int op, int ref,
                          Value const *callee);

bool
ty_inline_guard_member(Ty *ty, Value const *receiver, TyInlineTarget const *target);

bool
ty_inline_guard_operator(Ty *ty, Value const *left, Value const *right,
                         TyInlineTarget const *target);

#endif
