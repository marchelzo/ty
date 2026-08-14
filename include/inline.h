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
        TY_INLINE_GLOBAL,
} TyInlineKind;

typedef enum {
        TY_INLINE_LOCAL,
        TY_INLINE_FIELD,
        TY_INLINE_INTEGER,
        TY_INLINE_REAL,
        TY_INLINE_BOOLEAN,
        TY_INLINE_STORE_FIELD,
        TY_INLINE_POP,
        TY_INLINE_ADD,
        TY_INLINE_SUB,
        TY_INLINE_MUL,
        TY_INLINE_DIV,
        TY_INLINE_EQ,
        TY_INLINE_NE,
        TY_INLINE_LT,
        TY_INLINE_GT,
        TY_INLINE_LE,
        TY_INLINE_GE,
        TY_INLINE_BRANCH_TRUE,
        TY_INLINE_JUMP,
} TyInlineOp;

typedef struct {
        u8 op;
        i16 local;
        i16 target;
        i32 member;
        imax integer;
        double real;
} TyInlineInsn;

typedef struct {
        u8 count;
        u8 max_stack;
        u8 argc;
        i8 self_local;
        u8 depths[TY_INLINE_MAX_INSNS + 1];
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
