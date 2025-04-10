#ifndef TYPES_H_INCLUDED
#define TYPES_H_INCLUDED

#include "ty.h"
#include "value.h"
#include "scope.h"

typedef struct symbol     Symbol;
typedef struct expression Expr;
typedef struct class      Class;
typedef struct type       Type;
typedef struct constraint Constraint;
typedef vec(Constraint)   ConstraintVector;

struct constraint {
        enum {
                TC_2OP
        } type;
        union {
                struct {
                        int op;
                        Type *t0;
                        Type *t1;
                        Type *rt;
                };
        };
};

struct type {
        enum {
                TYPE_CLASS,
                TYPE_TAG,
                TYPE_OBJECT,
                TYPE_UNION,
                TYPE_TUPLE,
                TYPE_RECORD,
                TYPE_FUNCTION,
                TYPE_VARIABLE,
                TYPE_INTEGER,
                TYPE_INTERSECT,
                TYPE_NIL,
                TYPE_TYPE,
                TYPE_ALIAS
        } type;
        bool fixed;
        union {
                struct {
                        union {
                                Class *class;
                                struct {
                                        Type *rt;
                                        ParamVector fun_params;
                                };
                                struct {
                                        Type *_type;
                                        char const *name;
                                };
                                Expr *aliased;
                                struct {
                                        Symbol *var;
                                        bool mark;
                                };
                        };
                        vec(Type *) args;
                        symbol_vector params;
                        ConstraintVector constraints;
                };
                struct {
                        vec(Type *) types;
                        StringVector names;
                };
                intmax_t z;
        };
};

#define PARAM(v, t0) ((Param){ .var = (v), .type = (t0) })

extern Type *TYPE_INT;
extern Type *TYPE_FLOAT;
extern Type *TYPE_BOOL;
extern Type *TYPE_STRING;
extern Type *TYPE_BLOB;
extern Type *TYPE_ARRAY;
extern Type *TYPE_DICT;
extern Type *NIL_TYPE;
extern Type *TYPE_ANY;
extern Type *TYPE_CLASS_;

Type *
type_integer(Ty *ty, intmax_t z);

Type *
type_object(Ty *ty, Class *class);

Type *
type_type(Ty *ty, Type *t0);

Type *
type_variable(Ty *ty, Symbol *var);

Type *
type_class(Ty *ty, Class *class);

Type *
type_tag(Ty *ty, Class *class);

Type *
type_alias(Ty *ty, Stmt const *s);

Type *
type_function(Ty *ty, Expr const *e);

Type *
type_tuple(Ty *ty, Expr const *e);

Type *
type_array(Ty *ty, Expr const *e);

Type *
type_dict(Ty *ty, Expr const *e);

Type *
type_call(Ty *ty, Expr const *e);

Type *
type_method_call(Ty *ty, Expr const *e);

Type *
type_method_call_name(Ty *ty, Type *t0, char const *name);

Type *
type_subscript(Ty *ty, Expr const *e);

Type *
type_member_access(Ty *ty, Expr const *e);

Type *
type_member_access_t(Ty *ty, Type *t0, char const *name);

Type *
type_binary_op(Ty *ty, Expr const *e);

void
unify(Ty *ty, Type **t0, Type *t1);

void
type_intersect(Ty *ty, Type **t0, Type *t1);

Type *
type_resolve(Ty *ty, Expr const *e);

void
type_assign(Ty *ty, Expr *e, Type *t0);

Type *
type_fixed(Ty *ty, Type *t0);

char *
type_show(Ty *ty, Type *t0);

bool
type_check(Ty *ty, Type *t0, Type *t1);

Expr *
type_find_member(Ty *ty, Type *t0, char const *name);

Type *
type_array_of(Ty *ty, Type *t0);

Type *
type_iterable_type(Ty *ty, Type *t0);

void
type_scope_push(Ty *ty, bool fun);

void
type_scope_pop(Ty *ty);

void
type_function_fixup(Ty *ty, Type *t0);

bool
TypeCheck(Ty *ty, Type *t0, Value const *v);

#endif

/* vim: set sts=8 sw=8 expandtab: */
