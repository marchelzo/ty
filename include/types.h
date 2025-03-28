#ifndef TYPES_H_INCLUDED
#define TYPES_H_INCLUDED

#include "ty.h"
#include "value.h"
#include "scope.h"

typedef struct symbol     Symbol;
typedef struct expression Expr;
typedef struct type       Type;
typedef struct class      Class;

struct type {
        enum {
                TYPE_CLASS,
                TYPE_OBJECT,
                TYPE_UNION,
                TYPE_TUPLE,
                TYPE_RECORD,
                TYPE_FUNCTION,
                TYPE_VARIABLE,
                TYPE_INTEGER,
                TYPE_NIL,
                TYPE_TYPE
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
                                Type *_type;
                                Symbol *var;
                        };
                        vec(Type *) args;
                        symbol_vector params;
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
type_subscript(Ty *ty, Expr const *e);

Type *
type_member_access(Ty *ty, Expr const *e);

Type *
type_member_access_t(Ty *ty, Type *t0, char const *name);

void
unify(Ty *ty, Type **t0, Type *t1);

Type *
type_resolve(Ty *ty, Expr const *e);

void
type_assign(Ty *ty, Expr *e, Type *t0);

char const *
type_show(Ty *ty, Type *t0);

bool
type_check(Ty *ty, Type *t0, Type *t1);

Expr *
type_find_member(Ty *ty, Type *t0, char const *name);

#endif

/* vim: set sts=8 sw=8 expandtab: */
