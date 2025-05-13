#ifndef TYPES_H_INCLUDED
#define TYPES_H_INCLUDED

#include "ty.h"
#include "value.h"
#include "scope.h"
#include "itable.h"

typedef struct symbol     Symbol;
typedef struct expression Expr;
typedef struct class      Class;
typedef struct type       Type;
typedef struct constraint Constraint;

struct constraint {
        enum {
                TC_2OP,
                TC_EQ
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
                TYPE_FUNCTION,
                TYPE_TUPLE,
                TYPE_LIST,
                TYPE_SEQUENCE,
                TYPE_TAG,
                TYPE_CLASS,
                TYPE_OBJECT,
                TYPE_UNION,
                TYPE_VARIABLE,
                TYPE_SUBSCRIPT,
                TYPE_SLICE,
                TYPE_INTEGER,
                TYPE_INTERSECT,
                TYPE_NIL,
                TYPE_NONE,
                TYPE_BOTTOM,
                TYPE_COMPUTED,
                TYPE_TYPE,
                TYPE_ERROR,
                TYPE_ALIAS
        } type;
        bool fixed;
        bool concrete;
        bool variadic;
        bool forgive;
        union {
                struct {
                        union {
                                struct {
                                        Class *class;
                                        Type *ft;
                                        int tag;
                                };
                                struct {
                                        Type *rt;
                                        Type *yields;
                                        Type *consumes;
                                        ParamVector params;
                                };
                                struct {
                                        Type *_type;
                                        char const *name;
                                };
                                struct {
                                        union {
                                                struct {
                                                        int id;
                                                        int level;
                                                        bool bounded;
                                                };
                                                struct {
                                                        int i;
                                                        int j;
                                                        int k;
                                                };
                                                struct {
                                                        Value func;
                                                        bool inst;
                                                };
                                        };
                                        Type *val;
                                };
                        };
                        TypeVector args;
                        U32Vector bound;
                        ConstraintVector constraints;
                };
                struct {
                        TypeVector types;
                        ConstStringVector names;
                };
                intmax_t z;
        };
        Expr const *src;
};

struct type_env {
        TypeEnv *parent;
        struct itable vars;
        int level;
};


#define PARAM(id, t0, req) ((Param){ .name = (id), .type = (t0), .required = (req) })
#define PARAMx(...) ((Param){ __VA_ARGS__ })


extern Type *TYPE_INT;
extern Type *TYPE_FLOAT;
extern Type *TYPE_BOOL;
extern Type *TYPE_STRING;
extern Type *TYPE_REGEX;
extern Type *TYPE_BLOB;
extern Type *TYPE_ARRAY;
extern Type *TYPE_DICT;
extern Type *NIL_TYPE;
extern Type *NONE_TYPE;
extern Type *BOTTOM_TYPE;
extern Type *UNKNOWN_TYPE;
extern Type *TYPE_ANY;
extern Type *TYPE_CLASS_;


enum {
        T_FLAG_STRICT = 1,
        T_FLAG_UPDATE = 2
};


Type *
type_integer(Ty *ty, intmax_t z);

Type *
type_object(Ty *ty, Class *class);

Type *
type_type(Ty *ty, Type *t0);

Type *
type_variable(Ty *ty, Symbol *var);

Type *
type_var(Ty *ty);

Type *
type_class(Ty *ty, Class *class);

Type *
type_tag(Ty *ty, Class *class, int tag);

Type *
type_alias(Ty *ty, Symbol *var, Stmt const *s);

Type *
type_function(Ty *ty, Expr const *e, bool tmp);

Type *
type_tuple(Ty *ty, Expr const *e);

Type *
type_list(Ty *ty, Expr const *e);

Type *
type_array(Ty *ty, Expr const *e);

Type *
type_dict(Ty *ty, Expr const *e);

Type *
type_match(Ty *ty, Expr const *e);

Type *
type_match_stmt(Ty *ty, Stmt const *stmt);

Type *
type_call(Ty *ty, Expr const *e);

Type *
type_method_call(Ty *ty, Expr const *e);

Type *
type_method_call_name(Ty *ty, Type *t0, char const *name);

Type *
type_subscript(Ty *ty, Expr const *e);

Type *
type_slice(Ty *ty, Expr const *e);

Type *
type_member_access(Ty *ty, Expr const *e);

Type *
type_member_access_t(Ty *ty, Type const *t0, char const *name, bool strict);

Type *
type_binary_op(Ty *ty, Expr const *e);

Type *
type_unary_op(Ty *ty, Expr const *e);

Type *
type_wtf(Ty *ty, Expr const *e);

Type *
type_unary_hash_t(Ty *ty, Type const *t0);

void
unify(Ty *ty, Type **t0, Type *t1);

void
unify2(Ty *ty, Type **t0, Type *t1);

void
type_intersect(Ty *ty, Type **t0, Type *t1);

void
type_subtract(Ty *ty, Type **t0, Type *t1);

Type *
type_resolve(Ty *ty, Expr const *e);

Type *
type_inst(Ty *ty, Type const *t0);

Type *
type_inst0(Ty *ty, Type const *t0, U32Vector const *params, TypeVector const *args);

Type *
type_drill(Ty *ty, Type const *t0);

void
type_assign(Ty *ty, Expr *e, Type *t0, int flags);

Type *
type_fixed(Ty *ty, Type *t0);

Type *
type_unfixed(Ty *ty, Type *t0);

Type *
type_really_unfixed(Ty *ty, Type *t0);

Type *
type_tagged(Ty *ty, int tag, Type *t0);

Type *
type_generator(Ty *ty, Expr const *e);

char *
type_show(Ty *ty, Type const *t0);

bool
type_check(Ty *ty, Type *t0, Type *t1);

Expr *
type_find_member(Ty *ty, Type *t0, char const *name);

Type *
type_array_of(Ty *ty, Type *t0);

Type *
type_dict_of(Ty *ty, Type *t0, Type *t1);

Type *
type_iterable_type(Ty *ty, Type *t0);

Type *
type_not_nil(Ty *ty, Type *t0);

Type *
type_either(Ty *ty, Type *t0, Type *t1);

Type *
type_both(Ty *ty, Type *t0, Type *t1);

Type *
type_instance_of(Ty *ty, Type *t0, int class);

Type *
type_list_from(Ty *ty, expression_vector const *es);

Type *
type_list_item(Ty *ty, Type const *t0, int i);

void
type_scope_push(Ty *ty, bool fun);

void
type_scope_pop(Ty *ty);

void
type_function_fixup(Ty *ty, Expr const *e);

void
type_completions(Ty *ty, Type const *t0, char const *pre, ValueVector *out);

bool
TypeCheck(Ty *ty, Type *t0, Value const *v);

Value
type_to_ty(Ty *ty, Type *t0);

Type *
type_from_ty(Ty *ty, Value const *v);

void
types_init(Ty *ty);

bool
type_find_method(Ty *ty, Type const *t0, char const *name, Type **t1, Expr **e);

bool
type_is_concrete(Ty *ty, Type const *t0);

bool
type_is_tvar(Type const *t0);

#endif

/* vim: set sts=8 sw=8 expandtab: */
