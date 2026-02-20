#ifndef TYPES_H_INCLUDED
#define TYPES_H_INCLUDED

#include "ty.h"
#include "value.h"
#include "scope.h"
#include "itable.h"

typedef struct symbol       Symbol;
typedef struct expression   Expr;
typedef struct class        Class;
typedef struct type         Type;
typedef struct type_bound   TypeBound;
typedef struct constraint   Constraint;
typedef struct param_bounds ParamBounds;

#define WITH_TYPES_OFF                             \
        for (                                      \
                u32 _ctx_cond = (++TYPES_OFF, 1);  \
                _ctx_cond;                         \
                --_ctx_cond, --TYPES_OFF           \
        )

#define WITH_TYPES_OFF_2                               \
        for (                                          \
                u32 _ctx_cond = ((TYPES_OFF += 3), 1); \
                _ctx_cond;                             \
                --_ctx_cond, (TYPES_OFF -= 3)          \
        )

extern u32 TYPES_OFF;

struct constraint {
        enum {
                TC_2OP,
                TC_SUB
        } type;
        union {
                struct {
                        Type *t0;
                        Type *t1;
                        Type *t2;
                        Type *op0;
                        i32 op;
                        Expr const *src;
                        u64 time;
                        bool exhaustive;
                };
        };
};

struct param_bounds {
        U32Vector ids;
        TypeVector bounds;
};

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
        TYPE_INT,
        TYPE_RANGE,
        TYPE_STRING,
        TYPE_BOOL,
        TYPE_INTERSECT,
        TYPE_NIL,
        TYPE_NONE,
        TYPE_BOTTOM,
        TYPE_COMPUTED,
        TYPE_TYPE,
        TYPE_ERROR,
        TYPE_ALIAS
};

struct type {
        u8 type;
        bool fixed;
        bool concrete;
        bool variadic;
        bool forgive;
        bool packed;
        union {
                struct {
                        union {
                                struct {
                                        Class *class;
                                        Type *ft;
                                        i32 tag;
                                        U32Vector _bound;
                                        TypeVector _args;
                                };
                                struct {
                                        Type *rt;
                                        ParamVector params;
                                        ConstraintVector constraints;
                                        Type *pack;
                                        Type *yields;
                                        Type *sends;
                                };
                                struct {
                                        Type *_type;
                                        Expr const *asrc;
                                        char const *name;
                                };
                                struct {
                                        Type *a;
                                        Type *b;
                                        int op;
                                };
                                struct {
                                        union {
                                                struct {
                                                        u32 id;
                                                        i32 level;
                                                        bool bounded;
                                                };
                                                struct {
                                                        i32 i;
                                                        i32 j;
                                                        i32 k;
                                                };
                                                struct {
                                                        Value func;
                                                        bool inst;
                                                };
                                        };
                                        Type *val;
                                };
                        };
                        U32Vector bound;
                        TypeVector args;
                };
                struct {
                        TypeVector types;
                        ConstStringVector names;
                        BoolVector required;
                        Type *repeat;
                        bool frfr;
                        bool closed;
                };
                struct {
                        Type *lo;
                        Type *hi;
                };
                imax z;
                char const *str;
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

#define CONSTRAINT(...) ((Constraint){ __VA_ARGS__ })


extern Type *INT_TYPE;
extern Type *TYPE_FLOAT;
extern Type *BOOL_TYPE;
extern Type *STRING_TYPE;
extern Type *TYPE_REGEX;
extern Type *TYPE_REGEXV;
extern Type *TYPE_BLOB;
extern Type *TYPE_ARRAY;
extern Type *TYPE_DICT;
extern Type *NIL_TYPE;
extern Type *NONE_TYPE;
extern Type *BOTTOM_TYPE;
extern Type *UNKNOWN_TYPE;
extern Type *TYPE_ANY;
extern Type *TYPE_CLASS_;


#define TY_T_FLAGS      \
        X(UPDATE,    0) \
        X(STRICT,    1) \
        X(AVOID_NIL, 2) \
        X(BANG,      3)

#define X(f, i) T_FLAG_ ## f = 1 << i,
enum { TY_T_FLAGS };
#undef X

inline static u32
TypeType(Type const *t0)
{
        return (t0 == NULL) ? TYPE_BOTTOM : t0->type;
}

inline static bool
IsFuncT(Type const *t0)
{
        return (TypeType(t0) == TYPE_FUNCTION);
}

inline static bool
IsAliasT(Type const *t0)
{
        return (TypeType(t0) == TYPE_ALIAS);
}

inline static Type *
NewType(Ty *ty, int type)
{
        Type *t0 = amA0(sizeof *t0);
        t0->type = type;
        TypeAllocCounter += 1;
        return t0;
}

Type *
type_integer(Ty *ty, intmax_t z);

Type *
type_string(Ty *ty, char const *s);

Type *
type_bool(Ty *ty, bool b);

Type *
type_object(Ty *ty, Class *class);

Type *
type_regex(Ty *ty, Regex const *re);

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
type_alias_tmp(Ty *ty, char const *name, Expr const *src);

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
type_special_str(Ty *ty, Expr const *e);

Type *
type_match(Ty *ty, Expr const *e);

Type *
type_match_stmt(Ty *ty, Stmt const *stmt);

Type *
type_call(Ty *ty, Expr const *e);

Type *
type_method_call(Ty *ty, Expr const *e);

Type *
type_method_call_name(Ty *ty, Type *t0, char const *name, bool strict);

Type *
type_subscript(Ty *ty, Expr const *e);

Type *
type_slice(Ty *ty, Expr const *e);

Type *
type_member_access(Ty *ty, Expr const *e);

Type *
type_member_access_t(Ty *ty, Type const *t0, char const *name, bool strict);

Type *
type_op(Ty *ty, Expr const *e);

Type *
type_binary_op(Ty *ty, Expr const *e);

Type *
type_unary_op(Ty *ty, Expr const *e);

Type *
type_wtf(Ty *ty, Expr const *e);

Type *
type_unary_hash_t(Ty *ty, Type const *t0);

Type *
type_enter(Ty *ty, Type const *t0);

void
unify(Ty *ty, Type **t0, Type *t1);

void
unify2(Ty *ty, Type **t0, Type *t1);

void
type_intersect(Ty *ty, Type **t0, Type *t1);

void
type_subtract(Ty *ty, Type **t0, Type *t1);

bool
type_bind(Ty *ty, Type *t0, Type *t1);

void
type_accumulate_return(Ty *ty, Type **rt, Type *t0);

Type *
type_resolve(Ty *ty, Expr const *e);

Type *
type_inst(Ty *ty, Type const *t0);

Type *
type_inst0(Ty *ty, Type const *t0, U32Vector const *params, TypeVector const *args);

Type *
type_new_inst(Ty *ty, Type const *t0);

void
type_assign(Ty *ty, Expr *e, Type *t0, int flags);

Type *
type_fixed(Ty *ty, Type *t0);

Type *
type_unfixed(Ty *ty, Type *t0);

Type *
type_concrete(Ty *ty, Type *t0);

Type *
type_forgiving(Ty *ty, Type const *t0);

Type *
type_tagged(Ty *ty, int tag, Type *t0);

Type *
type_generator(Ty *ty, Expr const *e, Type *yield0, Type *send0);

char *
type_show(Ty *ty, Type const *t0);

bool
type_check(Ty *ty, Type *t0, Type *t1);

Expr *
type_find_member(Ty *ty, Type *t0, char const *name);

Type *
type_iterable_type(Ty *ty, Type *t0, int n);

Type *
type_not_nil(Ty *ty, Type *t0);

Type *
type_without(Ty *ty, Type *t0, Type *t1);

Type *
type_either(Ty *ty, Type *t0, Type *t1);

Type *
type_conditional(Ty *ty, Expr const *e);

Type *
type_any_of(Ty *ty, TypeVector const *types);

Type *
type_both(Ty *ty, Type *t0, Type *t1);

Type *
type_instance_of(Ty *ty, Type *t0, int class);

Type *
type_list_from(Ty *ty, ExprVec const *es);

Type *
type_list_item(Ty *ty, Type const *t0, int i);

void
type_fn_begin(Ty *ty, Expr *e);

void
type_fn_end(Ty *ty, Expr *e);

Type *
type_fn_tmp(Ty *ty, Expr const *e);

void
type_function_fixup(Ty *ty, Expr const *e);

void
type_finalize_generator(Ty *ty, Expr *e);

Type *
type_yield(Ty *ty, Type *f0, Type *y0);

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

i32
type_approx_class(Type const *t0);

bool
types_iter(Ty *ty);

void
types_begin(Ty *ty);

void
types_finish(Ty *ty);

void
types_reset(Ty *ty);

void
types_reset_names(Ty *ty);

inline static Type *
iterable_type_for(Ty *ty, Expr const *e, Type *t0)
{
        if (e != NULL && e->type == EXPRESSION_LIST) {
                return type_iterable_type(ty, t0, vN(e->es));
        } else {
                return type_iterable_type(ty, t0, 1);
        }
}


inline static void
type_assign_iterable(Ty *ty, Expr *e, Type *t0, int flags)
{
        type_assign(ty, e, iterable_type_for(ty, e, t0), flags);
}

Type *
type_inst_for(Ty *ty, Type const *t0, Type const *u0);

Type *
type_array_of(Ty *ty, Type *t0);

void
DumpTypeTimingInfo(Ty *ty);

#endif

/* vim: set sts=8 sw=8 expandtab: */
