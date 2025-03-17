struct value;

#ifndef VALUE_H_INCLUDED
#define VALUE_H_INCLUDED

#include <stdbool.h>
#include <stdint.h>
#include <stdarg.h>
#include <string.h>

#include "ty.h"
#include "vec.h"
#include "ast.h"
#include "gc.h"
#include "tags.h"
#include "tthread.h"
#include "token.h"
#include "scope.h"

#define V_ALIGN (_Alignof (Value))

#define CLASS_NIL      -2
#define CLASS_TOP      -1
#define CLASS_OBJECT    0
#define CLASS_CLASS     1
#define CLASS_FUNCTION  2
#define CLASS_ARRAY     3
#define CLASS_DICT      4
#define CLASS_STRING    5
#define CLASS_INT       6
#define CLASS_FLOAT     7
#define CLASS_BLOB      8
#define CLASS_BOOL      9
#define CLASS_REGEX     10
#define CLASS_GENERATOR 11
#define CLASS_TAG       12
#define CLASS_TUPLE     13
#define CLASS_PRIMITIVE 14
#define CLASS_RE_MATCH  14
#define CLASS_ITERABLE  15
#define CLASS_ITER      16
#define CLASS_REV_ITER  17
#define CLASS_QUEUE     18
#define CLASS_RANGE     19
#define CLASS_INC_RANGE 20

#define TY_AST_NODES            \
        X(Expr)                 \
        X(Stmt)                 \
        X(Value)                \
        X(Match)                \
        X(Each)                 \
        X(For)                  \
        X(While)                \
        X(WhileMatch)           \
        X(Func)                 \
        X(FuncDef)              \
        X(ImplicitFunc)         \
        X(Generator)            \
        X(Param)                \
        X(Arg)                  \
        X(Null)                 \
        X(If)                   \
        X(IfNot)                \
        X(In)                   \
        X(NotIn)                \
        X(Eq)                   \
        X(Matches)              \
        X(Operator)             \
        X(Or)                   \
        X(And)                  \
        X(BitAnd)               \
        X(BitOr)                \
        X(KwAnd)                \
        X(NotEq)                \
        X(Assign)               \
        X(Let)                  \
        X(Class)                \
        X(Spread)               \
        X(Splat)                \
        X(Gather)               \
        X(Kwargs)               \
        X(Any)                  \
        X(Add)                  \
        X(Mul)                  \
        X(Sub)                  \
        X(Div)                  \
        X(Mod)                  \
        X(Shl)                  \
        X(Shr)                  \
        X(Xor)                  \
        X(MutAdd)               \
        X(MutSub)               \
        X(MutMul)               \
        X(MutDiv)               \
        X(MutMod)               \
        X(MutAnd)               \
        X(MutOr)                \
        X(MutXor)               \
        X(MutShl)               \
        X(MutShr)               \
        X(Block)                \
        X(Multi)                \
        X(With)                 \
        X(Defer)                \
        X(Array)                \
        X(Dict)                 \
        X(String)               \
        X(SpecialString)        \
        X(LangString)           \
        X(Int)                  \
        X(Bool)                 \
        X(Float)                \
        X(Nil)                  \
        X(Regex)                \
        X(Id)                   \
        X(Record)               \
        X(RecordEntry)          \
        X(DictItem)             \
        X(ArrayItem)            \
        X(Call)                 \
        X(MethodCall)           \
        X(DynMethodCall)        \
        X(TagPattern)           \
        X(Tagged)               \
        X(PatternAlias)         \
        X(ChoicePattern)        \
        X(MemberAccess)         \
        X(DynMemberAccess)      \
        X(Subscript)            \
        X(Slice)                \
        X(NotNil)               \
        X(ArrayCompr)           \
        X(Try)                  \
        X(Eval)                 \
        X(Cond)                 \
        X(UserOp)               \
        X(Return)               \
        X(Yield)                \
        X(Break)                \
        X(Continue)             \
        X(Wtf)                  \
        X(GT)                   \
        X(GEQ)                  \
        X(LT)                   \
        X(LEQ)                  \
        X(Cmp)                  \
        X(Not)                  \
        X(Neg)                  \
        X(PreInc)               \
        X(PostInc)              \
        X(PreDec)               \
        X(PostDec)              \
        X(Count)                \
        X(Question)             \
        X(Resource)             \
        X(View)                 \
        X(NotNilView)           \
        X(IfDef)                \
        X(CompileTime)          \
        X(Defined)              \
        X(Throw)                \
        X(Range)                \
        X(IncRange)             \
        X(Super)                \
        X(Stop)

#define X(x) Ty ## x,
enum {
        TyZeroNode,
        TY_AST_NODES
        TyMaxNode
};
#undef X

enum {
        TAG_MATCH_ERR = TyMaxNode,
        TAG_INDEX_ERR,
        TAG_DISPATCH_ERR,
        TAG_NONE,
        TAG_SOME,
        TAG_OK,
        TAG_ERR
};

inline static char const *
TypeName(Ty const *ty, int t0)
{
        switch (t0) {
        case VALUE_INTEGER:             return "Int";
        case VALUE_REAL:                return "Float";
        case VALUE_STRING:              return "String";
        case VALUE_ARRAY:               return "Array";
        case VALUE_DICT:                return "Dict";
        case VALUE_BLOB:                return "Blob";
        case VALUE_OBJECT:              return "Object";
        case VALUE_BOOLEAN:             return "Bool";
        case VALUE_REGEX:               return "Regex";
        case VALUE_OPERATOR:            return "<operator>";
        case VALUE_CLASS:               return "Class";
        case VALUE_METHOD:
        case VALUE_BUILTIN_METHOD:
        case VALUE_BUILTIN_FUNCTION:
        case VALUE_FUNCTION:
                                        return "Function";
        case VALUE_GENERATOR:           return "Generator";
        case VALUE_TUPLE:               return "Tuple";
        case VALUE_TAG:                 return "Tag";
        case VALUE_THREAD:              return "<thread>";
        case VALUE_PTR:                 return "<ptr>";
        case VALUE_NIL:                 return "<nil>";

        default:                        return "<internal>";
        }
}

inline static char const *
ValueTypeName(Ty *ty, Value const *v)
{
        if (v->type & VALUE_TAGGED) {
                return tags_name(ty, tags_first(ty, v->tags));
        }

        return TypeName(ty, v->type);
}

char *
value_show_color(Ty *ty, struct value const *v);

#define DEFINE_METHOD_TABLE(...)                                     \
        static struct {                                              \
                char const *name;                                    \
                BuiltinMethod *func;                                 \
        } funcs[] = { __VA_ARGS__ };                                 \
        static size_t const nfuncs = sizeof funcs / sizeof funcs[0]; \
        static vec(BuiltinMethod *) ftable

#define DEFINE_METHOD_TABLE_BUILDER(type)                                     \
        void build_ ## type ## _method_table(void)                            \
        {                                                                     \
                for (int i = 0; i < nfuncs; ++i) {                            \
                        InternEntry *e = intern(&xD.members, funcs[i].name);  \
                        while (ftable.count <= e->id) { xvP(ftable, NULL); }  \
                        ftable.items[e->id] = funcs[i].func;                  \
                }                                                             \
        }

#define DEFINE_METHOD_LOOKUP(type)                                   \
        BuiltinMethod *get_ ## type ## _method_i(int i)              \
        {                                                            \
                return (i < ftable.count) ? ftable.items[i] : NULL;  \
        }                                                            \
                                                                     \
        BuiltinMethod *get_ ## type ## _method(char const *name)     \
        {                                                            \
                InternEntry *e = intern(&xD.members, name);          \
                return (get_ ## type ## _method_i)(e->id);           \
        }

#define DEFINE_METHOD_LOOKUP2(type) \
        BuiltinMethod *get_ ## type ## _method(char const *name) \
        {                                                        \
                int lo = 0,                                      \
                    hi = nfuncs - 1;                             \
                                                                 \
                while (lo <= hi) {                               \
                        int m = (lo + hi) / 2;                   \
                        int c = strcmp(name, funcs[m].name);     \
                        if      (c < 0) hi = m - 1;              \
                        else if (c > 0) lo = m + 1;              \
                        else            return funcs[m].func;    \
                }                                                \
                                                                 \
                return NULL;                                     \
        }

#define DEFINE_METHOD_COMPLETER(type)                                           \
        int                                                                     \
        type ## _get_completions(                                               \
                Ty *ty,                                                         \
                char const *prefix,                                             \
                char **out,                                                     \
                int max                                                         \
        )                                                                       \
        {                                                                       \
                int n = 0;                                                      \
                int len = strlen(prefix);                                       \
                                                                                \
                for (int i = 0; i < nfuncs; ++i) {                              \
                        if (                                                    \
                                (n < max)                                       \
                             && strncmp(funcs[i].name, prefix, len) == 0        \
                        ) {                                                     \
                                out[n++] = sclone_malloc(funcs[i].name);        \
                        }                                                       \
                }                                                               \
                                                                                \
                return n;                                                       \
        }

#define ARG(i) (*vm_get(ty, argc - 1 - (i)))
#define NAMED(s) ((kwargs != NULL) ? dict_get_member(ty, kwargs->dict, (s)) : NULL)

#define VA_COUNT_INNER( _1, _2, _3, _4, COUNT, ...) COUNT
#define                               VA_COUNT(...) VA_COUNT_INNER( __VA_ARGS__, 4, 3, 2, 1, 0)
#define                                   CAT(a, b) a ## b
#define                       VA_SELECT_INNER(f, i) CAT(f ## _, i)
#define                           VA_SELECT(f, ...) VA_SELECT_INNER(f, VA_COUNT(__VA_ARGS__))(__VA_ARGS__)


#define CHECK_ARGC_1(n0)                                 \
        if (argc != n0) {                                \
                zP(                                      \
                        "%s: expected %s but got %d",    \
                        _name__,                         \
                          (n0 == 0) ? "no arguments"     \
                        : (n0 == 1) ? "one argument"     \
                        :             #n0 " arguments",  \
                        argc                             \
                );                                       \
        } else if (0)

#define CHECK_ARGC_2(n0, n1)                                                        \
        if (argc != n0 && argc != n1) {                                             \
                zP(                                                                 \
                        "%s: expected " #n0 " or " #n1 " arguments but got %d",     \
                        _name__,                                                    \
                        argc                                                        \
                );                                                                  \
        } else if (0)

#define CHECK_ARGC_3(n0, n1, n2)                         \
        if (argc != n0 && argc != n1 && argc != n2) {    \
                zP(                                      \
                        "%s: expected "                  \
                        #n0 ", " #n1 ", or " #n2 " "     \
                        "arguments but got %d",          \
                        _name__,                         \
                        argc                             \
                );                                       \
        } else if (0)

#define CHECK_ARGC_4(n0, n1, n2, n3)                                 \
        if (argc != n0 && argc != n1 && argc != n2 && argc != n3) {  \
                zP(                                                  \
                        "%s: expected "                              \
                        #n0 ", " #n1 ", " #n2 ", or " #n2 " "        \
                        "arguments but got %d",                      \
                        _name__,                                     \
                        argc                                         \
                );                                                   \
        } else if (0)

#define CHECK_ARGC(...) VA_SELECT(CHECK_ARGC, __VA_ARGS__)

noreturn void vm_panic(Ty *, char const *, ...);

inline static Value
checked_arg_1(Ty *ty, char const *fun, int i, Value arg, int t0)
{
        if (arg.type != t0) {
                zP(
                        "%s: expected arg%d: %s but got: %s",
                        fun,
                        i,
                        TypeName(ty, t0),
                        VSC(&arg)
                );
        }

        return arg;
}

inline static Value
checked_arg_2(Ty *ty, char const *fun, int i, Value arg, int t0, int t1)
{
        if (arg.type != t0 && arg.type != t1) {
                zP(
                        "%s: expected arg%d: %s | %s but got: %s",
                        fun,
                        i,
                        TypeName(ty, t0),
                        TypeName(ty, t1),
                        VSC(&arg)
                );
        }

        return arg;
}

inline static Value
checked_arg_3(Ty *ty, char const *fun, int i, Value arg, int t0, int t1, int t2)
{
        if (arg.type != t0 && arg.type != t1 && arg.type != t2) {
                zP(
                        "%s: expected arg%d: %s | %s | %s but got: %s",
                        fun,
                        i,
                        TypeName(ty, t0),
                        TypeName(ty, t1),
                        TypeName(ty, t2),
                        VSC(&arg)
                );
        }

        return arg;
}

inline static Value
checked_arg_4(Ty *ty, char const *fun, int i, Value arg, int t0, int t1, int t2, int t3)
{
        if (arg.type != t0 && arg.type != t1 && arg.type != t2) {
                zP(
                        "%s: expected arg%d: %s | %s | %s | %s but got: %s",
                        fun,
                        i,
                        TypeName(ty, t0),
                        TypeName(ty, t1),
                        TypeName(ty, t2),
                        TypeName(ty, t3),
                        VSC(&arg)
                );
        }

        return arg;
}

#define ARGx(i, ...)                   \
        VA_SELECT_INNER(               \
                checked_arg,           \
                VA_COUNT(__VA_ARGS__)  \
        )(                             \
                ty,                    \
                _name__,               \
                i,                     \
                ARG(i),                \
                __VA_ARGS__            \
        )

#define    INT_ARG(i) ARGx(i, VALUE_INTEGER).integer
#define  FLOAT_ARG(i) ARGx(i, VALUE_REAL).real
#define   BOOL_ARG(i) ARGx(i, VALUE_BOOLEAN).boolean
#define  ARRAY_ARG(i) ARGx(i, VALUE_ARRAY).array
#define   DICT_ARG(i) ARGx(i, VALUE_DICT).dict

#if 0
  #define value_mark(ty, v) do { LOG("value_mark: %s:%d: %p", __FILE__, __LINE__, (v)); _value_mark(v); } while (0)
#else
  #define value_mark _value_mark
#endif

unsigned long
value_hash(Ty *ty, struct value const *val);

bool
value_test_equality(Ty *ty, struct value const *v1, struct value const *v2);

int
value_compare(Ty *ty, Value const *v1, Value const *v2);

bool
value_truthy(Ty *ty, struct value const *v);

bool
value_apply_predicate(Ty *ty, struct value *p, struct value *v);

struct value
value_apply_callable(Ty *ty, struct value *f, struct value *v);

char *
value_show(Ty *ty, struct value const *v);

char *
value_string_alloc(Ty *ty, int n);

char *
value_string_clone(Ty *ty, char const *s, int n);

char *
value_string_clone_nul(Ty *ty, char const *src, int n);


struct array *
value_array_clone(Ty *ty, struct array const *);

void
value_array_extend(Ty *ty, struct array *, struct array const *);

struct blob *
value_blob_new(Ty *ty);

struct value
value_tuple(Ty *ty, int n);

struct value
value_named_tuple(Ty *ty, char const *first, ...);

Value *
tuple_get(Value const *tuple, char const *name);

Value *
tuple_get_i(Value const *tuple, int id);

inline static Value *
tget_or_null(Value const *tuple, uintptr_t k)
{
        if (k < 16) {
                return (k >= tuple->count) ? NULL : &tuple->items[k];
        }

        char const *name = (char const *)k;
        int id = M_ID(name);

        if (tuple->ids != NULL) for (int i = 0; i < tuple->count; ++i) {
                if (tuple->ids[i] == id) {
                        return &tuple->items[i];
                }
        }

        return NULL;
}

inline static Value
tget_or(Value const *tuple, uintptr_t k, Value _)
{
        Value *v = tget_or_null(tuple, k);
        return (v != NULL) ? *v : _;
}

inline static Value *
tget_t(Value const *tuple, uintptr_t k, uint32_t t)
{
        Value *v = tget_or_null(tuple, k);
        return (v == NULL || v->type != t) ? NULL : v;
}

inline static Value *
tget_nn(Value const *tuple, uintptr_t k)
{
        Value *v = tget_or_null(tuple, k);
        return (v == NULL || v->type == VALUE_NIL) ? NULL : v;
}

inline static Value
tget_tagged(Value const *tuple, uintptr_t k)
{
        return NONE;
}

#define tget_or(t, i, v)  ((tget_or)((t), (uintptr_t)(i),  (v)))
#define tget_nn(t, i   )  ((tget_nn)((t), (uintptr_t)(i)      ))
#define  tget_t(t, i, t0) ((tget_t) ((t), (uintptr_t)(i), (t0)))

int
tuple_get_completions(Ty *ty, Value const *v, char const *prefix, char **out, int max);

void
_value_mark(Ty *ty, Value const *v);

inline static Array *
value_array_new(Ty *ty)
{
        return mAo0(sizeof (Array), GC_ARRAY);
}

inline static Array *
value_array_new_sized(Ty *ty, size_t n)
{
        Array *a = mAo(sizeof (Array), GC_ARRAY);

        if (n == 0)
                return memset(a, 0, sizeof *a);

        NOGC(a);

        a->items = mA(n * sizeof (Value));
        a->capacity = n;
        a->count = n;

        OKGC(a);

        return a;
}

inline static void
value_array_push(Ty *ty, Array *a, Value v)
{
        if (a->count == a->capacity) {
                a->capacity = a->capacity ? a->capacity * 2 : 4;
                mRE(a->items, a->capacity * sizeof (Value));
        }

        a->items[a->count++] = v;
}

inline static void
value_array_reserve(Ty *ty, Array *a, int count)
{
        if (a->capacity >= count)
                return;

        if (a->capacity == 0)
                a->capacity = 16;

        while (a->capacity < count)
                a->capacity *= 2;

        mRE(a->items, a->capacity * sizeof (Value));
}

inline static Value
STRING_CLONE(Ty *ty, char const *s, int n)
{
        char *clone = value_string_clone(ty, s, n);

        return (Value) {
                .type = VALUE_STRING,
                .tags = 0,
                .string = clone,
                .bytes = n,
                .gcstr = clone,
        };
}

inline static Value
STRING_CLONE_C(Ty *ty, char const *s)
{
        int n = strlen(s);
        char *clone = value_string_clone(ty, s, n);

        return (Value) {
                .type = VALUE_STRING,
                .tags = 0,
                .string = clone,
                .bytes = n,
                .gcstr = clone,
        };
}

inline static Value
STRING_C_CLONE_C(Ty *ty, char const *s)
{
        int n = strlen(s);
        char *clone = value_string_clone_nul(ty, s, n);

        return (Value) {
                .type = VALUE_STRING,
                .tags = 0,
                .string = clone,
                .bytes = n,
                .gcstr = clone,
        };
}

inline static Value
STRING_C_CLONE(Ty *ty, char const *s, int n)
{
        char *clone = value_string_clone_nul(ty, s, n);

        return (Value) {
                .type = VALUE_STRING,
                .tags = 0,
                .string = clone,
                .bytes = n,
                .gcstr = clone,
        };
}

inline static Value
STRING(char *s, int n)
{
        return (Value) {
                .type = VALUE_STRING,
                .tags = 0,
                .string = s,
                .bytes = n,
                .gcstr = s,
        };
}

inline static Value
STRING_VIEW(Value s, int offset, int n)
{
        return (Value) {
                .type = VALUE_STRING,
                .tags = 0,
                .string = s.string + offset,
                .bytes = n,
                .gcstr = s.gcstr
        };
}

inline static Value
STRING_NOGC(char const *s, int n)
{
        return (Value) {
                .type = VALUE_STRING,
                .tags = 0,
                .string = s,
                .bytes = n,
                .gcstr = NULL
        };
}

inline static Value
STRING_NOGC_C(char const *s)
{
        return (Value) {
                .type = VALUE_STRING,
                .tags = 0,
                .string = s,
                .bytes = strlen(s),
                .gcstr = NULL
        };
}

#define STRING_EMPTY (STRING_NOGC(NULL, 0))

inline static Value
PAIR_(Ty *ty, Value a, Value b)
{
        Value v = vT(2);
        v.items[0] = a;
        v.items[1] = b;
        return v;
}

inline static Value
TRIPLE_(Ty *ty, Value a, Value b, Value c)
{
        Value v = vT(3);
        v.items[0] = a;
        v.items[1] = b;
        v.items[2] = c;
        return v;
}

inline static Value
QUADRUPLE_(Ty *ty, Value a, Value b, Value c, Value d)
{
        Value v = vT(4);
        v.items[0] = a;
        v.items[1] = b;
        v.items[2] = c;
        v.items[3] = d;
        return v;
}

#define None                     TAG(TAG_NONE)

int
tags_push(Ty *ty, int, int);

inline static Value
Ok(Ty *ty, Value v)
{
        v.type |= VALUE_TAGGED;
        v.tags = tags_push(ty, v.tags, TAG_OK);
        return v;
}

inline static Value
Err(Ty *ty, Value v)
{
        v.type |= VALUE_TAGGED;
        v.tags = tags_push(ty, v.tags, TAG_ERR);
        return v;
}

inline static Value
Some(Ty *ty, Value v)
{
        v.type |= VALUE_TAGGED;
        v.tags = tags_push(ty, v.tags, TAG_SOME);
        return v;
}

#define Some(x) (Some)(ty, x)

inline static ptrdiff_t
code_size_of(Value const *v)
{
        return v->info[FUN_INFO_CODE_SIZE];
}

inline static char *
code_of(Value const *v)
{
        return (char *)v->info + v->info[0];
}

inline static int
class_of(Value const *v)
{
        return v->info[FUN_INFO_CLASS];
}

inline static char const *
proto_of(Value const *f)
{
        uintptr_t p;

        if (f->xinfo != NULL && f->xinfo->proto != NULL) {
                return f->xinfo->proto;
        }

        memcpy(&p, (char *)f->info + FUN_PROTO, sizeof p);
        return (p == 0) ?  "()" : (char const *)p;
}

inline static char const *
doc_of(Value const *f)
{
        uintptr_t p;

        if (f->xinfo != NULL && f->xinfo->doc != NULL) {
                return f->xinfo->doc;
        }

        memcpy(&p, (char *)f->info + FUN_DOC, sizeof p);
        return (char const *)p;
}

inline static char const *
name_of(Value const *f)
{
        uintptr_t p;

        if (f->xinfo != NULL && f->xinfo->name != NULL) {
                return f->xinfo->name;
        }

        memcpy(&p, (char *)f->info + FUN_NAME, sizeof p);
        return (char const *)p;
}

inline static void
set_name_of(Value const *f, uintptr_t p)
{
        memcpy((char *)f->info + FUN_NAME, &p, sizeof p);
}

inline static char *
from_eval(Value const *f)
{
        return (char *)f->info + FUN_FROM_EVAL;
}

#define PACK_TYPES(t1, t2) (((t1) << 8) | (t2))
#define    PAIR_OF(t)      PACK_TYPES(t, t)

inline static int
ClassOf(Value const *v)
{
        switch (v->type) {
        case VALUE_OBJECT:            return v->class;
        case VALUE_INTEGER:           return CLASS_INT;
        case VALUE_REAL:              return CLASS_FLOAT;
        case VALUE_STRING:            return CLASS_STRING;
        case VALUE_BLOB:              return CLASS_BLOB;
        case VALUE_ARRAY:             return CLASS_ARRAY;
        case VALUE_DICT:              return CLASS_DICT;
        case VALUE_TUPLE:             return CLASS_TUPLE;
        case VALUE_GENERATOR:         return CLASS_GENERATOR;
        case VALUE_REGEX:             return CLASS_REGEX;
        case VALUE_CLASS:             return CLASS_CLASS;
        case VALUE_FUNCTION:          return CLASS_FUNCTION;
        case VALUE_METHOD:            return CLASS_FUNCTION;
        case VALUE_BUILTIN_FUNCTION:  return CLASS_FUNCTION;
        case VALUE_BUILTIN_METHOD:    return CLASS_FUNCTION;
        case VALUE_OPERATOR:          return CLASS_FUNCTION;
        }

        return CLASS_TOP;
}

inline static bool
ArrayIsSmall(Array const *a)
{
        return ((uintptr_t)a & 7);
}

inline static Value *
ArrayItems(Array *a)
{
        uintptr_t p = (uintptr_t)a;
        return (p & 7)
             ? (Value *)(p & ~7)
             : a->items;
}

inline static size_t
ArrayCount(Array *a)
{
        uintptr_t p = (uintptr_t)a & ~7;
        return (p > 0) ? (p - 1) : a->count;
}

inline static Array *
ArrayClone(Ty *ty, Array const *a)
{
        if (a->count == 0)
                return vA();

        Array *new = vAn(a->count);

        memcpy(new->items, a->items, a->count * sizeof (Value));

        return new;
}

inline static Value
tagged(Ty *ty, int tag, Value v, ...)
{
        va_list ap;

        va_start(ap, v);

        vec(Value) vs = {0};

        Value next = va_arg(ap, Value);

        if (next.type == VALUE_NONE) {
                goto TagAndReturn;
        }

        svP(vs, v);

        while (next.type != VALUE_NONE) {
                svP(vs, next);
                next = va_arg(ap, Value);
        }

        v = vT(vs.count);
        for (int i = 0; i < vs.count; ++i) {
                v.items[i] = vs.items[i];
        }

TagAndReturn:
        v.type |= VALUE_TAGGED;
        v.tags = tags_push(ty, v.tags, tag);
        return v;
}


#endif
