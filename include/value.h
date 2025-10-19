typedef struct value Value;

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
#include "scope.h"
#include "util.h"

#define V_ALIGN (_Alignof (Value))

enum {
        CLASS_NIL = -2,
        CLASS_TOP,
        CLASS_OBJECT,
        CLASS_CLASS,
        CLASS_FUNCTION,
        CLASS_ARRAY,
        CLASS_DICT,
        CLASS_STRING,
        CLASS_INT,
        CLASS_FLOAT,
        CLASS_BLOB,
        CLASS_BOOL,
        CLASS_REGEX,
        CLASS_REGEXV,
        CLASS_PTR,
        CLASS_ERROR,
        CLASS_GENERATOR,
        CLASS_TAG,
        CLASS_TUPLE,
        CLASS_PRIMITIVE,
        CLASS_RE_MATCH = CLASS_PRIMITIVE,
        CLASS_INTO_PTR,
        CLASS_ITERABLE,
        CLASS_ITER,
        CLASS_REV_ITER,
        CLASS_QUEUE,
        CLASS_SHARED_QUEUE,
        CLASS_RANGE,
        CLASS_INC_RANGE,
        CLASS_BUILTIN_END,
        CLASS_BOTTOM = INT_MAX
};

#define TY_AST_NODES            \
        X(Expr)                 \
        X(Stmt)                 \
        X(Value)                \
        X(Each)                 \
        X(Match)                \
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
        X(Type)                 \
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
        X(Union)                \
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
        X(TryMethodCall)        \
        X(DynMethodCall)        \
        X(TryDynMethodCall)     \
        X(TagPattern)           \
        X(Tagged)               \
        X(PatternAlias)         \
        X(ChoicePattern)        \
        X(MemberAccess)         \
        X(TryMemberAccess)      \
        X(DynMemberAccess)      \
        X(TryDynMemberAccess)   \
        X(Subscript)            \
        X(Slice)                \
        X(NotNil)               \
        X(ArrayCompr)           \
        X(DictCompr)            \
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
        X(TypeOf)               \
        X(Cast)                 \
        X(Stop)

#define TY_TYPE_TAGS   \
        X(Error)       \
        X(Object)      \
        X(Tag)         \
        X(Class)       \
        X(Func)        \
        X(Var)         \
        X(Alias)       \
        X(Union)       \
        X(Intersect)   \
        X(List)        \
        X(Bottom)      \
        X(Unknown)     \
        X(Hole)        \
        X(Any)         \
        X(Nil)         \
        X(Record)      \
        X(String)      \
        X(Int)         \
        X(Float)       \
        X(Bool)        \
        X(Array)       \
        X(Dict)        \
        X(Ptr)         \
        X(Regex)       \
        X(RegexV)      \
        X(Iter)


enum {
        TAG_ZERO,

#define X(x) Ty ## x,
        TY_AST_NODES
#undef X

#define X(x) Ty ## x ## T,
        TY_TYPE_TAGS
#undef X

        TAG_MATCH_ERR,
        TAG_INDEX_ERR,
        TAG_DISPATCH_ERR,
        TAG_NONE,
        TAG_SOME,
        TAG_OK,
        TAG_ERR
};

enum {
        TY_SPAWN_PIPE       = -13,
        TY_SPAWN_INHERIT    = -14,
        TY_SPAWN_MERGE_ERR  = -15
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
        case VALUE_PTR:                 return "Ptr";
        case VALUE_NIL:                 return "nil";
        case VALUE_NONE:                return "<none>";

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
value_show_color(Ty *ty, Value const *v);

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
                                out[n++] = S2(funcs[i].name);                   \
                        }                                                       \
                }                                                               \
                                                                                \
                return n;                                                       \
        }

#define ARG(i) (*vm_get(ty, argc - 1 - (i)))
#define NAMED(s) ((kwargs != NULL) ? dict_get_member(ty, kwargs->dict, (s)) : NULL)
#define ARG_T(i) ((argc > i) ? (vm_get(ty, argc - 1 - (i))->type) : VALUE_NONE)

#define CHECK_ARGC_1(n0) do {                            \
        if (argc != n0) {                                \
                zP(                                      \
                        "%s: expected %s but got %d",    \
                        _name__,                         \
                          (n0 == 0) ? "no arguments"     \
                        : (n0 == 1) ? "one argument"     \
                        :             #n0 " arguments",  \
                        argc                             \
                );                                       \
        }                                                \
} while (0)

#define CHECK_ARGC_2(n0, n1) do {                                                   \
        if (argc != n0 && argc != n1) {                                             \
                zP(                                                                 \
                        "%s: expected " #n0 " or " #n1 " arguments but got %d",     \
                        _name__,                                                    \
                        argc                                                        \
                );                                                                  \
        }                                                                           \
} while (0)

#define CHECK_ARGC_3(n0, n1, n2) do {                    \
        if (argc != n0 && argc != n1 && argc != n2) {    \
                zP(                                      \
                        "%s: expected "                  \
                        #n0 ", " #n1 ", or " #n2 " "     \
                        "arguments but got %d",          \
                        _name__,                         \
                        argc                             \
                );                                       \
        }                                                \
} while (0)

#define CHECK_ARGC_4(n0, n1, n2, n3) do {                            \
        if (argc != n0 && argc != n1 && argc != n2 && argc != n3) {  \
                zP(                                                  \
                        "%s: expected "                              \
                        #n0 ", " #n1 ", " #n2 ", or " #n2 " "        \
                        "arguments but got %d",                      \
                        _name__,                                     \
                        argc                                         \
                );                                                   \
        }                                                            \
} while (0)

#define CHECK_ARGC(...) VA_SELECT(CHECK_ARGC, __VA_ARGS__)

#define ASSERT_ARGC(func, ...)      \
        char const *_name__ = func; \
        CHECK_ARGC(__VA_ARGS__)

noreturn void vm_panic(Ty *, char const *, ...);

inline static bool
IsNone(Value const v)
{
        return (v.type == VALUE_NONE);
}

inline static bool
IsNil(Value const v)
{
        return (v.type == VALUE_NIL);
}

inline static bool
IsMissing(Value const v)
{
        return IsNone(v) || IsNil(v);
}

inline static Value
checked_arg_1(
        Ty *ty,
        char const *fun,
        char const *name,
        Value const *argp,
        Value const *named,
        int t0
)
{
        Value arg = (named != NULL) ? *named
                  : (argp  != NULL) ? *argp
                  : NONE;
        int const _t = arg.type;

        if (
                (_t != t0)
             && (t0 != VALUE_ANY || IsNone(arg))
        ) {
                zP(
                        "%s: expected `%s` :: %s but got: %s",
                        fun,
                        name,
                        TypeName(ty, t0),
                        VSC(&arg)
                );
        }

        return arg;
}

inline static Value
checked_arg_2(
        Ty *ty,
        char const *fun,
        char const *name,
        Value const *argp,
        Value const *named,
        int t0,
        int t1
)
{
        Value arg = (named != NULL) ? *named
                  : (argp  != NULL) ? *argp
                  : NONE;
        int const _t = arg.type;

        if (_t != t0 && _t != t1) {
                zP(
                        "%s: expected `%s` :: (%s | %s) but got: %s",
                        fun,
                        name,
                        TypeName(ty, t0),
                        TypeName(ty, t1),
                        VSC(&arg)
                );
        }

        return arg;
}

inline static Value
checked_arg_3(
        Ty *ty,
        char const *fun,
        char const *name,
        Value const *argp,
        Value const *named,
        int t0,
        int t1,
        int t2
)
{
        Value arg = (named != NULL) ? *named
                  : (argp  != NULL) ? *argp
                  : NONE;
        int const _t = arg.type;

        if (_t != t0 && _t != t1 && _t != t2) {
                zP(
                        "%s: expected `%s` :: (%s | %s | %s) but got: %s",
                        fun,
                        name,
                        TypeName(ty, t0),
                        TypeName(ty, t1),
                        TypeName(ty, t2),
                        VSC(&arg)
                );
        }

        return arg;
}

inline static Value
checked_arg_4(
        Ty *ty,
        char const *fun,
        char const *name,
        Value const *argp,
        Value const *named,
        int t0,
        int t1,
        int t2,
        int t3
)
{
        Value arg = (named != NULL) ? *named
                  : (argp  != NULL) ? *argp
                  : NONE;

        int const _t = arg.type;

        if (_t != t0 && _t != t1 && _t != t2 && _t != t3) {
                zP(
                        "%s: expected `%s` :: (%s | %s | %s | %s) but got: %s",
                        fun,
                        name,
                        TypeName(ty, t0),
                        TypeName(ty, t1),
                        TypeName(ty, t2),
                        TypeName(ty, t3),
                        VSC(&arg)
                );
        }

        return arg;
}

inline static Value
checked_arg_5(
        Ty *ty,
        char const *fun,
        char const *name,
        Value const *argp,
        Value const *named,
        int t0,
        int t1,
        int t2,
        int t3,
        int t4
)
{
        Value arg = (named != NULL) ? *named
                  : (argp  != NULL) ? *argp
                  : NONE;

        int const _t = arg.type;

        if (_t != t0 && _t != t1 && _t != t2 && _t != t3 && _t != t4) {
                zP(
                        "%s: expected `%s` :: (%s | %s | %s | %s | %s) but got: %s",
                        fun,
                        name,
                        TypeName(ty, t0),
                        TypeName(ty, t1),
                        TypeName(ty, t2),
                        TypeName(ty, t3),
                        TypeName(ty, t4),
                        VSC(&arg)
                );
        }

        return arg;
}

inline static Value
checked_arg_6(
        Ty *ty,
        char const *fun,
        char const *name,
        Value const *argp,
        Value const *named,
        int t0,
        int t1,
        int t2,
        int t3,
        int t4,
        int t5
)
{
        Value arg = (named != NULL) ? *named
                  : (argp  != NULL) ? *argp
                  : NONE;

        int const _t = arg.type;

        if (_t != t0 && _t != t1 && _t != t2 && _t != t3 && _t != t4 && _t != t5) {
                zP(
                        "%s: expected `%s` :: (%s | %s | %s | %s | %s | %s) but got: %s",
                        fun,
                        name,
                        TypeName(ty, t0),
                        TypeName(ty, t1),
                        TypeName(ty, t2),
                        TypeName(ty, t3),
                        TypeName(ty, t4),
                        TypeName(ty, t5),
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
                "arg[" #i "]",         \
                &ARG(i),               \
                NULL,                  \
                __VA_ARGS__            \
        )

#define ARG__(i, name, ...)                            \
        VA_SELECT_INNER(                               \
                checked_arg,                           \
                VA_COUNT(__VA_ARGS__)                  \
        )(                                             \
                ty,                                    \
                _name__,                               \
                name,                                  \
                (i >= 0 && i < argc) ? &ARG(i) : NULL, \
                NAMED(name),                           \
                __VA_ARGS__                            \
        )

#define ARG_xD_3(i, name, t0)                     ARG__((i), (name), VALUE_##t0)
#define ARG_xD_4(i, name, t0, t1)                 ARG__((i), (name), VALUE_##t0, VALUE_##t1)
#define ARG_xD_5(i, name, t0, t1, t2)             ARG__((i), (name), VALUE_##t0, VALUE_##t1, VALUE_##t2)
#define ARG_xD_6(i, name, t0, t1, t2, t3)         ARG__((i), (name), VALUE_##t0, VALUE_##t1, VALUE_##t2, VALUE_##t3)
#define ARG_xD_7(i, name, t0, t1, t2, t3, t4)     ARG__((i), (name), VALUE_##t0, VALUE_##t1, VALUE_##t2, VALUE_##t3, VALUE_##t4)
#define ARG_xD_8(i, name, t0, t1, t2, t3, t4, t5) ARG__((i), (name), VALUE_##t0, VALUE_##t1, VALUE_##t2, VALUE_##t3, VALUE_##t4, VALUE_##t5)

#define KWARG_xD_2(name, t0)                     ARG__(-1, (name), VALUE_NONE, VALUE_##t0)
#define KWARG_xD_3(name, t0, t1)                 ARG__(-1, (name), VALUE_NONE, VALUE_##t0, VALUE_##t1)
#define KWARG_xD_4(name, t0, t1, t2)             ARG__(-1, (name), VALUE_NONE, VALUE_##t0, VALUE_##t1, VALUE_##t2)
#define KWARG_xD_5(name, t0, t1, t2, t3)         ARG__(-1, (name), VALUE_NONE, VALUE_##t0, VALUE_##t1, VALUE_##t2, VALUE_##t3)
#define KWARG_xD_6(name, t0, t1, t2, t3, t4)     ARG__(-1, (name), VALUE_NONE, VALUE_##t0, VALUE_##t1, VALUE_##t2, VALUE_##t3, VALUE_##t4)
#define KWARG_xD_7(name, t0, t1, t2, t3, t4, t5) ARG__(-1, (name), VALUE_NONE, VALUE_##t0, VALUE_##t1, VALUE_##t2, VALUE_##t3, VALUE_##t4, VALUE_##t5)

#define ARGxD(...) VA_SELECT(ARG_xD,   __VA_ARGS__)
#define KWARG(...) VA_SELECT(KWARG_xD, __VA_ARGS__)

#define    INT_ARG(i) ARGx(i, VALUE_INTEGER).integer
#define    PTR_ARG(i) ARGx(i, VALUE_PTR).ptr
#define  FLOAT_ARG(i) ARGx(i, VALUE_REAL).real
#define   BOOL_ARG(i) ARGx(i, VALUE_BOOLEAN).boolean
#define  ARRAY_ARG(i) ARGx(i, VALUE_ARRAY).array
#define   DICT_ARG(i) ARGx(i, VALUE_DICT).dict

#define bP(fmt, ...) zP("%s: " fmt, _name__ __VA_OPT__(,) __VA_ARGS__)

#if 0
  #define value_mark(ty, v) do { fprintf(stderr, "value_mark: %s:%d: %p\n", __FILE__, __LINE__, (v)); _value_mark(ty, v); } while (0)
#else
  #define value_mark _value_mark
#endif

u64
value_hash(Ty *ty, Value const *val);

bool
value_test_equality(Ty *ty, Value const *v1, Value const *v2);

int
value_compare(Ty *ty, Value const *v1, Value const *v2);

bool
value_truthy(Ty *ty, Value const *v);

bool
value_apply_predicate(Ty *ty, Value *p, Value *v);

Value
value_apply_callable(Ty *ty, Value *f, Value *v);

char *
value_show(Ty *ty, Value const *v);

inline static void *
value_string_alloc(Ty *ty, u32 n)
{
        return mAo(n, GC_STRING);
}

inline static void *
value_string_clone(Ty *ty, void const *src, u32 n)
{
        if (src == NULL) {
                return NULL;
        }

        u8 *str = mAo(n + 1, GC_STRING);

        memcpy(str, src, n);
        str[n] = '\0';

        return str;
}

inline static void *
value_string_clone_nul(Ty *ty, void const *src, u32 n)
{
        u8 *str = mAo(n + 1, GC_STRING);

        memcpy(str, src, n);
        str[n] = '\0';

        return str;
}


struct array *
value_array_clone(Ty *ty, struct array const *);

void
value_array_extend(Ty *ty, struct array *, struct array const *);

struct blob *
value_blob_new(Ty *ty);

Value
value_tuple(Ty *ty, int n);

Value
value_record(Ty *ty, int n);

Value
value_named_tuple(Ty *ty, char const *first, ...);

Value *
tuple_get(Value const *tuple, char const *name);

Value *
tuple_get_i(Value const *tuple, int id);

inline static Value *
tget_or_null(Value const *tuple, uintptr_t k)
{
        if ((tuple->type & ~VALUE_TAGGED) != VALUE_TUPLE) {
                return NULL;
        }

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

        if (n == 0) {
                return memset(a, 0, sizeof *a);
        }

        NOGC(a);

        a->items = mA(n * sizeof (Value));
        a->capacity = n;
        a->count = 0;

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
STRING_VFORMAT(Ty *ty, char const *fmt, va_list ap)
{
        va_list _ap;
        u8 *str;
        byte_vector buf = {0};

        SCRATCH_SAVE();
        va_copy(_ap, ap);
        scvdump(ty, &buf, fmt, _ap);
        va_end(_ap);
        str = mAo(vN(buf) + 1, GC_STRING);
        memcpy(str, vv(buf), vN(buf) + 1);
        SCRATCH_RESTORE();

        return (Value) {
                .type = VALUE_STRING,
                .tags = 0,
                .str = str,
                .bytes = vN(buf),
                .str0 = str,
        };
}

inline static Value
STRING_FORMAT(Ty *ty, char const *fmt, ...)
{
        va_list ap;
        Value str;

        va_start(ap, fmt);
        str = STRING_VFORMAT(ty, fmt, ap);
        va_end(ap);

        return str;
}

inline static Value
STRING_CLONE(Ty *ty, void const *s, u32 n)
{
        u8 *clone = value_string_clone(ty, s, n);

        return (Value) {
                .type = VALUE_STRING,
                .tags = 0,
                .str = clone,
                .bytes = n,
                .str0 = clone,
        };
}

inline static Value
STRING_CLONE_C(Ty *ty, void const *s)
{
        if (s == NULL) {
                return NIL;
        }

        u32 n = strlen(s);
        u8 *clone = value_string_clone(ty, s, n);

        return (Value) {
                .type = VALUE_STRING,
                .tags = 0,
                .str = clone,
                .bytes = n,
                .str0 = clone,
        };
}

inline static Value
STRING_C_CLONE_C(Ty *ty, void const *s)
{
        if (s == NULL) {
                return NIL;
        }

        u32 n = strlen(s);
        u8 *clone = value_string_clone_nul(ty, s, n);

        return (Value) {
                .type = VALUE_STRING,
                .tags = 0,
                .str = clone,
                .bytes = n,
                .str0 = clone,
        };
}

inline static Value
STRING_C_CLONE(Ty *ty, void const *s, u32 n)
{
        u8 *clone = value_string_clone_nul(ty, s, n);

        return (Value) {
                .type = VALUE_STRING,
                .tags = 0,
                .str = clone,
                .bytes = n,
                .str0 = clone,
        };
}

inline static Value
STRING(void *s, u32 n)
{
        return (Value) {
                .type = VALUE_STRING,
                .tags = 0,
                .str = s,
                .bytes = n,
                .str0 = s,
        };
}

inline static Value
STRING_VIEW(Value s, isize offset, u32 n)
{
        return (Value) {
                .type = VALUE_STRING,
                .tags = 0,
                .str = s.str + offset,
                .bytes = n,
                .str0 = s.str0,
                .ro = s.ro
        };
}

inline static Value
STRING_NOGC(void const *s, int n)
{
        return (Value) {
                .type = VALUE_STRING,
                .tags = 0,
                .str = s,
                .bytes = n,
                .str0 = (u8 *)s,
                .ro = true
        };
}

inline static Value
STRING_NOGC_C(void const *s)
{
        return (Value) {
                .type = VALUE_STRING,
                .tags = 0,
                .str = s,
                .bytes = strlen(s),
                .str0 = (u8 *)s,
                .ro = true
        };
}

#define STRING_EMPTY (STRING_NOGC(NULL, 0))

inline static bool
DecrementString(Value *v)
{
        if (
                (v->str0 == NULL)
             || (v->str0 == v->str)
        ) {
                return false;
        }

        while (v->str > v->str0) {
                v->str -= 1;
                v->bytes += 1;
                if ((*v->str & 0x80) != 0x80) {
                        break;
                }
        }

        return true;
}

inline static Value
OffsetString(Value const *v, isize n)
{
        Value str = *v;


        while (n > 0 && str.bytes > 0) {
                i32 sz = u8_rune_sz(v->str);
                str.str += sz;
                str.bytes -= sz;
                n -= 1;
        }

        while (n < 0 && DecrementString(&str)) {
                n += 1;
        }

        return str;
}

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

inline static void const *
info_of(Value const *f, int i)
{
        return ((char *)f->info) + i;
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

inline static Expr *
expr_of(Value const *f)
{
        uintptr_t p;
        memcpy(&p, (char *)f->info + FUN_EXPR, sizeof p);
        return (Expr *)p;
}

inline static Type *
type_of(Value const *f)
{
        return expr_of(f)->_type;
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

inline static Type *
as_type(Value const *v)
{
        return v->ptr;
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
        case VALUE_BOOLEAN:           return CLASS_BOOL;
        case VALUE_BLOB:              return CLASS_BLOB;
        case VALUE_ARRAY:             return CLASS_ARRAY;
        case VALUE_DICT:              return CLASS_DICT;
        case VALUE_TUPLE:             return CLASS_TUPLE;
        case VALUE_GENERATOR:         return CLASS_GENERATOR;
        case VALUE_CLASS:             return CLASS_CLASS;
        case VALUE_TAG:               return CLASS_TAG;
        case VALUE_FUNCTION:          return CLASS_FUNCTION;
        case VALUE_METHOD:            return CLASS_FUNCTION;
        case VALUE_BUILTIN_FUNCTION:  return CLASS_FUNCTION;
        case VALUE_BUILTIN_METHOD:    return CLASS_FUNCTION;
        case VALUE_OPERATOR:          return CLASS_FUNCTION;
        case VALUE_NIL:               return CLASS_NIL;

        case VALUE_REGEX:
                return v->regex->detailed ? CLASS_REGEXV
                                          : CLASS_REGEX;
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
        new->count = a->count;

        return new;
}

inline static Value
unwrap(Ty *ty, Value const *wrapped)
{
        Value v = *wrapped;

        if (v.tags != 0) {
                v.tags = tags_pop(ty, v.tags);
        }

        if (v.tags == 0) {
                v.type &= ~VALUE_TAGGED;
        }

        return v;
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

inline static Value
FunDef(Ty *ty, Value const *f)
{
        extern Value CToTyExpr(Ty *, Expr *);

        Value def = CToTyExpr(ty, expr_of(f));
        return unwrap(ty, &def);
}

inline static Value *
NewZero(void)
{
        return alloc0(sizeof *NewZero());
}

#endif

/* vim: set sts=8 sw=8 expandtab: */
