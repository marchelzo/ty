typedef struct value Value;

#ifndef VALUE_H_INCLUDED
#define VALUE_H_INCLUDED

#include <stdbool.h>
#include <stdint.h>
#include <stdarg.h>
#include <string.h>

#include "ty.h"
#include "ast.h"
#include "vec.h"
#include "object.h"
#include "gc.h"
#include "tags.h"
#include "tthread.h"
#include "scope.h"
#include "compiler.h"
#include "xd.h"
#include "class.h"
#include "queue.h"

#define V_ALIGN (_Alignof (Value))

#define RawObject(c) ((RawObject)(ty, (c)))
#define NewInstance(c, ...) ((NewInstance)(ty, (c), __VA_ARGS__ __VA_OPT__(,) NONE))

enum {
        CLASS_BOTTOM = INT_MIN,
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
        CLASS_GENERATOR,
        CLASS_TAG,
        CLASS_TUPLE,
        CLASS_QUEUE,
        CLASS_SHARED_QUEUE,
        CLASS_MODULE,
        CLASS_PRIMITIVE = CLASS_MODULE,
        CLASS_ERROR,
        CLASS_COMPILE_ERROR,
        CLASS_RUNTIME_ERROR,
        CLASS_VALUE_ERROR,
        CLASS_ASSERT_ERROR,
        CLASS_TIMEOUT_ERROR,
        CLASS_CANCELED_ERROR,
        CLASS_OS_ERROR,
        CLASS_RE_MATCH,
        CLASS_INTO_PTR,
        CLASS_ITERABLE,
        CLASS_ITER,
        CLASS_RANGE,
        CLASS_INC_RANGE,
        CLASS_TUPLE_SPEC,
        CLASS_BUILTIN_END
};

#define TY_AST_NODES            \
        X(Expr)                 \
        X(Stmt)                 \
        X(Value)                \
        X(Import)               \
        X(TypeDef)              \
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
        X(Pack)                 \
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
        X(DotDot)               \
        X(DotDotDot)            \
        X(Unsafe)               \
        X(Super)                \
        X(TypeOf)               \
        X(FuncType)             \
        X(Cast)                 \
        X(Resolved)             \
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
        TAG_ZERO_DIV_ERR,
        TAG_NONE,
        TAG_SOME,
        TAG_OK,
        TAG_ERR
};

enum {
        TY_SPAWN_NULL       = -12,
        TY_SPAWN_PIPE       = -13,
        TY_SPAWN_INHERIT    = -14,
        TY_SPAWN_MERGE_ERR  = -15
};

enum {
        TY_SHOW_REPR    = (1 << 0),
        TY_SHOW_BASIC   = (1 << 1),
        TY_SHOW_ABBREV  = (1 << 2),
        TY_SHOW_NOCOLOR = (1 << 3)

};

static inline char const *
TypeName(Ty const *ty, int t0)
{
        switch (t0) {
        case VALUE_INTEGER:             return "Int";
        case VALUE_REAL:                return "Float";
        case VALUE_STRING:              return "String";
        case VALUE_ARRAY:               return "Array";
        case VALUE_DICT:                return "Dict";
        case VALUE_BLOB:                return "Blob";
        case VALUE_QUEUE:               return "Queue";
        case VALUE_SHARED_QUEUE:        return "SharedQueue";
        case VALUE_OBJECT:              return "Object";
        case VALUE_BOOLEAN:             return "Bool";
        case VALUE_REGEX:               return "Regex";
        case VALUE_OPERATOR:            return "<operator>";
        case VALUE_CLASS:               return "Class";
        case VALUE_METHOD:
        case VALUE_BUILTIN_METHOD:
        case VALUE_BUILTIN_FUNCTION:
        case VALUE_FOREIGN_FUNCTION:
        case VALUE_BOUND_FUNCTION:
        case VALUE_FUNCTION:
                                        return "Function";
        case VALUE_GENERATOR:           return "Generator";
        case VALUE_TUPLE:               return "Tuple";
        case VALUE_TAG:                 return "Tag";
        case VALUE_THREAD:              return "<thread>";
        case VALUE_PTR:                 return "Ptr";
        case VALUE_NIL:                 return "nil";
        case VALUE_NONE:                return "<none>";
        case VALUE_ANY:                 return "Any";
        case VALUE_MODULE:              return "Module";

        default:                        return "<internal>";
        }
}

char const *
class_name(Ty *ty, int c);

static inline char const *
ValueTypeName(Ty *ty, Value const *v)
{
        if (V_TYPE(*(v)) & VALUE_TAGGED) {
                return tags_name(ty, tags_first(ty, V_TAGS(*(v))));
        }

        if (V_TYPE(*(v)) == VALUE_OBJECT) {
                return class_name(ty, V_CLASS(*(v)));
        }

        return TypeName(ty, V_TYPE(*(v)));
}

char *
value_show_color(Ty *ty, Value const *v, u32 flags);

Value
value_vshow_color(Ty *ty, Value const *v, u32 flags);

#define DEFINE_METHOD_TABLE(type, ...)                               \
        static struct {                                              \
                char const *name;                                    \
                BuiltinMethod *func;                                 \
        } type##_funcs[] = { __VA_ARGS__ };                          \
        static vec(BuiltinMethod *) type##_table

#define DEFINE_METHOD_TABLE_BUILDER(type)                                                 \
        void build_##type##_method_table(void)                                            \
        {                                                                                 \
                for (int i = 0; i < countof(type##_funcs); ++i) {                         \
                        InternEntry *e = intern(&xD.members, type##_funcs[i].name);       \
                        while (type##_table.count <= e->id) { xvP(type##_table, NULL); }  \
                        type##_table.items[e->id] = type##_funcs[i].func;                 \
                }                                                                         \
        }

#define DEFINE_METHOD_LOOKUP(type)                                               \
        BuiltinMethod *get_##type##_method_i(int i)                              \
        {                                                                        \
                return (i < type##_table.count) ? type##_table.items[i] : NULL;  \
        }                                                                        \
                                                                                 \
        BuiltinMethod *get_##type##_method(char const *name)                     \
        {                                                                        \
                InternEntry *e = intern(&xD.members, name);                      \
                return (get_##type##_method_i)(e->id);                           \
        }

#define DEFINE_METHOD_LOOKUP2(type)                                   \
        BuiltinMethod *get_##type##_method(char const *name)          \
        {                                                             \
                int lo = 0,                                           \
                    hi = countof(type##_funcs - 1);                   \
                                                                      \
                while (lo <= hi) {                                    \
                        int m = (lo + hi) / 2;                        \
                        int c = strcmp(name, type##_funcs[m].name);   \
                        if      (c < 0) hi = m - 1;                   \
                        else if (c > 0) lo = m + 1;                   \
                        else            return type##_funcs[m].func;  \
                }                                                     \
                                                                      \
                return NULL;                                          \
        }

#define DEFINE_METHOD_COMPLETER(type)                                              \
        int                                                                        \
        type##_get_completions(                                                    \
                Ty *ty,                                                            \
                char const *prefix,                                                \
                char **out,                                                        \
                int max                                                            \
        )                                                                          \
        {                                                                          \
                int n = 0;                                                         \
                int len = strlen(prefix);                                          \
                                                                                   \
                for (int i = 0; i < countof(type##_funcs); ++i) {                  \
                        if (                                                       \
                                (n < max)                                          \
                             && (strncmp(type##_funcs[i].name, prefix, len) == 0)  \
                        ) {                                                        \
                                out[n++] = S2(type##_funcs[i].name);               \
                        }                                                          \
                }                                                                  \
                                                                                   \
                return n;                                                          \
        }

#define ARG(i) (*vm_get(ty, argc - 1 - (i)))
#define NAMED(s) ((kwargs != NULL && !IsNil(*kwargs)) ? dict_get_member(ty, V_DICT(*kwargs), (s)) : NULL)
#define ARG_T(i) ((argc > i) ? V_TYPE(*vm_get(ty, argc - 1 - (i))) : VALUE_NONE)
#define HAVE_FLAG(s) (value_truthy_checked(ty, NAMED(s)))

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
                        #n0 ", " #n1 ", " #n2 ", or " #n3 " "        \
                        "arguments but got %d",                      \
                        _name__,                                     \
                        argc                                         \
                );                                                   \
        }                                                            \
} while (0)

#define CHECK_ARGC_5(n0, n1, n2, n3, n4) do {                                      \
        if (argc != n0 && argc != n1 && argc != n2 && argc != n3 && argc != n4) {  \
                zP(                                                                \
                        "%s: expected "                                            \
                        #n0 ", " #n1 ", " #n2 ", " #n3 ", or " #n4 " "             \
                        "arguments but got %d",                                    \
                        _name__,                                                   \
                        argc                                                       \
                );                                                                 \
        }                                                                          \
} while (0)

#define CHECK_ARGC(...) VA_SELECT(CHECK_ARGC, __VA_ARGS__)

#define ASSERT_ARGC(func, ...)      \
        char const *_name__ = func; \
        CHECK_ARGC(__VA_ARGS__)

#define ASSERT_ARGC_RANGE(func, n0, n1)                                 \
        char const *_name__ = func;                                     \
        if (argc < n0 || argc > n1) {                                   \
                zP(                                                     \
                        "%s: expected between " #n0 " and " #n1 " "     \
                        "arguments but got %d",                         \
                        _name__,                                        \
                        argc                                            \
                );                                                      \
        }

noreturn void vm_panic(Ty *, char const *, ...);

static inline bool
IsZero(Value const v)
{
        return (V_TYPE(v) == VALUE_ZERO);
}

static inline bool
IsNone(Value const v)
{
        return (V_TYPE(v) == VALUE_NONE);
}

static inline bool
IsNil(Value const v)
{
        return (V_TYPE(v) == VALUE_NIL);
}

static inline bool
IsMissing(Value const v)
{
        return IsNone(v) || IsNil(v);
}

static inline Value
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
        int const _t = V_TYPE(arg);

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

static inline Value
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
        int const _t = V_TYPE(arg);

        if (
                (_t != t0)
             && (_t != t1)
             && (t1 != VALUE_ANY)
        ) {
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

static inline Value
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
        int const _t = V_TYPE(arg);

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

static inline Value
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

        int const _t = V_TYPE(arg);

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

static inline Value
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

        int const _t = V_TYPE(arg);

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

static inline Value
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

        int const _t = V_TYPE(arg);

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

#define TRY_ARG(...) ARGxD(__VA_ARGS__, _NIL, _NONE)

#define    INT_ARG(i) V_Z(ARGx(i, VALUE_INTEGER))
#define  FLOAT_ARG(i) V_REAL(ARGx(i, VALUE_REAL))
#define   BOOL_ARG(i) V_BOOL(ARGx(i, VALUE_BOOLEAN))
#define  ARRAY_ARG(i) V_ARRAY(ARGx(i, VALUE_ARRAY))
#define   DICT_ARG(i) V_DICT(ARGx(i, VALUE_DICT))
#define    PTR_ARG(i) ((ARG_T(i) == VALUE_NIL) ? NULL : V_PTR(ARGx(i, VALUE_PTR)))

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
value_apply_predicate(Ty *ty, Value *p, Value *v);

char *
value_show(Ty *ty, Value const *v, u32 flags);

char *
value_show_scratch(Ty *ty, Value const *v, u32 flags);

Value
value_vshow(Ty *ty, Value const *v, u32 flags);

static inline void *
value_string_alloc(Ty *ty, u32 n)
{
        return mAo(n, GC_STRING);
}

static inline void *
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

static inline void *
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

static inline Value *
tget_or_null(Value const *tuple, uptr k)
{
        if ((V_TYPE(*(tuple)) & ~VALUE_TAGGED) != VALUE_TUPLE) {
                return NULL;
        }

        if (k < 16) {
                return (k >= V_COUNT(*(tuple))) ? NULL : &V_ITEMS(*(tuple))[k];
        }

        char const *name = (char const *)k;
        int id = M_ID(name);

        if (V_IDS(*(tuple)) != NULL) for (int i = 0; i < V_COUNT(*(tuple)); ++i) {
                if (V_IDS(*(tuple))[i] == id) {
                        return &V_ITEMS(*(tuple))[i];
                }
        }

        return NULL;
}

static inline Value
tget_or(Value const *tuple, uptr k, Value _)
{
        Value *v = tget_or_null(tuple, k);
        return (v != NULL) ? *v : _;
}

static inline Value *
tget_t(Value const *tuple, uptr k, u32 t)
{
        Value *v = tget_or_null(tuple, k);
        return (v == NULL || V_TYPE(*(v)) != t) ? NULL : v;
}

static inline Value *
tget_nn(Value const *tuple, uptr k)
{
        Value *v = tget_or_null(tuple, k);
        return (v == NULL || V_TYPE(*(v)) == VALUE_NIL) ? NULL : v;
}

static inline Value
tget_tagged(Value const *tuple, uptr k)
{
        return NONE;
}

#define tget_or(t, i, v)  ((tget_or)((t), (uptr)(i),  (v)))
#define tget_nn(t, i   )  ((tget_nn)((t), (uptr)(i)      ))
#define  tget_t(t, i, t0) ((tget_t) ((t), (uptr)(i), (t0)))

int
tuple_get_completions(Ty *ty, Value const *v, char const *prefix, char **out, int max);

void
_value_mark(Ty *ty, Value const *v);

void
value_mark_push(Ty *ty, Value const *v);

void
value_mark_drain(Ty *ty);

static inline Array *
value_array_new(Ty *ty)
{
        return mAo0(sizeof (Array), GC_ARRAY);
}

static inline Array *
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

static inline Array *
value_array_new_sized_unchecked(Ty *ty, size_t n)
{
        Array *a = uAo(sizeof (Array), GC_ARRAY);

        if (n == 0) {
                return memset(a, 0, sizeof *a);
        }

        a->items = uA(n * sizeof (Value));
        a->capacity = n;
        a->count = 0;

        return a;
}

static inline void
value_array_push(Ty *ty, Array *a, Value v)
{
        if (a->count == a->capacity) {
                /* mRE may trigger GC before v is stored in the array. */
                gP(&v);
                a->capacity = a->capacity ? a->capacity * 2 : 4;
                mRE(a->items, a->capacity * sizeof (Value));
                gX();
        }

        a->items[a->count++] = v;
}

static inline void
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

static inline Value
STRING_VFORMAT(Ty *ty, char const *fmt, va_list ap)
{
        va_list _ap;
        byte_vector buf = {0};

        SCRATCH_SAVE();
        va_copy(_ap, ap);
        scvdump(ty, &buf, fmt, _ap);
        va_end(_ap);
        Value result = value_string_clone_nul_value(ty, vv(buf), vN(buf));
        SCRATCH_RESTORE();
        return result;
}

static inline Value
STRING_FORMAT(Ty *ty, char const *fmt, ...)
{
        va_list ap;
        Value str;

        va_start(ap, fmt);
        str = STRING_VFORMAT(ty, fmt, ap);
        va_end(ap);

        return str;
}

static inline Value
STRING_CLONE(Ty *ty, void const *s, u32 n)
{
        return value_string_clone_value(ty, s, n);
}

static inline Value
STRING_CLONE_C(Ty *ty, void const *s)
{
        if (s == NULL) {
                return NIL;
        }

        u32 n = strlen(s);
        return value_string_clone_value(ty, s, n);
}

static inline Value
STRING_C_CLONE_C(Ty *ty, void const *s)
{
        if (s == NULL) {
                return NIL;
        }

        u32 n = strlen(s);
        return value_string_clone_nul_value(ty, s, n);
}

static inline Value
STRING_C_CLONE(Ty *ty, void const *s, u32 n)
{
        return value_string_clone_nul_value(ty, s, n);
}

static inline Value
STRING(Ty *ty, void *s, u32 n)
{
        return value_string_wrap(ty, s, n, false);
}

static inline Value
STRING_VIEW(Ty *ty, Value s, isize offset, u32 n)
{
        return value_string_view(ty, s, offset, n);
}

static inline Value
STRING_NOGC(Ty *ty, void const *s, u32 n)
{
        return value_string_wrap(ty, s, n, true);
}

static inline Value
STRING_NOGC_C(Ty *ty, void const *s)
{
        return value_string_wrap(ty, s, strlen(s), true);
}

#define STRING_EMPTY (STRING_NOGC(ty, NULL, 0))

static inline bool
DecrementString(Ty *ty, Value *v)
{
        if (
                (V_STR0(*(v)) == NULL)
             || (V_STR0(*(v)) == V_STR(*(v)))
        ) {
                return false;
        }

        u8 const *str = V_STR(*v);
        u32 bytes = V_BYTES(*v);
        while (str > V_STR0(*v)) {
                str -= 1;
                bytes += 1;
                if ((*str & 0x80) != 0x80) {
                        break;
                }
        }
        Value view = value_string_view(ty, *v, str - V_STR(*v), bytes);
        *v = view;

        return true;
}

static inline Value
OffsetString(Ty *ty, Value const *v, i32 n)
{
        u8 const *str = V_STR(*v);
        u32 bytes = V_BYTES(*v);

        while (n > 0 && bytes > 0) {
                i32 sz = u8_rune_sz(str);
                if (sz <= 0) {
                        sz = 1;
                }
                if (sz > bytes) {
                        sz = bytes;
                }
                str += sz;
                bytes -= sz;
                n -= 1;
        }

        while (n < 0 && str > V_STR0(*v)) {
                do { str -= 1; bytes += 1; } while (str > V_STR0(*v) && (*str & 0x80) == 0x80);
                ++n;
        }
        Value view = value_string_view(ty, *v, str - V_STR(*v), bytes);
        return view;
}

struct timespec
tuple_timespec(Ty *ty, char const *func, Value const *v);

static inline Value
(RawObject)(Ty *ty, int c)
{
        return OBJECT(class_new_instance(ty, c), c);
}

Value
(NewInstance)(Ty *ty, int c, ...);

static inline Value
PAIR_(Ty *ty, Value a, Value b)
{
        gP(&a); gP(&b);
        Value v = vT(2);
        gX(); gX();
        V_ITEMS(v)[0] = a;
        V_ITEMS(v)[1] = b;
        return v;
}

static inline Value
TRIPLE_(Ty *ty, Value a, Value b, Value c)
{
        gP(&a); gP(&b); gP(&c);
        Value v = vT(3);
        gX(); gX(); gX();
        V_ITEMS(v)[0] = a;
        V_ITEMS(v)[1] = b;
        V_ITEMS(v)[2] = c;
        return v;
}

static inline Value
QUADRUPLE_(Ty *ty, Value a, Value b, Value c, Value d)
{
        gP(&a); gP(&b); gP(&c); gP(&d);
        Value v = vT(4);
        gX(); gX(); gX(); gX();
        V_ITEMS(v)[0] = a;
        V_ITEMS(v)[1] = b;
        V_ITEMS(v)[2] = c;
        V_ITEMS(v)[3] = d;
        return v;
}

#define None TAG(TAG_NONE)

int
tags_push(Ty *ty, int, int);

static inline Value
Ok(Ty *ty, Value v)
{
        return value_with_tags(ty, v, tags_push(ty, V_TAGS(v), TAG_OK));
}

static inline Value
Err(Ty *ty, Value v)
{
        return value_with_tags(ty, v, tags_push(ty, V_TAGS(v), TAG_ERR));
}

static inline u16
some_tag_chain(Ty *ty)
{
        if (UNLIKELY(ty->some_tag_chain == 0))
                ty->some_tag_chain = tags_push(ty, 0, TAG_SOME);
        return ty->some_tag_chain;
}

static inline Value
Some(Ty *ty, Value v)
{
        if (LIKELY(nanbox_is_int(v.bits)))
                return value_direct_tagged_int(nanbox_to_int(v.bits), some_tag_chain(ty));
        int base = V_TAGS(v);
        if (base == 0)
                return value_with_tags(ty, v, some_tag_chain(ty));
        return value_with_tags(ty, v, tags_push(ty, base, TAG_SOME));
}

#define Some(x) (Some)(ty, x)

static inline u32
header_size_of(Value const *f)
{
        return V_INFO(*(f))[FUN_INFO_HEADER_SIZE];
}

static inline u32
code_size_of(Value const *f)
{
        return V_INFO(*(f))[FUN_INFO_CODE_SIZE];
}

static inline i32
param_count_of(Value const *f)
{
        return V_INFO(*(f))[FUN_INFO_PARAM_COUNT];
}

static inline void *
info_of(Value const *f, int i)
{
        return ((char *)V_INFO(*(f))) + i;
}

static inline i16 *
flags_of(Value const *f)
{
        return (i16 *)info_of(f, FUN_FLAGS);
}

static inline i32
meth_of(Value const *f)
{
        return *((i32 *)info_of(f, FUN_METH));
}

static inline int
rest_idx_of(Value const *v)
{
        return *((i16 *)info_of(v, FUN_REST_IDX));
}

static inline int
kwargs_idx_of(Value const *v)
{
        return *((i16 *)info_of(v, FUN_KWARGS_IDX));
}

static inline char *
code_of(Value const *v)
{
        return (char *)V_INFO(*(v)) + V_INFO(*(v))[0];
}

static inline i32
class_of(Value const *v)
{
        return (V_XINFO(*(v)) != NULL && V_XINFO(*(v))->class > 0)
             ? V_XINFO(*(v))->class
             : V_INFO(*(v))[FUN_INFO_CLASS];
}

static inline Expr *
expr_of(Value const *f)
{
        uptr expr;
        memcpy(&expr, (char *)V_INFO(*f) + FUN_EXPR, sizeof expr);
        return (Expr *)expr;
}

static inline char const *
fqn_of(Value const *f)
{
        return QualifiedName(expr_of(f));
}

static inline bool
is_hidden_fun(Value const *f)
{
        return (*flags_of(f) & FF_HIDDEN);
}

static inline bool
is_overload(Value const *f)
{
        return (*flags_of(f) & FF_OVERLOAD);
}

static inline bool
is_decorated(Value const *f)
{
        return (*flags_of(f) & FF_DECORATED);
}

static inline bool
is_starred(Value const *f)
{
        return (*flags_of(f) & FF_STAR);
}

static inline Type *
type_of(Value const *f)
{
        return expr_of(f)->_type;
}

static inline char const *
proto_of(Value const *f)
{
        if (V_XINFO(*(f)) != NULL && V_XINFO(*(f))->proto != NULL) {
                return V_XINFO(*(f))->proto;
        } else {
                return (char const *)*(uptr *)info_of(f, FUN_PROTO);
        }
}

static inline char const *
doc_of(Value const *f)
{
        if (V_XINFO(*(f)) != NULL && V_XINFO(*(f))->doc != NULL) {
                return V_XINFO(*(f))->doc;
        } else {
                return (char const *)*(uptr *)info_of(f, FUN_DOC);
        }
}

static inline char const *
name_of(Value const *f)
{
        if (V_XINFO(*(f)) != NULL && V_XINFO(*(f))->name != NULL) {
                return V_XINFO(*(f))->name;
        } else {
                return (char const *)*(uptr *)info_of(f, FUN_NAME);
        }
}

static inline void
set_name_of(Value const *f, uptr name)
{
        *(uptr *)info_of(f, FUN_NAME) = name;
}

static inline bool
has_meta(Value const *f)
{
        return (*flags_of(f) & FF_HAS_META);
}

static inline Value *
meta_of(Ty *ty, Value const *f)
{
        uptr p;
        Value *meta;

        char *addr = (char *)V_INFO(*(f)) + FUN_META;

        memcpy(&p, addr, sizeof p);
        if (p == 0) {
                meta = mAo(sizeof (Value), GC_VALUE);
                *meta = NewInstance(CLASS_OBJECT);
                p = (uptr)meta;
                memcpy(addr, &p, sizeof p);
                *flags_of(f) |= FF_HAS_META;
        } else {
                meta = (Value *)p;
        }

        return meta;
}

static inline Value
self_of(Value const *f)
{
        if (V_TYPE(*(f)) == VALUE_BOUND_FUNCTION) {
                return *V_ENV(*(f))[V_INFO(*(f))[FUN_INFO_CAPTURES]];
        } else {
                return NIL;
        }
}

static inline void *
jit_of(Value const *f)
{
        uptr jit;
#if !defined(TY_NO_JIT)
        memcpy(&jit, (char *)V_INFO(*f) + FUN_JIT, sizeof jit);
#else
        jit = 0;
#endif
        return (void *)jit;
}

static inline void
set_jit_of(Value const *f, void *code)
{
        uptr jit = (uptr)code;
#if !defined(TY_NO_JIT)
        memcpy((char *)V_INFO(*f) + FUN_JIT, &jit, sizeof jit);
#endif
}

static inline bool
from_eval(Value const *f)
{
        return (*flags_of(f) & FF_FROM_EVAL);
}

static inline Type *
as_type(Value const *v)
{
        return V_PTR(*(v));
}

#define PACK_TYPES(t1, t2) ((((u64)t1) << 32) | ((u32)t2))
#define    PAIR_OF(t)      PACK_TYPES(t, t)

static inline int
ClassOf(Value const *v)
{
        switch (V_TYPE(*(v))) {
        case VALUE_OBJECT:            return V_CLASS(*(v));
        case VALUE_INTEGER:           return CLASS_INT;
        case VALUE_REAL:              return CLASS_FLOAT;
        case VALUE_STRING:            return CLASS_STRING;
        case VALUE_BOOLEAN:           return CLASS_BOOL;
        case VALUE_BLOB:              return CLASS_BLOB;
        case VALUE_QUEUE:             return CLASS_QUEUE;
        case VALUE_SHARED_QUEUE:      return CLASS_SHARED_QUEUE;
        case VALUE_ARRAY:             return CLASS_ARRAY;
        case VALUE_DICT:              return CLASS_DICT;
        case VALUE_TUPLE:             return CLASS_TUPLE;
        case VALUE_GENERATOR:         return CLASS_GENERATOR;
        case VALUE_CLASS:             return CLASS_CLASS;
        case VALUE_TAG:               return CLASS_TAG;
        case VALUE_FUNCTION:          return CLASS_FUNCTION;
        case VALUE_BOUND_FUNCTION:    return CLASS_FUNCTION;
        case VALUE_METHOD:            return CLASS_FUNCTION;
        case VALUE_BUILTIN_FUNCTION:  return CLASS_FUNCTION;
        case VALUE_BUILTIN_METHOD:    return CLASS_FUNCTION;
        case VALUE_FOREIGN_FUNCTION:  return CLASS_FUNCTION;
        case VALUE_OPERATOR:          return CLASS_FUNCTION;
        case VALUE_MODULE:            return CLASS_MODULE;
        case VALUE_NIL:               return CLASS_NIL;
        case VALUE_PTR:               return CLASS_PTR;

        case VALUE_REGEX:
                return V_REGEX(*(v))->detailed ? CLASS_REGEXV
                                          : CLASS_REGEX;
        }

        return CLASS_TOP;
}

static inline bool
ArrayIsSmall(Array const *a)
{
        return ((uptr)a & 7);
}

static inline Value *
ArrayItems(Array *a)
{
        uptr p = (uptr)a;
        return (p & 7)
             ? (Value *)(p & ~7)
             : a->items;
}

static inline size_t
ArrayCount(Array *a)
{
        uptr p = (uptr)a & ~7;
        return (p > 0) ? (p - 1) : a->count;
}

static inline Array *
ArrayClone(Ty *ty, Array const *a)
{
        if (a->count == 0)
                return vA();

        Array *new = vAn(a->count);

        memcpy(new->items, a->items, a->count * sizeof (Value));
        new->count = a->count;

        return new;
}

static inline DictItem *
DictFirst(Dict const *d)
{
        DictItem *it = d->last;

        while (it != NULL && it->prev != NULL) {
                it = it->prev;
        }

        return it;
}

static inline Value
stripped(Ty *ty, Value const *wrapped)
{
        return value_with_tags(ty, *wrapped, 0);
}

static inline Value
unwrap(Ty *ty, Value const *wrapped)
{
        u16 tags = V_TAGS(*wrapped);
        if (tags != 0) tags = tags_pop(ty, tags);
        return value_with_tags(ty, *wrapped, tags);
}

#define TryUnwrap(v, t) ((TryUnwrap)(ty, (v), (t)))
static inline bool
(TryUnwrap)(Ty *ty, Value *wrapped, int tag)
{
        if (value_is_direct_tagged_int(*wrapped) && tag == TAG_SOME
            && value_direct_tagged_int_tags(*wrapped) == some_tag_chain(ty)) {
                *wrapped = value_integer(ty, value_direct_tagged_int_value(*wrapped));
                return true;
        }
        u16 tags = V_TAGS(*wrapped);
        if (!tags_try_pop(ty, &tags, tag)) return false;
        if (tags == 0 && value_is_direct_tagged_int(*wrapped))
                *wrapped = value_integer(ty, value_direct_tagged_int_value(*wrapped));
        else
                *wrapped = value_with_tags(ty, *wrapped, (u16)tags);
        return true;
}

#define PopTag(v) ((PopTag)(ty, (v)))
inline static void
(PopTag)(Ty *ty, Value *val)
{
        *val = value_with_tags(ty, *val, tags_pop(ty, V_TAGS(*val)));
}

static inline Value
tagged(Ty *ty, int tag, Value v, ...)
{
        va_list ap;
        va_start(ap, v);
        vec(Value) vs = {0};
        Value next = va_arg(ap, Value);
        if (V_TYPE(next) == VALUE_NONE) goto TagAndReturn;
        svP(vs, v);
        while (V_TYPE(next) != VALUE_NONE) {
                svP(vs, next);
                next = va_arg(ap, Value);
        }
        v = vT(vs.count);
        for (int i = 0; i < vs.count; ++i) V_ITEMS(v)[i] = vs.items[i];
TagAndReturn:
        return value_with_tags(ty, v, tags_push(ty, V_TAGS(v), tag));
}

static inline Value
FunDef(Ty *ty, Value const *f)
{
        Value def = CToTyExpr(ty, expr_of(f));
        return unwrap(ty, &def);
}

static inline Value
ClassDef(Ty *ty, Value const *c)
{
        Value def = CToTyStmt(ty, class_get(ty, V_CLASS(*(c)))->def);
        return unwrap(ty, &def);
}

Value
PrettySource(Ty *ty, Value const *v);

static inline Value *
NewZero(void)
{
        return alloc0(sizeof (struct alloc) + sizeof *NewZero())
             + sizeof (struct alloc);
}

#define PutMember(o, m, x) ((PutMember)(ty, (o), (m), (x)))
static inline void
(PutMember)(Ty *ty, Value v, i32 m, Value x)
{
        Class *c = V_OBJECT(v)->class;
        u16 off;

        if (
                (m < vN(c->offsets_r))
             && ((off = v__(c->offsets_r, m)) != OFF_NOT_FOUND)
        ) {
                V_OBJECT(v)->slots[off & OFF_MASK] = x;
        } else {
                if (V_OBJECT(v)->dynamic == NULL) {
                        V_OBJECT(v)->dynamic = mA0(sizeof (struct itable));
                }
                itable_add(ty, V_OBJECT(v)->dynamic, m, x);
        }
}

#define ObjectMember(o, m) ((ObjectMember)(ty, (o), (m)))
static inline Value *
(ObjectMember)(Ty *ty, Value v, i32 m)
{
        Class *c = V_OBJECT(v)->class;
        u16 off;

        if (
                (m < vN(c->offsets_r))
             && ((off = v__(c->offsets_r, m)) != OFF_NOT_FOUND)
             && ((off >> OFF_SHIFT) == OFF_FIELD)
        ) {
                return &V_OBJECT(v)->slots[off & OFF_MASK];
        } else if (V_OBJECT(v)->dynamic != NULL) {
                return itable_lookup(ty, V_OBJECT(v)->dynamic, m);
        } else {
                return NULL;
        }
}

inline static i64
TryIntoTime(Ty *ty, char const *ctx, Value const *t, i64 factor)
{
        struct timespec spec;

        switch (V_TYPE(*(t))) {
        case VALUE_REAL:
                return (factor * V_REAL(*(t)));

        case VALUE_INTEGER:
                return V_Z(*(t));

        case VALUE_TUPLE:
                spec = tuple_timespec(ty, ctx, t);
                return (factor * (TY_1e9*spec.tv_sec + spec.tv_nsec)) / TY_1e9;

        case VALUE_NIL:
                return -1;

        default:
                zP("%s: invalid timespec: %s", ctx, VSC(t));
        }
}

#define NSEC_ARG(i) TryIntoTime(ty, _name__, &ARG(i), 1000000000)
#define USEC_ARG(i) TryIntoTime(ty, _name__, &ARG(i), 1000000)
#define MSEC_ARG(i) TryIntoTime(ty, _name__, &ARG(i), 1000)

#define MSEC_TIMEOUT_ARG(i) (                          \
        (ARG_T(i) == VALUE_REAL) ? max(MSEC_ARG(i), 0) \
      : (ARG_T(i) == VALUE_NONE) ? (u64)-1             \
      : MSEC_ARG(i)                                    \
)

#define NSEC_TIMEOUT_ARG(i) (                          \
        (ARG_T(i) == VALUE_REAL) ? max(NSEC_ARG(i), 0) \
      : (ARG_T(i) == VALUE_NONE) ? (u64)-1             \
      : NSEC_ARG(i)                                    \
)

Value
ConstructPrimitive(Ty *ty, int class_id, int argc, Value *kwargs);

inline static bool
value_truthy(Ty *ty, Value const *v)
{
        switch (V_TYPE(*(v))) {
        case VALUE_REAL:             return (V_REAL(*(v)) != 0.0);
        case VALUE_BOOLEAN:          return V_BOOL(*(v));
        case VALUE_INTEGER:          return (V_Z(*(v)) != 0);
        case VALUE_STRING:           return (sN(*v) != 0);
        case VALUE_ARRAY:            return (vN(*V_ARRAY(*v)) != 0);
        case VALUE_TUPLE:            return (V_COUNT(*(v)) != 0);
        case VALUE_BLOB:             return (vN(*V_BLOB(*v)) != 0);
        case VALUE_QUEUE:            return (queue_count(V_QUEUE(*(v))) != 0);
        case VALUE_SHARED_QUEUE:     return true;
        case VALUE_REGEX:            return true;
        case VALUE_FUNCTION:         return true;
        case VALUE_BOUND_FUNCTION:   return true;
        case VALUE_BUILTIN_FUNCTION: return true;
        case VALUE_BUILTIN_METHOD:   return true;
        case VALUE_FOREIGN_FUNCTION: return true;
        case VALUE_OPERATOR:         return true;
        case VALUE_DICT:             return true;
        case VALUE_CLASS:            return true;
        case VALUE_OBJECT:           return true;
        case VALUE_METHOD:           return true;
        case VALUE_TAG:              return true;
        case VALUE_GENERATOR:        return true;
        case VALUE_TRACE:            return true;
        case VALUE_PTR:              return (V_PTR(*(v)) != NULL);
        default:                     return false;
        }
}

static inline bool
value_truthy_checked(Ty *ty, Value const *v)
{
        return (v != NULL) && value_truthy(ty, v);
}

#endif

/* vim: set sts=8 sw=8 expandtab: */
