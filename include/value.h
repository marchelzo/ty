struct value;

#ifndef VALUE_H_INCLUDED
#define VALUE_H_INCLUDED

#include <stdbool.h>
#include <stdint.h>
#include <string.h>

#include "ty.h"
#include "vec.h"
#include "ast.h"
#include "gc.h"
#include "tags.h"
#include "tthread.h"
#include "token.h"
#include "scope.h"

#define V_ALIGN (_Alignof (struct value))

#define POINTER(p)    { .type = VALUE_PTR,              .ptr              = (p), .tags = 0 }

#define INTEGER(k)               ((struct value){ .type = VALUE_INTEGER,        .integer        = (k),                                                   .tags = 0 })
#define REAL(f)                  ((struct value){ .type = VALUE_REAL,           .real           = (f),                                                   .tags = 0 })
#define BOOLEAN(b)               ((struct value){ .type = VALUE_BOOLEAN,        .boolean        = (b),                                                   .tags = 0 })
#define ARRAY(a)                 ((struct value){ .type = VALUE_ARRAY,          .array          = (a),                                                   .tags = 0 })
#define TUPLE(vs, ns, n, gc)     ((struct value){ .type = VALUE_TUPLE,          .items          = (vs), .count = (n),  .names = (ns), .gc_names = (gc),  .tags = 0 })
#define BLOB(b)                  ((struct value){ .type = VALUE_BLOB,           .blob           = (b),                                                   .tags = 0 })
#define DICT(d)                  ((struct value){ .type = VALUE_DICT,           .dict           = (d),                                                   .tags = 0 })
#define REGEX(r)                 ((struct value){ .type = VALUE_REGEX,          .regex          = (r),                                                   .tags = 0 })
#define FUNCTION()               ((struct value){ .type = VALUE_FUNCTION,                                                                                .tags = 0 })
#define PTR(p)                   ((struct value){ .type = VALUE_PTR,            .ptr            = (p),  .gcptr = NULL,                                   .tags = 0 })
#define TPTR(t, p)               ((struct value){ .type = VALUE_PTR,            .ptr            = (p),  .gcptr = NULL,  .extra = (t),                    .tags = 0 })
#define GCPTR(p, gcp)            ((struct value){ .type = VALUE_PTR,            .ptr            = (p),  .gcptr = (gcp),                                  .tags = 0 })
#define TGCPTR(p, t, gcp)        ((struct value){ .type = VALUE_PTR,            .ptr            = (p),  .gcptr = (gcp), .extra = (t),                    .tags = 0 })
#define EPTR(p, gcp, ep)         ((struct value){ .type = VALUE_PTR,            .ptr            = (p),  .gcptr = (gcp), .extra = (ep),                   .tags = 0 })
#define BLOB(b)                  ((struct value){ .type = VALUE_BLOB,           .blob           = (b),                                                   .tags = 0 })
#define REF(p)                   ((struct value){ .type = VALUE_REF,            .ptr            = (p),                                                   .tags = 0 })
#define UNINITIALIZED(p)         ((struct value){ .type = VALUE_UNINITIALIZED,  .ptr            = (p),                                                   .tags = 0 })
#define TAG(t)                   ((struct value){ .type = VALUE_TAG,            .tag            = (t),                                                   .tags = 0 })
#define CLASS(c)                 ((struct value){ .type = VALUE_CLASS,          .class          = (c),  .object = NULL,                                  .tags = 0 })
#define OBJECT(o, c)             ((struct value){ .type = VALUE_OBJECT,         .object         = (o),  .class  = (c),                                   .tags = 0 })
#define METHOD(n, m, t)          ((struct value){ .type = VALUE_METHOD,         .method         = (m),  .this   = (t),  .name = (n),                     .tags = 0 })
#define GENERATOR(g)             ((struct value){ .type = VALUE_GENERATOR,      .gen            = (g),                                                   .tags = 0 })
#define THREAD(t)                ((struct value){ .type = VALUE_THREAD,         .thread         = (t),                                                   .tags = 0 })
#define BUILTIN_METHOD(n, m, t)  ((struct value){ .type = VALUE_BUILTIN_METHOD, .builtin_method = (m),  .this   = (t),  .name = (n),                     .tags = 0 })
#define NIL                      ((struct value){ .type = VALUE_NIL,                                                                                     .tags = 0 })

/* Special kind of value, only used as an iteration counter in for-each loops */
#define INDEX(ix, o, n)          ((struct value){ .type = VALUE_INDEX,          .i              = (ix), .off   = (o), .nt = (n),     .tags = 0 })

/* Another special one, used for functions with multiple return values */
#define SENTINEL                 ((struct value){ .type = VALUE_SENTINEL,       .i              = 0,    .off   = 0,                  .tags = 0 })

/* This is getting ugly */
#define NONE                     ((struct value){ .type = VALUE_NONE,           .i              = 0,    .off   = 0,                  .tags = 0 })

//#define CALLABLE(v) ((!((v).type & VALUE_TAGGED)) && (((v).type & (VALUE_CLASS | VALUE_METHOD | VALUE_BUILTIN_METHOD | VALUE_FUNCTION | VALUE_BUILTIN_FUNCTION | VALUE_REGEX | VALUE_TAG)) != 0))

#define CALLABLE(v) ((v).type <= VALUE_REGEX)

#define ARITY(f) ((f).type == VALUE_FUNCTION ? (((int16_t *)((f).info + 5))[0] == -1 ? (f).info[4] : 100) : 1)

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

#define TY_AST_NODES \
        X(Expr) \
        X(Stmt) \
        X(Value) \
        X(Match) \
        X(Each) \
        X(For) \
        X(While) \
        X(WhileMatch) \
        X(Func) \
        X(FuncDef) \
        X(ImplicitFunc) \
        X(Generator) \
        X(Param) \
        X(Arg) \
        X(Null) \
        X(If) \
        X(IfNot) \
        X(In) \
        X(NotIn) \
        X(Eq) \
        X(Matches) \
        X(Or) \
        X(And) \
        X(BitAnd) \
        X(BitOr) \
        X(NotEq) \
        X(Assign) \
        X(Let) \
        X(Class) \
        X(Spread) \
        X(Splat) \
        X(Gather) \
        X(Kwargs) \
        X(Any) \
        X(Add) \
        X(Mul) \
        X(Sub) \
        X(Div) \
        X(Mod) \
        X(Block) \
        X(Multi) \
        X(With) \
        X(Defer) \
        X(Array) \
        X(Dict) \
        X(String) \
        X(SpecialString) \
        X(Int) \
        X(Bool) \
        X(Float) \
        X(Nil) \
        X(Regex) \
        X(Id) \
        X(Record) \
        X(RecordEntry) \
        X(DictItem) \
        X(ArrayItem) \
        X(Call) \
        X(MethodCall) \
        X(TagPattern) \
        X(Tagged) \
        X(PatternAlias) \
        X(MemberAccess) \
        X(Subscript) \
        X(Slice) \
        X(NotNil) \
        X(ArrayCompr) \
        X(Try) \
        X(Eval) \
        X(Cond) \
        X(UserOp) \
        X(Return) \
        X(Yield) \
        X(Break) \
        X(Continue) \
        X(Wtf) \
        X(GT) \
        X(GEQ) \
        X(LT) \
        X(LEQ) \
        X(Cmp) \
        X(Not) \
        X(Neg) \
        X(PreInc) \
        X(PostInc) \
        X(PreDec) \
        X(PostDec) \
        X(Count) \
        X(Question) \
        X(Resource) \
        X(View) \
        X(NotNilView) \
        X(IfDef) \
        X(CompileTime) \
        X(Defined) \
        X(Throw) \
        X(Range) \
        X(IncRange) \
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

#define DEFINE_METHOD_TABLE(...) \
        static struct { \
                char const *name; \
                BuiltinMethod *func; \
        } funcs[] = { __VA_ARGS__ }; \
        static size_t const nfuncs = sizeof funcs / sizeof funcs[0]

#define DEFINE_METHOD_LOOKUP(type) \
        BuiltinMethod *get_ ## type ## _method(char const *name) \
        { \
                int lo = 0, \
                    hi = nfuncs - 1; \
\
                while (lo <= hi) { \
                        int m = (lo + hi) / 2; \
                        int c = strcmp(name, funcs[m].name); \
                        if      (c < 0) hi = m - 1; \
                        else if (c > 0) lo = m + 1; \
                        else            return funcs[m].func; \
                } \
\
                return NULL; \
        }

#define DEFINE_METHOD_COMPLETER(type) \
        int \
        type ## _get_completions(Ty *ty, char const *prefix, char **out, int max) \
        { \
                int n = 0; \
                int len = strlen(prefix); \
\
                for (int i = 0; i < nfuncs; ++i) { \
                        if (n < max && strncmp(funcs[i].name, prefix, len) == 0) { \
                                out[n++] = sclone_malloc(funcs[i].name); \
                        } \
                } \
\
                return n; \
        }

#define ARG(i) (*vm_get(ty, argc - 1 - (i)))
#define NAMED(s) ((kwargs != NULL) ? dict_get_member(ty, kwargs->dict, (s)) : NULL)

//#define value_mark(ty, v) do { LOG("value_mark: %s:%d: %p", __FILE__, __LINE__, (v)); _value_mark(v); } while (0)
#define value_mark _value_mark

typedef struct array {
        Value *items;
        size_t count;
        size_t capacity;
} Array;

typedef struct blob {
        unsigned char *items;
        size_t count;
        size_t capacity;
} Blob;

typedef struct dict Dict;

typedef struct generator Generator;
typedef struct thread Thread;
typedef struct channel Channel;
typedef struct chanval ChanVal;

enum {
        VALUE_FUNCTION = 1     ,
        VALUE_METHOD           ,
        VALUE_BUILTIN_FUNCTION ,
        VALUE_BUILTIN_METHOD   ,
        VALUE_CLASS            ,
        VALUE_GENERATOR        ,
        VALUE_TAG              ,
        VALUE_REGEX            , // CALLABLE here and above
        VALUE_INTEGER          ,
        VALUE_REAL             ,
        VALUE_BOOLEAN          ,
        VALUE_NIL              ,
        VALUE_ARRAY            ,
        VALUE_DICT             ,
        VALUE_OBJECT           ,
        VALUE_STRING           ,
        VALUE_BLOB             ,
        VALUE_SENTINEL         ,
        VALUE_INDEX            ,
        VALUE_NONE             ,
        VALUE_UNINITIALIZED    ,
        VALUE_PTR              ,
        VALUE_REF              ,
        VALUE_THREAD           ,
        VALUE_TUPLE            ,
        VALUE_TAGGED           = 1 << 7
};

typedef Value BuiltinFunction(Ty *, int, Value *);
typedef Value BuiltinMethod(Ty *, Value *, int, Value *);

enum {
        FUN_HEADER_SIZE = 0,
        FUN_TOTAL_SIZE  = FUN_HEADER_SIZE + sizeof (int),
        FUN_CAPTURES    = FUN_TOTAL_SIZE  + sizeof (int),
        FUN_BOUND       = FUN_CAPTURES    + sizeof (int),
        FUN_PARAM_COUNT = FUN_BOUND       + sizeof (int),
        FUN_REST_IDX    = FUN_PARAM_COUNT + sizeof (int),
        FUN_KWARGS_IDX  = FUN_REST_IDX    + sizeof (int16_t),
        FUN_CLASS       = FUN_REST_IDX    + sizeof (int),
        FUN_FROM_EVAL   = FUN_CLASS       + sizeof (int),
        FUN_HIDDEN      = FUN_FROM_EVAL   + 1,
        FUN_PROTO       = FUN_HIDDEN      + 1,
        FUN_DOC         = FUN_PROTO       + sizeof (uintptr_t),
        FUN_NAME        = FUN_DOC         + sizeof (uintptr_t)
};

struct value {
        uint8_t type;
        uint16_t tags;
        uint32_t src;
        union {
                short tag;
                double real;
                bool boolean;
                Array *array;
                Dict *dict;
                Blob *blob;
                Thread *thread;
                Symbol *sym;
                struct {
                        void *ptr;
                        void *gcptr;
                        void *extra;
                };
                struct {
                        intmax_t integer;
                        char const *constant;
                };
                struct {
                        int class;
                        struct table *object;
                };
                struct {
                        union {
                                struct {
                                        struct value *this;
                                        union {
                                                struct value *method;
                                                BuiltinMethod *builtin_method;
                                        };
                                };
                                struct {
                                        BuiltinFunction *builtin_function;
                                        char const *module;
                                };
                        };
                        char const *name;
                };
                struct {
                        char const *string;
                        uint32_t bytes;
                        char *gcstr;
                };
                struct {
                        intmax_t i;
                        int off;
                        int nt;
                };
                struct {
                        struct value *items;
                        char **names;
                        int count;
                        bool gc_names;
                };
                Regex const *regex;
                struct {
                        int *info;
                        struct value **env;
                };
                Generator *gen;
        };
};

typedef struct value Value;

struct frame {
        size_t fp;
        struct value f;
        char const *ip;
};

struct generator {
        char *ip;
        struct value f;
        int fp;
        ValueVector frame;
        FrameStack frames;
        CallStack calls;
        SPStack sps;
        TargetStack targets;
        ValueVector deferred;
        ValueVector to_drop;
};

struct thread {
#ifdef _WIN32
        HANDLE t;
        CRITICAL_SECTION mutex;
        CONDITION_VARIABLE cond;
#else
        pthread_t t;
        pthread_mutex_t mutex;
        pthread_cond_t cond;
#endif
        struct value v;
        uint64_t i;
        bool alive;
};

struct chanval {
        vec(void *) as;
        struct value v;
};

struct channel {
        bool open;
        TyMutex m;
        TyCondVar c;
        vec(ChanVal) q;
};

struct dict {
        unsigned long *hashes;
        struct value *keys;
        struct value *values;
        size_t size;
        size_t count;
        struct value dflt;
};

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
value_show_color(Ty *ty, struct value const *v);

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

inline static Value *
tget_or_null(Value const *tuple, uintptr_t k)
{
        if (k < 16) {
                return (k >= tuple->count) ? NULL : &tuple->items[k];
        }

        char const *name = (char const *)k;

        if (tuple->names != NULL) for (int i = 0; i < tuple->count; ++i) {
                if (tuple->names[i] != NULL && strcmp(tuple->names[i], name) == 0) {
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

#define tget_or(t, i, v) ((tget_or)((t), (uintptr_t)(i), (v)))
#define tget_nn(t, i   ) ((tget_nn)((t), (uintptr_t)(i)     ))
#define  tget_t(t, i, v) ((tget_t) ((t), (uintptr_t)(i), (v)))

int
tuple_get_completions(Ty *ty, struct value const *v, char const *prefix, char **out, int max);

void
_value_mark(Ty *ty, struct value const *v);

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
value_array_push(Ty *ty, struct array *a, struct value v)
{
        if (a->count == a->capacity) {
                a->capacity = a->capacity ? a->capacity * 2 : 4;
                mRE(a->items, a->capacity * sizeof (struct value));
        }

        a->items[a->count++] = v;
}

inline static void
value_array_reserve(Ty *ty, struct array *a, int count)
{
        if (a->capacity >= count)
                return;

        if (a->capacity == 0)
                a->capacity = 16;

        while (a->capacity < count)
                a->capacity *= 2;

        mRE(a->items, a->capacity * sizeof (struct value));
}

inline static struct value
STRING_CLONE(Ty *ty, char const *s, int n)
{
        char *clone = value_string_clone(ty, s, n);

        return (struct value) {
                .type = VALUE_STRING,
                .tags = 0,
                .string = clone,
                .bytes = n,
                .gcstr = clone,
        };
}

inline static struct value
STRING_CLONE_C(Ty *ty, char const *s)
{
        int n = strlen(s);
        char *clone = value_string_clone(ty, s, n);

        return (struct value) {
                .type = VALUE_STRING,
                .tags = 0,
                .string = clone,
                .bytes = n,
                .gcstr = clone,
        };
}

inline static struct value
STRING_C_CLONE_C(Ty *ty, char const *s)
{
        int n = strlen(s);
        char *clone = value_string_clone_nul(ty, s, n);

        return (struct value) {
                .type = VALUE_STRING,
                .tags = 0,
                .string = clone,
                .bytes = n,
                .gcstr = clone,
        };
}

inline static struct value
STRING_C_CLONE(Ty *ty, char const *s, int n)
{
        char *clone = value_string_clone_nul(ty, s, n);

        return (struct value) {
                .type = VALUE_STRING,
                .tags = 0,
                .string = clone,
                .bytes = n,
                .gcstr = clone,
        };
}

inline static struct value
STRING(char *s, int n)
{
        return (struct value) {
                .type = VALUE_STRING,
                .tags = 0,
                .string = s,
                .bytes = n,
                .gcstr = s,
        };
}

inline static struct value
STRING_VIEW(struct value s, int offset, int n)
{
        return (struct value) {
                .type = VALUE_STRING,
                .tags = 0,
                .string = s.string + offset,
                .bytes = n,
                .gcstr = s.gcstr
        };
}

inline static struct value
STRING_NOGC(char const *s, int n)
{
        return (struct value) {
                .type = VALUE_STRING,
                .tags = 0,
                .string = s,
                .bytes = n,
                .gcstr = NULL
        };
}

#define STRING_EMPTY (STRING_NOGC(NULL, 0))

inline static struct value
PAIR_(Ty *ty, struct value a, struct value b)
{
        struct value v = vT(2);
        v.items[0] = a;
        v.items[1] = b;
        return v;
}

inline static struct value
TRIPLE_(Ty *ty, struct value a, struct value b, struct value c)
{
        struct value v = vT(3);
        v.items[0] = a;
        v.items[1] = b;
        v.items[2] = c;
        return v;
}

#define None                     TAG(TAG_NONE)

int
tags_push(Ty *ty, int, int);

inline static struct value
Ok(Ty *ty, struct value v)
{
        v.type |= VALUE_TAGGED;
        v.tags = tags_push(ty, v.tags, TAG_OK);
        return v;
}

inline static struct value
Err(Ty *ty, struct value v)
{
        v.type |= VALUE_TAGGED;
        v.tags = tags_push(ty, v.tags, TAG_ERR);
        return v;
}

inline static struct value
Some(Ty *ty, struct value v)
{
        v.type |= VALUE_TAGGED;
        v.tags = tags_push(ty, v.tags, TAG_SOME);
        return v;
}

inline static char *
code_of(struct value const *v)
{
        return (char *)v->info + v->info[0];
}

inline static char const *
proto_of(struct value const *f)
{
        uintptr_t p;
        memcpy(&p, (char *)f->info + FUN_PROTO, sizeof p);
        return (char const *)p;
}

inline static char const *
doc_of(struct value const *f)
{
        uintptr_t p;
        memcpy(&p, (char *)f->info + FUN_DOC, sizeof p);
        return (char const *)p;
}

inline static char const *
name_of(struct value const *f)
{
        return (char *)f->info + FUN_NAME;
}

inline static char *
from_eval(struct value const *f)
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

#endif
