struct value;

#ifndef VALUE_H_INCLUDED
#define VALUE_H_INCLUDED

#include <stdbool.h>
#include <stdint.h>
#include <string.h>

#include "vec.h"
#include "ast.h"
#include "gc.h"
#include "tags.h"

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

#define TY_AST_NODES \
        X(Expr) \
        X(Stmt) \
        X(Value) \
        X(Match) \
        X(Each) \
        X(While) \
        X(Func) \
        X(FuncDef) \
        X(ImplicitFunc) \
        X(Param) \
        X(Arg) \
        X(Null) \
        X(If) \
        X(IfNot) \
        X(In) \
        X(NotIn) \
        X(Eq) \
        X(Or) \
        X(And) \
        X(NotEq) \
        X(Assign) \
        X(Let) \
        X(Class) \
        X(Spread) \
        X(Gather) \
        X(Kwargs) \
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
        X(Id) \
        X(Record) \
        X(RecordEntry) \
        X(DictItem) \
        X(ArrayItem) \
        X(Call) \
        X(MethodCall) \
        X(MemberAccess) \
        X(Subscript) \
        X(NotNil) \
        X(ArrayCompr) \
        X(Try) \
        X(Eval) \
        X(Cond) \
        X(UserOp) \
        X(Return) \
        X(Wtf) \
        X(GT) \
        X(LT) \
        X(Count) \
        X(IfDef) \
        X(CompileTime) \
        X(Defined) \
        X(Throw)

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
        TAG_NONE,
        TAG_SOME,
        TAG_OK,
        TAG_ERR
};

#define DEFINE_METHOD_TABLE(...) \
        static struct { \
                char const *name; \
                struct value (*func)(struct value *, int, struct value *); \
        } funcs[] = { __VA_ARGS__ }; \
        static size_t const nfuncs = sizeof funcs / sizeof funcs[0]

#define DEFINE_METHOD_LOOKUP(type) \
        struct value (*get_ ## type ## _method(char const *name))(struct value *, int, struct value *) \
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
        type ## _get_completions(char const *prefix, char **out, int max) \
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

#define ARG(i) (*vm_get(argc - 1 - (i)))
#define NAMED(s) ((kwargs != NULL) ? dict_get_member(kwargs->dict, (s)) : NULL)

//#define value_mark(v) do { LOG("value_mark: %s:%d: %p", __FILE__, __LINE__, (v)); _value_mark(v); } while (0)
#define value_mark _value_mark

typedef struct array {
        struct value *items;
        size_t count;
        size_t capacity;
} Array;

typedef struct blob {
        unsigned char *items;
        size_t count;
        size_t capacity;
} Blob;

struct target {
        struct {
                struct value *t;
                void *gc;
        };
};

typedef struct target Target;

struct frame;
typedef struct frame Frame;

typedef vec(struct value) ValueVector;
typedef vec(Target) TargetStack;
typedef vec(size_t) SPStack;
typedef vec(char *) CallStack;
typedef vec(Frame) FrameStack;

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
        VALUE_PTR              ,
        VALUE_REF              ,
        VALUE_THREAD           ,
        VALUE_TUPLE            ,
        VALUE_TAGGED           = 1 << 7
};

struct value {
        uint8_t type;
        uint16_t tags;
        union {
                short tag;
                double real;
                bool boolean;
                struct array *array;
                struct dict *dict;
                struct blob *blob;
                Thread *thread;
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
                                                struct value (*builtin_method)(struct value *, int, struct value *);
                                        };
                                };
                                struct {
                                        struct value (*builtin_function)(int, struct value *);
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
                struct regex *regex;
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
};

struct thread {
        pthread_t t;
        struct value v;
        uint64_t i;
};

struct chanval {
        vec(void *) as;
        struct value v;
};

struct channel {
        bool open;
        pthread_mutex_t m;
        pthread_cond_t c;
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
value_hash(struct value const *val);

bool
value_test_equality(struct value const *v1, struct value const *v2);

int
value_compare(void const *v1, void const *v2);

bool
value_truthy(struct value const *v);

bool
value_apply_predicate(struct value *p, struct value *v);

struct value
value_apply_callable(struct value *f, struct value *v);

char *
value_show(struct value const *v);

char *
value_show_color(struct value const *v);

char *
value_string_alloc(int n);

char *
value_string_clone(char const *s, int n);

char *
value_string_clone_nul(char const *src, int n);

struct array *
value_array_new(void);

struct array *
value_array_clone(struct array const *);

void
value_array_extend(struct array *, struct array const *);

struct blob *
value_blob_new(void);

struct value
value_tuple(int n);

struct value
value_named_tuple(char const *first, ...);

struct value *
tuple_get(struct value *tuple, char const *name);

int
tuple_get_completions(struct value const *v, char const *prefix, char **out, int max);

void
_value_mark(struct value const *v);

inline static void
value_array_push(struct array *a, struct value v)
{
        if (a->count == a->capacity) {
                a->capacity = a->capacity ? a->capacity * 2 : 4;
                a->items = gc_resize(a->items, a->capacity * sizeof (struct value));
        }

        a->items[a->count++] = v;
}

inline static void
value_array_reserve(struct array *a, int count)
{
        if (a->capacity >= count)
                return;

        if (a->capacity == 0)
                a->capacity = 16;

        while (a->capacity < count)
                a->capacity *= 2;

        a->items = gc_resize(a->items, a->capacity * sizeof (struct value));
}

inline static struct value
STRING_CLONE(char const *s, int n)
{
        char *clone = value_string_clone(s, n);

        return (struct value) {
                .type = VALUE_STRING,
                .tags = 0,
                .string = clone,
                .bytes = n,
                .gcstr = clone,
        };
}

inline static struct value
STRING_CLONE_NUL(char const *s, int n)
{
        char *clone = value_string_clone_nul(s, n);

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
PAIR(struct value a, struct value b)
{
        struct value v = value_tuple(2);
        v.items[0] = a;
        v.items[1] = b;
        return v;
}

inline static struct value
TRIPLE(struct value a, struct value b, struct value c)
{
        struct value v = value_tuple(3);
        v.items[0] = a;
        v.items[1] = b;
        v.items[2] = c;
        return v;
}

#define None                     TAG(TAG_NONE)

int tags_push(int, int);

inline static struct value
Ok(struct value v)
{
        v.type |= VALUE_TAGGED;
        v.tags = tags_push(v.tags, TAG_OK);
        return v;
}

inline static struct value
Err(struct value v)
{
        v.type |= VALUE_TAGGED;
        v.tags = tags_push(v.tags, TAG_ERR);
        return v;
}

inline static struct value
Some(struct value v)
{
        v.type |= VALUE_TAGGED;
        v.tags = tags_push(v.tags, TAG_SOME);
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
        memcpy(&p, f->info + 7, sizeof p);
        return (char const *)p;
}

inline static char const *
doc_of(struct value const *f)
{
        uintptr_t p;
        memcpy(&p, (char *)(f->info + 7) + sizeof (uintptr_t), sizeof p);
        return (char const *)p;
}

inline static char const *
name_of(struct value const *f)
{
        return (char *)(f->info + 7) + 2 * sizeof (uintptr_t);
}

#endif

/* vim: set sts=8 sw=8 expandtab: */
