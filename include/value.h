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
#include "vec.h"

#define V_ALIGN (_Alignof (struct value))

#define POINTER(p)    { .type = VALUE_PTR,              .ptr              = (p), .tags = 0 }

#define INTEGER(k)               ((struct value){ .type = VALUE_INTEGER,        .integer        = (k),                               .tags = 0 })
#define REAL(f)                  ((struct value){ .type = VALUE_REAL,           .real           = (f),                               .tags = 0 })
#define BOOLEAN(b)               ((struct value){ .type = VALUE_BOOLEAN,        .boolean        = (b),                               .tags = 0 })
#define ARRAY(a)                 ((struct value){ .type = VALUE_ARRAY,          .array          = (a),                               .tags = 0 })
#define TUPLE(vs, ns, n)         ((struct value){ .type = VALUE_TUPLE,          .items          = (vs), .count = (n), .names = (ns), .tags = 0 })
#define BLOB(b)                  ((struct value){ .type = VALUE_BLOB,           .blob           = (b),                               .tags = 0 })
#define DICT(d)                  ((struct value){ .type = VALUE_DICT,           .dict           = (d),                               .tags = 0 })
#define REGEX(r)                 ((struct value){ .type = VALUE_REGEX,          .regex          = (r),                               .tags = 0 })
#define FUNCTION()               ((struct value){ .type = VALUE_FUNCTION,                                                            .tags = 0 })
#define PTR(p)                   ((struct value){ .type = VALUE_PTR,            .ptr            = (p),  .gcptr = NULL,               .tags = 0 })
#define GCPTR(p, gcp)            ((struct value){ .type = VALUE_PTR,            .ptr            = (p),  .gcptr = (gcp),              .tags = 0 })
#define REF(p)                   ((struct value){ .type = VALUE_REF,            .ptr            = (p),                               .tags = 0 })
#define TAG(t)                   ((struct value){ .type = VALUE_TAG,            .tag            = (t),                               .tags = 0 })
#define CLASS(c)                 ((struct value){ .type = VALUE_CLASS,          .class          = (c),  .object = NULL,              .tags = 0 })
#define OBJECT(o, c)             ((struct value){ .type = VALUE_OBJECT,         .object         = (o),  .class  = (c),               .tags = 0 })
#define METHOD(n, m, t)          ((struct value){ .type = VALUE_METHOD,         .method         = (m),  .this   = (t), .name = (n),  .tags = 0 })
#define GENERATOR(g)             ((struct value){ .type = VALUE_GENERATOR,      .gen            = (g),                               .tags = 0 })
#define BUILTIN_METHOD(n, m, t)  ((struct value){ .type = VALUE_BUILTIN_METHOD, .builtin_method = (m),  .this   = (t), .name = (n),  .tags = 0 })
#define NIL                      ((struct value){ .type = VALUE_NIL,                                                                 .tags = 0 })

/* Special kind of value, only used as an iteration counter in for-each loops */
#define INDEX(ix, o, n)          ((struct value){ .type = VALUE_INDEX,          .i              = (ix), .off   = (o), .nt = (n),     .tags = 0 })

/* Another special one, used for functions with multiple return values */
#define SENTINEL                 ((struct value){ .type = VALUE_SENTINEL,       .i              = 0,    .off   = 0,                  .tags = 0 })

/* This is getting ugly */
#define NONE                     ((struct value){ .type = VALUE_NONE,           .i              = 0,    .off   = 0,                  .tags = 0 })

//#define CALLABLE(v) ((!((v).type & VALUE_TAGGED)) && (((v).type & (VALUE_CLASS | VALUE_METHOD | VALUE_BUILTIN_METHOD | VALUE_FUNCTION | VALUE_BUILTIN_FUNCTION | VALUE_REGEX | VALUE_TAG)) != 0))

#define CALLABLE(v) ((v).type <= VALUE_REGEX)

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

#define TAG_MATCH_ERR 1
#define TAG_INDEX_ERR 2
#define TAG_NONE      3
#define TAG_SOME      4

#define DEFINE_METHOD_TABLE(...) \
        static struct { \
                char const *name; \
                struct value (*func)(struct value *, int); \
        } funcs[] = { __VA_ARGS__ }; \
        static size_t const nfuncs = sizeof funcs / sizeof funcs[0]

#define DEFINE_METHOD_LOOKUP(type) \
        struct value (*get_ ## type ## _method(char const *name))(struct value *, int) \
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

//#define value_mark(v) do { LOG("value_mark: %s:%d: %p", __FILE__, __LINE__, (v)); _value_mark(v); } while (0)
#define value_mark _value_mark

struct array {
        struct value *items;
        size_t count;
        size_t capacity;
};

struct blob {
        unsigned char *items;
        size_t count;
        size_t capacity;
};

struct target {
        struct value *t;
        void *gc;
};

typedef struct target Target;

typedef vec(struct value) ValueVector;
typedef vec(Target) TargetStack;
typedef vec(size_t) SPStack;

typedef struct generator Generator;

enum {
        VALUE_FUNCTION         ,
        VALUE_METHOD           ,
        VALUE_BUILTIN_FUNCTION ,
        VALUE_BUILTIN_METHOD   ,
        VALUE_CLASS            ,
        VALUE_GENERATOR        ,
        VALUE_REGEX            , // CALLABLE here and above
        VALUE_INTEGER          ,
        VALUE_REAL             ,
        VALUE_BOOLEAN          ,
        VALUE_NIL              ,
        VALUE_ARRAY            ,
        VALUE_DICT             ,
        VALUE_OBJECT           ,
        VALUE_TAG              ,
        VALUE_STRING           ,
        VALUE_BLOB             ,
        VALUE_SENTINEL         ,
        VALUE_INDEX            ,
        VALUE_NONE             ,
        VALUE_PTR              ,
        VALUE_REF              ,
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
                struct value (*builtin_function)(int);
                struct blob *blob;
                struct {
                        void *ptr;
                        void *gcptr;
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
                        struct value *this;
                        union {
                                struct value *method;
                                struct value (*builtin_method)(struct value *, int);
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
                };
                struct regex *regex;
                struct {
                        int *info;
                        struct value **env;
                };
                Generator *gen;
        };
};

struct generator {
        char *ip;
        struct value f;
        ValueVector frame;
        SPStack sps;
        TargetStack targets;
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

inline static char *
code_of(struct value const *v)
{
        return ((char *)v->info) + v->info[0];
}

#define None                     TAG(TAG_NONE)

inline static struct value
Some(struct value v)
{
        v.tags = tags_push(v.tags, TAG_SOME);
        return v;
}

#endif
