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

#define INTEGER(k)               ((struct value){ .type = VALUE_INTEGER,        .integer        = (k),                              .tags = 0 })
#define REAL(f)                  ((struct value){ .type = VALUE_REAL,           .real           = (f),                              .tags = 0 })
#define BOOLEAN(b)               ((struct value){ .type = VALUE_BOOLEAN,        .boolean        = (b),                              .tags = 0 })
#define ARRAY(a)                 ((struct value){ .type = VALUE_ARRAY,          .array          = (a),                              .tags = 0 })
#define BLOB(b)                  ((struct value){ .type = VALUE_BLOB,           .blob           = (b),                              .tags = 0 })
#define DICT(d)                  ((struct value){ .type = VALUE_DICT,           .dict           = (d),                              .tags = 0 })
#define REGEX(r)                 ((struct value){ .type = VALUE_REGEX,          .regex          = (r),                              .tags = 0 })
#define FUNCTION()               ((struct value){ .type = VALUE_FUNCTION,                                                           .tags = 0 })
#define PTR(p)                   ((struct value){ .type = VALUE_PTR,            .ptr            = (p),                              .tags = 0 })
#define REF(p)                   ((struct value){ .type = VALUE_REF,            .ptr            = (p),                              .tags = 0 })
#define TAG(t)                   ((struct value){ .type = VALUE_TAG,            .tag            = (t),                              .tags = 0 })
#define CLASS(c)                 ((struct value){ .type = VALUE_CLASS,          .class          = (c),  .object = NULL,             .tags = 0 })
#define OBJECT(o, c)             ((struct value){ .type = VALUE_OBJECT,         .object         = (o),  .class  = (c),              .tags = 0 })
#define METHOD(n, m, t)          ((struct value){ .type = VALUE_METHOD,         .method         = (m),  .this   = (t), .name = (n), .tags = 0 })
#define GENERATOR(g)             ((struct value){ .type = VALUE_GENERATOR,      .gen            = (g),                              .tags = 0 })
#define BUILTIN_METHOD(n, m, t)  ((struct value){ .type = VALUE_BUILTIN_METHOD, .builtin_method = (m),  .this   = (t), .name = (n), .tags = 0 })
#define NIL                      ((struct value){ .type = VALUE_NIL,                                                                .tags = 0 })

/* Special kind of value, only used as an iteration counter in for-each loops */
#define INDEX(ix, o, n)          ((struct value){ .type = VALUE_INDEX,          .i              = (ix), .off   = (o), .nt = (n),    .tags = 0 })

/* Another special one, used for functions with multiple return values */
#define SENTINEL                 ((struct value){ .type = VALUE_SENTINEL,       .i              = 0,    .off   = 0,                 .tags = 0 })

/* This is getting ugly */
#define NONE                     ((struct value){ .type = VALUE_NONE,           .i              = 0,    .off   = 0,                 .tags = 0 })

//#define CALLABLE(v) ((!((v).type & VALUE_TAGGED)) && (((v).type & (VALUE_CLASS | VALUE_METHOD | VALUE_BUILTIN_METHOD | VALUE_FUNCTION | VALUE_BUILTIN_FUNCTION | VALUE_REGEX | VALUE_TAG)) != 0))

#define CALLABLE(v) ((v).type <= VALUE_BUILTIN_METHOD)

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
#define CLASS_PRIMITIVE 12

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

#define ARG(i) (*vm_get(argc - 1 - (i)))

#define value_mark(v) do { LOG("value_mark: %s:%d: %p", __FILE__, __LINE__, (v)); _value_mark(v); } while (0)

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

typedef vec(struct value) ValueVector;

typedef struct generator Generator;

enum {
        VALUE_FUNCTION         , // = 1 << 9,
        VALUE_METHOD           , // = 1 << 10,
        VALUE_BUILTIN_FUNCTION , // = 1 << 11,
        VALUE_BUILTIN_METHOD   , // = 1 << 12,
        VALUE_REGEX            , // = 1 << 0,
        VALUE_INTEGER          , // = 1 << 1,
        VALUE_REAL             , // = 1 << 2,
        VALUE_BOOLEAN          , // = 1 << 3,
        VALUE_NIL              , // = 1 << 4,
        VALUE_ARRAY            , // = 1 << 5,
        VALUE_DICT             , // = 1 << 6,
        VALUE_OBJECT           , // = 1 << 7,
        VALUE_CLASS            , // = 1 << 8,
        VALUE_TAG              , // = 1 << 13,
        VALUE_STRING           , // = 1 << 14,
        VALUE_BLOB             , // = 1 << 15,
        VALUE_SENTINEL         , // = 1 << 16,
        VALUE_INDEX            , // = 1 << 17,
        VALUE_NONE             , // = 1 << 18,
        VALUE_PTR              , // = 1 << 19,
        VALUE_REF              ,
        VALUE_GENERATOR        ,
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
                void *ptr;
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
        struct {
                struct value *items;
                uint16_t count;
                uint16_t capacity;
        } frame;
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

struct array *
value_array_new(void);

struct array *
value_array_clone(struct array const *);

void
value_array_extend(struct array *, struct array const *);

struct blob *
value_blob_new(void);

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

inline static char *
code_of(struct value const *v)
{
        return ((char *)v->info) + v->info[0];
}

#endif
