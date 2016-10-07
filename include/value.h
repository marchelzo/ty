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

#define INTEGER(k)               ((struct value){ .type = VALUE_INTEGER,        .integer        = (k),                              .tags = 0 })
#define REAL(f)                  ((struct value){ .type = VALUE_REAL,           .real           = (f),                              .tags = 0 })
#define BOOLEAN(b)               ((struct value){ .type = VALUE_BOOLEAN,        .boolean        = (b),                              .tags = 0 })
#define ARRAY(a)                 ((struct value){ .type = VALUE_ARRAY,          .array          = (a),                              .tags = 0 })
#define BLOB(b)                  ((struct value){ .type = VALUE_BLOB,           .blob           = (b),                              .tags = 0 })
#define DICT(d)                  ((struct value){ .type = VALUE_DICT,           .dict           = (d),                              .tags = 0 })
#define REGEX(r)                 ((struct value){ .type = VALUE_REGEX,          .regex          = (r),                              .tags = 0 })
#define FUNCTION()               ((struct value){ .type = VALUE_FUNCTION,                                                           .tags = 0 })
#define TAG(t)                   ((struct value){ .type = VALUE_TAG,            .tag            = (t),                              .tags = 0 })
#define CLASS(c)                 ((struct value){ .type = VALUE_CLASS,          .class          = (c), .object = NULL,              .tags = 0 })
#define OBJECT(o, c)             ((struct value){ .type = VALUE_OBJECT,         .object         = (o), .class  = (c),               .tags = 0 })
#define METHOD(n, m, t)          ((struct value){ .type = VALUE_METHOD,         .method         = (m), .this   = (t), .name = (n),  .tags = 0 })
#define BUILTIN_METHOD(n, m, t)  ((struct value){ .type = VALUE_BUILTIN_METHOD, .builtin_method = (m), .this   = (t), .name = (n),  .tags = 0 })
#define NIL                      ((struct value){ .type = VALUE_NIL,                                                                .tags = 0 })

#define CALLABLE(v) ((!((v).type & VALUE_TAGGED)) && (((v).type & (VALUE_CLASS | VALUE_METHOD | VALUE_BUILTIN_METHOD | VALUE_FUNCTION | VALUE_BUILTIN_FUNCTION | VALUE_REGEX | VALUE_TAG)) != 0))

#define BUILTIN_OBJECT_TYPE(v) ((!((v).type & VALUE_TAGGED)) && (((v).type & (VALUE_STRING | VALUE_ARRAY | VALUE_BLOB)) != 0))

#define DEFINE_METHOD_TABLE(...) \
        static struct { \
                char const *name; \
                struct value (*func)(struct value *, value_vector *); \
        } funcs[] = { __VA_ARGS__ }; \
        static size_t const nfuncs = sizeof funcs / sizeof funcs[0]

#define DEFINE_METHOD_LOOKUP(type) \
        struct value (*get_ ## type ## _method(char const *name))(struct value *, value_vector *) \
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

typedef vec(struct value) value_vector;
#define NO_ARGS ((value_vector){ .count = 0 })

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

struct reference {
        union {
                uintptr_t symbol;
                uintptr_t pointer;
        };
        uintptr_t offset;
};

struct ref_vector {
        size_t count;
        struct reference refs[];
};

enum {
        VALUE_REGEX            = 1 << 0,
        VALUE_INTEGER          = 1 << 2,
        VALUE_REAL             = 1 << 3,
        VALUE_BOOLEAN          = 1 << 4,
        VALUE_NIL              = 1 << 5,
        VALUE_ARRAY            = 1 << 6,
        VALUE_DICT             = 1 << 7,
        VALUE_OBJECT           = 1 << 8,
        VALUE_CLASS            = 1 << 9,
        VALUE_FUNCTION         = 1 << 10,
        VALUE_METHOD           = 1 << 11,
        VALUE_BUILTIN_FUNCTION = 1 << 12,
        VALUE_BUILTIN_METHOD   = 1 << 13,
        VALUE_TAG              = 1 << 14,
        VALUE_STRING           = 1 << 15,
        VALUE_BLOB             = 1 << 16,
        VALUE_TAGGED           = 1 << 17,
};

struct value {
        uint32_t type;
        uint16_t tags;
        union {
                short tag;
                intmax_t integer;
                float real;
                bool boolean;
                struct array *array;
                struct dict *dict;
                struct value (*builtin_function)(value_vector *);
                struct blob *blob;
                struct {
                        int class;
                        struct table *object;
                };
                struct {
                        struct value *this;
                        union {
                                struct value *method;
                                struct value (*builtin_method)(struct value *, value_vector *);
                        };
                        char const *name;
                };
                struct {
                        char const *string;
                        size_t bytes;
                        char *gcstr;
                };
                struct {
                        pcre *regex;
                        pcre_extra *extra;
                        char const *pattern;
                };
                struct {
                        int *symbols;
                        unsigned char params;
                        unsigned short bound;
                        struct ref_vector *refs;
                        char *code;
                };
        };
};

struct dict_node {
        struct value key;
        struct value value;
        struct dict_node *next;
};

#define DICT_NUM_BUCKETS 128
struct dict {
        struct dict_node *buckets[DICT_NUM_BUCKETS];
        struct value *dflt;
        size_t count;
};

struct variable {
        struct value value;
        struct variable *prev;
        struct variable *next;
        bool captured;
        int try;
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
value_clone_string(char const *s, int n);

struct array *
value_array_new(void);

struct array *
value_array_clone(struct array const *);

void
value_array_extend(struct array *, struct array const *);

struct ref_vector *
ref_vector_new(int n);

struct blob *
value_blob_new(void);

void
value_mark(struct value *v);

inline static void
value_array_push(struct array *a, struct value v)
{
        if (a->count == a->capacity) {
                a->capacity = a->capacity ? a->capacity * 2 : 4;
                struct value *new_items = gc_alloc(a->capacity * sizeof (struct value));

                if (a->items != NULL)
                        memcpy(new_items, a->items, a->count * sizeof (struct value));

                a->items = new_items;
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

        struct value *new_items = gc_alloc(a->capacity * sizeof (struct value));
        if (a->count != 0)
                memcpy(new_items, a->items, a->count * sizeof (struct value));

        a->items = new_items;
}

inline static struct value
STRING_CLONE(char const *s, int n)
{
        char *clone = value_clone_string(s, n);
        return (struct value) {
                .type = VALUE_STRING,
                .tags = 0,
                .string = clone,
                .bytes = n,
                .gcstr = clone,
        };
}

inline static struct value
STRING(char const *s, int n, char *gcstr)
{
        return (struct value) {
                .type = VALUE_STRING,
                .tags = 0,
                .string = s,
                .bytes = n,
                .gcstr = gcstr,
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
                .gcstr = s.gcstr,
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
                .gcstr = NULL,
        };
}

#endif
