#include <string.h>
#include <stdlib.h>
#include <assert.h>
#include <stdbool.h>
#include <inttypes.h>
#include <math.h>

#include "value.h"
#include "test.h"
#include "util.h"
#include "object.h"
#include "tags.h"
#include "log.h"
#include "gc.h"
#include "vm.h"

static struct value_array *array_chain;
static struct ref_vector *ref_vector_chain;
static struct string *string_chain;
static struct blob *blob_chain;

static bool
arrays_equal(struct value const *v1, struct value const *v2)
{
        if (v1->array->count != v2->array->count)
                return false;

        size_t n = v1->array->count;

        for (size_t i = 0; i < n; ++i) {
                if (!value_test_equality(&v1->array->items[i], &v2->array->items[i])) {
                        return false;
                }
        }

        return true;
}

// These hash functions are based on djb's djb2 hash function, copied from http://www.cse.yorku.ca/~oz/hash.html

static unsigned long
str_hash(char const *str, register int n)
{
        unsigned long hash = 5381;

        while (n > 0)
                hash = ((hash << 5) + hash) + str[--n]; /* hash * 33 + c */

        return hash;
}

static unsigned long
int_hash(intmax_t k)
{
        unsigned long hash = 5381;
        char const *bytes = (char const *) &k;
        char c;

        for (int i = 0; i < sizeof k; ++i) {
                c = bytes[i];
                hash = ((hash << 5) + hash) + c; /* hash * 33 + c */
        }

        return hash;
}

static unsigned long
ptr_hash(void const *p)
{
        unsigned long hash = 5381;
        char const *bytes = (char const *) &p;
        char c;

        for (int i = 0; i < sizeof p; ++i) {
                c = bytes[i];
                hash = ((hash << 5) + hash) + c; /* hash * 33 + c */
        }

        return hash;
}

static unsigned long
flt_hash(float flt)
{
        unsigned long hash = 5381;
        char const *bytes = (char const *) &flt;
        char c;

        for (int i = 0; i < sizeof flt; ++i) {
                c = bytes[i];
                hash = ((hash << 5) + hash) + c; /* hash * 33 + c */
        }

        return hash;
}

static unsigned long
ary_hash(struct value const *a)
{
        unsigned long hash = 5381;

        for (int i = 0; i < a->array->count; ++i) {
                unsigned long c = value_hash(&a->array->items[i]);
                hash = ((hash << 5) + hash) + c; /* hash * 33 + c */
        }

        return hash;
}

unsigned long
value_hash(struct value const *val)
{
        switch (val->type) {
        case VALUE_NIL:       return 1;
        case VALUE_BOOLEAN:   return val->boolean ? 2 : 3;
        case VALUE_STRING:    return str_hash(val->string, val->bytes);
        case VALUE_INTEGER:   return int_hash(val->integer);
        case VALUE_REAL:      return flt_hash(val->real);
        case VALUE_ARRAY:     return ary_hash(val);
        case VALUE_OBJECT:    return ptr_hash(val->object);
        case VALUE_FUNCTION:  return ptr_hash(val->code);
        case VALUE_REGEX:     return ptr_hash(val->regex);
        }

        assert(false);
}

char *
show_array(struct value const *a)
{
        static vec(struct value_array *) show_arrays;

        for (int i = 0; i < show_arrays.count; ++i)
                if (show_arrays.items[i] == a->array)
                        return sclone("[...]");

        vec_push(show_arrays, a->array);

        size_t capacity = 1;
        size_t len = 1;
        size_t n;
        char *s = alloc(2);
        strcpy(s, "[");

#define add(str) \
                n = strlen(str); \
                if (len + n >= capacity) {\
                        capacity = 2 * (len + n) + 1; \
                        resize(s, capacity); \
                } \
                strcpy(s + len, str); \
                len += n;

        for (size_t i = 0; i < a->array->count; ++i) {
                char *val = value_show(&a->array->items[i]);
                add(i == 0 ? "" : ", ");
                add(val);
                free(val);
        }

        add("]");
#undef add
        
        --show_arrays.count;

        return s;
}

static char *
show_string(char const *s, size_t n)
{
        vec(char) v;
        vec_init(v);

        vec_push(v, '\'');

        for (char const *c = s; c < s + n;) {
                if (*c == '\'') {
                        vec_push(v, '\\');
                }
                vec_push(v, *c++);
        }

        vec_push(v, '\'');
        vec_push(v, '\0');

        return v.items;
}

char *
value_show(struct value const *v)
{
        static char buffer[1024];
        char const *s = buffer;

        switch (v->type & ~VALUE_TAGGED) {
        case VALUE_INTEGER:
                snprintf(buffer, 1024, "%"PRIiMAX, v->integer);
                break;
        case VALUE_REAL:
                snprintf(buffer, 1024, "%g", v->real);
                break;
        case VALUE_STRING:
                s = show_string(v->string, v->bytes);
                break;
        case VALUE_BOOLEAN:
                snprintf(buffer, 1024, "%s", v->boolean ? "true" : "false");
                break;
        case VALUE_NIL:
                snprintf(buffer, 1024, "%s", "nil");
                break;
        case VALUE_ARRAY:
                s = show_array(v);
                break;
        case VALUE_REGEX:
                snprintf(buffer, 1024, "/%s/", v->pattern);
                break;
        case VALUE_OBJECT:
                snprintf(buffer, 1024, "<object at %p>", (void *) v->object);
                break;
        case VALUE_FUNCTION:
                snprintf(buffer, 1024, "<function at %p>", (void *) v->code);
                break;
        case VALUE_BUILTIN_FUNCTION:
                snprintf(buffer, 1024, "<builtin function>");
                break;
        case VALUE_TAG:
                s = tags_name(v->tag);
                break;
        case VALUE_BLOB:
                snprintf(buffer, 1024, "<blob at %p (%zu bytes)>", (void *) v->blob, v->blob->count);
                break;
        default:
                return sclone("UNKNOWN VALUE");
        }

        return sclone(tags_wrap(s, v->tags));
}

int
value_compare(void const *_v1, void const *_v2)
{
        struct value const *v1 = _v1;
        struct value const *v2 = _v2;

        if (v1->type != v2->type) {
                vm_panic("attempt to compare values of different types");
        }

        switch (v1->type) {
        case VALUE_INTEGER: return (v1->integer - v2->integer); // TODO
        case VALUE_REAL:    return round(v1->real - v2->real);
        case VALUE_STRING:  return memcmp(v1->string, v2->string, min(v1->bytes, v2->bytes));
        default:            vm_panic("attempt to compare values of invalid types");
        }
}

bool
value_truthy(struct value const *v)
{
        switch (v->type) {
        case VALUE_REAL:             return v->real != 0.0f;
        case VALUE_BOOLEAN:          return v->boolean;
        case VALUE_INTEGER:          return (v->integer != 0);
        case VALUE_STRING:           return (v->string[0] != '\0');
        case VALUE_ARRAY:            return (v->array->count != 0);
        case VALUE_REGEX:            return true;
        case VALUE_FUNCTION:         return true;
        case VALUE_BUILTIN_FUNCTION: return true;
        case VALUE_OBJECT:           return true;
        default:                     return false;
        }
}

bool
value_apply_predicate(struct value *p, struct value *v)
{
        struct value b;

        switch (p->type) {
        case VALUE_FUNCTION:
        case VALUE_BUILTIN_FUNCTION:
                b = vm_eval_function(p, v);
                return value_truthy(&b);
        case VALUE_REGEX:
                if (v->type != VALUE_STRING) {
                        vm_panic("regex applied as predicate to non-string");
                }
                {
                        char const *s = v->string;
                        int len = v->bytes;
                        int rc;

                        rc = pcre_exec(
                                p->regex,
                                NULL,
                                s,
                                len,
                                0,
                                0,
                                NULL,
                                0
                        );

                        if (rc < -1) {
                                vm_panic("error while executing regular expression");
                        }

                        return rc == 0;
                }
        case VALUE_TAG:
                return tags_first(v->tags) == p->tag;
        default:
                vm_panic("invalid type of value used as a predicate");
        }
}

struct value
value_apply_callable(struct value const *f, struct value *v)
{
        switch (f->type) {
        case VALUE_FUNCTION:
        case VALUE_BUILTIN_FUNCTION:
                return vm_eval_function(f, v);
        case VALUE_REGEX:
                if (v->type != VALUE_STRING) {
                        vm_panic("regex applied as predicate to non-string");
                }

                static int ovec[30];
                char const *s = v->string;
                int len = v->bytes;
                int rc;

                rc = pcre_exec(
                        f->regex,
                        NULL,
                        s,
                        len,
                        0,
                        0,
                        ovec,
                        30
                );

                if (rc < -1) {
                        vm_panic("error while executing regular expression");
                }

                if (rc == -1) {
                        return NIL;
                }

                struct value match;

                if (rc == 1) {
                        match = STRING_VIEW(*v, ovec[0], ovec[1] - ovec[0]);
                } else {
                        match = ARRAY(value_array_new());
                        vec_reserve(*match.array, rc);

                        int j = 0;
                        for (int i = 0; i < rc; ++i, j += 2) {
                                vec_push(*match.array, STRING_VIEW(*v, ovec[j], ovec[j + 1] - ovec[j]));
                        }
                }

                return match;
        case VALUE_TAG:
                {
                        struct value result = *v;
                        result.tags = tags_push(result.tags, f->tag);
                        result.type |= VALUE_TAGGED;
                        return result;
                }
        default:
                vm_panic("invalid type of value used as a predicate");
        }
}

bool
value_test_equality(struct value const *v1, struct value const *v2)
{
        if (v1->type != v2->type) {
                return false;
        }

        switch (v1->type & ~VALUE_TAGGED) {
        case VALUE_REAL:             if (v1->real != v2->real)                                                      return false; break;
        case VALUE_BOOLEAN:          if (v1->boolean != v2->boolean)                                                return false; break;
        case VALUE_INTEGER:          if (v1->integer != v2->integer)                                                return false; break;
        case VALUE_STRING:           if (v1->bytes != v2->bytes || memcmp(v1->string, v2->string, v1->bytes) != 0)  return false; break;
        case VALUE_ARRAY:            if (!arrays_equal(v1, v2))                                                     return false; break;
        case VALUE_REGEX:            if (v1->regex != v2->regex)                                                    return false; break;
        case VALUE_FUNCTION:         if (v1->code != v2->code)                                                      return false; break;
        case VALUE_BUILTIN_FUNCTION: if (v1->builtin_function != v2->builtin_function)                              return false; break;
        case VALUE_OBJECT:           if (v1->object != v2->object)                                                  return false; break;
        case VALUE_TAG:              if (v1->tag != v2->tag)                                                        return false; break;
        case VALUE_BLOB:             if (v1->blob->items != v2->blob->items)                                        return false; break;
        case VALUE_NIL:                                                                                                           break;
        }

        if (v1->tags != v2->tags || !tags_same(v1->tags, v2->tags)) {
                return false;
        }

        return true;
}

inline static void
value_array_mark(struct value_array *a)
{
        a->mark |= GC_MARK;

        for (int i = 0; i < a->count; ++i) {
                value_mark(&a->items[i]);
        }
}

inline static void
function_mark_references(struct value *v)
{
        for (int i = 0; i < v->refs->count; ++i) {
                vm_mark_variable((struct variable *)v->refs->refs[i].pointer);
        }

        v->refs->mark |= GC_MARK;
}

struct string *
value_clone_string(char const *s, int n)
{
        struct string *str = gc_alloc(sizeof *str + n);
        str->mark = GC_MARK;
        str->next = string_chain;
        string_chain = str;

        memcpy(str->data, s, n);

        return str;
}

struct string *
value_string_alloc(int n)
{
        struct string *str = gc_alloc(sizeof *str + n);
        str->mark = GC_MARK;
        str->next = string_chain;
        string_chain = str;

        return str;
}

void
value_mark(struct value *v)
{
        switch (v->type) {
        case VALUE_ARRAY:    value_array_mark(v->array);                      break;
        case VALUE_OBJECT:   object_mark(v->object);                          break;
        case VALUE_FUNCTION: function_mark_references(v);                     break;
        case VALUE_STRING:   if (v->gcstr != NULL) v->gcstr->mark |= GC_MARK; break;
        case VALUE_BLOB:     v->blob->mark |= GC_MARK;                        break;
        default:                                                              break;
        }
}

struct blob *
value_blob_new(void)
{
        struct blob *blob = gc_alloc(sizeof *blob);
        blob->next = blob_chain;
        blob->mark = GC_MARK;
        blob_chain = blob;

        vec_init(*blob);

        return blob;
}

struct value_array *
value_array_new(void)
{
        struct value_array *a = gc_alloc(sizeof *a);
        a->next = array_chain;
        a->mark = GC_MARK;
        array_chain = a;

        vec_init(*a);

        return a;
}

struct value_array *
value_array_clone(struct value_array const *a)
{
        struct value_array *new = value_array_new();

        /*
         * If a is empty, then we'd end up passing a null pointer
         * to memcpy which is UB, so we handle it specially.
         */
        if (a->count == 0)
                return new;

        new->count = a->count;
        new->capacity = a->count;
        new->items = alloc(sizeof *new->items * new->count);
        memcpy(new->items, a->items, sizeof *new->items * new->count);

        return new;
}

void
value_array_extend(struct value_array *a, struct value_array const *other)
{
        int n = a->count + other->count;

        if (n != 0)
                vec_reserve(*a, n);
        if (other->count != 0)
                memcpy(a->items + a->count, other->items, other->count * sizeof (struct value));

        a->count = n;
}

struct ref_vector *
ref_vector_new(int n)
{
        struct ref_vector *v = gc_alloc(sizeof *v + sizeof (struct reference) * n);
        v->count = n;
        v->mark = GC_MARK;
        v->next = ref_vector_chain;
        ref_vector_chain = v;

        return v;
}

void
value_array_sweep(void)
{
        while (array_chain != NULL && array_chain->mark == GC_NONE) {
                struct value_array *next = array_chain->next;
                vec_empty(*array_chain);
                free(array_chain);
                array_chain = next;
        }
        if (array_chain != NULL) {
                array_chain->mark &= ~GC_MARK;
        }
        for (struct value_array *array = array_chain; array != NULL && array->next != NULL;) {
                struct value_array *next;
                if (array->next->mark == GC_NONE) {
                        next = array->next->next;
                        vec_empty(*array->next);
                        free(array->next);
                        array->next = next;
                } else {
                        next = array->next;
                }
                if (next != NULL) {
                        next->mark &= ~GC_MARK;
                }
                array = next;
        }
}

void
value_blob_sweep(void)
{
        while (blob_chain != NULL && blob_chain->mark == GC_NONE) {
                struct blob *next = blob_chain->next;
                vec_empty(*blob_chain);
                free(blob_chain);
                blob_chain = next;
        }
        if (blob_chain != NULL) {
                blob_chain->mark &= ~GC_MARK;
        }
        for (struct blob *blob = blob_chain; blob != NULL && blob->next != NULL;) {
                struct blob *next;
                if (blob->next->mark == GC_NONE) {
                        next = blob->next->next;
                        vec_empty(*blob->next);
                        free(blob->next);
                        blob->next = next;
                } else {
                        next = blob->next;
                }
                if (next != NULL) {
                        next->mark &= ~GC_MARK;
                }
                blob = next;
        }
}

void
value_string_sweep(void)
{
        while (string_chain != NULL && string_chain->mark == GC_NONE) {
                struct string *next = string_chain->next;
                free(string_chain);
                string_chain = next;
        }
        if (string_chain != NULL) {
                string_chain->mark &= ~GC_MARK;
        }
        for (struct string *str = string_chain; str != NULL && str->next != NULL;) {
                struct string *next;
                if (str->next->mark == GC_NONE) {
                        next = str->next->next;
                        free(str->next);
                        str->next = next;
                } else {
                        next = str->next;
                }
                if (next != NULL) {
                        next->mark &= ~GC_MARK;
                }
                str = next;
        }
}
void
value_ref_vector_sweep(void)
{
        while (ref_vector_chain != NULL && ref_vector_chain->mark == GC_NONE) {
                struct ref_vector *next = ref_vector_chain->next;
                free(ref_vector_chain);
                ref_vector_chain = next;
        }
        if (ref_vector_chain != NULL) {
                ref_vector_chain->mark &= ~GC_MARK;
        }
        for (struct ref_vector *ref_vector = ref_vector_chain; ref_vector != NULL && ref_vector->next != NULL;) {
                struct ref_vector *next;
                if (ref_vector->next->mark == GC_NONE) {
                        next = ref_vector->next->next;
                        free(ref_vector->next);
                        ref_vector->next = next;
                } else {
                        next = ref_vector->next;
                }
                if (next != NULL) {
                        next->mark &= ~GC_MARK;
                }
                ref_vector = next;
        }
}

void
value_gc_reset(void)
{
        array_chain = NULL;
}

TEST(hash)
{
        struct value v1 = STRING_NOGC("hello", 5);
        struct value v2 = STRING_NOGC("world", 5);

        claim(value_hash(&v1) != value_hash(&v2));
}

TEST(equality)
{
        vm_init();

        struct value v1 = BOOLEAN(true);
        struct value v2 = BOOLEAN(false);
        claim(!value_test_equality(&v1, &v2));

        v1.type = VALUE_INTEGER;
        v2.type = VALUE_STRING;
        claim(!value_test_equality(&v1, &v2));

        v2.type = VALUE_INTEGER;

        v1.integer = v2.integer = 19;
        claim(value_test_equality(&v1, &v2));

        claim(
                value_test_equality(
                        &NIL,
                        &NIL
                )
        );
}
