#include <string.h>
#include <stdlib.h>
#include <assert.h>
#include <stdbool.h>
#include <inttypes.h>
#include <math.h>

#include "value.h"
#include "test.h"
#include "util.h"
#include "dict.h"
#include "object.h"
#include "tags.h"
#include "class.h"
#include "log.h"
#include "gc.h"
#include "vm.h"

static bool
arrays_equal(struct value const *v1, struct value const *v2)
{
        if (v1->array->count != v2->array->count)
                return false;

        size_t n = v1->array->count;

        for (size_t i = 0; i < n; ++i)
                if (!value_test_equality(&v1->array->items[i], &v2->array->items[i]))
                        return false;

        return true;
}

/*
 * These hash functions are based on djb's djb2 hash function,
 * copied from http://www.cse.yorku.ca/~oz/hash.html
 */

inline static unsigned long
str_hash(char const *str, int n)
{
        unsigned long hash = 5381;

        while (n > 0)
                hash = ((hash << 5) + hash) + str[--n]; /* hash * 33 + c */

        return hash;
}

inline static unsigned long
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

inline static unsigned long
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

inline static unsigned long
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

static unsigned long
obj_hash(struct value const *v)
{
        struct value const *f = class_lookup_method(v->class, "__hash__");

        if (f != NULL) {
                struct value h = vm_eval_function(f, v);
                if (h.type != VALUE_INTEGER) {
                        vm_panic("%s.__hash__ return non-integer: %s", class_name(v->class), value_show(v));
                }
                return (unsigned long)h.integer;
        } else {
                return ptr_hash(v->object);
        }
}

inline static unsigned long
hash(struct value const *val)
{
        switch (val->type & ~VALUE_TAGGED) {
        case VALUE_NIL:               return 0xDEADBEEFULL;
        case VALUE_BOOLEAN:           return val->boolean ? 0xABCULL : 0xDEFULL;
        case VALUE_STRING:            return str_hash(val->string, val->bytes);
        case VALUE_INTEGER:           return int_hash(val->integer);
        case VALUE_REAL:              return flt_hash(val->real);
        case VALUE_ARRAY:             return ary_hash(val);
        case VALUE_DICT:              return ptr_hash(val->dict);
        case VALUE_OBJECT:            return obj_hash(val);
        case VALUE_METHOD:            return ptr_hash(val->method) ^ ptr_hash(val->this);
        case VALUE_BUILTIN_METHOD:    return ptr_hash(val->builtin_method) ^ ptr_hash(val->this);
        case VALUE_BUILTIN_FUNCTION:  return ptr_hash(val->code);
        case VALUE_FUNCTION:          return ptr_hash(val->builtin_function);
        case VALUE_REGEX:             return ptr_hash(val->regex);
        case VALUE_TAG:               return (((unsigned long)val->tag) * 91238) ^ 0x123AEDDULL;
        case VALUE_CLASS:             return (((unsigned long)val->class) * 2048) ^ 0xAABB1012ULL;
        default:                      vm_panic("attempt to hash invalid value: %s", value_show(val));
        }
}

unsigned long
value_hash(struct value const *val)
{
        return (((unsigned long)val->tags) << 14) + hash(val);
}

char *
show_dict(struct value const *d)
{
        static vec(struct dict *) show_dicts;

        for (int i = 0; i < show_dicts.count; ++i)
                if (show_dicts.items[i] == d->dict)
                        return sclone("{...}");

        vec_push(show_dicts, d->dict);

        size_t capacity = 1;
        size_t len = 1;
        size_t n;
        char *s = alloc(2);
        strcpy(s, "{");

#define add(str) \
                n = strlen(str); \
                if (len + n >= capacity) {\
                        capacity = 2 * (len + n) + 1; \
                        resize(s, capacity); \
                } \
                strcpy(s + len, str); \
                len += n;

        for (size_t i = 0, j = 0; i < d->dict->size; ++i) {
                if (d->dict->keys[i].type == 0) continue;
                char *key = value_show(&d->dict->keys[i]);
                char *val = value_show(&d->dict->values[i]);
                add(j == 0 ? "" : ", ");
                add(key);
                add(": ");
                add(val);
                free(key);
                free(val);
                j += 1;
        }

        add("}");
#undef add
        
        --show_dicts.count;

        return s;
}

char *
show_array(struct value const *a)
{
        static vec(struct array *) show_arrays;

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

        for (char const *c = s; c < s + n; ++c) switch (*c) {
        case '\t':
                vec_push(v, '\\');
                vec_push(v, 't');
                break;
        case '\r':
                vec_push(v, '\\');
                vec_push(v, 'r');
                break;
        case '\n':
                vec_push(v, '\\');
                vec_push(v, 'n');
                break;
        case '\'':
                vec_push(v, '\\');
        default:
                vec_push(v, *c);
        }

        vec_push(v, '\'');
        vec_push(v, '\0');

        return v.items;
}

char *
value_show(struct value const *v)
{
        static char buffer[1024];
        char *s = NULL;

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
        case VALUE_DICT:
                s = show_dict(v);
                break;
        case VALUE_FUNCTION:
                snprintf(buffer, 1024, "<function at %p>", (void *) v->code);
                break;
        case VALUE_METHOD:
                if (v->this == NULL)
                        snprintf(buffer, 1024, "<method '%s' at %p>", v->name, (void *)v->method);
                else
                        snprintf(buffer, 1024, "<method '%s' at %p bound to <value at %p>>", v->name, (void *)v->method, (void *)v->this);
                break;
        case VALUE_BUILTIN_METHOD:
                snprintf(buffer, 1024, "<bound builtin method '%s'>", v->name);
                break;
        case VALUE_BUILTIN_FUNCTION:
                snprintf(buffer, 1024, "<builtin function>");
                break;
        case VALUE_CLASS:
                snprintf(buffer, 1024, "<class %s>", class_name(v->class));
                break;
        case VALUE_OBJECT:
                snprintf(buffer, 1024, "<%s object at %p>", class_name(v->class), (void *)v->object);
                break;
        case VALUE_TAG:
                snprintf(buffer, 1024, "%s", tags_name(v->tag));
                break;
        case VALUE_BLOB:
                snprintf(buffer, 1024, "<blob at %p (%zu bytes)>", (void *) v->blob, v->blob->count);
                break;
        case VALUE_PTR:
                snprintf(buffer, 1024, "<pointer at %p>", v->ptr);
                break;
        case VALUE_SENTINEL:
                return sclone("<sentinel>");
        case VALUE_NONE:
                return sclone("<none>");
        case VALUE_INDEX:
                snprintf(buffer, 1024, "<index: (%d, %d, %d)>", (int)v->i, (int)v->off, (int)v->nt);
                break;
        default:
                return sclone("< !!! >");
        }

        char *result = sclone(tags_wrap(s == NULL ? buffer : s, v->type & VALUE_TAGGED ? v->tags : 0));
        free(s);

        return result;
}

int
value_compare(void const *_v1, void const *_v2)
{
        struct value const *v1 = _v1;
        struct value const *v2 = _v2;

        if (v1->type != v2->type)
                vm_panic("attempt to compare values of different types");

        switch (v1->type) {
        case VALUE_INTEGER: return (v1->integer - v2->integer); // TODO
        case VALUE_REAL:    return (v1->real < v2->real) ? -1 : (v1->real != v2->real);
        case VALUE_STRING:  return memcmp(v1->string, v2->string, min(v1->bytes, v2->bytes));
        case VALUE_ARRAY:
                for (int i = 0; i < v1->array->count && i < v2->array->count; ++i) {
                        int o = value_compare(&v1->array->items[i], &v2->array->items[i]);
                        if (o != 0)
                                return o;
                }
                return ((int)v1->array->count) - ((int)v2->array->count);
        case VALUE_OBJECT:;
                struct value const *cmpfn = class_lookup_method(v1->class, "<=>");
                if (cmpfn == NULL)
                        goto Fail;
                struct value v = vm_eval_function2(cmpfn, v1, v2);
                if (v.type != VALUE_INTEGER)
                        vm_panic("user-defined %s.<=> method returned non-integer", class_name(v1->class));
                return v.integer;
        default:
        Fail:
                vm_panic("attempt to compare values of invalid types: %s and %s", value_show(v1), value_show(v2));
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
        case VALUE_DICT:             return true;
        case VALUE_CLASS:            return true;
        case VALUE_OBJECT:           return true;
        case VALUE_METHOD:           return true;
        case VALUE_PTR:              return v->ptr != NULL;
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
                if (v->type != VALUE_STRING)
                        vm_panic("regex applied as predicate to non-string");
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

                        if (rc < -1)
                                vm_panic("error while executing regular expression");

                        return rc == 0;
                }
        case VALUE_TAG:
                return tags_first(v->tags) == p->tag;
        case VALUE_CLASS:
                return v->type == VALUE_OBJECT && v->class == p->class;
        default:
                vm_panic("invalid type of value used as a predicate");
        }
}

struct value
value_apply_callable(struct value *f, struct value *v)
{
        switch (f->type) {
        case VALUE_FUNCTION:
        case VALUE_BUILTIN_FUNCTION:
        case VALUE_METHOD:
        case VALUE_BUILTIN_METHOD:
                return vm_eval_function(f, v);
        case VALUE_REGEX:
                if (v->type != VALUE_STRING)
                        vm_panic("regex applied as predicate to non-string");

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

                if (rc < -1)
                        vm_panic("error while executing regular expression");

                if (rc == -1)
                        return NIL;

                struct value match;

                if (rc == 1) {
                        match = STRING_VIEW(*v, ovec[0], ovec[1] - ovec[0]);
                } else {
                        match = ARRAY(value_array_new());
                        NOGC(match.array);
                        value_array_reserve(match.array, rc);

                        int j = 0;
                        for (int i = 0; i < rc; ++i, j += 2)
                                value_array_push(match.array, STRING_VIEW(*v, ovec[j], ovec[j + 1] - ovec[j]));

                        OKGC(match.array);
                }

                return match;
        case VALUE_TAG:
                {
                        struct value result = *v;
                        result.tags = tags_push(result.tags, f->tag);
                        result.type |= VALUE_TAGGED;
                        return result;
                }
        case VALUE_CLASS:
                {
                        struct value result = OBJECT(object_new(), f->class);
                        struct value *init = class_lookup_method(f->class, "init");
                        if (init != NULL)
                                vm_eval_function(&METHOD(NULL, init, &result), v);
                        return result;
                }
        default:
                vm_panic("invalid type of value used as a predicate");
        }
}

bool
value_test_equality(struct value const *v1, struct value const *v2)
{
        if (v1->type != v2->type)
                return false;

        struct value *f;

        switch (v1->type & ~VALUE_TAGGED) {
        case VALUE_REAL:             if (v1->real != v2->real)                                                      return false; break;
        case VALUE_BOOLEAN:          if (v1->boolean != v2->boolean)                                                return false; break;
        case VALUE_INTEGER:          if (v1->integer != v2->integer)                                                return false; break;
        case VALUE_STRING:           if (v1->bytes != v2->bytes || memcmp(v1->string, v2->string, v1->bytes) != 0)  return false; break;
        case VALUE_ARRAY:            if (!arrays_equal(v1, v2))                                                     return false; break;
        case VALUE_REGEX:            if (v1->regex != v2->regex)                                                    return false; break;
        case VALUE_FUNCTION:         if (v1->code != v2->code)                                                      return false; break;
        case VALUE_BUILTIN_FUNCTION: if (v1->builtin_function != v2->builtin_function)                              return false; break;
        case VALUE_DICT:             if (v1->dict != v2->dict)                                                      return false; break;
        case VALUE_METHOD:           if (v1->method != v2->method || v1->this != v2->this)                          return false; break;
        case VALUE_BUILTIN_METHOD:   if (v1->builtin_method != v2->builtin_method || v1->this != v2->this)          return false; break;
        case VALUE_TAG:              if (v1->tag != v2->tag)                                                        return false; break;
        case VALUE_BLOB:             if (v1->blob->items != v2->blob->items)                                        return false; break;
        case VALUE_PTR:              if (v1->ptr != v2->ptr)                                                        return false;
        case VALUE_NIL:                                                                                                           break;
        case VALUE_OBJECT:
                f = class_lookup_method(v1->class, "<=>");
                if (f != NULL) {
                        if (value_compare(v1, v2) != 0) {
                                return false;
                        }
                } else if (v1->object != v2->object) {
                        return false;
                }
        }

        if (v1->tags != v2->tags)
                return false;

        return true;
}

inline static void
value_array_mark(struct array *a)
{
        MARK(a);

        for (int i = 0; i < a->count; ++i)
                value_mark(&a->items[i]);
}

inline static void
function_mark_references(struct value *v)
{
        for (size_t i = 0; i < v->refs->count; ++i) {
                struct variable *var = (struct variable *)v->refs->refs[i].pointer;
                if (MARKED(var))
                        continue;
                MARK(var);
                value_mark(&var->value);
        }

        MARK(v->refs);
}

char *
value_clone_string(char const *src, int n)
{
        char *s = gc_alloc_object(n, GC_STRING);
        memcpy(s, src, n);
        return s;
}

char *
value_string_alloc(int n)
{
        return gc_alloc_object(n, GC_STRING);
}

void
_value_mark(struct value *v)
{
        switch (v->type) {
        case VALUE_METHOD:          MARK(v->this); value_mark(v->this);                break;
        case VALUE_BUILTIN_METHOD:  MARK(v->this); value_mark(v->this);                break;
        case VALUE_ARRAY:           value_array_mark(v->array);                        break;
        case VALUE_DICT:            dict_mark(v->dict);                                break;
        case VALUE_FUNCTION:        if (v->refs != NULL) function_mark_references(v);  break;
        case VALUE_STRING:          if (v->gcstr != NULL) MARK(v->gcstr);              break;
        case VALUE_OBJECT:          object_mark(v->object);                            break;
        case VALUE_BLOB:            MARK(v->blob);                                     break;
        default:                                                                       break;
        }
}

struct blob *
value_blob_new(void)
{
        struct blob *blob = gc_alloc_object(sizeof *blob, GC_BLOB);
        vec_init(*blob);
        return blob;
}

struct array *
value_array_new(void)
{
        struct array *a = gc_alloc_object(sizeof *a, GC_ARRAY);
        vec_init(*a);
        return a;
}

struct array *
value_array_clone(struct array const *a)
{
        struct array *new = value_array_new();

        /*
         * If a is empty, then we'd end up passing a null pointer
         * to memcpy which is UB, so we handle it specially.
         */
        if (a->count == 0)
                return new;

        NOGC(new);

        new->count = a->count;
        new->capacity = a->count;
        new->items = gc_alloc(sizeof *new->items * new->count);
        memcpy(new->items, a->items, sizeof *new->items * new->count);

        OKGC(new);

        return new;
}

void
value_array_extend(struct array *a, struct array const *other)
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
        struct ref_vector *v = gc_alloc_object(sizeof *v + sizeof (struct reference) * n, GC_REF_VECTOR);
        v->count = n;
        return v;
}

TEST(hash)
{
        struct value v1 = STRING_NOGC("hello", 5);
        struct value v2 = STRING_NOGC("world", 5);

        claim(value_hash(&v1) != value_hash(&v2));
}

TEST(equality)
{
        vm_init(0, NULL);

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
