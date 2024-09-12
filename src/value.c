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
#include "token.h"
#include "ast.h"
#include "compiler.h"

static bool
arrays_equal(struct value const *v1, struct value const *v2)
{
        if (v1->array == v2->array)
                return true;

        if (v1->array->count != v2->array->count)
                return false;

        size_t n = v1->array->count;

        for (size_t i = 0; i < n; ++i)
                if (!value_test_equality(&v1->array->items[i], &v2->array->items[i]))
                        return false;

        return true;
}

static bool
tuples_equal(struct value const *v1, struct value const *v2)
{
        if (v1->items == v2->items)
                return true;

        if (v1->count != v2->count)
                return false;

        size_t n = v1->count;

        for (size_t i = 0; i < n; ++i)
                if (!value_test_equality(&v1->items[i], &v2->items[i]))
                        return false;

        return true;
}

inline static unsigned long
str_hash(char const *str, int n)
{
        unsigned long hash = 2166136261UL;

        for (int i = 0; i < n; ++i)
                hash = (hash ^ str[i]) * 16777619UL;

        return hash;
}

inline static unsigned long
int_hash(intmax_t k)
{
        unsigned long hash = 2166136261UL;
        char const *bytes = (char const *) &k;
        unsigned char c;

        for (int i = 0; i < sizeof k; ++i) {
                c = bytes[i];
                hash = (hash ^ c) * 16777619UL;
        }

        return hash;
}

inline static unsigned long
ptr_hash(void const *p)
{
        unsigned long hash = 2166136261UL;
        char const *bytes = (char const *) &p;
        unsigned char c;

        for (int i = 0; i < sizeof p; ++i) {
                c = bytes[i];
                hash = (hash ^ c) * 16777619UL;
        }

        return hash;
}

inline static unsigned long
flt_hash(float flt)
{
        unsigned long hash = 2166136261UL;
        char const *bytes = (char const *) &flt;
        unsigned char c;

        for (int i = 0; i < sizeof flt; ++i) {
                c = bytes[i];
                hash = (hash ^ c) * 16777619UL;
        }

        return hash;
}

inline static unsigned long
ary_hash(struct value const *a)
{
        unsigned long hash = 2166136261UL;

        for (int i = 0; i < a->array->count; ++i) {
                unsigned char c = value_hash(&a->array->items[i]);
                hash = (hash ^ c) * 16777619UL;
        }

        return hash;
}

inline static unsigned long
tpl_hash(struct value const *t)
{
        unsigned long hash = 2166136261UL;

        for (int i = 0; i < t->count; ++i) {
                unsigned char c = value_hash(&t->items[i]);
                hash = (hash ^ c) * 16777619UL;
        }

        return hash;
}

inline static unsigned long
obj_hash(struct value const *v)
{
        struct value const *f = class_method(v->class, "__hash__");

        if (f != NULL) {
                struct value h = vm_eval_function(f, v, NULL);
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
        case VALUE_TUPLE:             return tpl_hash(val);
        case VALUE_DICT:              return ptr_hash(val->dict);
        case VALUE_OBJECT:            return obj_hash(val);
        case VALUE_METHOD:            return ptr_hash(val->method) ^ str_hash((void *)val->this, sizeof (Value));
        case VALUE_BUILTIN_METHOD:    return ptr_hash(val->builtin_method) ^ ptr_hash(val->this);
        case VALUE_FUNCTION:          return ptr_hash(val->builtin_function);
        case VALUE_BUILTIN_FUNCTION:  return ptr_hash(val->info) ^ ptr_hash(val->env);
        case VALUE_REGEX:             return ptr_hash(val->regex);
        case VALUE_PTR:               return ptr_hash(val->ptr);
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
show_dict(struct value const *d, bool color)
{
        static _Thread_local vec(struct dict *) show_dicts;

        for (int i = 0; i < show_dicts.count; ++i)
                if (show_dicts.items[i] == d->dict)
                        return sclone("{...}");

        vec_push(show_dicts, d->dict);

        size_t capacity = 1;
        size_t len = 1;
        size_t n;
        char *s = gc_alloc(2);
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
                char *key = color ? value_show_color(&d->dict->keys[i]) : value_show(&d->dict->keys[i]);
                char *val = color ? value_show_color(&d->dict->values[i]) : value_show(&d->dict->values[i]);
                add(j == 0 ? "" : ", ");
                add(key);
                if (d->dict->values[i].type != VALUE_NIL) {
                        add(": ");
                        add(val);
                }
                gc_free(key);
                gc_free(val);
                j += 1;
        }

        add("}");
#undef add

        --show_dicts.count;

        return s;
}

char *
show_array(struct value const *a, bool color)
{
        static _Thread_local vec(struct array *) show_arrays;

        for (int i = 0; i < show_arrays.count; ++i)
                if (show_arrays.items[i] == a->array)
                        return sclone("[...]");

        vec_push(show_arrays, a->array);

        size_t capacity = 1;
        size_t len = 1;
        size_t n;
        char *s = gc_alloc(2);
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
                char *val = color ? value_show_color(&a->array->items[i]) : value_show(&a->array->items[i]);
                add(i == 0 ? "" : ", ");
                add(val);
                gc_free(val);
        }

        add("]");
#undef add

        --show_arrays.count;

        return s;
}

char *
show_tuple(struct value const *v, bool color)
{
        static _Thread_local vec(struct value *) show_tuples;

        for (int i = 0; i < show_tuples.count; ++i)
                if (show_tuples.items[i] == v->items)
                        return sclone("(...)");

        vec_push(show_tuples, v->items);

        bool tagged = v->type & VALUE_TAGGED;
        size_t capacity = 1;
        size_t len = !tagged;
        size_t n;
        char *s = gc_alloc(2);

        strcpy(s, !tagged ? "(" : "");

#define add(str) \
                n = strlen(str); \
                if (len + n >= capacity) {\
                        capacity = 2 * (len + n) + 1; \
                        resize(s, capacity); \
                } \
                strcpy(s + len, str); \
                len += n;

        for (size_t i = 0; i < v->count; ++i) {
                add(i == 0 ? "" : ", ");

                if (v->names != NULL && v->names[i] != NULL) {
                        if (color) {
                                add(TERM(34));
                                add(v->names[i]);
                                add(TERM(0));
                                add(": ");
                        } else {
                                add(v->names[i]);
                                add(": ");
                        }
                }

                char *val = color ? value_show_color(&v->items[i]) : value_show(&v->items[i]);
                add(val);
                gc_free(val);
        }

        if (!tagged) {
                add(")");
        }
#undef add

        --show_tuples.count;

        return s;
}

static char *
show_string(char const *s, size_t n, bool color)
{
        vec(char) v;
        vec_init(v);

#define COLOR(i) if (color) vec_push_n(v, TERM(i), strlen(TERM(i)))

        COLOR(92);

        vec_push(v, '\'');

        if (s != NULL) for (char const *c = s; c < s + n; ++c) switch (*c) {
        case '\t':
                COLOR(95);
                vec_push(v, '\\');
                vec_push(v, 't');
                COLOR(92);
                break;
        case '\r':
                COLOR(95);
                vec_push(v, '\\');
                vec_push(v, 'r');
                COLOR(92);
                break;
        case '\n':
                COLOR(95);
                vec_push(v, '\\');
                vec_push(v, 'n');
                COLOR(92);
                break;
        case '\\':
                COLOR(95);
                vec_push(v, '\\');
                vec_push(v, '\\');
                COLOR(92);
                break;
        case '\'':
                COLOR(95);
                vec_push(v, '\\');
                vec_push(v, '\'');
                COLOR(92);
                break;
        default:
                vec_push(v, *c);
        }

        vec_push(v, '\'');

        COLOR(0);

#undef COLOR

        vec_push(v, '\0');

        return v.items;
}

char *
value_show(struct value const *v)
{
        char buffer[1024];
        char *s = NULL;

        switch (v->type & ~VALUE_TAGGED) {
        case VALUE_INTEGER:
                snprintf(buffer, 1024, "%"PRIiMAX, v->integer);
                break;
        case VALUE_REAL:
                snprintf(buffer, 1024, "%g", v->real);
                break;
        case VALUE_STRING:
                s = show_string(v->string, v->bytes, false);
                break;
        case VALUE_BOOLEAN:
                snprintf(buffer, 1024, "%s", v->boolean ? "true" : "false");
                break;
        case VALUE_NIL:
                snprintf(buffer, 1024, "%s", "nil");
                break;
        case VALUE_ARRAY:
                s = show_array(v, false);
                break;
        case VALUE_TUPLE:
                s = show_tuple(v, false);
                break;
        case VALUE_REGEX:
                snprintf(buffer, 1024, "/%s/", v->regex->pattern);
                break;
        case VALUE_DICT:
                s = show_dict(v, false);
                break;
        case VALUE_FUNCTION:
                if (v->info[6] == -1) {
                        snprintf(buffer, 1024, "<function '%s' at %p>", name_of(v), (void *)((char *)v->info + v->info[0]));
                } else {
                        char const *class = class_name(v->info[6]);
                        snprintf(buffer, 1024, "<function '%s.%s' at %p>", class, name_of(v), (void *)((char *)v->info + v->info[0]));
                }
                break;
        case VALUE_METHOD:
                if (v->this == NULL)
                        snprintf(buffer, 1024, "<method '%s' at %p>", v->name, (void *)v->method);
                else
                        snprintf(buffer, 1024, "<method '%s' at %p bound to %s>", v->name, (void *)v->method, value_show(v->this));
                break;
        case VALUE_BUILTIN_METHOD:
                snprintf(buffer, 1024, "<bound builtin method '%s'>", v->name);
                break;
        case VALUE_BUILTIN_FUNCTION:
                if (v->name == NULL)
                        snprintf(buffer, 1024, "<builtin function>");
                else if (v->module == NULL)
                        snprintf(buffer, 1024, "<builtin function '%s'>", v->name);
                else
                        snprintf(buffer, 1024, "<builtin function '%s::%s'>", v->module, v->name);
                break;
        case VALUE_CLASS:
                snprintf(buffer, 1024, "<class %s>", class_name(v->class));
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
        case VALUE_GENERATOR:
                snprintf(buffer, 1024, "<generator at %p>", v->gen);
                break;
        case VALUE_THREAD:
                snprintf(buffer, 1024, "<thread %"PRIu64">", v->thread->i);
                break;
        case VALUE_SENTINEL:
                return sclone("<sentinel>");
        case VALUE_REF:
                snprintf(buffer, 1024, "<reference to %p>", v->ptr);
                break;
        case VALUE_NONE:
                return sclone("<none>");
        case VALUE_INDEX:
                snprintf(buffer, 1024, "<index: (%d, %d, %d)>", (int)v->i, (int)v->off, (int)v->nt);
                break;
        case VALUE_OBJECT:;
#ifdef TY_NO_LOG
                struct value *fp = class_method(v->class, "__str__");
#else
                struct value *fp = NULL;
#endif
                if (fp != NULL && fp != class_method(CLASS_OBJECT, "__str__")) {
                        struct value str = vm_eval_function(fp, v, NULL);
                        if (str.type != VALUE_STRING)
                                vm_panic("%s.__str__() returned non-string", class_name(v->class));
                        s = gc_resize_unchecked(NULL, str.bytes + 1);
                        memcpy(s, str.string, str.bytes);
                        s[str.bytes] = '\0';
                } else {
                        snprintf(buffer, 1024, "<%s object at %p>", class_name(v->class), (void *)v->object);
                }
                break;
        default:
                return sclone("< !!! >");
        }

        char *result = tags_wrap(s == NULL ? buffer : s, v->type & VALUE_TAGGED ? v->tags : 0, false);
        gc_free(s);

        return result;
}

char *
value_show_color(struct value const *v)
{
        char buffer[4096];
        char *s = NULL;

        switch (v->type & ~VALUE_TAGGED) {
        case VALUE_INTEGER:
                snprintf(buffer, sizeof buffer, "%s%"PRIiMAX"%s", TERM(93), v->integer, TERM(0));
                break;
        case VALUE_REAL:
                snprintf(buffer, sizeof buffer, "%s%g%s", TERM(93), v->real, TERM(0));
                break;
        case VALUE_STRING:
                s = show_string(v->string, v->bytes, true);
                break;
        case VALUE_BOOLEAN:
                snprintf(buffer, sizeof buffer, "%s%s%s", TERM(36), v->boolean ? "true" : "false", TERM(0));
                break;
        case VALUE_NIL:
                snprintf(buffer, sizeof buffer, "%s%s%s", TERM(95), "nil", TERM(0));
                break;
        case VALUE_ARRAY:
                s = show_array(v, true);
                break;
        case VALUE_TUPLE:
                s = show_tuple(v, true);
                break;
        case VALUE_REGEX:
                snprintf(buffer, sizeof buffer, "%s/%s/%s", TERM(96), v->regex->pattern, TERM(0));
                break;
        case VALUE_DICT:
                s = show_dict(v, true);
                break;
        case VALUE_FUNCTION:
                if (v->info[6] == -1) {
                        snprintf(
                                buffer,
                                sizeof buffer,
                                "%s<function %s'%s'%s at %s%p%s>%s",
                                TERM(96),
                                TERM(92),
                                name_of(v),
                                TERM(96),
                                TERM(94),
                                (void *)((char *)v->info + v->info[0]),
                                TERM(96),
                                TERM(0)
                        );
                } else {
                        char const *class = class_name(v->info[6]);
                        snprintf(
                                buffer,
                                sizeof buffer,
                                "%s<function %s'%s.%s'%s at %s%p%s>%s",
                                TERM(96),
                                TERM(92),
                                class,
                                name_of(v),
                                TERM(96),
                                TERM(94),
                                (void *)((char *)v->info + v->info[0]),
                                TERM(96),
                                TERM(0)
                        );
                }
                break;
        case VALUE_METHOD:
                if (v->this == NULL) {
                        snprintf(
                                buffer,
                                sizeof buffer,
                                "%s<method %s'%s'%s at %s%p%s>%s",
                                TERM(96),
                                TERM(92),
                                v->name,
                                TERM(96),
                                TERM(94),
                                (void *)v->method,
                                TERM(96),
                                TERM(0)
                        );
                } else {
                        char *vs = value_show_color(v->this);
                        snprintf(
                                buffer,
                                sizeof buffer,
                                "%s<method %s'%s'%s at %s%p%s bound to %s%s%s>%s",
                                TERM(96),
                                TERM(92),
                                v->name,
                                TERM(96),
                                TERM(94),
                                (void *)v->method,
                                TERM(96),
                                TERM(0),
                                vs,
                                TERM(96),
                                TERM(0)
                        );
                        gc_free(vs);
                }
                break;
        case VALUE_BUILTIN_METHOD:
                snprintf(
                        buffer,
                        sizeof buffer,
                        "%s<bound builtin method %s'%s'%s>%s",
                        TERM(96),
                        TERM(92),
                        v->name,
                        TERM(96),
                        TERM(0)
                );
                break;
        case VALUE_BUILTIN_FUNCTION:
                if (v->name == NULL)
                        snprintf(
                                buffer,
                                sizeof buffer,
                                "%s<builtin function>%s",
                                TERM(96),
                                TERM(0)
                        );
                else if (v->module == NULL)
                        snprintf(
                                buffer,
                                sizeof buffer,
                                "%s<builtin function %s'%s'%s>%s",
                                TERM(96),
                                TERM(92),
                                v->name,
                                TERM(96),
                                TERM(0)
                        );
                else
                        snprintf(
                                buffer,
                                sizeof buffer,
                                "%s<builtin function %s'%s::%s'%s>%s",
                                TERM(96),
                                TERM(92),
                                v->module,
                                v->name,
                                TERM(96),
                                TERM(0)
                        );
                break;
        case VALUE_CLASS:
                snprintf(
                        buffer,
                        sizeof buffer,
                        "%s<%sclass %s%s%s>%s",
                        TERM(96),
                        TERM(92),
                        TERM(94),
                        class_name(v->class),
                        TERM(96),
                        TERM(0)
                );
                break;
        case VALUE_TAG:
                snprintf(buffer, sizeof buffer, "%s%s%s", TERM(34), tags_name(v->tag), TERM(0));
                break;
        case VALUE_BLOB:
                snprintf(buffer, sizeof buffer, "<blob at %p (%zu bytes)>", (void *) v->blob, v->blob->count);
                break;
        case VALUE_PTR:
                snprintf(
                        buffer,
                        sizeof buffer,
                        "%s<pointer at %s%s%p%s%s>%s",
                        TERM(32),
                        TERM(1),
                        TERM(92),
                        v->ptr,
                        TERM(0),
                        TERM(32),
                        TERM(0)
                );
                break;
        case VALUE_GENERATOR:
                snprintf(buffer, sizeof buffer, "<generator at %p>", v->gen);
                break;
        case VALUE_THREAD:
                snprintf(buffer, sizeof buffer, "%s<thread %"PRIu64">%s", TERM(33), v->thread->i, TERM(0));
                break;
        case VALUE_SENTINEL:
                return sclone("<sentinel>");
        case VALUE_REF:
                snprintf(buffer, sizeof buffer, "<reference to %p>", v->ptr);
                break;
        case VALUE_NONE:
                return sclone("<none>");
        case VALUE_INDEX:
                snprintf(buffer, sizeof buffer, "<index: (%d, %d, %d)>", (int)v->i, (int)v->off, (int)v->nt);
                break;
        case VALUE_OBJECT:;
#ifdef TY_NO_LOG
                struct value *fp = class_method(v->class, "__str__");
#else
                struct value *fp = NULL;
#endif
                if (fp != NULL && fp != class_method(CLASS_OBJECT, "__str__")) {
                        struct value str = vm_eval_function(fp, v, NULL);
                        gc_push(&str);
                        if (str.type != VALUE_STRING)
                                vm_panic("%s.__str__() returned non-string", class_name(v->class));
                        s = gc_alloc(str.bytes + 1);
                        gc_pop();
                        memcpy(s, str.string, str.bytes);
                        s[str.bytes] = '\0';
                } else {
                        snprintf(
                                buffer,
                                sizeof buffer,
                                "%s<%s%s%s object at %s%p%s>%s",
                                TERM(96),
                                TERM(34),
                                class_name(v->class),
                                TERM(96),
                                TERM(94),
                                (void *)v->object,
                                TERM(96),
                                TERM(0)
                        );
                }
                break;
        default:
                return sclone("< !!! >");
        }

        char *result = tags_wrap(s == NULL ? buffer : s, v->type & VALUE_TAGGED ? v->tags : 0, true);
        gc_free(s);

        return result;
}

int
value_compare(void const *_v1, void const *_v2)
{
        struct value const *v1 = _v1;
        struct value const *v2 = _v2;
        struct value v;

        if (v1->type == VALUE_REAL && v2->type == VALUE_INTEGER) {
                v = REAL(v2->integer);
                v2 = &v;
        }

        if (v1->type == VALUE_INTEGER && v2->type == VALUE_REAL) {
                v = REAL(v1->integer);
                v1 = &v;
        }

        if (v1->type != v2->type && v1->type != VALUE_OBJECT) {
                vm_panic(
                        "attempt to compare values of different types: %s%s%s and %s%s%s",
                        TERM(33),
                        value_show(v1),
                        TERM(0),
                        TERM(33),
                        value_show(v2),
                        TERM(0)
                );
        }

        switch (v1->type & ~VALUE_TAGGED) {
        case VALUE_INTEGER: return (v1->integer < v2->integer) ? -1 : (v1->integer != v2->integer);
        case VALUE_REAL:    return (v1->real < v2->real) ? -1 : (v1->real != v2->real);
        case VALUE_STRING:;
                int c = memcmp(v1->string, v2->string, min(v1->bytes, v2->bytes));
                if (c == 0) return ((int)v1->bytes - (int)v2->bytes);
                return c;
        case VALUE_ARRAY:
                for (int i = 0; i < v1->array->count && i < v2->array->count; ++i) {
                        int o = value_compare(&v1->array->items[i], &v2->array->items[i]);
                        if (o != 0)
                                return o;
                }
                return ((int)v1->array->count) - ((int)v2->array->count);
        case VALUE_TUPLE:
                for (int i = 0; i < v1->count && i < v2->count; ++i) {
                        int o = value_compare(&v1->items[i], &v2->items[i]);
                        if (o != 0)
                                return o;
                }
                return ((int)v1->count) - ((int)v2->count);
        case VALUE_OBJECT:;
                struct value const *cmpfn = class_method(v1->class, "<=>");
                struct value method = METHOD("<=>", cmpfn, v1);
                if (cmpfn == NULL)
                        goto Fail;
                struct value v = vm_eval_function(&method, v2, NULL);
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
        case VALUE_STRING:           return (v->bytes > 0);
        case VALUE_ARRAY:            return (v->array->count != 0);
        case VALUE_TUPLE:            return (v->count != 0);
        case VALUE_BLOB:             return (v->blob->count != 0);
        case VALUE_REGEX:            return true;
        case VALUE_FUNCTION:         return true;
        case VALUE_BUILTIN_FUNCTION: return true;
        case VALUE_BUILTIN_METHOD:   return true;
        case VALUE_DICT:             return true;
        case VALUE_CLASS:            return true;
        case VALUE_OBJECT:           return true;
        case VALUE_METHOD:           return true;
        case VALUE_TAG:              return true;
        case VALUE_GENERATOR:        return true;
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
        case VALUE_METHOD:
        case VALUE_BUILTIN_METHOD:
                vm_push(v);
                b = vm_call(p, 1);
                return value_truthy(&b);
        case VALUE_REGEX:
                if (v->type != VALUE_STRING)
                        vm_panic("regex applied as predicate to non-string");
                {
                        char const *s = v->string;
                        int len = v->bytes;
                        int rc;

                        rc = pcre_exec(
                                p->regex->pcre,
                                p->regex->extra,
                                s,
                                len,
                                0,
                                0,
                                NULL,
                                0
                        );

                        if (rc < -2)
                                vm_panic("error while executing regular expression: %d", rc);

                        return rc == 0;
                }
        case VALUE_TAG:
                return tags_first(v->tags) == p->tag;
        case VALUE_CLASS:
                return v->type == VALUE_OBJECT && v->class == p->class;
        default:
                vm_panic("invalid type of value used as a predicate: %s", value_show(v));
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
        case VALUE_CLASS:
        case VALUE_TAG:
                vm_push(v);
                return vm_call(f, 1);
        case VALUE_REGEX:
                if (v->type != VALUE_STRING)
                        vm_panic("regex applied as predicate to non-string");

                static _Thread_local int ovec[30];
                char const *s = v->string;
                int len = v->bytes;
                int rc;

                rc = pcre_exec(
                        f->regex->pcre,
                        f->regex->extra,
                        s,
                        len,
                        0,
                        0,
                        ovec,
                        30
                );

                if (rc < -2)
                        vm_panic("error while executing regular expression: %d", rc);

                if (rc < 0)
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
        default:
                vm_panic("invalid type of value used as a callable: %s", value_show(f));
        }
}

bool
value_test_equality(struct value const *v1, struct value const *v2)
{
        if (v1->type != v2->type && v1->type != VALUE_OBJECT)
                return false;

        struct value *f;

        switch (v1->type & ~VALUE_TAGGED) {
        case VALUE_REAL:             if (v1->real != v2->real)                                                      return false; break;
        case VALUE_BOOLEAN:          if (v1->boolean != v2->boolean)                                                return false; break;
        case VALUE_INTEGER:          if (v1->integer != v2->integer)                                                return false; break;
        case VALUE_STRING:           if (v1->bytes != v2->bytes || memcmp(v1->string, v2->string, v1->bytes) != 0)  return false; break;
        case VALUE_ARRAY:            if (!arrays_equal(v1, v2))                                                     return false; break;
        case VALUE_TUPLE:            if (!tuples_equal(v1, v2))                                                     return false; break;
        case VALUE_REGEX:            if (v1->regex != v2->regex)                                                    return false; break;
        case VALUE_FUNCTION:         if (v1->info != v2->info)                                                      return false; break;
        case VALUE_BUILTIN_FUNCTION: if (v1->builtin_function != v2->builtin_function)                              return false; break;
        case VALUE_DICT:             if (v1->dict != v2->dict)                                                      return false; break;
        case VALUE_METHOD:           if (v1->method != v2->method || v1->this != v2->this)                          return false; break;
        case VALUE_BUILTIN_METHOD:   if (v1->builtin_method != v2->builtin_method || memcmp(v1->this, v2->this, sizeof (Value)) != 0) return false; break;
        case VALUE_TAG:              if (v1->tag != v2->tag)                                                        return false; break;
        case VALUE_CLASS:            if (v1->class != v2->class)                                                    return false; break;
        case VALUE_BLOB:             if (v1->blob->items != v2->blob->items)                                        return false; break;
        case VALUE_PTR:              if (v1->ptr != v2->ptr)                                                        return false; break;
        case VALUE_NIL:                                                                                                           break;
        case VALUE_OBJECT:
                f = class_method(v1->class, "<=>");
                if (f != NULL) {
                        if (value_compare(v1, v2) != 0) {
                                return false;
                        }
                } else if (v2->type != VALUE_OBJECT || v1->object != v2->object) {
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
        if (MARKED(a)) return;

        MARK(a);

        for (int i = 0; i < a->count; ++i) {
                value_mark(&a->items[i]);
        }
}

inline static void
mark_tuple(struct value const *v)
{
        if (v->items == NULL || MARKED(v->items)) return;

        MARK(v->items);

        for (int i = 0; i < v->count; ++i) {
                value_mark(&v->items[i]);
        }

        if (v->names != NULL) {
                MARK(v->names);
                if (v->gc_names) {
                        for (int i = 0; i < v->count; ++i) {
                                if (v->names[i] != NULL) {
                                        MARK(v->names[i]);
                                        break;
                                }
                        }
                }
        }
}

inline static void
mark_thread(struct value const *v)
{
        if (MARKED(v->thread)) return;
        MARK(v->thread);
        value_mark(&v->thread->v);
}

inline static void
mark_generator(struct value const *v)
{
        if (MARKED(v->gen)) return;

        MARK(v->gen);

        value_mark(&v->gen->f);

        for (int i = 0; i < v->gen->frame.count; ++i) {
                value_mark(&v->gen->frame.items[i]);
        }
}

inline static void
mark_function(struct value const *v)
{
        int n = v->info[2];

        if (*from_eval(v))
                MARK(v->info);

        if (n == 0 || MARKED(v->env))
                return;

        MARK(v->env);

        for (size_t i = 0; i < n; ++i) {
                if (v->env[i] == NULL)
                        continue;
                MARK(v->env[i]);
                value_mark(v->env[i]);
        }
}

inline static void
mark_pointer(struct value const *v)
{
        if (v->gcptr != NULL) {
                MARK(v->gcptr);
                if (ALLOC_OF(v->gcptr)->type == GC_VALUE) {
                        value_mark((const struct value *)v->gcptr);
                }
        }
}

char *
value_string_clone_nul(char const *src, int n)
{
        char *s = gc_alloc_object(n + 1, GC_STRING);

        memcpy(s, src, n);
        s[n] = '\0';

        return s;
}

char *
value_string_clone(char const *src, int n)
{
        if (n == 0) {
                return NULL;
        }

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
_value_mark(struct value const *v)
{
        void **src = source_lookup(v->src);
        if (src != NULL && *src != NULL) {
                MARK(*src);
        }

#ifndef TY_RELEASE
        static _Thread_local int d;

        ++GC_OFF_COUNT;
        //GCLOG("Marking: %s", value_show(v));
        --GC_OFF_COUNT;

        ++d;
#endif

        switch (v->type & ~VALUE_TAGGED) {
        case VALUE_METHOD:          if (!MARKED(v->this)) { MARK(v->this); value_mark(v->this); } break;
        case VALUE_BUILTIN_METHOD:  if (!MARKED(v->this)) { MARK(v->this); value_mark(v->this); } break;
        case VALUE_ARRAY:           value_array_mark(v->array);                                   break;
        case VALUE_TUPLE:           mark_tuple(v);                                                break;
        case VALUE_DICT:            dict_mark(v->dict);                                           break;
        case VALUE_FUNCTION:        mark_function(v);                                             break;
        case VALUE_GENERATOR:       mark_generator(v);                                            break;
        case VALUE_THREAD:          mark_thread(v);                                               break;
        case VALUE_STRING:          if (v->gcstr != NULL) MARK(v->gcstr);                         break;
        case VALUE_OBJECT:          object_mark(v->object);                                       break;
        case VALUE_REF:             MARK(v->ptr); value_mark(v->ptr);                             break;
        case VALUE_BLOB:            MARK(v->blob);                                                break;
        case VALUE_PTR:             mark_pointer(v);                                              break;
        case VALUE_REGEX:           if (v->regex->gc) MARK(v->regex);                             break;
        default:                                                                                  break;
        }

#ifndef TY_RELEASE
        --d;
#endif
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

struct value
value_tuple(int n)
{
        struct value *items = gc_alloc_object(n * sizeof (Value), GC_TUPLE);

        for (int i = 0; i < n; ++i) {
                items[i] = NIL;
        }

        return TUPLE(items, NULL, n, false);
}

struct value
value_named_tuple(char const *first, ...)
{
        va_list ap;
        va_start(ap, first);

        int n = 0;

        do {
                va_arg(ap, struct value);
                n += 1;
        } while (va_arg(ap, char const *) != NULL);

        va_end(ap);

        struct value *items = gc_alloc_object(n * sizeof (Value), GC_TUPLE);

        NOGC(items);
        char const **names = gc_alloc_object(n * sizeof (char *), GC_TUPLE);
        OKGC(items);

        va_start(ap, first);

        names[0] = first[0] == '\0' ? NULL : first;
        items[0] = va_arg(ap, struct value);

        for (int i = 1; i < n; ++i) {
                names[i] = va_arg(ap, char *);
                items[i] = va_arg(ap, struct value);
                names[i] = names[i][0] == '\0' ? NULL : names[i];
        }

        va_end(ap);

        return TUPLE(items, (char **)names, n, false);
}

struct value *
tuple_get(struct value *tuple, char const *name)
{
        if (tuple->names == NULL) {
                return NULL;
        }

        for (int i = 0; i < tuple->count; ++i) {
                if (tuple->names[i] != NULL && strcmp(tuple->names[i], name) == 0) {
                        return &tuple->items[i];
                }
        }

        return NULL;
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

int
tuple_get_completions(struct value const *v, char const *prefix, char **out, int max)
{
        int n = 0;
        int prefix_len = strlen(prefix);

        for (int i = 0; i < v->count; ++i) {
                if (n < max && v->names != NULL && strncmp(v->names[i], prefix, prefix_len) == 0) {
                        out[n++] = sclone_malloc(v->names[i]);
                }
        }

        return n;
}

/* vim: set sts=8 sw=8 expandtab: */
