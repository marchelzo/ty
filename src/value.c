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
#include "intern.h"
#include "compiler.h"
#include "types.h"

static char *value_showx(Ty *ty, Value const *v);
static char *value_show_colorx(Ty *ty, Value const *v);

static bool
arrays_equal(Ty *ty, Value const *v1, Value const *v2)
{
        if (v1->array == v2->array) {
                return true;
        }

        if (vN(*v1->array) != vN(*v2->array)) {
                return false;
        }

        usize n = vN(*v1->array);

        for (usize i = 0; i < n; ++i) {
                if (
                        !value_test_equality(
                                ty,
                                v_(*v1->array, i),
                                v_(*v2->array, i)
                        )
                )  {
                        return false;
                }
        }

        return true;
}

static bool
tuples_equal(Ty *ty, Value const *v1, Value const *v2)
{
        if (v1->items == v2->items)
                return true;

        if (v1->count != v2->count)
                return false;

        usize n = v1->count;

        for (usize i = 0; i < n; ++i) {
                if (
                        !value_test_equality(
                                ty,
                                &v1->items[i],
                                &v2->items[i]
                        )
                ) {
                        return false;
                }
        }

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
int_hash(Ty *ty, intmax_t k)
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
ptr_hash(Ty *ty, void const *p)
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
flt_hash(Ty *ty, float flt)
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
ary_hash(Ty *ty, Value const *a)
{
        unsigned long hash = 2166136261UL;

        for (int i = 0; i < a->array->count; ++i) {
                unsigned char c = value_hash(ty, &a->array->items[i]);
                hash = (hash ^ c) * 16777619UL;
        }

        return hash;
}

inline static unsigned long
tpl_hash(Ty *ty, Value const *t)
{
        unsigned long hash = 2166136261UL;

        for (int i = 0; i < t->count; ++i) {
                unsigned char c = value_hash(ty, &t->items[i]);
                hash = (hash ^ c) * 16777619UL;
        }

        return hash;
}

inline static unsigned long
obj_hash(Ty *ty, Value const *v)
{
        Value const *f = class_method(ty, v->class, "__hash__");

        if (f != NULL) {
                Value h = vm_eval_function(ty, f, v, NULL);
                if (h.type != VALUE_INTEGER) {
                        zP("%s.__hash__ return non-integer: %s", class_name(ty, v->class), VSC(v));
                }
                return (unsigned long)h.integer;
        } else {
                return ptr_hash(ty, v->object);
        }
}

inline static unsigned long
hash(Ty *ty, Value const *val)
{
        switch (val->type & ~VALUE_TAGGED) {
        case VALUE_NIL:               return 0xDEADBEEFULL;
        case VALUE_BOOLEAN:           return val->boolean ? 0xABCULL : 0xDEFULL;
        case VALUE_STRING:            return str_hash(val->str, val->bytes);
        case VALUE_INTEGER:           return int_hash(ty, val->integer);
        case VALUE_REAL:              return flt_hash(ty, val->real);
        case VALUE_ARRAY:             return ary_hash(ty, val);
        case VALUE_TUPLE:             return tpl_hash(ty, val);
        case VALUE_DICT:              return ptr_hash(ty, val->dict);
        case VALUE_OBJECT:            return obj_hash(ty, val);
        case VALUE_METHOD:            return ptr_hash(ty, val->method) ^ str_hash((void *)val->this, sizeof (Value));
        case VALUE_BUILTIN_METHOD:    return ptr_hash(ty, val->builtin_method) ^ ptr_hash(ty, val->this);
        case VALUE_FUNCTION:          return ptr_hash(ty, val->builtin_function);
        case VALUE_BUILTIN_FUNCTION:  return ptr_hash(ty, val->info) ^ ptr_hash(ty, val->env);
        case VALUE_REGEX:             return ptr_hash(ty, val->regex);
        case VALUE_PTR:               return ptr_hash(ty, val->ptr);
        case VALUE_TAG:               return (((unsigned long)val->tag) * 91238) ^ 0x123AEDDULL;
        case VALUE_CLASS:             return (((unsigned long)val->class) * 2048) ^ 0xAABB1012ULL;
        default:                      zP("attempt to hash invalid value: %s", VSC(val));
        }
}

unsigned long
value_hash(Ty *ty, Value const *val)
{
        return (((unsigned long)val->tags) << 14) + hash(ty, val);
}

char *
show_dict(Ty *ty, Value const *d, bool color)
{
        static _Thread_local vec(struct dict *) show_dicts;

        for (int i = 0; i < show_dicts.count; ++i)
                if (show_dicts.items[i] == d->dict)
                        return sclone(ty, "{...}");

        vvP(show_dicts, d->dict);

        size_t capacity = 1;
        size_t len = 1;
        size_t n;
        char *s = mA(2);
        strcpy(s, "{");

#define add(str) \
                n = strlen(str); \
                if (len + n >= capacity) {\
                        capacity = 2 * (len + n) + 1; \
                        mRE(s, capacity); \
                } \
                strcpy(s + len, str); \
                len += n;

        for (size_t i = 0, j = 0; i < d->dict->size; ++i) {
                if (d->dict->keys[i].type == 0) continue;
                char *key = color ? value_show_colorx(ty, &d->dict->keys[i]) : value_showx(ty, &d->dict->keys[i]);
                char *val = color ? value_show_colorx(ty, &d->dict->values[i]) : value_showx(ty, &d->dict->values[i]);
                add(j == 0 ? "" : ", ");
                add(key);
                if (d->dict->values[i].type != VALUE_NIL) {
                        add(": ");
                        add(val);
                }
                mF(key);
                mF(val);
                j += 1;
        }

        add("}");
#undef add

        --show_dicts.count;

        return s;
}

char *
show_array(Ty *ty, Value const *a, bool color)
{
        static _Thread_local vec(Array *) show_arrays;

        for (int i = 0; i < show_arrays.count; ++i)
                if (show_arrays.items[i] == a->array)
                        return sclone(ty, "[...]");

        vvP(show_arrays, a->array);

        size_t capacity = 1;
        size_t len = 1;
        size_t n;
        char *s = mA(2);
        strcpy(s, "[");

#define add(str) \
                n = strlen(str); \
                if (len + n >= capacity) {\
                        capacity = 2 * (len + n) + 1; \
                        mRE(s, capacity); \
                } \
                strcpy(s + len, str); \
                len += n;

        for (size_t i = 0; i < a->array->count; ++i) {
                char *val = color ? value_show_colorx(ty, &a->array->items[i]) : value_showx(ty, &a->array->items[i]);
                add(i == 0 ? "" : ", ");
                add(val);
                mF(val);
        }

        add("]");
#undef add

        --show_arrays.count;

        return s;
}

char *
show_tuple(Ty *ty, Value const *v, bool color)
{
        static _Thread_local vec(Value *) show_tuples;

        for (int i = 0; i < show_tuples.count; ++i)
                if (show_tuples.items[i] == v->items)
                        return sclone(ty, "(...)");

        vvP(show_tuples, v->items);

        bool tagged = v->type & VALUE_TAGGED;
        size_t capacity = 1;
        size_t len = !tagged;
        size_t n;
        char *s = mA(2);

        strcpy(s, !tagged ? "(" : "");

#define add(str) \
                n = strlen(str); \
                if (len + n >= capacity) {\
                        capacity = 2 * (len + n) + 1; \
                        mRE(s, capacity); \
                } \
                strcpy(s + len, str); \
                len += n;

        for (size_t i = 0; i < v->count; ++i) {
                add(i == 0 ? "" : ", ");
                if (v->ids != NULL && v->ids[i] != -1) {
                        char const *name = M_NAME(v->ids[i]);
                        if (color) {
                                add(TERM(34));
                                add(name);
                                add(TERM(0));
                                add(": ");
                        } else {
                                add(name);
                                add(": ");
                        }
                }

                char *val = color ? value_show_colorx(ty, &v->items[i]) : value_showx(ty, &v->items[i]);
                add(val);
                mF(val);
        }

        if (!tagged) {
                add(")");
        }
#undef add

        --show_tuples.count;

        return s;
}

static char *
show_string(Ty *ty, char const *s, size_t n, bool color)
{
        vec(char) v = {0};

#define COLOR(i) if (color) vvPn(v, TERM(i), strlen(TERM(i)))

        COLOR(92);

        vvP(v, '\'');

        if (s != NULL) for (char const *c = s; c < s + n; ++c) switch (*c) {
        case '\t':
                COLOR(95);
                vvP(v, '\\');
                vvP(v, 't');
                COLOR(92);
                break;
        case '\r':
                COLOR(95);
                vvP(v, '\\');
                vvP(v, 'r');
                COLOR(92);
                break;
        case '\n':
                COLOR(95);
                vvP(v, '\\');
                vvP(v, 'n');
                COLOR(92);
                break;
        case '\\':
                COLOR(95);
                vvP(v, '\\');
                vvP(v, '\\');
                COLOR(92);
                break;
        case '\'':
                COLOR(95);
                vvP(v, '\\');
                vvP(v, '\'');
                COLOR(92);
                break;
        case '\0':
                COLOR(91);
                vvP(v, '\\');
                vvP(v, '0');
                COLOR(92);
                break;
        default:
                vvP(v, *c);
        }

        vvP(v, '\'');

        COLOR(0);

#undef COLOR

        vvP(v, '\0');

        return v.items;
}

static noreturn void
uninit(Ty *ty, Symbol const *s)
{
        zP(
                "use of uninitialized variable %s%s%s%s (defined at %s%s%s:%s%d%s:%s%d%s)",
                TERM(1),
                TERM(93),
                s->identifier,
                TERM(0),
                TERM(34),
                s->mod->path,
                TERM(0),
                TERM(33),
                s->loc.line + 1,
                TERM(0),
                TERM(33),
                s->loc.col + 1,
                TERM(0)
        );
}

static char *
value_showx(Ty *ty, Value const *v)
{
        static _Thread_local vec(void const *) visiting;

        char buffer[1024];
        char *s = NULL;

        Value val = *v;

        switch (v->type & ~VALUE_TAGGED) {
        case VALUE_INTEGER:
                snprintf(buffer, 1024, "%"PRIiMAX, v->integer);
                break;
        case VALUE_REAL:
                snprintf(buffer, 1024, "%g", v->real);
                break;
        case VALUE_STRING:
                s = show_string(ty, v->str, v->bytes, false);
                break;
        case VALUE_BOOLEAN:
                snprintf(buffer, 1024, "%s", v->boolean ? "true" : "false");
                break;
        case VALUE_NIL:
                snprintf(buffer, 1024, "%s", "nil");
                break;
        case VALUE_TYPE:
                return sclone(ty, type_show(ty, v->ptr));
        case VALUE_NAMESPACE:
                snprintf(
                        buffer,
                        sizeof buffer,
                        "<namespace '%s'>",
                        v->namespace->name
                );
                break;
        case VALUE_ARRAY:
                s = show_array(ty, v, false);
                break;
        case VALUE_TUPLE:
                s = show_tuple(ty, v, false);
                break;
        case VALUE_REGEX:
                snprintf(buffer, 1024, "/%s/", v->regex->pattern);
                break;
        case VALUE_DICT:
                s = show_dict(ty, v, false);
                break;
        case VALUE_FUNCTION:
                if (class_of(v) == -1) {
                        snprintf(buffer, 1024, "<function '%s' at %p>", name_of(v), (void *)((char *)v->info + v->info[0]));
                } else {
                        char const *class = class_name(ty, v->info[6]);
                        snprintf(buffer, 1024, "<function '%s.%s' at %p>", class, name_of(v), (void *)((char *)v->info + v->info[0]));
                }
                break;
        case VALUE_METHOD:
                if (v->this == NULL)
                        snprintf(buffer, 1024, "<method '%s' at %p>", M_NAME(v->name), (void *)v->method);
                else
                        snprintf(buffer, 1024, "<method '%s' at %p bound to %s>", M_NAME(v->name), (void *)v->method, value_showx(ty, v->this));
                break;
        case VALUE_BUILTIN_METHOD:
                snprintf(buffer, 1024, "<bound builtin method '%s'>", M_NAME(v->name));
                break;
        case VALUE_BUILTIN_FUNCTION:
                if (v->name == -1)
                        snprintf(buffer, 1024, "<builtin function>");
                else if (v->module == NULL)
                        snprintf(buffer, 1024, "<builtin function '%s'>", M_NAME(v->name));
                else
                        snprintf(buffer, 1024, "<builtin function '%s::%s'>", v->module, M_NAME(v->name));
                break;
        case VALUE_OPERATOR:
                snprintf(buffer, 1024, "<operator %s>", M_NAME(v->uop));
                break;
        case VALUE_CLASS:
                snprintf(buffer, 1024, "<class %s>", class_name(ty, v->class));
                break;
        case VALUE_TAG:
                snprintf(buffer, 1024, "%s", tags_name(ty, v->tag));
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
                return sclone(ty, "<sentinel>");
        case VALUE_REF:
                snprintf(buffer, 1024, "<reference to %p>", v->ptr);
                break;
        case VALUE_NONE:
                return sclone(ty, "<none>");
        case VALUE_INDEX:
                snprintf(buffer, 1024, "<index: (%d, %d, %d)>", (int)v->i, (int)v->off, (int)v->nt);
                break;
        case VALUE_OBJECT:;
                for (int i = 0; i < vN(visiting); ++i) {
                        if (*v_(visiting, i) == v->object) {
                                goto BasicObject;
                        }
                }

                xvP(visiting, v->object);
#ifdef TY_NO_LOG
                Value *fp = class_method(ty, v->class, "__str__");
#else
                Value *fp = NULL;
#endif
                if (fp != NULL && fp != class_method(ty, CLASS_OBJECT, "__str__")) {
                        Value str = vm_eval_function(ty, fp, v, NULL);
                        if (str.type != VALUE_STRING) {
                                zP("%s.__str__() returned non-string", class_name(ty, v->class));
                        }
                        s = gc_resize_unchecked(ty, NULL, str.bytes + 1);
                        memcpy(s, str.str, str.bytes);
                        s[str.bytes] = '\0';
                } else {
BasicObject:
                        snprintf(buffer, 1024, "<%s object at %p>", class_name(ty, v->class), (void *)v->object);
                }
                
                vvX(visiting);

                break;
        case VALUE_UNINITIALIZED:
                uninit(ty, v->sym);
        default:
                return sclone(ty, "< !!! >");
        }

        char *result = tags_wrap(
                ty,
                (s == NULL) ? buffer : s,
                (val.type & VALUE_TAGGED) ? val.tags : 0,
                false
        );

        mF(s);

        return result;
}

static char *
value_show_colorx(Ty *ty, Value const *v)
{
        static _Thread_local vec(void const *) visiting;

        char buffer[4096];
        char *s = NULL;

        Value val = *v;

        switch (v->type & ~VALUE_TAGGED) {
        case VALUE_INTEGER:
                snprintf(buffer, sizeof buffer, "%s%"PRIiMAX"%s", TERM(93), v->integer, TERM(0));
                break;
        case VALUE_REAL:
                snprintf(buffer, sizeof buffer, "%s%g%s", TERM(93), v->real, TERM(0));
                break;
        case VALUE_STRING:
                s = show_string(ty, v->str, v->bytes, true);
                break;
        case VALUE_BOOLEAN:
                snprintf(buffer, sizeof buffer, "%s%s%s", TERM(36), v->boolean ? "true" : "false", TERM(0));
                break;
        case VALUE_NIL:
                snprintf(buffer, sizeof buffer, "%snil%s", TERM(95), TERM(0));
                break;
        case VALUE_NAMESPACE:
                snprintf(
                        buffer,
                        sizeof buffer,
                        "%s<namespace %s'%s'%s>%s",
                        TERM(93),
                        TERM(95),
                        v->namespace->name,
                        TERM(93),
                        TERM(0)
                );
                break;
        case VALUE_ARRAY:
                s = show_array(ty, v, true);
                break;
        case VALUE_TUPLE:
                s = show_tuple(ty, v, true);
                break;
        case VALUE_REGEX:
                snprintf(buffer, sizeof buffer, "%s/%s/%s", TERM(96), v->regex->pattern, TERM(0));
                break;
        case VALUE_DICT:
                s = show_dict(ty, v, true);
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
                        char const *class = class_name(ty, v->info[6]);
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
                                M_NAME(v->name),
                                TERM(96),
                                TERM(94),
                                (void *)v->method,
                                TERM(96),
                                TERM(0)
                        );
                } else {
                        char *vs = value_show_colorx(ty, v->this);
                        snprintf(
                                buffer,
                                sizeof buffer,
                                "%s<method %s'%s'%s at %s%p%s bound to %s%s%s>%s",
                                TERM(96),
                                TERM(92),
                                M_NAME(v->name),
                                TERM(96),
                                TERM(94),
                                (void *)v->method,
                                TERM(96),
                                TERM(0),
                                vs,
                                TERM(96),
                                TERM(0)
                        );
                        mF(vs);
                }
                break;
        case VALUE_BUILTIN_METHOD:
                snprintf(
                        buffer,
                        sizeof buffer,
                        "%s<bound builtin method %s'%s'%s>%s",
                        TERM(96),
                        TERM(92),
                        M_NAME(v->name),
                        TERM(96),
                        TERM(0)
                );
                break;
        case VALUE_BUILTIN_FUNCTION:
                if (v->name == -1)
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
                                M_NAME(v->name),
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
                                M_NAME(v->name),
                                TERM(96),
                                TERM(0)
                        );
                break;
        case VALUE_OPERATOR:
                snprintf(
                        buffer,
                        sizeof buffer,
                        "%s<%soperator %s%s%s>%s",
                        TERM(96),
                        TERM(92),
                        TERM(94),
                        M_NAME(v->uop),
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
                        class_name(ty, v->class),
                        TERM(96),
                        TERM(0)
                );
                break;
        case VALUE_TAG:
                snprintf(buffer, sizeof buffer, "%s%s%s", TERM(34), tags_name(ty, v->tag), TERM(0));
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
                return sclone(ty, "<sentinel>");
        case VALUE_REF:
                snprintf(buffer, sizeof buffer, "<reference to %p>", v->ptr);
                break;
        case VALUE_NONE:
                return sclone(ty, "<none>");
        case VALUE_INDEX:
                snprintf(buffer, sizeof buffer, "<index: (%d, %d, %d)>", (int)v->i, (int)v->off, (int)v->nt);
                break;
        case VALUE_OBJECT:;
                for (int i = 0; i < vN(visiting); ++i) {
                        if (*v_(visiting, i) == v->object) {
                                goto BasicObject;
                        }
                }

                xvP(visiting, v->object);

#ifdef TY_NO_LOG
                Value *fp = class_method(ty, v->class, "__str__");
#else
                Value *fp = NULL;
#endif

                if (fp != NULL && fp != class_method(ty, CLASS_OBJECT, "__str__")) {
                        Value str = vm_eval_function(ty, fp, v, NULL);
                        gP(&str);
                        if (str.type != VALUE_STRING)
                                zP("%s.__str__() returned non-string", class_name(ty, v->class));
                        s = mA(str.bytes + 1);
                        gX();
                        memcpy(s, str.str, str.bytes);
                        s[str.bytes] = '\0';
                } else {
BasicObject:
                        snprintf(
                                buffer,
                                sizeof buffer,
                                "%s<%s%s%s object at %s%p%s>%s",
                                TERM(96),
                                TERM(34),
                                class_name(ty, v->class),
                                TERM(96),
                                TERM(94),
                                (void *)v->object,
                                TERM(96),
                                TERM(0)
                        );
                }

                vvX(visiting);

                break;
        case VALUE_UNINITIALIZED:
                uninit(ty, v->sym);
        default:
                return value_showx(ty, v);
        }

        char *result = tags_wrap(
                ty,
                (s == NULL) ? buffer : s,
                (val.type & VALUE_TAGGED) ? val.tags : 0,
                true
        );

        mF(s);

        return result;
}

char *
value_show_color(Ty *ty, Value const *v)
{
        char *str = value_show_colorx(ty, v);
        return str;
}

char *
value_show(Ty *ty, Value const *v)
{
        char *str = value_showx(ty, v);
        return str;
}

inline static int
check_cmp_result(Ty *ty, Value const *v1, Value const *v2, Value v)
{
        if (v.type == VALUE_NONE) {
                zP(
                        "attempt to compare incomparable values\n"
                        FMT_MORE " %sleft%s: %s"
                        FMT_MORE "%sright%s: %s\n",
                        TERM(95), TERM(0),
                        value_show_color(ty, v1),
                        TERM(95), TERM(0),
                        value_show_color(ty, v2)
                );
        }

        if (v.type != VALUE_INTEGER) {
                zP(
                        "non-integer returned by user-defined <=> operator\n"
                        FMT_MORE "  %sleft%s: %s"
                        FMT_MORE " %sright%s: %s"
                        FMT_MORE "%sresult%s: %s\n",
                        TERM(95), TERM(0),
                        value_show_color(ty, v1),
                        TERM(95), TERM(0),
                        value_show_color(ty, v2),
                        TERM(95), TERM(0),
                        value_show_color(ty, &v)
                );
        }

        return v.integer;
}

int
value_compare(Ty *ty, Value const *v1, Value const *v2)
{
        int c;

        switch (PACK_TYPES(v1->type & ~VALUE_TAGGED, v2->type & ~VALUE_TAGGED)) {
        case PAIR_OF(VALUE_INTEGER):
                return (v1->integer < v2->integer) ? -1 : (v1->integer != v2->integer);

        case PAIR_OF(VALUE_REAL):
                return (v1->real < v2->real) ? -1 : (v1->real != v2->real);

        case PACK_TYPES(VALUE_REAL, VALUE_INTEGER):
                return (v1->real < v2->integer) ? -1 : (v1->real != v2->integer);

        case PACK_TYPES(VALUE_INTEGER, VALUE_REAL):
                return (v1->integer < v2->real) ? -1 : (v1->integer != v2->real);

        case PAIR_OF(VALUE_STRING):
                c = memcmp(v1->str, v2->str, min(v1->bytes, v2->bytes));
                return (c != 0) ? c : ((int)v1->bytes - (int)v2->bytes);

        case PAIR_OF(VALUE_PTR):
                return ((uintptr_t)v1->ptr < (uintptr_t)v2->ptr)
                     ? -1
                     :  ((uintptr_t)v1->ptr != (uintptr_t)v2->ptr)
                     ;

        case PAIR_OF(VALUE_ARRAY):
                for (int i = 0; i < v1->array->count && i < v2->array->count; ++i) {
                        int o = value_compare(ty, &v1->array->items[i], &v2->array->items[i]);
                        if (o != 0)
                                return o;
                }
                return ((ptrdiff_t)v1->array->count) - ((ptrdiff_t)v2->array->count);

        case PAIR_OF(VALUE_TUPLE):
                for (int i = 0; i < v1->count && i < v2->count; ++i) {
                        int o = value_compare(ty, &v1->items[i], &v2->items[i]);
                        if (o != 0)
                                return o;
                }
                return ((int)v1->count) - ((int)v2->count);
        }

        return check_cmp_result(ty, v1, v2, vm_try_2op(ty, OP_CMP, v1, v2));
}

bool
value_truthy(Ty *ty, Value const *v)
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
value_apply_predicate(Ty *ty, Value *p, Value *v)
{
        Value b;
        char err[256];

        switch (p->type) {
        case VALUE_FUNCTION:
        case VALUE_BUILTIN_FUNCTION:
        case VALUE_METHOD:
        case VALUE_BUILTIN_METHOD:
        case VALUE_OPERATOR:
                vmP(v);
                b = vmC(p, 1);
                return value_truthy(ty, &b);
        case VALUE_REGEX:
                if (v->type != VALUE_STRING) {
                        zP("regex applied as predicate to non-string");
                } else {
                        int rc = pcre2_match(
                                p->regex->pcre2,
                                (PCRE2_SPTR)v->str,
                                v->bytes,
                                0,
                                0,
                                ty->pcre2.match,
                                ty->pcre2.ctx
                        );

                        if (rc >= 0) {
                                return true;
                        }

                        if (rc == PCRE2_ERROR_NOMATCH) {
                                return false;
                        }

                        pcre2_get_error_message(rc, (uint8_t *)err, sizeof err);
                        zP("apply_predicate(): PCRE2 error: %s", err);
                }
        case VALUE_TAG:
                return tags_first(ty, v->tags) == p->tag;
        case VALUE_CLASS:
                return (v->type == VALUE_OBJECT) && (v->class == p->class);
        default:
                zP("invalid type of value used as a predicate: %s", value_showx(ty, v));
        }
}

Value
value_apply_callable(Ty *ty, Value *f, Value *v)
{
        switch (f->type) {
        case VALUE_FUNCTION:
        case VALUE_BUILTIN_FUNCTION:
        case VALUE_METHOD:
        case VALUE_BUILTIN_METHOD:
        case VALUE_OPERATOR:
        case VALUE_CLASS:
        case VALUE_TAG:
        case VALUE_DICT:
        case VALUE_ARRAY:
                vmP(v);
                return vmC(f, 1);
        case VALUE_REGEX:
                if (v->type != VALUE_STRING)
                        zP("regex applied as predicate to non-string");

                size_t *ovec = pcre2_get_ovector_pointer(ty->pcre2.match);

                int rc = pcre2_match(
                        f->regex->pcre2,
                        (PCRE2_SPTR)v->str,
                        v->bytes,
                        0,
                        0,
                        ty->pcre2.match,
                        ty->pcre2.ctx
                );

                if (rc < -2)
                        zP("error while executing regular expression: %d", rc);

                if (rc <= 0)
                        return NIL;

                Value match;

                if (rc == 1) {
                        match = STRING_VIEW(*v, ovec[0], ovec[1] - ovec[0]);
                } else {
                        match = ARRAY(vA());
                        NOGC(match.array);
                        value_array_reserve(ty, match.array, rc);

                        int j = 0;
                        for (int i = 0; i < rc; ++i, j += 2) {
                                vAp(
                                        match.array,
                                        STRING_VIEW(
                                                *v,
                                                ovec[j],
                                                ovec[j + 1] - ovec[j]
                                        )
                                );
                        }

                        OKGC(match.array);
                }

                return match;
        default:
                zP("invalid type of value used as a callable: %s", value_showx(ty, f));
        }
}

bool
value_test_equality(Ty *ty, Value const *v1, Value const *v2)
{
        if (v1->tags != v2->tags)
                return false;

        int t0 = v1->type & ~VALUE_TAGGED;
        int t1 = v2->type & ~VALUE_TAGGED;

        switch (PACK_TYPES(t0, t1)) {
        case PAIR_OF(VALUE_INTEGER):
                return v1->integer == v2->integer;

        case PAIR_OF(VALUE_STRING):
                return v1->bytes == v2->bytes
                    && memcmp(v1->str, v2->str, v1->bytes) == 0;

        case PAIR_OF(VALUE_BOOLEAN):
                return v1->boolean == v2->boolean;

        case PAIR_OF(VALUE_ARRAY):
                return arrays_equal(ty, v1, v2);

        case PAIR_OF(VALUE_TUPLE):
                return tuples_equal(ty, v1, v2);

        case PAIR_OF(VALUE_DICT):
                return v1->dict == v2->dict;

        case PAIR_OF(VALUE_CLASS):
                return v1->class == v2->class;

        case PAIR_OF(VALUE_TAG):
                return v1->tag == v2->tag;

        case PAIR_OF(VALUE_PTR):
                return v1->ptr == v2->ptr;

        case PAIR_OF(VALUE_BLOB):
                return v1->blob == v2->blob;

        case PAIR_OF(VALUE_FUNCTION):
                return v1->info == v2->info;

        case PAIR_OF(VALUE_BUILTIN_FUNCTION):
                return v1->builtin_function == v2->builtin_function;

        case PAIR_OF(VALUE_BUILTIN_METHOD):
                return v1->builtin_method == v2->builtin_method
                    && memcmp(v1->this, v2->this, sizeof (Value)) == 0;

        case PAIR_OF(VALUE_REGEX):
                return v1->regex == v2->regex;

        case PAIR_OF(VALUE_REAL):
                return v1->real == v2->real;

        case PAIR_OF(VALUE_NIL):
                return true;
        }

        if ((t0 | t1) & VALUE_NIL) {
                return false;
        }

        Value v = vm_try_2op(ty, OP_EQL, v1, v2);

        if (v.type != VALUE_NONE) {
                return value_truthy(ty, &v);
        }

        v = vm_try_2op(ty, OP_CMP, v1, v1);

        if (v.type == VALUE_NONE) {
                return false;
        }

        return check_cmp_result(ty, v1, v2, v) == 0;
}

inline static void
value_array_mark(Ty *ty, struct array *a)
{
        if (MARKED(a)) return;

        MARK(a);

        for (int i = 0; i < a->count; ++i) {
                value_mark(ty, &a->items[i]);
        }
}

inline static void
mark_tuple(Ty *ty, Value const *v)
{
        if (v->items == NULL || MARKED(v->items)) return;

        MARK(v->items);

        for (int i = 0; i < v->count; ++i) {
                value_mark(ty, &v->items[i]);
        }

        if (v->ids != NULL) {
                MARK(v->ids);
        }
}

inline static void
mark_thread(Ty *ty, Value const *v)
{
        if (MARKED(v->thread)) return;
        MARK(v->thread);
        value_mark(ty, &v->thread->v);
}

inline static void
mark_generator(Ty *ty, Value const *v)
{
        if (MARKED(v->gen)) return;

        MARK(v->gen);

        value_mark(ty, &v->gen->f);

        for (int i = 0; i < vN(v->gen->frame); ++i) {
                value_mark(ty, v_(v->gen->frame, i));
        }

        for (int i = 0; i < v->gen->st.targets.count; ++i) {
                if ((((uintptr_t)v_(v->gen->st.targets, i)->t) & 0x07) == 0) {
                        value_mark(ty, v_(v->gen->st.targets, i)->t);
                }
        }

        for (int i = 0; i < vN(v->gen->st.to_drop); ++i) {
                value_mark(ty, v_(v->gen->st.to_drop, i));
        }

        for (int i = 0; i < vN(v->gen->gc_roots); ++i) {
                value_mark(ty, v_(v->gen->gc_roots, i));
        }
}

inline static void
mark_function(Ty *ty, Value const *v)
{
        int n = v->info[FUN_INFO_CAPTURES];

        if (*from_eval(v))
                MARK(v->info);

        if (v->xinfo != NULL)
                MARK(v->xinfo);

        if (n == 0 || MARKED(v->env))
                return;

        MARK(v->env);

        for (size_t i = 0; i < n; ++i) {
                if (v->env[i] == NULL)
                        continue;
                MARK(v->env[i]);
                value_mark(ty, v->env[i]);
        }
}

inline static void
mark_pointer(Ty *ty, Value const *v)
{
        if (v->gcptr != NULL) {
                MARK(v->gcptr);
                switch (ALLOC_OF(v->gcptr)->type) {
                case GC_VALUE:
                        value_mark(ty, (const Value *)v->gcptr);
                        break;

                case GC_FFI_AUTO:
                        value_mark(ty, ((const Value *)v->gcptr));
                        break;
                }
        }
}

void
_value_mark(Ty *ty, Value const *v)
{
        void **src = source_lookup(ty, v->src);
        if (src != NULL && *src != NULL) {
                MARK(*src);
        }

#ifndef TY_RELEASE
        static _Thread_local int d;

        GC_STOP();
        //GCLOG("Marking: %s", value_show(ty, v));
        GC_RESUME();

        ++d;
#endif

        switch (v->type & ~VALUE_TAGGED) {
        case VALUE_METHOD:          if (!MARKED(v->this)) { MARK(v->this); value_mark(ty, v->this); } break;
        case VALUE_BUILTIN_METHOD:  if (!MARKED(v->this)) { MARK(v->this); value_mark(ty, v->this); } break;
        case VALUE_ARRAY:           value_array_mark(ty, v->array);                                   break;
        case VALUE_TUPLE:           mark_tuple(ty, v);                                                break;
        case VALUE_DICT:            dict_mark(ty, v->dict);                                           break;
        case VALUE_FUNCTION:        mark_function(ty, v);                                             break;
        case VALUE_GENERATOR:       mark_generator(ty, v);                                            break;
        case VALUE_THREAD:          mark_thread(ty, v);                                               break;
        case VALUE_STRING:          if (v->gcstr != NULL) MARK(v->gcstr);                             break;
        case VALUE_OBJECT:          object_mark(ty, v->object);                                       break;
        case VALUE_REF:             MARK(v->ptr); value_mark(ty, v->ptr);                             break;
        case VALUE_BLOB:            MARK(v->blob);                                                    break;
        case VALUE_PTR:             mark_pointer(ty, v);                                              break;
        case VALUE_REGEX:           if (v->regex->gc) MARK(v->regex);                                 break;
        default:                                                                                      break;
        }

#ifndef TY_RELEASE
        --d;
#endif
}

Blob *
value_blob_new(Ty *ty)
{
        Blob *blob = mAo(sizeof *blob, GC_BLOB);
        vec_init(*blob);
        return blob;
}

Value
value_tuple(Ty *ty, int n)
{
        Value *items = mAo(n * sizeof (Value), GC_TUPLE);

        for (int i = 0; i < n; ++i) {
                items[i] = NIL;
        }

        return TUPLE(items, NULL, n, false);
}

Value
value_record(Ty *ty, int n)
{
        Value *items = mAo(n * sizeof (Value), GC_TUPLE);

        NOGC(items);
        int *ids = mAo(n * sizeof (int), GC_TUPLE);
        OKGC(items);

        for (int i = 0; i < n; ++i) {
                items[i] = NIL;
                ids[i] = -1;
        }

        return TUPLE(items, ids, n, false);
}

Value
value_named_tuple(Ty *ty, char const *first, ...)
{
        va_list ap;
        va_start(ap, first);

        int n = 0;

        do {
                va_arg(ap, Value);
                n += 1;
        } while (va_arg(ap, char const *) != NULL);

        va_end(ap);

        Value *items = mAo(n * sizeof (Value), GC_TUPLE);

        NOGC(items);
        int *ids = mAo(n * sizeof (int), GC_TUPLE);
        OKGC(items);

        va_start(ap, first);

        ids[0] = (first[0] == '\0') ? -1 : M_ID(first);
        items[0] = va_arg(ap, Value);

        for (int i = 1; i < n; ++i) {
                char const *name = va_arg(ap, char *);
                items[i] = va_arg(ap, Value);
                ids[i] = (name[0] == '\0') ? -1 : M_ID(name);
        }

        va_end(ap);

        return TUPLE(items, ids, n, false);
}

Value *
tuple_get_i(Value const *tuple, int id)
{
        if (tuple->ids == NULL) {
                return NULL;
        }

        for (int i = 0; i < tuple->count; ++i) {
                if (tuple->ids[i] == id) {
                        return &tuple->items[i];
                }
        }

        return NULL;
}

Value *
tuple_get(Value const *tuple, char const *name)
{
        return tuple_get_i(tuple, M_ID(name));
}

void
value_array_extend(Ty *ty, Array *a, Array const *other)
{
        isize n = vN(*a) + vN(*other);

        if (n != 0) {
                vvR(*a, n);
        }

        if (other->count != 0) {
                memcpy(a->items + a->count, other->items, other->count * sizeof (Value));
        }

        a->count = n;
}

int
tuple_get_completions(Ty *ty, Value const *v, char const *prefix, char **out, int max)
{
        int n = 0;
        int prefix_len = strlen(prefix);

        if (v->ids == NULL) return 0;

        for (int i = 0; i < v->count && n < max; ++i) {
                if (v->ids[i] == -1) continue;
                char const *name = M_NAME(v->ids[i]);
                if (strncmp(name, prefix, prefix_len) == 0) {
                        out[n++] = sclone_malloc(name);
                }
        }

        return n;
}

/* vim: set sts=8 sw=8 expandtab: */
