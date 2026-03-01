#include <ctype.h>
#include <string.h>
#include <stdlib.h>
#include <assert.h>
#include <stdbool.h>
#include <inttypes.h>

#include <pcre2.h>
#include <xxhash.h>

#include "ty.h"
#include "dtoa.h"
#include "value.h"
#include "xd.h"
#include "dict.h"
#include "blob.h"
#include "tags.h"
#include "class.h"
#include "gc.h"
#include "vm.h"
#include "ast.h"
#include "compiler.h"
#include "types.h"

static _Thread_local vec(Dict *) show_dicts;
static _Thread_local vec(Value *) show_tuples;
static _Thread_local vec(Array *) show_arrays;

void
TyValueCleanup(void)
{
        xvF(show_dicts);
        xvF(show_tuples);
        xvF(show_arrays);
}

inline static void
MarkNext(Ty *ty, Value *v)
{
        xvP(ty->marking, v);
}

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

typedef struct {
        i32 id;
        Value val;
} RecordItem;

typedef vec(RecordItem) RecordItems;

static int
itemcmp(const void *a, const void *b)
{
        RecordItem const *x = a;
        RecordItem const *y = b;

        return (x->id < y->id) ? -1
             : (x->id > y->id) ?  1
             :                    0
             ;
}

static bool
records_equal(Ty *ty, Value const *v1, Value const *v2)
{
        RecordItems xs_named = {0};
        RecordItems ys_named = {0};

        ValueVector xs_unnamed = {0};
        ValueVector ys_unnamed = {0};

        SCRATCH_SAVE();

        for (usize i = 0; i < v1->count; ++i) {
                if (LIKELY(v1->ids[i] != -1)) {
                        svP(xs_named, ((RecordItem) {
                                .id  = v1->ids[i],
                                .val = v1->items[i]
                        }));
                } else {
                        svP(xs_unnamed, v1->items[i]);
                }
        }

        for (usize i = 0; i < v2->count; ++i) {
                if (LIKELY(v2->ids[i] != -1)) {
                        svP(ys_named, ((RecordItem) {
                                .id  = v2->ids[i],
                                .val = v2->items[i]
                        }));
                } else {
                        svP(ys_unnamed, v2->items[i]);
                }
        }

        if (
                (vN(xs_named) != vN(ys_named))
             || (vN(xs_unnamed) != vN(ys_unnamed))
        ) {
                SCRATCH_RESTORE();
                return false;
        }

        qsort(vv(xs_named), vN(xs_named), sizeof (RecordItem), itemcmp);
        qsort(vv(ys_named), vN(ys_named), sizeof (RecordItem), itemcmp);

        for (usize i = 0; i < vN(xs_named); ++i) {
                if (v_(xs_named, i)->id != v_(ys_named, i)->id) {
                        SCRATCH_RESTORE();
                        return false;
                }
                if (!v_eq(&v_(xs_named, i)->val, &v_(ys_named, i)->val)) {
                        SCRATCH_RESTORE();
                        return false;
                }
        }

        for (usize i = 0; i < vN(xs_unnamed); ++i) {
                if (!v_eq(v_(xs_unnamed, i), v_(ys_unnamed, i))) {
                        SCRATCH_RESTORE();
                        return false;
                }
        }

        SCRATCH_RESTORE();

        return true;
}

static int
compare_records(Ty *ty, Value const *v1, Value const *v2)
{
        RecordItems xs = {0};
        RecordItems ys = {0};

        SCRATCH_SAVE();

        for (usize i = 0; i < v1->count; ++i) {
                if (LIKELY(v1->ids[i] != -1)) {
                        svP(xs, ((RecordItem) {
                                .id  = v1->ids[i],
                                .val = v1->items[i]
                        }));
                } else {
                        svP(xs, ((RecordItem) {
                                .id  = -1,
                                .val = v1->items[i]
                        }));
                }
        }

        for (usize i = 0; i < v2->count; ++i) {
                if (LIKELY(v2->ids[i] != -1)) {
                        svP(ys, ((RecordItem) {
                                .id  = v2->ids[i],
                                .val = v2->items[i]
                        }));
                } else {
                        svP(ys, ((RecordItem) {
                                .id  = -1,
                                .val = v2->items[i]
                        }));
                }
        }

        qsort(vv(xs), vN(xs), sizeof (RecordItem), itemcmp);
        qsort(vv(ys), vN(ys), sizeof (RecordItem), itemcmp);

        for (usize i = 0; i < vN(xs); ++i) {
                if (v_(xs, i)->id != v_(ys, i)->id) {
                        SCRATCH_RESTORE();
                        return (v_(xs, i)->id < v_(ys, i)->id) ? -1 : 1;
                }
                int cmp = value_compare(ty, &v_(xs, i)->val, &v_(ys, i)->val);
                if (cmp != 0) {
                        SCRATCH_RESTORE();
                        return cmp;
                }
        }

        SCRATCH_RESTORE();

        return 0;
}

static bool
tuples_equal(Ty *ty, Value const *v1, Value const *v2)
{
        if (v1->items == v2->items)
                return true;

        if (v1->count != v2->count)
                return false;

        if (v1->ids != NULL && v2->ids != NULL) {
                return records_equal(ty, v1, v2);
        }

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

inline static u64
str_hash(char const *str, u32 len)
{
        return XXH3_64bits(str, len);
}

inline static u64
hash64(u64 x)
{
        x ^= x >> 30;
        x *= 0xBF58476D1CE4E5B9ULL;
        x ^= x >> 27;
        x *= 0x94D049BB133111EBULL;
        x ^= x >> 31;
        return x;
}

inline static u64
ptr_hash(void const *p)
{
        return hash64((u64)(uptr)p);
}

inline static u64
flt_hash(double _x)
{
        u64 x;
        memcpy(&x, &_x, sizeof x);
        return hash64(x);
}

inline static u64
ary_hash(Ty *ty, Value const *a)
{
        u64 hash = 7234782527432842341ULL;

        for (usize i = 0; i < vN(*a->array); ++i) {
                u64 x = value_hash(ty, &a->array->items[i]);
                hash = HashCombine(hash, x);
        }

        return hash;
}

inline static u64
tpl_hash(Ty *ty, Value const *t)
{
        u64 hash = 1127573292757587281ULL;

        for (int i = 0; i < t->count; ++i) {
                u64 x = value_hash(ty, &t->items[i]);
                hash = HashCombine(hash, x);
                if (t->ids != NULL && t->ids[i] != -1) {
                        hash *= (t->ids[i] + 1);
                }
        }

        return hash;
}

inline static u64
obj_hash(Ty *ty, Value const *v)
{
        Value const *f = class_lookup_method_i(ty, v->class, NAMES._hash_);

        if (f != NULL) {
                Value hash = vm_call_method(ty, v, f, 0);
                if (hash.type != VALUE_INTEGER) {
                        zP(
                                "%s.__hash__() returned non-integer: %s",
                                class_name(ty, v->class),
                                VSC(v)
                        );
                }
                return (u64)hash.z;
        } else {
                return ptr_hash(v->object);
        }
}

static u64
hash(Ty *ty, Value const *val)
{
        switch (val->type & ~VALUE_TAGGED) {
        case VALUE_NIL:               return 0xDEADDEADDEADULL;
        case VALUE_BOOLEAN:           return val->boolean ? 0xABCULL : 0xDEFULL;
        case VALUE_STRING:            return XXH3_64bits(ss(*val), sN(*val));
        case VALUE_INTEGER:           return hash64(val->z);
        case VALUE_REAL:              return flt_hash(val->real);
        case VALUE_ARRAY:             return ary_hash(ty, val);
        case VALUE_TUPLE:             return tpl_hash(ty, val);
        case VALUE_DICT:              return ptr_hash(val->dict);
        case VALUE_OBJECT:            return obj_hash(ty, val);
        case VALUE_METHOD:            return HashCombine(ptr_hash(val->method), ptr_hash(val->this));
        case VALUE_BUILTIN_METHOD:    return HashCombine(ptr_hash(val->builtin_method), ptr_hash(val->this));
        case VALUE_BUILTIN_FUNCTION:  return ptr_hash(val->builtin_function);
        case VALUE_BOUND_FUNCTION:
        case VALUE_FUNCTION:          return HashCombine(ptr_hash(val->info), ptr_hash(val->env));
        case VALUE_FOREIGN_FUNCTION:  return HashCombine(ptr_hash((void *)val->ff), ptr_hash(val->ffi));
        case VALUE_REGEX:             return ptr_hash(val->regex);
        case VALUE_PTR:               return ptr_hash(val->ptr);
        case VALUE_TAG:               return (((u64)val->tag) * 517929173925273293ULL);
        case VALUE_CLASS:             return (((u64)val->class) * 817364735284283413ULL);
        default:                      zP("attempt to hash invalid value: %s", VSC(val));
        }
}

u64
value_hash(Ty *ty, Value const *val)
{
        return ((u64)val->tags) ^ hash(ty, val);
}

static char *
show_string(Ty *ty, u8 const *s, size_t n, bool use_color)
{
        byte_vector v = {0};
        i32 color = 0;

#define COLOR(i) do {                               \
        if (use_color && color != i) {              \
                svPn(v, TERM(i), strlen(TERM(i)));  \
                color = i;                          \
        }                                           \
} while (0)

        COLOR(92);

        svP(v, '\'');

        if (s != NULL) for (u8 const *c = s; c < s + n; ++c) switch (*c) {
        case '\t':
                COLOR(95);
                svP(v, '\\');
                svP(v, 't');
                break;

        case '\r':
                COLOR(95);
                svP(v, '\\');
                svP(v, 'r');
                break;

        case '\n':
                COLOR(95);
                svP(v, '\\');
                svP(v, 'n');
                break;

        case '\\':
                COLOR(95);
                svP(v, '\\');
                svP(v, '\\');
                break;

        case '\'':
                COLOR(95);
                svP(v, '\\');
                svP(v, '\'');
                break;

        case '\0':
                COLOR(91);
                svP(v, '\\');
                svP(v, '0');
                break;

        default:
                if (iscntrl(*c)) {
                        COLOR(93);
                        sxdf(&v, "\\x%02x", (u32)*c);

                } else {
                        COLOR(92);
                        svP(v, *c);
                }
                break;
        }

        COLOR(92);
        svP(v, '\'');

        COLOR(0);

#undef COLOR

        svP(v, '\0');

        return vv(v);
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

enum {
        SW_LIT     = 0x40,
        SW_POP_ARY,
        SW_POP_TPL,
        SW_POP_DCT,
        SW_POP_VIS,
};

#define WLIT(s) svP(work, ((Value) {   \
        .type = SW_LIT,                \
        .ptr  = (void *)(s)            \
}))

#define WPOP(op) svP(work, ((Value) {  \
        .type = (op)                   \
}))

static char *
show_impl(
        Ty *ty,
        Value const *root,
        u32 flags
)
{
        bool color = !(flags & TY_SHOW_NOCOLOR);

        byte_vector buf  = {0};
        ValueVector work = {0};

        svP(work, *root);

        while (vN(work) > 0) {
                Value v = vXx(work);

                switch (v.type) {
                case SW_LIT:
                {
                        char const *s = v.ptr;
                        svPn(buf, s, strlen(s));
                        continue;
                }
                case SW_POP_ARY: { vvX(show_arrays);   continue; }
                case SW_POP_TPL: { vvX(show_tuples);   continue; }
                case SW_POP_DCT: { vvX(show_dicts);    continue; }
                case SW_POP_VIS: { vvX(ty->visiting);  continue; }
                }

                if (
                        (v.type & VALUE_TAGGED)
                     && (v.type & ~VALUE_TAGGED) != VALUE_TUPLE
                ) {
                        WLIT(tags_close(ty, v.tags, color));
                        svP(work, stripped(&v));
                        WLIT(tags_open(ty, v.tags, color));
                        continue;
                }

                switch (v.type & ~VALUE_TAGGED) {
                case VALUE_INTEGER:
                        if (color) {
                                sxdf(&buf, "%s%"PRIiMAX"%s", TERM(93), v.z, TERM(0));
                        } else {
                                sxdf(&buf, "%"PRIiMAX, v.z);
                        }
                        break;

                case VALUE_REAL:
                {
                        char *r = smA(512);
                        dtoa(v.real, r, 512);
                        if (color) {
                                sxdf(&buf, "%s%s%s", TERM(93), r, TERM(0));
                        } else {
                                sxdf(&buf, "%s", r);
                        }
                        break;
                }

                case VALUE_STRING:
                {
                        char *s = show_string(ty, ss(v), sN(v), color);
                        u32 len = strlen(s);
                        svPn(buf, s, len);
                        break;
                }

                case VALUE_BOOLEAN:
                {
                        char const *s = v.boolean ? "true" : "false";
                        if (color) {
                                sxdf(&buf, "%s%s%s", TERM(36), s, TERM(0));
                        } else {
                                sxdf(&buf, "%s", s);
                        }
                        break;
                }

                case VALUE_NIL:
                        if (color) {
                                sxdf(&buf, "%snil%s", TERM(95), TERM(0));
                        } else {
                                sxdf(&buf, "nil");
                        }
                        break;

                case VALUE_TYPE:
                {
                        char *s = type_show(ty, v.ptr);
                        svPn(buf, s, strlen(s));
                        break;
                }

                case VALUE_NAMESPACE:
                        if (color) {
                                sxdf(
                                        &buf,
                                        "%s<ns %s'%s'%s>%s",
                                        TERM(93),
                                        TERM(95),
                                        v.namespace->name,
                                        TERM(93),
                                        TERM(0)
                                );
                        } else {
                                sxdf(
                                        &buf,
                                        "<ns '%s'>",
                                        v.namespace->name
                                );
                        }
                        break;

                case VALUE_MODULE:
                        if (color) {
                                sxdf(
                                        &buf,
                                        "%s<module %s'%s'%s>%s",
                                        TERM(93),
                                        TERM(95),
                                        v.mod->name,
                                        TERM(93),
                                        TERM(0)
                                );
                        } else {
                                sxdf(
                                        &buf,
                                        "<module '%s'>",
                                        v.mod->name
                                );
                        }
                        break;

                case VALUE_ARRAY:
                {
                        for (int i = 0; i < vN(show_arrays); ++i) {
                                if (v__(show_arrays, i) == v.array) {
                                        sxdf(&buf, "[...]");
                                        goto Next;
                                }
                        }

                        xvP(show_arrays, v.array);

                        int n = vN(*v.array);

                        WPOP(SW_POP_ARY);
                        WLIT("]");

                        for (int i = n - 1; i >= 0; --i) {
                                svP(work, *v_(*v.array, i));
                                if (i > 0) {
                                        WLIT(", ");
                                }
                        }

                        WLIT("[");

                        break;
                }

                case VALUE_TUPLE:
                {
                        for (int i = 0; i < vN(show_tuples); ++i) {
                                if (v__(show_tuples, i) == v.items) {
                                        sxdf(&buf, "(...)");
                                        goto Next;
                                }
                        }

                        xvP(show_tuples, v.items);

                        bool tagged = (v.type & VALUE_TAGGED);

                        WPOP(SW_POP_TPL);

                        if (tagged) {
                                WLIT(tags_close(ty, v.tags, color));
                        } else {
                                WLIT(")");
                        }

                        for (int i = v.count - 1; i >= 0; --i) {
                                svP(work, v.items[i]);
                                if (v.ids != NULL && v.ids[i] != -1) {
                                        char const *name = M_NAME(v.ids[i]);
                                        if (color) {
                                                WLIT(sfmt(
                                                        "%s%s%s: ",
                                                        TERM(34),
                                                        name,
                                                        TERM(0)
                                                ));
                                        } else {
                                                WLIT(sfmt(
                                                        "%s: ",
                                                        name
                                                ));
                                        }
                                }
                                if (i > 0) {
                                        WLIT(", ");
                                }
                        }

                        if (tagged) {
                                WLIT(tags_open(ty, v.tags, color));
                        } else {
                                WLIT("(");
                        }

                        break;
                }

                case VALUE_DICT:
                {
                        for (int i = 0; i < vN(show_dicts); ++i) {
                                if (v__(show_dicts, i) == v.dict) {
                                        sxdf(&buf, "{...}");
                                        goto Next;
                                }
                        }

                        xvP(show_dicts, v.dict);

                        typedef struct { Value k, v; } KV;
                        vec(KV) items = {0};

                        dfor(v.dict, {
                                svP(items, ((KV){
                                        *key,
                                        *val
                                }));
                        });

                        int n = vN(items);

                        WPOP(SW_POP_DCT);
                        WLIT(color ? sfmt("%s}%s", TERM(94;1), TERM(0)) : "}");

                        for (int i = n - 1; i >= 0; --i) {
                                KV kv = v__(items, i);
                                if (kv.v.type != VALUE_NIL) {
                                        svP(work, kv.v);
                                        WLIT(": ");
                                }
                                svP(work, kv.k);
                                if (i > 0) {
                                        WLIT(", ");
                                }
                        }

                        WLIT(color ? sfmt("%s%%{%s", TERM(94;1), TERM(0)) : "%{");

                        break;
                }

                case VALUE_REGEX:
                {
                        long bits = 0;
                        int  nf   = 0;
                        char flags[16] = {0};

                        pcre2_pattern_info(v.regex->pcre2, PCRE2_INFO_ALLOPTIONS, &bits);

                        if (bits & PCRE2_MULTILINE) { flags[nf++] = 'm'; }
                        if (bits & PCRE2_DOTALL)    { flags[nf++] = 's'; }
                        if (bits & PCRE2_UTF)       { flags[nf++] = 'u'; }
                        if (bits & PCRE2_CASELESS)  { flags[nf++] = 'i'; }
                        if (bits & PCRE2_EXTENDED)  { flags[nf++] = 'x'; }
                        if (bits & PCRE2_ANCHORED)  { flags[nf++] = 'a'; }
                        if (bits & PCRE2_UNGREEDY)  { flags[nf++] = 'U'; }
                        if (bits & PCRE2_NEVER_UTF) { flags[nf++] = '7'; }
                        flags[nf] = '\0';

                        if (color) {
                                sxdf(
                                        &buf,
                                        "%s/%s/%s%s%s",
                                        TERM(38;2;127;197;78),
                                        v.regex->pattern,
                                        TERM(38;2;63;189;142),
                                        flags,
                                        TERM(0)
                                );
                        } else {
                                sxdf(&buf, "/%s/%s", v.regex->pattern, flags);
                        }
                        break;
                }

                case VALUE_FUNCTION:
                {
                        char const *cls  = class_name(ty, class_of(&v));
                        char const *name = name_of(&v);
                        char const *jit  = jit_of(&v) ? " [jit]" : "";

                        if (color) {
                                if (class_of(&v) == -1) {
                                        sxdf(
                                                &buf,
                                                "%s<func %s%s%s%s%s>%s",
                                                TERM(96),
                                                TERM(92),
                                                name,
                                                TERM(95),
                                                jit,
                                                TERM(96),
                                                TERM(0)
                                        );
                                } else {
                                        sxdf(
                                                &buf,
                                                "%s<func %s%s.%s%s%s%s>%s",
                                                TERM(96),
                                                TERM(92),
                                                cls,
                                                name,
                                                TERM(95),
                                                jit,
                                                TERM(96),
                                                TERM(0)
                                        );
                                }
                        } else {
                                if (class_of(&v) == -1) {
                                        sxdf(&buf, "<func %s>", name);
                                } else {
                                        sxdf(&buf, "<func %s.%s>", cls, name);
                                }
                        }
                        break;
                }

                case VALUE_BOUND_FUNCTION:
                {
                        char const *cls  = class_name(ty, class_of(&v));
                        char const *name = name_of(&v);

                        if (color) {
                                Value self = self_of(&v);
                                WLIT(sfmt(
                                        "%s>%s",
                                        TERM(96),
                                        TERM(0)
                                ));
                                svP(work, self);
                                WLIT(sfmt(
                                        "%s<func %s%s.%s %sbound to %s",
                                        TERM(96),
                                        TERM(92),
                                        cls,
                                        name,
                                        TERM(96),
                                        TERM(0)
                                ));
                        } else {
                                if (class_of(&v) == -1) {
                                        sxdf(
                                                &buf,
                                                "<func %s>",
                                                name
                                        );
                                } else {
                                        sxdf(
                                                &buf,
                                                "<func %s.%s>",
                                                cls,
                                                name
                                        );
                                }
                        }
                        break;
                }

                case VALUE_METHOD:
                        if (v.this == NULL) {
                                if (color) {
                                        sxdf(
                                                &buf,
                                                "%s<method %s'%s'%s>%s",
                                                TERM(96),
                                                TERM(92),
                                                name_of(v.method),
                                                TERM(96),
                                                TERM(0)
                                        );
                                } else {
                                        sxdf(
                                                &buf,
                                                "<method '%s' at %p>",
                                                M_NAME(v.name),
                                                (void *)v.method
                                        );
                                }
                        } else if (color) {
                                WLIT(sfmt(
                                        "%s>%s",
                                        TERM(96),
                                        TERM(0)
                                ));
                                svP(work, *v.this);
                                WLIT(sfmt(
                                        "%s<method %s'%s'%s bound to %s",
                                        TERM(96),
                                        TERM(92),
                                        name_of(v.method),
                                        TERM(96),
                                        TERM(0)
                                ));
                        } else {
                                WLIT(">");
                                svP(work, *v.this);
                                WLIT(sfmt(
                                        "<method '%s' bound to ",
                                        M_NAME(v.name)
                                ));
                        }
                        break;

                case VALUE_BUILTIN_METHOD:
                        if (color) {
                                sxdf(
                                        &buf,
                                        "%s<bound builtin method %s'%s'%s>%s",
                                        TERM(96),
                                        TERM(92),
                                        M_NAME(v.name),
                                        TERM(96),
                                        TERM(0)
                                );
                        } else {
                                sxdf(
                                        &buf,
                                        "<bound builtin method '%s'>",
                                        M_NAME(v.name)
                                );
                        }
                        break;

                case VALUE_BUILTIN_FUNCTION:
                        if (v.name == -1) {
                                if (color) {
                                        sxdf(
                                                &buf,
                                                "%s<builtin>%s",
                                                TERM(96),
                                                TERM(0)
                                        );
                                } else {
                                        sxdf(&buf, "<builtin>");
                                }
                        } else if (v.module == NULL) {
                                if (color) {
                                        sxdf(
                                                &buf,
                                                "%s<builtin %s'%s'%s>%s",
                                                TERM(96),
                                                TERM(92),
                                                M_NAME(v.name),
                                                TERM(96),
                                                TERM(0)
                                        );
                                } else {
                                        sxdf(
                                                &buf,
                                                "<builtin %s>",
                                                M_NAME(v.name)
                                        );
                                }
                        } else {
                                if (color) {
                                        sxdf(
                                                &buf,
                                                "%s<builtin %s'%s::%s'%s>%s",
                                                TERM(96),
                                                TERM(92),
                                                v.module,
                                                M_NAME(v.name),
                                                TERM(96),
                                                TERM(0)
                                        );
                                } else {
                                        sxdf(
                                                &buf,
                                                "<builtin %s.%s>",
                                                v.module,
                                                M_NAME(v.name)
                                        );
                                }
                        }
                        break;

                case VALUE_FOREIGN_FUNCTION:
                        if (v.xinfo == NULL || v.xinfo->name == NULL) {
                                if (color) {
                                        sxdf(
                                                &buf,
                                                "%s<foreign function>%s",
                                                TERM(96),
                                                TERM(0)
                                        );
                                } else {
                                        sxdf(&buf, "<foreign func>");
                                }
                        } else {
                                if (color) {
                                        sxdf(
                                                &buf,
                                                "%s<foreign function %s'%s'%s>%s",
                                                TERM(96),
                                                TERM(92),
                                                v.xinfo->name,
                                                TERM(96),
                                                TERM(0)
                                        );
                                } else {
                                        sxdf(
                                                &buf,
                                                "<foreign func %s>",
                                                v.xinfo->name
                                        );
                                }
                        }
                        break;

                case VALUE_OPERATOR:
                        if (color) {
                                sxdf(
                                        &buf,
                                        "%s<%soperator %s%s%s>%s",
                                        TERM(96),
                                        TERM(92),
                                        TERM(94),
                                        M_NAME(v.uop),
                                        TERM(96),
                                        TERM(0)
                                );
                        } else {
                                sxdf(
                                        &buf,
                                        "<operator %s>",
                                        M_NAME(v.uop)
                                );
                        }
                        break;

                case VALUE_CLASS:
                        if (color) {
                                sxdf(
                                        &buf,
                                        "%s<%sclass %s%s%s>%s",
                                        TERM(96),
                                        TERM(92),
                                        TERM(94),
                                        class_name(ty, v.class),
                                        TERM(96),
                                        TERM(0)
                                );
                        } else {
                                sxdf(
                                        &buf,
                                        "<class %s>",
                                        class_name(ty, v.class)
                                );
                        }
                        break;

                case VALUE_TAG:
                        if (color) {
                                sxdf(
                                        &buf,
                                        "%s%s%s",
                                        TERM(34),
                                        tags_name(ty, v.tag),
                                        TERM(0)
                                );
                        } else {
                                sxdf(
                                        &buf,
                                        "%s",
                                        tags_name(ty, v.tag)
                                );
                        }
                        break;

                case VALUE_BLOB:
                {
                        void *addr = (void *)v.blob;
                        usize size = vN(*v.blob);
                        if (color) {
                                sxdf(
                                        &buf,
                                        "%s<blob at %s%p%s (%zu bytes)>%s",
                                        TERM(96),
                                        TERM(92),
                                        addr,
                                        TERM(96),
                                        size,
                                        TERM(0)
                                );
                        } else {
                                sxdf(&buf, "<blob at %p (%zu bytes)>", addr, size);
                        }
                        break;
                }

                case VALUE_PTR:
                        if (color) {
                                sxdf(
                                        &buf,
                                        "%s<pointer at %s%s%p%s%s>%s",
                                        TERM(32),
                                        TERM(1),
                                        TERM(92),
                                        v.ptr,
                                        TERM(0),
                                        TERM(32),
                                        TERM(0)
                                );
                        } else {
                                sxdf(&buf, "<pointer at %p>", v.ptr);
                        }
                        break;

                case VALUE_GENERATOR:
                        if (color) {
                                sxdf(
                                        &buf,
                                        "%s<generator at %s%p%s>%s",
                                        TERM(96),
                                        TERM(92),
                                        v.gen,
                                        TERM(96),
                                        TERM(0)
                                );
                        } else {
                                sxdf(&buf, "<generator at %p>", v.gen);
                        }
                        break;

                case VALUE_THREAD:
                        if (color) {
                                sxdf(
                                        &buf,
                                        "%s<thread %"PRIu64">%s",
                                        TERM(33),
                                        v.thread->i,
                                        TERM(0)
                                );
                        } else {
                                sxdf(
                                        &buf,
                                        "<thread %"PRIu64">",
                                        v.thread->i
                                );
                        }
                        break;

                case VALUE_SENTINEL:
                        sxdf(&buf, "<sentinel>");
                        break;

                case VALUE_REF:
                        sxdf(&buf, "<reference to %p>", v.ptr);
                        break;

                case VALUE_NONE:
                        sxdf(&buf, "<none>");
                        break;

                case VALUE_TRACE:
                        if (color) {
                                sxdf(
                                        &buf,
                                        "%s<stack trace %s(%zu frames)%s>%s",
                                        TERM(38;2;49;161;173),
                                        TERM(34),
                                        vN(*(ThrowCtx *)v.ptr),
                                        TERM(38;2;49;161;173),
                                        TERM(0)
                                );
                        } else {
                                byte_vector tmp = {0};
                                svR(tmp, 2048 * 2048);
                                char *s = FormatTrace(ty, v.ptr, &tmp);
                                u32 len = strlen(s);
                                if (s != NULL) {
                                        svPn(buf, s, len);
                                }
                        }
                        break;

                case VALUE_INDEX:
                        sxdf(
                                &buf,
                                "<index: (%"PRIiMAX", %jd, %d)>",
                                v.i,
                                v.off,
                                v.nt
                        );
                        break;

                case VALUE_OBJECT:
                {
                        Value *fp = NULL;

                        if (flags & TY_SHOW_BASIC) {
                                goto BasicObject;
                        }

                        for (int i = 0; i < vN(ty->visiting); ++i) {
                                if (*v_(ty->visiting, i) == v.object) {
                                        goto BasicObject;
                                }
                        }

                        i32 meth = (flags & TY_SHOW_REPR) ? NAMES._repr_ : NAMES._str_;

                        if (color) {
#ifdef TY_NO_LOG
                                fp = class_lookup_method_i(ty, v.class, meth);
#endif
                        } else {
                                fp = class_lookup_method_i(ty, v.class, meth);
                        }

                        if (fp != NULL) {
                                xvP(ty->visiting, v.object);
                                Value self = stripped(&v);
                                Value str = vm_call_method(ty, &self, fp, 0);
                                vvX(ty->visiting);
                                if (str.type != VALUE_STRING) {
                                        goto BasicObject;
                                }
                                svPn(buf, ss(str), sN(str));
                        } else {
BasicObject:
                                if (color) {
                                        sxdf(
                                                &buf,
                                                "%s<%s%s%s%s%s"
                                                " object at %s%p%s>%s",
                                                TERM(96),
                                                TERM(34),
                                                class_name(ty, v.class),
                                                TERM(91;1),
                                                v.object->dynamic ? "*" : "",
                                                TERM(96),
                                                TERM(94),
                                                (void *)v.object,
                                                TERM(96),
                                                TERM(0)
                                        );
                                } else {
                                        sxdf(
                                                &buf,
                                                "<%s object at %p>",
                                                class_name(ty, v.class),
                                                (void *)v.object
                                        );
                                }
                        }
                        break;
                }

                case VALUE_ZERO:
                        sxdf(&buf, "<zero>");
                        break;

                case VALUE_UNINITIALIZED:
                        uninit(ty, v.sym);
                        break;

                default:
                        if (color) {
                                sxdf(&buf, "%s<??>%s", TERM(91;1), TERM(0));
                        } else {
                                sxdf(&buf, "<??>");
                        }
                        break;
                }

Next:
                continue;
        }

        svP(buf, '\0');
        vXx(buf);

        if (flags & TY_SHOW_ABBREV) {
                int keep = term_fit_cols(vv(buf), vN(buf), 80);
                if (keep < vN(buf)) {
                        return sfmt(
                                "%.*s%s...%s",
                                keep,
                                vv(buf),
                                TERM(90),
                                TERM(0)
                        );
                }
        }

        return vv(buf);
}

#undef WLIT
#undef WPOP

char *
value_show_color(Ty *ty, Value const *v, u32 flags)
{
        char *str;

        WITH_SCRATCH {
                str = S2(show_impl(ty, v, flags));
        }

        return str;
}

char *
value_show(Ty *ty, Value const *v, u32 flags)
{
        char *str;

        flags |= TY_SHOW_NOCOLOR;

        WITH_SCRATCH {
                str = S2(show_impl(ty, v, flags));
        }

        return str;
}

char *
value_show_scratch(Ty *ty, Value const *v, u32 flags)
{
        return show_impl(ty, v, flags);
}

Value
value_vshow_color(Ty *ty, Value const *v, u32 flags)
{
        Value str;

        WITH_SCRATCH {
                str = vSsz(show_impl(ty, v, flags));
        }

        return str;
}

Value
value_vshow(Ty *ty, Value const *v, u32 flags)
{
        Value str;

        flags |= TY_SHOW_NOCOLOR;

        WITH_SCRATCH {
                str = vSsz(show_impl(ty, v, flags));
        }

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
                        SHOW(v1),
                        TERM(95), TERM(0),
                        SHOW(v2)
                );
        }

        if (v.type != VALUE_INTEGER) {
                zP(
                        "non-integer returned by user-defined <=> operator\n"
                        FMT_MORE "  %sleft%s: %s"
                        FMT_MORE " %sright%s: %s"
                        FMT_MORE "%sresult%s: %s\n",
                        TERM(95), TERM(0),
                        SHOW(v1),
                        TERM(95), TERM(0),
                        SHOW(v2),
                        TERM(95), TERM(0),
                        SHOW(&v)
                );
        }

        return v.z;
}

int
value_compare(Ty *ty, Value const *v1, Value const *v2)
{
        int c;

        switch (PACK_TYPES(v1->type & ~VALUE_TAGGED, v2->type & ~VALUE_TAGGED)) {
        case PAIR_OF(VALUE_INTEGER):
                return (v1->z < v2->z) ? -1 : (v1->z != v2->z);

        case PAIR_OF(VALUE_REAL):
                return (v1->real < v2->real) ? -1 : (v1->real != v2->real);

        case PACK_TYPES(VALUE_REAL, VALUE_INTEGER):
                return (v1->real < v2->z) ? -1 : (v1->real != v2->z);

        case PACK_TYPES(VALUE_INTEGER, VALUE_REAL):
                return (v1->z < v2->real) ? -1 : (v1->z != v2->real);

        case PAIR_OF(VALUE_STRING):
                c = memcmp(ss(*v1), ss(*v2), min(sN(*v1), sN(*v2)));
                return (c != 0) ? c : (int)((isize)sN(*v1) - (isize)sN(*v2));

        case PAIR_OF(VALUE_PTR):
                return ((uptr)v1->ptr < (uptr)v2->ptr)
                     ? -1
                     :  ((uptr)v1->ptr != (uptr)v2->ptr)
                     ;

        case PAIR_OF(VALUE_ARRAY):
                for (int i = 0; i < v1->array->count && i < v2->array->count; ++i) {
                        int o = value_compare(ty, &v1->array->items[i], &v2->array->items[i]);
                        if (o != 0)
                                return o;
                }
                return ((ptrdiff_t)v1->array->count) - ((ptrdiff_t)v2->array->count);

        case PAIR_OF(VALUE_TUPLE):
                if (v1->items == v2->items) {
                        return 0;
                }
                if (v1->ids != NULL && v2->ids != NULL) {
                        return compare_records(ty, v1, v2);
                }
                for (int i = 0; i < v1->count && i < v2->count; ++i) {
                        int o = value_compare(ty, &v1->items[i], &v2->items[i]);
                        if (o != 0) {
                                return o;
                        }
                }
                return ((int)v1->count) - ((int)v2->count);
        }

        return check_cmp_result(ty, v1, v2, vm_try_2op(ty, OP_CMP, v1, v2));
}

bool
value_truthy(Ty *ty, Value const *v)
{
        switch (v->type) {
        case VALUE_REAL:             return (v->real != 0.0);
        case VALUE_BOOLEAN:          return v->boolean;
        case VALUE_INTEGER:          return (v->z != 0);
        case VALUE_STRING:           return (sN(*v) != 0);
        case VALUE_ARRAY:            return (vN(*v->array) != 0);
        case VALUE_TUPLE:            return (v->count != 0);
        case VALUE_BLOB:             return (vN(*v->blob) != 0);
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
        case VALUE_PTR:              return (v->ptr != NULL);
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
        case VALUE_BOUND_FUNCTION:
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
                                (PCRE2_SPTR)ss(*v),
                                sN(*v),
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
                zP("invalid type of value used as a predicate: %s", VSC(v));
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
                if (v->type != VALUE_STRING) {
                        zP("regex applied as predicate to non-string");
                }

                size_t *ovec = pcre2_get_ovector_pointer(ty->pcre2.match);

                int rc = pcre2_match(
                        f->regex->pcre2,
                        (PCRE2_SPTR)ss(*v),
                        sN(*v),
                        0,
                        0,
                        ty->pcre2.match,
                        ty->pcre2.ctx
                );

                if (rc < -2) {
                        zP("error while executing regular expression: %d", rc);
                }

                if (rc <= 0) {
                        return NIL;
                }

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
                zP("invalid type of value used as a callable: %s", VSC(f));
        }
}

bool
value_test_equality(Ty *ty, Value const *v1, Value const *v2)
{
        if (v1->tags != v2->tags) {
                return false;
        }

        int t0 = v1->type & ~VALUE_TAGGED;
        int t1 = v2->type & ~VALUE_TAGGED;

        switch (PACK_TYPES(t0, t1)) {
        case PAIR_OF(VALUE_INTEGER):
                return v1->z == v2->z;

        case PAIR_OF(VALUE_STRING):
                return (sN(*v1) == sN(*v2))
                    && (memcmp(ss(*v1), ss(*v2), sN(*v1)) == 0);

        case PAIR_OF(VALUE_BOOLEAN):
                return (v1->boolean == v2->boolean);

        case PAIR_OF(VALUE_ARRAY):
                return arrays_equal(ty, v1, v2);

        case PAIR_OF(VALUE_TUPLE):
                return tuples_equal(ty, v1, v2);

        case PAIR_OF(VALUE_DICT):
                return (v1->dict == v2->dict);

        case PAIR_OF(VALUE_CLASS):
                return (v1->class == v2->class);

        case PAIR_OF(VALUE_TAG):
                return (v1->tag == v2->tag);

        case PAIR_OF(VALUE_PTR):
                return (v1->ptr == v2->ptr);

        case PAIR_OF(VALUE_BLOB):
                return (v1->blob == v2->blob);

        case PAIR_OF(VALUE_FUNCTION):
                return (v1->info == v2->info);

        case PAIR_OF(VALUE_BUILTIN_FUNCTION):
                return (v1->builtin_function == v2->builtin_function);

        case PAIR_OF(VALUE_BUILTIN_METHOD):
                return (v1->builtin_method == v2->builtin_method)
                    && (v1->this == v2->this);

        case PAIR_OF(VALUE_REGEX):
                return v1->regex == v2->regex;

        case PAIR_OF(VALUE_REAL):
                return v1->real == v2->real;

        case PAIR_OF(VALUE_NIL):
                return true;

        case PAIR_OF(VALUE_OBJECT):
                if (v1->object == v2->object) {
                        return true;
                }
                break;
        }

        if ((t0 == VALUE_NIL) || (t1 == VALUE_NIL)) {
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

#if defined(TY_TRACE_GC)
        if (a->items != NULL) {
                ADD_REACHED(ALLOC_OF(a->items)->size);
        }
#endif

        for (int i = 0; i < a->count; ++i) {
                MarkNext(ty, &a->items[i]);
        }
}

inline static void
mark_tuple(Ty *ty, Value const *v)
{
        if (v->items == NULL || MARKED(v->items)) return;

        MARK(v->items);

        for (int i = 0; i < v->count; ++i) {
                MarkNext(ty, &v->items[i]);
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
        MarkNext(ty, &v->thread->v);
}

inline static void
mark_string(Ty *ty, Value const *v)
{
        if (!v->ro && v->str0 != NULL) {
                MARK(v->str0);
        }
}

inline static void
mark_generator(Ty *ty, Value const *v)
{
        if (MARKED(v->gen)) return;

        MARK(v->gen);

        MarkNext(ty, &v->gen->f);

        for (int i = 0; i < vN(v->gen->frame); ++i) {
                MarkNext(ty, v_(v->gen->frame, i));
        }

        for (int i = 0; i < vN(v->gen->st.targets); ++i) {
                if ((((uptr)v_(v->gen->st.targets, i)->t) & 0x07) == 0) {
                        MarkNext(ty, v_(v->gen->st.targets, i)->t);
                }
        }

        for (int i = 0; i < vN(v->gen->st.try_stack); ++i) {
                struct try *t = v__(v->gen->st.try_stack, i);
                for (int i = 0; i < vN(t->defer); ++i) {
                        MarkNext(ty, v_(t->defer, i));
                }
        }

        for (int i = 0; i < vN(v->gen->st.to_drop); ++i) {
                MarkNext(ty, v_(v->gen->st.to_drop, i));
        }

        for (int i = 0; i < vN(v->gen->gc_roots); ++i) {
                MarkNext(ty, v_(v->gen->gc_roots, i));
        }
}

inline static void
mark_function(Ty *ty, Value const *v)
{
        int n = v->info[FUN_INFO_CAPTURES]
              + (v->type == VALUE_BOUND_FUNCTION);

        if (from_eval(v)) {
                MARK(v->info);
        }

        if (has_meta(v)) {
                Value *meta = meta_of(ty, v);
                if (!MARKED(meta)) {
                        MARK(meta);
                        MarkNext(ty, meta);
                }
        }

        if (v->xinfo != NULL) {
                MARK(v->xinfo);
        }

        if (n == 0 || MARKED(v->env)) {
                return;
        }

        MARK(v->env);

        for (int i = 0; i < n; ++i) {
                if (v->env[i] != NULL) {
                        MARK(v->env[i]);
                        MarkNext(ty, v->env[i]);
                }
        }
}

inline static void
mark_method(Ty *ty, Value const *v)
{
        MARK(v->this);
        MarkNext(ty, v->this);
}

inline static void
mark_native_function(Ty *ty, Value const *v)
{
        if (v->xinfo != NULL) {
                MARK(v->xinfo);
        }
        // TODO: when JIT closures are supported, mark env entries via JitInfo
}

inline static void
mark_pointer(Ty *ty, Value const *v)
{
        if (v->gcptr != NULL) {
                MARK(v->gcptr);
                switch (ALLOC_OF(v->gcptr)->type) {
                case GC_VALUE:
                        MarkNext(ty, (Value *)v->gcptr);
                        break;

                case GC_FFI_AUTO:
                        MarkNext(ty, ((Value *)v->gcptr));
                        break;
                }
        }
}

inline static void
mark_trace(Ty *ty, ThrowCtx *ctx)
{
        if (MARKED(ctx)) {
                return;
        }

        MARK(ctx);

        if (DetailedExceptions) {
                for (int i = 0; i < vN(*ctx); ++i) {
                        ValueVector *locals = v_(ctx->locals, i);
                        vfor(*locals, MarkNext(ty, it));
                }
        }
}

static inline void
_value_mark_xd(Ty *ty, Value const *v)
{
        void **src = source_lookup(ty, v->src);
        if (src != NULL && *src != NULL) {
                MARK(*src);
        }

#ifndef TY_RELEASE
        static _Thread_local int d;

        GC_STOP();
        //GCLOG("Marking: %s", SHOW(v, BASIC));
        GC_RESUME();

        ++d;
#endif

        switch (v->type & ~VALUE_TAGGED) {
        case VALUE_METHOD:           if (!MARKED(v->this)) { mark_method(ty, v); }                     break;
        case VALUE_BUILTIN_METHOD:   if (!MARKED(v->this)) { MARK(v->this); MarkNext(ty, v->this); }   break;
        case VALUE_FOREIGN_FUNCTION: if (v->xinfo != NULL) { MARK(v->xinfo); }                         break;
        case VALUE_ARRAY:            value_array_mark(ty, v->array);                                   break;
        case VALUE_TUPLE:            mark_tuple(ty, v);                                                break;
        case VALUE_DICT:             dict_mark(ty, v->dict);                                           break;
        case VALUE_BOUND_FUNCTION:
        case VALUE_FUNCTION:         mark_function(ty, v);                                             break;
        case VALUE_GENERATOR:        mark_generator(ty, v);                                            break;
        case VALUE_THREAD:           mark_thread(ty, v);                                               break;
        case VALUE_STRING:           mark_string(ty, v);                                               break;
        case VALUE_OBJECT:           object_mark(ty, v->object);                                       break;
        case VALUE_CLASS:            class_mark(ty, v->class);                                         break;
        case VALUE_REF:              MARK(v->ref); MarkNext(ty, v->ref);                               break;
        case VALUE_BLOB:             MARK(v->blob);                                                    break;
        case VALUE_PTR:              mark_pointer(ty, v);                                              break;
        case VALUE_TRACE:            mark_trace(ty, v->ptr);                                           break;
        case VALUE_REGEX:            if (v->regex->gc) MARK(v->regex);                                 break;
        default:                                                                                       break;
        }

#ifndef TY_RELEASE
        --d;
#endif
}

void
_value_mark(Ty *ty, Value const *v)
{
        RESET_REACHED();

        _value_mark_xd(ty, v);

        while (vN(ty->marking) > 0) {
                v = vXx(ty->marking);
                _value_mark_xd(ty, v);
        }
}

Blob *
value_blob_new(Ty *ty)
{
        return mAo0(sizeof (Blob), GC_BLOB);
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
                        out[n++] = S2(name);
                }
        }

        return n;
}

Value
(NewInstance)(Ty *ty, int c, ...)
{
        Class *class = class_get(ty, c);
        Value object = RawObject(c);

        va_list ap;
        va_start(ap, c);

        int argc = 0;

        for (;; ++argc) {
                Value arg = va_arg(ap, Value);

                if (IsNone(arg)) {
                        break;
                }

                vmP(&arg);
        }

        if (!IsMissing(class->init)) {
                (void)vm_call_method(ty, &object, &class->init, argc);
        }

        return object;
}


/* vim: set sts=8 sw=8 expandtab: */
