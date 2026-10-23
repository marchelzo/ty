#include <setjmp.h>
#include <ctype.h>
#include <stdlib.h>
#include <errno.h>
#include <utf8proc.h>

#if defined(__SSE2__)
 #include <emmintrin.h>
#elif defined(__aarch64__)
 #include <arm_neon.h>
#endif

#include "value.h"
#include "dict.h"
#include "set.h"
#include "xd.h"
#include "dtoa.h"
#include "itable.h"
#include "intern.h"
#include "class.h"
#include "vec.h"
#include "vm.h"
#include "ty.h"
#include "types2.h"

typedef byte_vector str;

static _Thread_local vec(void const *) Visiting;

inline static bool
visiting(void const *p)
{
        for (int i = 0; i < Visiting.count; ++i) {
                if (Visiting.items[i] == p) {
                        return true;
                }
        }

        return false;
}

inline static bool
try_visit(void const *p)
{
        if (visiting(p)) {
                return false;
        } else {
                xvP(Visiting, p);
                return true;
        }
}

static bool
encode(Ty *ty, Value const *v, str *out)
{
        if (v->type & VALUE_TAGGED) {
                Value val = *v;
                char const *tn = tags_name(ty, tags_first(ty, v->tags));

                val.tags = tags_pop(ty, v->tags);
                if (val.tags == 0) {
                        val.type &= ~VALUE_TAGGED;
                }

                dump((void *)out, "{\"type\":\"%s\",\"value\":", tn);

                if (!encode(ty, &val, out)) {
                        return false;
                }

                xvP(*out, '}');

                return true;
        }

        bool first = true;

        switch (v->type & ~VALUE_TAGGED) {
        case VALUE_NIL:
                xvPn(*out, "null", 4);
                break;

        case VALUE_TAG:
                dump((void *)out, "\"%s\"", tags_name(ty, v->tag));
                break;

        case VALUE_STRING:
                xvP(*out, '"');
                for (int i = 0; i < sN(*v); ++i) {
                        int n;
                        int32_t cp;
                        switch (ss(*v)[i]) {
                        case '\t':
                                xvP(*out, '\\');
                                xvP(*out, 't');
                                break;
                        case '\n':
                                xvP(*out, '\\');
                                xvP(*out, 'n');
                                break;
                        case '\\':
                        case '"':
                                xvP(*out, '\\');
                        default:
                                if ((ss(*v)[i]) > 127) {
                                        n = utf8proc_iterate(&ss(*v)[i], sN(*v) - i, &cp);
                                        if (n <= 0) {
                                                xvPn(*out, "\\ufffd", 6);
                                                n = 1;
                                        } else {
                                                if (cp <= 0xFFFF) {
                                                        dump(out, "\\u%04x", cp);
                                                } else {
                                                        cp -= 0x10000;
                                                        u16 hi = 0xD800 + (cp >> 10);
                                                        u16 lo = 0xDC00 + (cp & 0x3FF);
                                                        dump(out, "\\u%04x\\u%04x", hi, lo);
                                                }
                                        }
                                        i += n - 1;
                                } else if (iscntrl(ss(*v)[i])) {
                                        dump(out, "\\u%04x", (u8)ss(*v)[i]);
                                } else {
                                        xvP(*out, ss(*v)[i]);
                                }
                                break;
                        }
                }
                xvP(*out, '"');
                break;

        case VALUE_BOOLEAN:
                if (v->boolean)
                        xvPn(*out, "true", 4);
                else
                        xvPn(*out, "false", 5);
                break;

        case VALUE_INTEGER:
                xvR(*out, out->count + 64);
                out->count += ty_snprintf(out->items + out->count, 64, "%"PRIiMAX, v->z);
                break;

        case VALUE_REAL:
                xvR(*out, out->count + 64);
                out->count += dtoa(v->real, out->items + out->count, 64);
                break;

        case VALUE_ARRAY:
                xvP(*out, '[');
                if (!try_visit(v->array))
                        return false;
                for (int i = 0; i < v->array->count; ++i) {
                        if (!encode(ty, &v->array->items[i], out))
                                return false;
                        if (i + 1 < v->array->count)
                                xvP(*out, ',');
                }
                vvX(Visiting);
                xvP(*out, ']');
                break;

        case VALUE_HEAP:
        {
                Value view = HEAP_VIEW(v->heap);
                return encode(ty, &view, out);
        }

        case VALUE_SET:
                xvP(*out, '[');
                if (!try_visit(v->set)) {
                        return false;
                }
                sfor(v->set, {
                        if (!first) {
                                xvP(*out, ',');
                        }
                        if (!encode(ty, x, out)) {
                                return false;
                        }
                        first = false;
                });
                vvX(Visiting);
                xvP(*out, ']');
                break;

        case VALUE_DICT:
                xvP(*out, '{');
                if (!try_visit(v->dict)) {
                        return false;
                }
                dfor(v->dict, {
                        if (key->type != VALUE_STRING) {
                                continue;
                        }
                        if (!first) {
                                xvP(*out, ',');
                        }
                        if (!encode(ty, key, out)) {
                                return false;
                        }
                        xvP(*out, ':');
                        if (!encode(ty, val, out)) {
                                return false;
                        }
                        first = false;
                });
                vvX(Visiting);
                xvP(*out, '}');
                break;

        case VALUE_OBJECT:
        {
                if (!try_visit(v->object))
                        return false;

                Value *vp = class_lookup_method_i(ty, v->class, NAMES.json);

                if (vp != NULL) {
                        Value method = METHOD(NAMES.json, vp, v);
                        Value s = vm_eval_function(ty, &method, NULL);
                        if (s.type == VALUE_STRING) {
                                gP(&s);
                                xvPn(*out, ss(s), sN(s));
                                gX();
                        } else {
                                return encode(ty, &s, out);
                        }
                } else {
                        xvP(*out, '{');
                        for (int i = 0; i < v->object->nslot; ++i) {
                                char const *name = M_NAME(v__(v->object->class->fields.ids, i));
                                xvP(*out, '"');
                                xvPn(*out, name, strlen(name));
                                xvP(*out, '"');
                                xvP(*out, ':');
                                if (!encode(ty, &v->object->slots[i], out)) {
                                        return false;
                                }
                                xvP(*out, ',');
                        }
                        if (v->object->dynamic != NULL) {
                                for (int i = 0; i < vN(v->object->dynamic->ids); ++i) {
                                        char const *name = M_NAME(v__(v->object->dynamic->ids, i));
                                        xvP(*out, '"');
                                        xvPn(*out, name, strlen(name));
                                        xvP(*out, '"');
                                        xvP(*out, ':');
                                        if (!encode(ty, v_(v->object->dynamic->values, i), out)) {
                                                return false;
                                        }
                                        xvP(*out, ',');
                                }
                        }
                        vvX(Visiting);
                        if (*vvL(*out) == ',') {
                                *vvL(*out) = '}';
                        } else {
                                xvP(*out, '}');
                        }
                }
                break;
        }

        case VALUE_TUPLE:
                xvP(*out, '{');
                if (!try_visit(v->items)) {
                        return false;
                }
                for (int i = 0; i < v->count; ++i) {
                        xvP(*out, '"');
                        if (v->ids != NULL && v->ids[i] != -1) {
                                char const *name = M_NAME(v->ids[i]);
                                xvPn(*out, name, strlen(name));
                        } else {
                                char b[32];
                                ty_snprintf(b, sizeof b - 1, "%d", i);
                                xvPn(*out, b, strlen(b));
                        }
                        xvP(*out, '"');
                        xvP(*out, ':');
                        if (!encode(ty, &v->items[i], out)) {
                                return false;
                        }
                        xvP(*out, ',');
                }
                vvX(Visiting);
                if (*vvL(*out) == ',') {
                        *vvL(*out) = '}';
                } else {
                        xvP(*out, '}');
                }
                break;

        case VALUE_BLOB:
                xvP(*out, '"');
                for (int i = 0; i < v->blob->count; ++i) {
                        char b[3];
                        ty_snprintf(b, sizeof b, "%.2X", (unsigned)v->blob->items[i]);
                        xvP(*out, '\\');
                        xvP(*out, 'x');
                        xvP(*out, b[0]);
                        xvP(*out, b[1]);
                }
                xvP(*out, '"');
                break;

        default:
                return false;

        }

        return true;
}

typedef struct jnode  JNode;
typedef struct jfield JField;
typedef struct jsum   JSum;

typedef vec(u16) JList;

enum {
        JN_LAZY,
        JN_ANY,
        JN_NIL,
        JN_BOOL,
        JN_INT,
        JN_FLOAT,
        JN_STRING,
        JN_LSTR,
        JN_LINT,
        JN_LBOOL,
        JN_CHECK,
        JN_ARRAY,
        JN_SET,
        JN_DICT,
        JN_TUPLE,
        JN_RECORD,
        JN_OBJECT,
        JN_UNION
};

enum {
        JD_NONE,
        JD_WILD,
        JD_LIT
};

typedef struct {
        char **s;
        u32   *n;
        u32   *slot;
        u32    count;
        u32    cap;
        u32    mask;
} JTab;

struct jfield {
        i32    id;
        bool   required;
        JNode *type;
        u32    next;
};

struct jnode {
        u8     kind;
        bool   busy;
        bool   flat;
        T2Type t2;
        union {
                JNode *elem;
                struct {
                        JNode **items;
                        u32     typed;
                } tup;
                struct {
                        JField *f;
                        JTab    keys;
                        u32     first;
                        u32     nslot;
                        int     class;
                        Class  *c;
                        bool    raw;
                } obj;
                struct {
                        char *s;
                        u32   n;
                } lit;
                i64   z;
                bool  b;
                JSum *sum;
        };
};

struct jsum {
        JNode **alt;
        u32     n;
        bool    str;
        bool    chk;
        bool    filter;
        JTab    lits;
        JList   num;
        JList   sca;
        JList   arr;
        JList   obj;
        JTab    keys;
        u64    *req;
        i32     disc;
        JTab    dlits;
        JList  *dlist;
        JList   dwild;
};

typedef struct {
        Ty          *ty;
        char const  *s;
        char const  *end;
        char const  *start;
        Value const *input;
        jmp_buf     *jb;
        bool         view;
        bool         xd;
} JP;

typedef struct {
        u64         mask;
        i32         dlist;
        char const *dpos;
        char const *close;
} JScan;

enum {
        JS_UNSEEN = -1,
        JS_WILD   = -2
};

static JNode AnyNode = { .kind = JN_ANY };

static _Thread_local struct {
        Value *v;
        u32    n;
        u32    cap;
} Stk;

static _Thread_local byte_vector Esc;

static _Thread_local char const *Furthest;

static _Thread_local struct {
        char const *s[16];
        char const *e[16];
        u32         n;
} Memo;

static _Thread_local struct {
        T2Universe const *u;
        T2Type           *key;
        JNode           **node;
        u32               count;
        u32               mask;
} Plans;

static _Thread_local struct {
        char *s;
        u32   n;
        i32   id;
} KeyCache[1024];

static _Thread_local struct {
        u16 slot;
        i32 id;
} KeyNext[1024];

static u8 const JSPACE[256] = {
        [' ']  = 1,
        ['\t'] = 1,
        ['\n'] = 1,
        ['\r'] = 1,
        ['\v'] = 1,
        ['\f'] = 1
};

static u8 const NUMTAIL[256] = {
        ['0'] = 1, ['1'] = 1, ['2'] = 1, ['3'] = 1, ['4'] = 1,
        ['5'] = 1, ['6'] = 1, ['7'] = 1, ['8'] = 1, ['9'] = 1,
        ['.'] = 1, ['e'] = 1, ['E'] = 1
};

static u8 const SKIPSTOP[256] = {
        [' ']  = 1,
        ['\t'] = 1,
        ['\n'] = 1,
        ['\r'] = 1,
        ['\v'] = 1,
        ['\f'] = 1,
        [',']  = 1,
        [']']  = 1,
        ['}']  = 1,
        ['"']  = 1,
        ['[']  = 1,
        ['{']  = 1
};

static u8 const xtable[256] = {
        ['0'] = 0, ['1'] = 1, ['2'] = 2, ['3'] = 3, ['4'] = 4,
        ['5'] = 5, ['6'] = 6, ['7'] = 7, ['8'] = 8, ['9'] = 9,

        ['A'] = 10, ['a'] = 10,
        ['B'] = 11, ['b'] = 11,
        ['C'] = 12, ['c'] = 12,
        ['D'] = 13, ['d'] = 13,
        ['E'] = 14, ['e'] = 14,
        ['F'] = 15, ['f'] = 15
};

#define FAIL Fail(p, p->s)

static noreturn void
Fail(JP *p, char const *at)
{
        if (at > Furthest) {
                Furthest = at;
        }

        longjmp(*p->jb, 1);
}

inline static char
peek(JP const *p)
{
        return (p->s < p->end) ? *p->s : '\0';
}

inline static void
space(JP *p)
{
        while (p->s < p->end && JSPACE[(u8)*p->s]) {
                p->s += 1;
        }
}

static void
sgrow(void)
{
        Stk.cap = (Stk.cap == 0) ? 1024 : 2 * Stk.cap;
        Stk.v   = mrealloc(Stk.v, Stk.cap * sizeof (Value));
}

inline static void
spush(Value v)
{
        if (UNLIKELY(Stk.n == Stk.cap)) {
                sgrow();
        }

        Stk.v[Stk.n++] = v;
}

inline static u64
khash(char const *s, u32 n)
{
        u64 a = 0;
        u64 b = 0;
        u32 x;
        u32 y;

        if (n >= 8) {
                memcpy(&a, s, 8);
                memcpy(&b, s + n - 8, 8);
        } else if (n >= 4) {
                memcpy(&x, s, 4);
                memcpy(&y, s + n - 4, 4);
                a = x;
                b = y;
        } else if (n > 0) {
                a = (u8)s[0]
                  | ((u64)(u8)s[n >> 1] << 8)
                  | ((u64)(u8)s[n - 1] << 16);
        }

        u64 h = (a ^ 0x9E3779B97F4A7C15ull) * 0xBF58476D1CE4E5B9ull;
        h ^= (b + n) * 0x94D049BB133111EBull;

        return h ^ (h >> 31);
}

inline static i32
tfind(JTab const *t, char const *s, u32 n)
{
        if (t->slot == NULL) {
                return -1;
        }

        for (u64 i = khash(s, n);; ++i) {
                u32 k = t->slot[i & t->mask];
                if (k == 0) {
                        return -1;
                }
                if (t->n[k - 1] == n && memcmp(t->s[k - 1], s, n) == 0) {
                        return k - 1;
                }
        }
}

static void
trehash(JTab *t, u32 cap)
{
        xmF(t->slot);

        t->slot = xtA0(u32, cap);
        t->mask = cap - 1;

        for (u32 k = 0; k < t->count; ++k) {
                u64 i = khash(t->s[k], t->n[k]);
                while (t->slot[i & t->mask] != 0) {
                        i += 1;
                }
                t->slot[i & t->mask] = k + 1;
        }
}

static u32
tadd(JTab *t, char const *s, u32 n)
{
        i32 i = tfind(t, s, n);

        if (i >= 0) {
                return i;
        }

        if (t->count == t->cap) {
                t->cap = (t->cap == 0) ? 8 : 2 * t->cap;
                t->s   = mrealloc(t->s, t->cap * sizeof *t->s);
                t->n   = mrealloc(t->n, t->cap * sizeof *t->n);
        }

        char *copy = alloc0(n + 9);
        if (n > 0) {
                memcpy(copy, s, n);
        }

        t->s[t->count] = copy;
        t->n[t->count] = n;
        t->count += 1;

        u32 cap = 16;
        while (cap < 4 * t->count) {
                cap *= 2;
        }

        if (t->slot == NULL || cap > t->mask + 1) {
                trehash(t, cap);
        } else {
                u64 j = khash(copy, n);
                while (t->slot[j & t->mask] != 0) {
                        j += 1;
                }
                t->slot[j & t->mask] = t->count;
        }

        return t->count - 1;
}

inline static u32
keyslot(char const *k, u32 n)
{
        u32 h = khash(k, n) & (countof(KeyCache) - 1);

        if (
                (KeyCache[h].s != NULL)
             && (KeyCache[h].n == n)
             && (memcmp(KeyCache[h].s, k, n) == 0)
        ) {
                return h;
        }

        InternEntry *e = intern_n(&xD.members, k, n);

        xmF(KeyCache[h].s);

        KeyCache[h].s  = alloc0(n + 9);
        KeyCache[h].n  = n;
        KeyCache[h].id = e->id;

        if (n > 0) {
                memcpy(KeyCache[h].s, k, n);
        }

        return h;
}

inline static i32
keyid(char const *k, u32 n)
{
        return KeyCache[keyslot(k, n)].id;
}

inline static char const *
StrStop(char const *s, char const *end)
{
#if defined(__SSE2__)
        __m128i const q = _mm_set1_epi8('"');
        __m128i const b = _mm_set1_epi8('\\');

        if (end - s >= 16) {
                __m128i x = _mm_loadu_si128((__m128i const *)s);
                int m = _mm_movemask_epi8(_mm_or_si128(_mm_cmpeq_epi8(x, q), _mm_cmpeq_epi8(x, b)));
                if (m != 0) {
                        return s + __builtin_ctz(m);
                }
                s += 16;
        }

        while (end - s >= 64) {
                __m128i x0 = _mm_loadu_si128((__m128i const *)(s +  0));
                __m128i x1 = _mm_loadu_si128((__m128i const *)(s + 16));
                __m128i x2 = _mm_loadu_si128((__m128i const *)(s + 32));
                __m128i x3 = _mm_loadu_si128((__m128i const *)(s + 48));
                __m128i m0 = _mm_or_si128(_mm_cmpeq_epi8(x0, q), _mm_cmpeq_epi8(x0, b));
                __m128i m1 = _mm_or_si128(_mm_cmpeq_epi8(x1, q), _mm_cmpeq_epi8(x1, b));
                __m128i m2 = _mm_or_si128(_mm_cmpeq_epi8(x2, q), _mm_cmpeq_epi8(x2, b));
                __m128i m3 = _mm_or_si128(_mm_cmpeq_epi8(x3, q), _mm_cmpeq_epi8(x3, b));
                if (_mm_movemask_epi8(_mm_or_si128(_mm_or_si128(m0, m1), _mm_or_si128(m2, m3))) != 0) {
                        u64 m = (u64)_mm_movemask_epi8(m0)
                              | ((u64)_mm_movemask_epi8(m1) << 16)
                              | ((u64)_mm_movemask_epi8(m2) << 32)
                              | ((u64)_mm_movemask_epi8(m3) << 48);
                        return s + __builtin_ctzll(m);
                }
                s += 64;
        }

        while (end - s >= 16) {
                __m128i x = _mm_loadu_si128((__m128i const *)s);
                int m = _mm_movemask_epi8(_mm_or_si128(_mm_cmpeq_epi8(x, q), _mm_cmpeq_epi8(x, b)));
                if (m != 0) {
                        return s + __builtin_ctz(m);
                }
                s += 16;
        }
#elif defined(__aarch64__)
        uint8x16_t const q = vdupq_n_u8('"');
        uint8x16_t const b = vdupq_n_u8('\\');

        while (end - s >= 16) {
                uint8x16_t x = vld1q_u8((u8 const *)s);
                uint8x16_t m = vorrq_u8(vceqq_u8(x, q), vceqq_u8(x, b));
                u64 bits = vget_lane_u64(vreinterpret_u64_u8(vshrn_n_u16(vreinterpretq_u16_u8(m), 4)), 0);
                if (bits != 0) {
                        return s + (__builtin_ctzll(bits) >> 2);
                }
                s += 16;
        }
#endif

        while (s < end && *s != '"' && *s != '\\') {
                s += 1;
        }

        return s;
}

inline static char const *
strstop(JP *p, char const *s)
{
        if (UNLIKELY(Memo.n != 0)) {
                for (u32 i = 0; i < Memo.n && i < countof(Memo.s); ++i) {
                        if (Memo.s[i] == s) {
                                return Memo.e[i];
                        }
                }
        }

        return StrStop(s, p->end);
}

inline static void
keyword(JP *p, char const *kw, usize n)
{
        if ((usize)(p->end - p->s) < n || memcmp(p->s, kw, n) != 0) {
                FAIL;
        }

        char const *after = p->s + n;

        if (
                (after < p->end)
             && !JSPACE[(u8)*after]
             && (*after != ',')
             && (*after != ']')
             && (*after != '}')
        ) {
                Fail(p, after);
        }

        p->s = after;
}

inline static void
jnull(JP *p, Value *out)
{
        keyword(p, "null", 4);
        *out = NIL;
}

inline static void
jbool(JP *p, Value *out)
{
        if (peek(p) == 't') {
                keyword(p, "true", 4);
                *out = BOOLEAN(true);
        } else {
                keyword(p, "false", 5);
                *out = BOOLEAN(false);
        }
}

static double const POW10[] = {
        1e0,  1e1,  1e2,  1e3,  1e4,  1e5,  1e6,  1e7,
        1e8,  1e9,  1e10, 1e11, 1e12, 1e13, 1e14, 1e15,
        1e16, 1e17, 1e18, 1e19, 1e20, 1e21, 1e22
};

static void
SlowNumber(JP *p, Value *out)
{
        JsonNumber num;
        char const *end = ty_json_number(p->s, p->end, &num);

        if (end == NULL) {
                FAIL;
        }

        p->s = end;
        *out = num.real ? REAL(num.x) : INTEGER(num.z);
}

[[gnu::always_inline]] inline static void
number(JP *p, Value *out)
{
        char const *s = p->s;
        char const *e = p->end;
        char const *q = s + (s < e && *s == '-');
        char const *d = q;
        char const *f;
        u64 m = 0;
        double x;

        if (q == e || (u8)(*q - '0') >= 10) {
                SlowNumber(p, out);
                return;
        }

        if (*q == '0') {
                d += 1;
        } else {
                while (d < e && (u8)(*d - '0') < 10 && d - q < 15) {
                        m = 10 * m + (*d - '0');
                        d += 1;
                }
        }

        if (d == e || !NUMTAIL[(u8)*d]) {
                if (s != q && m == 0) {
                        SlowNumber(p, out);
                        return;
                }
                p->s = d;
                *out = INTEGER((s == q) ? (i64)m : -(i64)m);
                return;
        }

        if (*d != '.') {
                SlowNumber(p, out);
                return;
        }

        f = d + 1;

        while (f < e && (u8)(*f - '0') < 10 && (d - q) + (f - d - 1) < 15) {
                m = 10 * m + (*f - '0');
                f += 1;
        }

        if (f == d + 1 || (f < e && NUMTAIL[(u8)*f])) {
                SlowNumber(p, out);
                return;
        }

        x = (double)m / POW10[f - d - 1];

        p->s = f;
        *out = REAL((s == q) ? x : -x);
}

inline static u32
hexn(JP *p, char const **s, int n)
{
        u32 x = 0;

        if (p->end - *s < n) {
                p->s = p->end;
                FAIL;
        }

        for (int i = 0; i < n; ++i) {
                x = (x << 4) | xtable[(u8)(*s)[i]];
        }

        *s += n;

        return x;
}

static char const *
unescape(JP *p, char const *s, char const *e)
{
        char b[8];
        u32 cp;
        u32 lo;

        v0(Esc);

        for (;;) {
                xvPn(Esc, s, e - s);

                if (e == p->end) {
                        p->s = e;
                        FAIL;
                }

                if (*e == '"') {
                        return e + 1;
                }

                s = e + 1;

                if (s == p->end) {
                        p->s = s;
                        FAIL;
                }

                switch (*s++) {
                case 't':  xvP(Esc, '\t'); break;
                case 'f':  xvP(Esc, '\f'); break;
                case 'n':  xvP(Esc, '\n'); break;
                case 'r':  xvP(Esc, '\r'); break;
                case 'b':  xvP(Esc, '\b'); break;

                case 'x':
                        xvP(Esc, (char)hexn(p, &s, 2));
                        break;

                case 'u':
                        cp = hexn(p, &s, 4);
                        if ((cp & 0xF800) == 0xD800) {
                                if (s == p->end || s[0] != '\\') {
                                        p->s = s;
                                        FAIL;
                                }
                                if (s + 1 == p->end || s[1] != 'u') {
                                        p->s = s + 1;
                                        FAIL;
                                }
                                s += 2;
                                lo = hexn(p, &s, 4);
                                cp = 0x10000 + ((cp - 0xD800) << 10) + (lo - 0xDC00);
                        }
                        xvPn(Esc, b, utf8proc_encode_char(cp, (u8 *)b));
                        break;

                default:
                        xvP(Esc, s[-1]);
                }

                e = strstop(p, s);
        }
}

inline static void
mkstr(JP *p, char const *s, u32 n, Value *out)
{
        Ty *ty = p->ty;

        if (n == 0) {
                *out = STRING_NOGC(NULL, 0);
                return;
        }

        if (p->view) {
                *out = STRING_VIEW(*p->input, s - (char const *)ss(*p->input), n);
                return;
        }

        char *m = value_string_alloc(ty, n);
        memcpy(m, s, n);

        *out = STRING(m, n);
}

static void
dstr(JP *p, Value *out)
{
        Ty *ty = p->ty;

        if (peek(p) != '"') {
                FAIL;
        }

        char const *s = p->s + 1;
        char const *e = strstop(p, s);

        if (LIKELY(e < p->end && *e == '"')) {
                p->s = e + 1;
                mkstr(p, s, e - s, out);
                return;
        }

        p->s = unescape(p, s, e);

        u32 n = vN(Esc);

        if (n == 0) {
                *out = STRING_NOGC(NULL, 0);
                return;
        }

        char *m = value_string_alloc(ty, n);
        memcpy(m, vv(Esc), n);

        *out = STRING(m, n);
}

inline static char const *
dspan(JP *p, u32 *n)
{
        if (peek(p) != '"') {
                FAIL;
        }

        char const *s = p->s + 1;
        char const *e = strstop(p, s);

        if (LIKELY(e < p->end && *e == '"')) {
                p->s = e + 1;
                *n = e - s;
                return s;
        }

        p->s = unescape(p, s, e);
        *n = vN(Esc);

        return vv(Esc);
}

inline static void
colon(JP *p)
{
        space(p);

        if (peek(p) != ':') {
                FAIL;
        }

        p->s += 1;
}

inline static bool
jmore(JP *p, char close)
{
        space(p);

        char c = peek(p);

        if (c == ',') {
                p->s += 1;
                space(p);
                return peek(p) != close;
        }

        if (c != close) {
                FAIL;
        }

        return false;
}

inline static bool
jopen(JP *p, char c, char close)
{
        if (peek(p) != c) {
                FAIL;
        }

        p->s += 1;
        space(p);

        return peek(p) != close;
}

static void
skipstr(JP *p)
{
        char const *s = p->s + 1;

        for (;;) {
                char const *e = strstop(p, s);
                if (e - s >= 1024) {
                        Memo.s[Memo.n % countof(Memo.s)] = s;
                        Memo.e[Memo.n % countof(Memo.s)] = e;
                        Memo.n += 1;
                }
                if (e == p->end) {
                        p->s = e;
                        FAIL;
                }
                if (*e == '"') {
                        p->s = e + 1;
                        return;
                }
                s = e + 2;
                if (s > p->end) {
                        p->s = p->end;
                        FAIL;
                }
        }
}

static void
skip(JP *p)
{
        int depth = 0;

        space(p);

        switch (peek(p)) {
        case '"':
                skipstr(p);
                return;

        case '{':
        case '[':
                break;

        default:
                if (p->s == p->end || SKIPSTOP[(u8)*p->s]) {
                        FAIL;
                }
                while (p->s < p->end && !SKIPSTOP[(u8)*p->s]) {
                        p->s += 1;
                }
                return;
        }

        while (p->s < p->end) {
                switch (*p->s) {
                case '"':
                        skipstr(p);
                        continue;

                case '{':
                case '[':
                        depth += 1;
                        break;

                case '}':
                case ']':
                        if (--depth == 0) {
                                p->s += 1;
                                return;
                        }
                        break;
                }
                p->s += 1;
        }

        FAIL;
}

static JNode *
plan(Ty *ty, T2Type t);

static void
fill(Ty *ty, JNode *n);

inline static JNode *
force(Ty *ty, JNode *n)
{
        if (UNLIKELY(n->kind == JN_LAZY)) {
                if (n->busy) {
                        return &AnyNode;
                }
                fill(ty, n);
        }

        return n;
}

static JNode *
plan(Ty *ty, T2Type t)
{
        T2Universe const *u = t2_global_universe();

        if (Plans.u != u) {
                xmF(Plans.key);
                xmF(Plans.node);
                memset(&Plans, 0, sizeof Plans);
                Plans.u = u;
        }

        if (Plans.key == NULL || 2 * (Plans.count + 1) > Plans.mask + 1) {
                u32     cap  = (Plans.key == NULL) ? 64 : 2 * (Plans.mask + 1);
                T2Type *key  = xtA0(T2Type, cap);
                JNode **node = xtA0(JNode *, cap);
                for (u32 i = 0; Plans.key != NULL && i <= Plans.mask; ++i) {
                        if (Plans.key[i] != T2_TYPE_INVALID) {
                                u32 j = (Plans.key[i] * 0x9E3779B1u) & (cap - 1);
                                while (key[j] != T2_TYPE_INVALID) {
                                        j = (j + 1) & (cap - 1);
                                }
                                key[j]  = Plans.key[i];
                                node[j] = Plans.node[i];
                        }
                }
                xmF(Plans.key);
                xmF(Plans.node);
                Plans.key  = key;
                Plans.node = node;
                Plans.mask = cap - 1;
        }

        u32 i = (t * 0x9E3779B1u) & Plans.mask;

        while (Plans.key[i] != T2_TYPE_INVALID) {
                if (Plans.key[i] == t) {
                        return Plans.node[i];
                }
                i = (i + 1) & Plans.mask;
        }

        JNode *n = alloc0(sizeof *n);
        n->kind = JN_LAZY;
        n->t2   = t;

        Plans.key[i]   = t;
        Plans.node[i]  = n;
        Plans.count   += 1;

        return n;
}

inline static JNode *
child(Ty *ty, T2Type t, usize i)
{
        T2Type c = t2_type_child(t2_global_universe(), t, i);
        return (c == T2_TYPE_INVALID) ? &AnyNode : plan(ty, c);
}

static void
alias(Ty *ty, JNode *n, T2Type t)
{
        JNode *m = force(ty, plan(ty, t));
        bool busy = n->busy;

        *n = *m;
        n->busy = busy;
}

static T2Type
object_field_type(Ty *ty, T2Type receiver, Class *c, int id)
{
        for (; c != NULL && c->def != NULL; c = c->super) {
                ClassDefinition const *def = &sF(c->def, class);
                for (u32 i = 0; i < vN(def->fields); ++i) {
                        Expr const *field = v__(def->fields, i);
                        if (field->type == EXPRESSION_EQ) {
                                field = xF(field, target);
                        }
                        if (field->type == EXPRESSION_IDENTIFIER && M_ID(xF(field, identifier)) == id) {
                                return t2_member_type(ty, receiver, field->_type);
                        }
                }
                if (def->super != NULL) {
                        receiver = t2_member_type(ty, receiver, t2_resolve_in_class(ty, c, def->super));
                }
        }
        return T2_TYPE_INVALID;
}

static void
fill_object(Ty *ty, JNode *n, T2Type t, int class)
{
        Class *c = class_get(ty, class);

        class_ctor(ty, class);

        u32 nslot = vN(c->fields.ids);

        n->obj.class = class;
        n->obj.c     = c;
        n->obj.nslot = nslot;
        n->obj.raw   = (class_get_finalizer(ty, class).type == VALUE_NONE);
        n->obj.first = 0;
        n->obj.f     = xtA0(JField, nslot + 1);

        for (u32 i = 0; i < nslot; ++i) {
                int id = v__(c->fields.ids, i);
                char const *name = M_NAME(id);
                tadd(&n->obj.keys, name, strlen(name));
                T2Type ft = object_field_type(ty, t, c, id);
                n->obj.f[i].id       = id;
                n->obj.f[i].required = true;
                n->obj.f[i].type     = (ft == T2_TYPE_INVALID) ? &AnyNode : plan(ty, ft);
                n->obj.f[i].next     = i + 1;
        }

        n->kind = JN_OBJECT;
}

static void
fill_record(Ty *ty, JNode *n, T2Type t)
{
        T2Universe *u = t2_global_universe();
        usize nf = t2_record_field_count(u, t);

        n->obj.class = -1;
        n->obj.first = 0;
        n->obj.f     = xtA0(JField, nf + 1);

        for (usize i = 0; i < nf; ++i) {
                T2FieldSpec field;
                if (!t2_record_field(u, t, i, &field) || field.name == NULL) {
                        continue;
                }
                u32 k = n->obj.keys.count;
                if (tadd(&n->obj.keys, field.name, strlen(field.name)) != k) {
                        continue;
                }
                n->obj.f[k].id       = M_ID(field.name);
                n->obj.f[k].required = (field.presence == T2_PRESENCE_REQUIRED);
                n->obj.f[k].type     = (field.type == T2_TYPE_INVALID) ? &AnyNode : plan(ty, field.type);
                n->obj.f[k].next     = k + 1;
        }

        n->kind = JN_RECORD;
}

static void
fill_tuple(Ty *ty, JNode *n, T2Type t, usize typed)
{
        n->tup.typed = typed;
        n->tup.items = xtA0(JNode *, typed + 1);

        for (usize i = 0; i < typed; ++i) {
                n->tup.items[i] = child(ty, t, i);
        }

        n->kind = JN_TUPLE;
}

static void
fill_nominal(Ty *ty, JNode *n, T2Type t)
{
        int class = t2_symbol_class(t2_type_payload(t2_global_universe(), t));

        switch (class) {
        case CLASS_INT:     n->kind = JN_INT;     break;
        case CLASS_FLOAT:   n->kind = JN_FLOAT;   break;
        case CLASS_STRING:  n->kind = JN_STRING;  break;
        case CLASS_BOOL:    n->kind = JN_BOOL;    break;

        case CLASS_ARRAY:
                n->elem = child(ty, t, 0);
                n->kind = JN_ARRAY;
                break;

        case CLASS_DICT:
                n->elem = child(ty, t, 1);
                n->kind = JN_DICT;
                break;

        case CLASS_SET:
                n->elem = child(ty, t, 0);
                n->kind = JN_SET;
                break;

        default:
                if (
                        (class >= 0)
                     && (class_get(ty, class)->def != NULL)
                     && !class_get(ty, class)->is_trait
                ) {
                        fill_object(ty, n, t, class);
                } else {
                        n->kind = JN_ANY;
                }
        }
}

static int
dclass(Ty *ty, JNode *cand, char const *name, u32 len)
{
        if (cand->kind != JN_OBJECT && cand->kind != JN_RECORD) {
                return JD_WILD;
        }

        i32 fi = tfind(&cand->obj.keys, name, len);

        if (fi < 0) {
                return JD_WILD;
        }

        JNode *f = force(ty, cand->obj.f[fi].type);

        switch (f->kind) {
        case JN_LSTR:
                return JD_LIT;

        case JN_UNION:
                if (f->sum->str || f->sum->chk) {
                        return JD_WILD;
                }
                return (f->sum->lits.count > 0) ? JD_LIT : JD_NONE;

        case JN_STRING:
        case JN_ANY:
        case JN_CHECK:
                return JD_WILD;

        default:
                return JD_NONE;
        }
}

static bool
dmatch(Ty *ty, JNode *cand, char const *name, u32 len, char const *lit, u32 n)
{
        JNode *f = force(ty, cand->obj.f[tfind(&cand->obj.keys, name, len)].type);

        if (f->kind == JN_LSTR) {
                return f->lit.n == n && memcmp(f->lit.s, lit, n) == 0;
        }

        return tfind(&f->sum->lits, lit, n) >= 0;
}

static void
fill_disc(Ty *ty, JSum *u)
{
        u32 nc = vN(u->obj);
        i32 best = -1;
        u32 score = 0;

        for (u32 k = 0; k < u->keys.count; ++k) {
                u32 m = 0;
                for (u32 j = 0; j < nc; ++j) {
                        JNode *cand = u->alt[v__(u->obj, j)];
                        if (dclass(ty, cand, u->keys.s[k], u->keys.n[k]) == JD_LIT) {
                                m += 1;
                        }
                }
                if (m > score) {
                        score = m;
                        best  = k;
                }
        }

        u->disc = best;

        if (best < 0) {
                return;
        }

        char const *name = u->keys.s[best];
        u32         len  = u->keys.n[best];
        u8          cls[nc];

        for (u32 j = 0; j < nc; ++j) {
                JNode *cand = u->alt[v__(u->obj, j)];
                cls[j] = dclass(ty, cand, name, len);
                if (cls[j] != JD_LIT) {
                        continue;
                }
                JNode *f = force(ty, cand->obj.f[tfind(&cand->obj.keys, name, len)].type);
                if (f->kind == JN_LSTR) {
                        tadd(&u->dlits, f->lit.s, f->lit.n);
                } else {
                        for (u32 i = 0; i < f->sum->lits.count; ++i) {
                                tadd(&u->dlits, f->sum->lits.s[i], f->sum->lits.n[i]);
                        }
                }
        }

        u->dlist = xtA0(JList, u->dlits.count + 1);

        for (u32 d = 0; d < u->dlits.count; ++d) {
                for (u32 j = 0; j < nc; ++j) {
                        JNode *cand = u->alt[v__(u->obj, j)];
                        if (
                                (cls[j] == JD_WILD)
                             || (
                                        (cls[j] == JD_LIT)
                                     && dmatch(ty, cand, name, len, u->dlits.s[d], u->dlits.n[d])
                                )
                        ) {
                                xvP(u->dlist[d], j);
                        }
                }
        }

        for (u32 j = 0; j < nc; ++j) {
                if (cls[j] == JD_WILD) {
                        xvP(u->dwild, j);
                }
        }
}

static void
fill_filter(Ty *ty, JSum *u)
{
        u32 nc = vN(u->obj);

        for (u32 j = 0; j < nc; ++j) {
                JNode *cand = u->alt[v__(u->obj, j)];
                if (cand->kind == JN_OBJECT || cand->kind == JN_RECORD) {
                        for (u32 i = 0; i < cand->obj.keys.count; ++i) {
                                tadd(&u->keys, cand->obj.keys.s[i], cand->obj.keys.n[i]);
                        }
                }
        }

        u->req = xtA0(u64, nc + 1);

        for (u32 j = 0; j < nc; ++j) {
                JNode *cand = u->alt[v__(u->obj, j)];
                if (cand->kind != JN_OBJECT && cand->kind != JN_RECORD) {
                        continue;
                }
                for (u32 i = 0; i < cand->obj.keys.count; ++i) {
                        if (!cand->obj.f[i].required) {
                                continue;
                        }
                        i32 k = tfind(&u->keys, cand->obj.keys.s[i], cand->obj.keys.n[i]);
                        if (k < 64) {
                                u->req[j] |= 1ull << k;
                        }
                }
                if (u->req[j] != 0) {
                        u->filter = true;
                }
        }
}

static void
fill_union(Ty *ty, JNode *n, T2Type t)
{
        T2Universe *universe = t2_global_universe();
        usize arity = t2_type_arity(universe, t);
        JSum *u = alloc0(sizeof *u);
        vec(JNode *) alts = {0};

        u->disc = -1;

        for (usize i = 0; i < arity; ++i) {
                JNode *a = force(ty, child(ty, t, i));
                if (a->kind == JN_UNION) {
                        xvPn(alts, a->sum->alt, a->sum->n);
                } else {
                        xvP(alts, a);
                }
        }

        u->alt = vv(alts);
        u->n   = vN(alts);

        for (u32 i = 0; i < u->n; ++i) {
                JNode *a = u->alt[i];
                switch (a->kind) {
                case JN_ANY:
                        u->str = true;
                        xvP(u->num, i);
                        xvP(u->sca, i);
                        xvP(u->arr, i);
                        xvP(u->obj, i);
                        break;

                case JN_NIL:
                case JN_BOOL:
                case JN_LBOOL:
                        xvP(u->sca, i);
                        break;

                case JN_INT:
                case JN_FLOAT:
                case JN_LINT:
                        xvP(u->num, i);
                        break;

                case JN_STRING:
                        u->str = true;
                        break;

                case JN_LSTR:
                        tadd(&u->lits, a->lit.s, a->lit.n);
                        break;

                case JN_CHECK:
                        u->chk = true;
                        xvP(u->num, i);
                        xvP(u->sca, i);
                        break;

                case JN_ARRAY:
                case JN_SET:
                case JN_TUPLE:
                        xvP(u->arr, i);
                        break;

                case JN_DICT:
                case JN_RECORD:
                case JN_OBJECT:
                        xvP(u->obj, i);
                        break;
                }
        }

        n->sum  = u;
        n->kind = JN_UNION;

        if (vN(u->obj) > 1) {
                fill_filter(ty, u);
                fill_disc(ty, u);
        }
}

static void
fill(Ty *ty, JNode *n)
{
        T2Universe *u = t2_global_universe();
        T2Type t = t2_type_scheme_body(u, n->t2);
        T2Type r;
        char const *text;

        n->busy = true;

        switch (t2_type_kind(u, t)) {
        case T2_TYPE_NIL:     n->kind = JN_NIL;     break;
        case T2_TYPE_BOOL:    n->kind = JN_BOOL;    break;
        case T2_TYPE_INT:     n->kind = JN_INT;     break;
        case T2_TYPE_FLOAT:   n->kind = JN_FLOAT;   break;
        case T2_TYPE_STRING:  n->kind = JN_STRING;  break;

        case T2_TYPE_LITERAL_STRING:
                text = t2_type_name(u, t);
                n->lit.n = (text == NULL) ? 0 : t2_type_payload(u, t);
                n->lit.s = xmA(n->lit.n + 1);
                if (n->lit.n > 0) {
                        memcpy(n->lit.s, text, n->lit.n);
                }
                n->lit.s[n->lit.n] = '\0';
                n->kind = JN_LSTR;
                break;

        case T2_TYPE_LITERAL_INT:
                n->z    = (i64)t2_type_payload(u, t);
                n->kind = JN_LINT;
                break;

        case T2_TYPE_LITERAL_BOOL:
                n->b    = (t2_type_payload(u, t) != 0);
                n->kind = JN_LBOOL;
                break;

        case T2_TYPE_INT_RANGE:
                n->t2   = t;
                n->kind = JN_CHECK;
                break;

        case T2_TYPE_REFINEMENT:
                alias(ty, n, t2_type_child(u, t, 0));
                break;

        case T2_TYPE_COMPUTED:
                r = t2_type_resolve_computed(u, t);
                if (r == T2_TYPE_INVALID || r == t) {
                        n->kind = JN_ANY;
                } else {
                        alias(ty, n, r);
                }
                break;

        case T2_TYPE_RECURSIVE:
                r = t2_recursive_unfold(u, t);
                if (r == T2_TYPE_INVALID || r == t) {
                        n->kind = JN_ANY;
                } else {
                        alias(ty, n, r);
                }
                break;

        case T2_TYPE_NOMINAL:
                fill_nominal(ty, n, t);
                break;

        case T2_TYPE_RECORD:
                fill_record(ty, n, t);
                break;

        case T2_TYPE_TUPLE:
                fill_tuple(ty, n, t, t2_type_arity(u, t));
                break;

        case T2_TYPE_VARIADIC_TUPLE:
                fill_tuple(ty, n, t, (usize)t2_type_payload(u, t));
                break;

        case T2_TYPE_UNION:
                fill_union(ty, n, t);
                break;

        default:
                n->kind = JN_ANY;
        }

        if (n->kind == JN_LAZY) {
                n->kind = JN_ANY;
        }

        switch (n->kind) {
        case JN_NIL:
        case JN_BOOL:
        case JN_INT:
        case JN_FLOAT:
        case JN_STRING:
        case JN_LSTR:
        case JN_LINT:
        case JN_LBOOL:
                n->flat = true;
                break;

        case JN_UNION:
                n->flat = (vN(n->sum->arr) == 0) && (vN(n->sum->obj) == 0);
                break;

        default:
                n->flat = false;
        }

        n->busy = false;
}

static void
dany(JP *p, Value *out);

static void
dval(JP *p, JNode *n, Value *out);

inline static bool
flat(JP *p, JNode *n)
{
        if (n->kind == JN_ANY) {
                space(p);
                return peek(p) != '[' && peek(p) != '{';
        }

        return n->flat;
}

[[gnu::always_inline]] inline static void
dfast(JP *p, JNode *n, Value *out)
{
        char const *s;
        char const *e;

        space(p);

        switch (n->kind) {
        case JN_INT:
                s = p->s;
                number(p, out);
                if (out->type != VALUE_INTEGER) {
                        Fail(p, s);
                }
                return;

        case JN_FLOAT:
                number(p, out);
                if (out->type == VALUE_INTEGER) {
                        *out = REAL((double)out->z);
                }
                return;

        case JN_STRING:
                s = p->s + 1;
                if (peek(p) == '"') {
                        e = strstop(p, s);
                        if (e < p->end && *e == '"') {
                                p->s = e + 1;
                                mkstr(p, s, e - s, out);
                                return;
                        }
                }
                break;

        case JN_BOOL:
                jbool(p, out);
                return;
        }

        dval(p, n, out);
}

[[gnu::always_inline]] inline static void
dslot(JP *p, JNode *n)
{
        Value v;

        if (flat(p, n)) {
                if (UNLIKELY(Stk.n == Stk.cap)) {
                        sgrow();
                }
                dfast(p, n, &Stk.v[Stk.n]);
                Stk.n += 1;
        } else {
                dval(p, n, &v);
                spush(v);
        }
}

static void
darr(JP *p, JNode *elem, Value *out)
{
        Ty *ty = p->ty;
        u32 base = Stk.n;

        elem = force(ty, elem);

        if (jopen(p, '[', ']')) {
                do {
                        dslot(p, elem);
                } while (jmore(p, ']'));
        }

        p->s += 1;

        u32 n = Stk.n - base;
        Array *a = mAo(sizeof (Array), GC_ARRAY);

        a->count    = n;
        a->capacity = n;
        a->items    = NULL;

        if (n > 0) {
                a->items = mA(n * sizeof (Value));
                memcpy(a->items, Stk.v + base, n * sizeof (Value));
        }

        Stk.n = base;

        *out = ARRAY(a);
}

static void
dset(JP *p, JNode *elem, Value *out)
{
        Ty *ty = p->ty;
        Set *s = set_new(ty);
        Value v;

        if (jopen(p, '[', ']')) {
                do {
                        dval(p, elem, &v);
                        set_add(ty, s, v);
                } while (jmore(p, ']'));
        }

        p->s += 1;

        *out = SET(s);
}

static void
ddict(JP *p, JNode *elem, Value *out)
{
        Ty *ty = p->ty;
        Dict *d = dict_new(ty);
        Value key;
        Value val;

        if (jopen(p, '{', '}')) {
                do {
                        dstr(p, &key);
                        colon(p);
                        dval(p, elem, &val);
                        dict_put_value(ty, d, key, val);
                } while (jmore(p, '}'));
        }

        p->s += 1;

        *out = DICT(d);
}

static void
dtup(JP *p, JNode *n, Value *out)
{
        Ty *ty = p->ty;
        u32 base = Stk.n;
        u32 typed = n->tup.typed;

        if (jopen(p, '[', ']')) {
                do {
                        u32 i = Stk.n - base;
                        dslot(p, (i < typed) ? n->tup.items[i] : &AnyNode);
                } while (jmore(p, ']'));
        }

        char const *close = p->s;
        u32 count = Stk.n - base;

        p->s += 1;

        if (count < typed) {
                Fail(p, close);
        }

        Value tuple = vT(count);

        memcpy(tuple.items, Stk.v + base, count * sizeof (Value));

        Stk.n = base;

        *out = tuple;
}

inline static bool
keq(char const *k, char const *name, u32 n, char const *end)
{
        u64 a;
        u64 b;

        if (n <= 8 && end - k >= 8) {
                memcpy(&a, k, 8);
                memcpy(&b, name, 8);
                return n == 0 || ((a ^ b) << (64 - 8 * n)) == 0;
        }

        if (n <= 16 && n > 8) {
                u64 c;
                u64 d;
                memcpy(&a, k, 8);
                memcpy(&b, name, 8);
                memcpy(&c, k + n - 8, 8);
                memcpy(&d, name + n - 8, 8);
                return ((a ^ b) | (c ^ d)) == 0;
        }

        return memcmp(k, name, n) == 0;
}

[[gnu::always_inline]] inline static i32
dkey(JP *p, JNode *n, u32 want, char const **k, u32 *kn)
{
        JTab const *keys = &n->obj.keys;

        if (want < keys->count) {
                u32 wn = keys->n[want];
                char const *ks = p->s + 1;
                if (
                        (p->end - ks > wn)
                     && (*p->s == '"')
                     && (ks[wn] == '"')
                     && keq(ks, keys->s[want], wn, p->end)
                ) {
                        p->s = ks + wn + 1;
                        return want;
                }
        }

        *k = dspan(p, kn);

        return tfind(keys, *k, *kn);
}

inline static void
dlearn(JNode *n, i32 prev, i32 fi)
{
        if (prev < 0) {
                n->obj.first = fi;
        } else {
                n->obj.f[prev].next = fi;
        }
}

static void
drec(JP *p, JNode *n, Value *out)
{
        Ty *ty = p->ty;
        u32 base = Stk.n;
        u32 nf = n->obj.keys.count;
        u64 seen[(nf + 63) / 64 + 1];
        u32 want = n->obj.first;
        i32 prev = -1;
        u32 kn;

        memset(seen, 0, sizeof seen);

        if (jopen(p, '{', '}')) {
                do {
                        char const *k = NULL;
                        i32 fi = dkey(p, n, want, &k, &kn);
                        if (fi >= 0) {
                                colon(p);
                                spush(INTEGER(n->obj.f[fi].id));
                                dslot(p, n->obj.f[fi].type);
                                seen[fi >> 6] |= 1ull << (fi & 63);
                                if (want != (u32)fi) {
                                        dlearn(n, prev, fi);
                                }
                                prev = fi;
                                want = n->obj.f[fi].next;
                        } else {
                                spush(INTEGER(keyid(k, kn)));
                                colon(p);
                                dslot(p, &AnyNode);
                        }
                } while (jmore(p, '}'));
        }

        char const *close = p->s;

        p->s += 1;

        for (u32 i = 0; i < nf; ++i) {
                if (n->obj.f[i].required && !(seen[i >> 6] & (1ull << (i & 63)))) {
                        Fail(p, close);
                }
        }

        u32 count = (Stk.n - base) / 2;
        Value record = value_record(ty, count);

        for (u32 i = 0; i < count; ++i) {
                record.ids[i]   = Stk.v[base + 2 * i].z;
                record.items[i] = Stk.v[base + 2 * i + 1];
        }

        Stk.n = base;

        *out = record;
}

static void
dobj(JP *p, JNode *n, Value *out)
{
        Ty *ty = p->ty;
        u32 nf = n->obj.keys.count;
        u64 seen[(nf + 63) / 64 + 1];
        u32 want = n->obj.first;
        i32 prev = -1;
        TyObject *o;
        Value v;
        u32 kn;

        if (peek(p) != '{') {
                FAIL;
        }

        memset(seen, 0, sizeof seen);

        if (n->obj.raw) {
                o = mAo(sizeof (TyObject) + n->obj.nslot * sizeof (Value), GC_OBJECT);
                o->init      = false;
                o->finalized = false;
                o->class     = n->obj.c;
                o->dynamic   = NULL;
                o->nslot     = n->obj.nslot;
        } else {
                o = class_new_instance(ty, n->obj.class);
        }

        if (jopen(p, '{', '}')) {
                do {
                        char const *k = NULL;
                        i32 fi = dkey(p, n, want, &k, &kn);
                        if (fi >= 0) {
                                colon(p);
                                dfast(p, n->obj.f[fi].type, &o->slots[fi]);
                                seen[fi >> 6] |= 1ull << (fi & 63);
                                if (want != (u32)fi) {
                                        dlearn(n, prev, fi);
                                }
                                prev = fi;
                                want = n->obj.f[fi].next;
                        } else {
                                i32 id = keyid(k, kn);
                                colon(p);
                                dany(p, &v);
                                if (o->dynamic == NULL) {
                                        o->dynamic = mA0(sizeof (struct itable));
                                }
                                itable_add(ty, o->dynamic, id, v);
                        }
                } while (jmore(p, '}'));
        }

        char const *close = p->s;

        p->s += 1;

        for (u32 i = 0; i < nf / 64; ++i) {
                if (seen[i] != UINT64_MAX) {
                        Fail(p, close);
                }
        }

        if ((nf & 63) != 0 && seen[nf / 64] != (1ull << (nf & 63)) - 1) {
                Fail(p, close);
        }

        o->init = true;

        *out = OBJECT(o, n->obj.class);
}

static void
prescan(JP *p, JSum *u, JScan *out)
{
        char const *save = p->s;
        u32 kn;

        out->mask  = 0;
        out->dlist = JS_UNSEEN;
        out->dpos  = NULL;

        if (jopen(p, '{', '}')) {
                do {
                        char const *k = dspan(p, &kn);
                        i32 ki = tfind(&u->keys, k, kn);
                        colon(p);
                        space(p);
                        if (ki >= 0 && ki < 64) {
                                out->mask |= 1ull << ki;
                        }
                        if (ki >= 0 && ki == u->disc && peek(p) == '"') {
                                out->dpos = p->s;
                                k = dspan(p, &kn);
                                i32 d = tfind(&u->dlits, k, kn);
                                out->dlist = (d >= 0) ? d : JS_WILD;
                        } else {
                                skip(p);
                        }
                } while (jmore(p, '}'));
        }

        out->close = p->s;
        p->s = save;
}

static i32
dpeek(JP *p, JSum *u, char const **dpos)
{
        char const *save = p->s;
        i32 r = JS_UNSEEN;
        u32 kn;

        p->s += 1;
        space(p);

        if (peek(p) == '"') {
                char const *k = dspan(p, &kn);
                if (tfind(&u->keys, k, kn) == u->disc) {
                        colon(p);
                        space(p);
                        if (peek(p) == '"') {
                                *dpos = p->s;
                                k = dspan(p, &kn);
                                i32 d = tfind(&u->dlits, k, kn);
                                r = (d >= 0) ? d : JS_WILD;
                        }
                }
        }

        p->s = save;

        return r;
}

static void
speculate(JP *p, JSum *u, u16 const *cand, u32 nc, u16 const *map, Value *out)
{
        char const *start = p->s;
        jmp_buf *saved = p->jb;
        u32 sp = Stk.n;
        jmp_buf jb;

        for (u32 volatile i = 0; i + 1 < nc; ++i) {
                p->s  = start;
                p->jb = &jb;
                if (setjmp(jb) == 0) {
                        dval(p, u->alt[(map != NULL) ? map[cand[i]] : cand[i]], out);
                        p->jb = saved;
                        return;
                }
                p->jb = saved;
                Stk.n = sp;
        }

        p->s = start;

        dval(p, u->alt[(map != NULL) ? map[cand[nc - 1]] : cand[nc - 1]], out);
}

static void
dunion_obj(JP *p, JSum *u, Value *out)
{
        u32 nc = vN(u->obj);
        u16 const *cand = NULL;
        u16 pick[nc + 1];
        bool scanned = false;
        bool hit = false;
        char const *dpos = NULL;
        JScan scan;
        i32 d = JS_UNSEEN;

        if (nc == 1) {
                dval(p, u->alt[v__(u->obj, 0)], out);
                return;
        }

        if (u->disc >= 0) {
                d = dpeek(p, u, &dpos);
                if (d == JS_UNSEEN) {
                        prescan(p, u, &scan);
                        scanned = true;
                        d    = scan.dlist;
                        dpos = scan.dpos;
                }
        }

        if (d >= 0) {
                cand = vv(u->dlist[d]);
                nc   = vN(u->dlist[d]);
                hit  = true;
        } else if (d == JS_WILD) {
                cand = vv(u->dwild);
                nc   = vN(u->dwild);
        } else {
                for (u32 j = 0; j < nc; ++j) {
                        pick[j] = j;
                }
                cand = pick;
        }

        if (!hit && nc > 1 && u->filter) {
                if (!scanned) {
                        prescan(p, u, &scan);
                        scanned = true;
                }
                u32 m = 0;
                for (u32 j = 0; j < nc; ++j) {
                        if ((u->req[cand[j]] & ~scan.mask) == 0) {
                                pick[m++] = cand[j];
                        }
                }
                cand = pick;
                nc   = m;
        }

        if (nc == 0 && dpos != NULL) {
                Fail(p, dpos);
        }

        if (nc == 0) {
                if (!scanned) {
                        prescan(p, u, &scan);
                }
                Fail(p, scan.close);
        }

        speculate(p, u, cand, nc, vv(u->obj), out);
}

static void
dunion(JP *p, JSum *u, Value *out)
{
        Ty *ty = p->ty;
        char const *start = p->s;
        u32 kn;

        switch (peek(p)) {
        case '"':
                if (u->str) {
                        dstr(p, out);
                        return;
                }
                if (u->lits.count > 0) {
                        char const *k = dspan(p, &kn);
                        i32 i = tfind(&u->lits, k, kn);
                        if (i >= 0) {
                                *out = (kn == 0) ? STRING_NOGC(NULL, 0) : STRING_NOGC(u->lits.s[i], kn);
                                return;
                        }
                        p->s = start;
                }
                if (u->chk) {
                        dstr(p, out);
                        for (u32 i = 0; i < u->n; ++i) {
                                if (u->alt[i]->kind == JN_CHECK && t2_check(ty, u->alt[i]->t2, out)) {
                                        return;
                                }
                        }
                }
                Fail(p, start);

        case '{':
                if (vN(u->obj) == 0) {
                        FAIL;
                }
                dunion_obj(p, u, out);
                return;

        case '[':
                if (vN(u->arr) == 0) {
                        FAIL;
                }
                speculate(p, u, vv(u->arr), vN(u->arr), NULL, out);
                return;

        case 't':
        case 'f':
        case 'n':
                if (vN(u->sca) == 0) {
                        FAIL;
                }
                if (peek(p) == 'n') {
                        jnull(p, out);
                } else {
                        jbool(p, out);
                }
                for (u32 i = 0; i < vN(u->sca); ++i) {
                        JNode *a = u->alt[v__(u->sca, i)];
                        switch (a->kind) {
                        case JN_ANY:
                                return;

                        case JN_NIL:
                                if (out->type == VALUE_NIL) {
                                        return;
                                }
                                break;

                        case JN_BOOL:
                                if (out->type == VALUE_BOOLEAN) {
                                        return;
                                }
                                break;

                        case JN_LBOOL:
                                if (out->type == VALUE_BOOLEAN && out->boolean == a->b) {
                                        return;
                                }
                                break;

                        case JN_CHECK:
                                if (t2_check(ty, a->t2, out)) {
                                        return;
                                }
                                break;
                        }
                }
                Fail(p, start);

        default:
                if (vN(u->num) == 0) {
                        FAIL;
                }
                number(p, out);
                for (u32 i = 0; i < vN(u->num); ++i) {
                        JNode *a = u->alt[v__(u->num, i)];
                        switch (a->kind) {
                        case JN_ANY:
                                return;

                        case JN_INT:
                                if (out->type == VALUE_INTEGER) {
                                        return;
                                }
                                break;

                        case JN_FLOAT:
                                if (out->type == VALUE_INTEGER) {
                                        *out = REAL((double)out->z);
                                }
                                return;

                        case JN_LINT:
                                if (out->type == VALUE_INTEGER && out->z == a->z) {
                                        return;
                                }
                                break;

                        case JN_CHECK:
                                if (t2_check(ty, a->t2, out)) {
                                        return;
                                }
                                break;
                        }
                }
                Fail(p, start);
        }
}

static void
dval(JP *p, JNode *n, Value *out)
{
        Ty *ty = p->ty;
        char const *start;
        u32 kn;

        space(p);

        start = p->s;

        switch (n->kind) {
        case JN_LAZY:
                dval(p, force(ty, n), out);
                return;

        case JN_ANY:
                dany(p, out);
                return;

        case JN_NIL:
                jnull(p, out);
                return;

        case JN_BOOL:
                jbool(p, out);
                return;

        case JN_INT:
                number(p, out);
                if (out->type != VALUE_INTEGER) {
                        Fail(p, start);
                }
                return;

        case JN_FLOAT:
                number(p, out);
                if (out->type == VALUE_INTEGER) {
                        *out = REAL((double)out->z);
                }
                return;

        case JN_STRING:
                dstr(p, out);
                return;

        case JN_LSTR:
        {
                char const *k = dspan(p, &kn);
                if (kn != n->lit.n || memcmp(k, n->lit.s, kn) != 0) {
                        Fail(p, start);
                }
                *out = (kn == 0) ? STRING_NOGC(NULL, 0) : STRING_NOGC(n->lit.s, kn);
                return;
        }

        case JN_LINT:
                number(p, out);
                if (out->type != VALUE_INTEGER || out->z != n->z) {
                        Fail(p, start);
                }
                return;

        case JN_LBOOL:
                jbool(p, out);
                if (out->boolean != n->b) {
                        Fail(p, start);
                }
                return;

        case JN_CHECK:
                dany(p, out);
                if (!t2_check(ty, n->t2, out)) {
                        Fail(p, start);
                }
                return;

        case JN_ARRAY:
                darr(p, n->elem, out);
                return;

        case JN_SET:
                dset(p, n->elem, out);
                return;

        case JN_DICT:
                ddict(p, n->elem, out);
                return;

        case JN_TUPLE:
                dtup(p, n, out);
                return;

        case JN_RECORD:
                drec(p, n, out);
                return;

        case JN_OBJECT:
                dobj(p, n, out);
                return;

        case JN_UNION:
                dunion(p, n->sum, out);
                return;
        }

        UNREACHABLE();
}

static void
dobj_dict(JP *p, Value *out)
{
        Ty *ty = p->ty;
        u32 base = Stk.n;

        if (jopen(p, '{', '}')) {
                do {
                        if (UNLIKELY(Stk.n == Stk.cap)) {
                                sgrow();
                        }
                        dstr(p, &Stk.v[Stk.n]);
                        Stk.n += 1;
                        colon(p);
                        dslot(p, &AnyNode);
                } while (jmore(p, '}'));
        }

        p->s += 1;

        u32 count = (Stk.n - base) / 2;
        Dict *d = dict_new_sized(ty, count);

        for (u32 i = 0; i < count; ++i) {
                dict_put_value(ty, d, Stk.v[base + 2 * i], Stk.v[base + 2 * i + 1]);
        }

        Stk.n = base;

        *out = DICT(d);
}

static void
dobj_xd(JP *p, Value *out)
{
        Ty *ty = p->ty;
        u32 base = Stk.n;
        i32 prev = -1;
        u32 kn;

        if (jopen(p, '{', '}')) {
                do {
                        u32 hint = (u32)(prev + 1) & (countof(KeyNext) - 1);
                        u32 slot = KeyNext[hint].slot;
                        u32 wn = KeyCache[slot].n;
                        char const *ks = p->s + 1;
                        i32 id;
                        if (
                                (KeyCache[slot].s != NULL)
                             && (KeyCache[slot].id == KeyNext[hint].id)
                             && (p->end - ks > wn)
                             && (*p->s == '"')
                             && (ks[wn] == '"')
                             && keq(ks, KeyCache[slot].s, wn, p->end)
                        ) {
                                p->s = ks + wn + 1;
                                id = KeyNext[hint].id;
                        } else {
                                char const *k = dspan(p, &kn);
                                slot = keyslot(k, kn);
                                id = KeyCache[slot].id;
                                KeyNext[hint].slot = slot;
                                KeyNext[hint].id   = id;
                        }
                        spush(INTEGER(id));
                        colon(p);
                        dslot(p, &AnyNode);
                        prev = id;
                } while (jmore(p, '}'));
        }

        p->s += 1;

        u32 count = (Stk.n - base) / 2;
        Value record = value_record(ty, count);

        for (u32 i = 0; i < count; ++i) {
                record.ids[i]   = Stk.v[base + 2 * i].z;
                record.items[i] = Stk.v[base + 2 * i + 1];
        }

        Stk.n = base;

        *out = record;
}

static void
dany(JP *p, Value *out)
{
        space(p);

        switch (peek(p)) {
        case '{':
                if (p->xd) {
                        dobj_xd(p, out);
                } else {
                        dobj_dict(p, out);
                }
                return;

        case '[':
                darr(p, &AnyNode, out);
                return;

        case '"':
                dstr(p, out);
                return;

        case 'n':
                jnull(p, out);
                return;

        case 't':
        case 'f':
                jbool(p, out);
                return;

        case '-': case '0': case '1': case '2': case '3': case '4':
        case '5': case '6': case '7': case '8': case '9':
                number(p, out);
                return;

        default:
                FAIL;
        }
}

static noreturn void
Throw(Ty *ty, Value const *input, usize offset, char const *reason)
{
        GC_STOP();

        Value exc = NewInstance(
                CLASS_JSON_ERROR,
                (input->type == VALUE_BLOB) ? vSs(vv(*input->blob), vN(*input->blob)) : *input,
                INTEGER(offset),
                (reason != NULL) ? vSsz(reason) : NIL
        );

        GC_RESUME();

        vmE(&exc);
}

static noreturn void
ThrowTyped(Ty *ty, Value const *input, usize offset, char const *fmt, T2Type t0)
{
        char *shown = t2_show(ty, t0);
        char *reason = afmt(fmt, shown);

        t2_string_free(shown);

        Throw(ty, input, offset, reason);
}

static Value
parse(Ty *ty, Value const *input, T2Type t0, bool records)
{
        JP p = {0};
        jmp_buf jb;

        switch (input->type) {
        case VALUE_STRING:
                p.start = (char const *)ss(*input);
                p.end   = p.start + sN(*input);
                p.view  = true;
                break;

        case VALUE_BLOB:
                p.start = (char const *)vv(*input->blob);
                p.end   = p.start + vN(*input->blob);
                p.view  = false;
                break;

        default:
                UNREACHABLE();
        }

        p.ty       = ty;
        p.s        = p.start;
        p.input    = input;
        p.xd       = records;
        p.jb       = &jb;

        Furthest = p.start;
        Memo.n   = 0;

        JNode *root = (t0 == T2_TYPE_INVALID) ? NULL : plan(ty, t0);
        u32 sp = Stk.n;

        ScratchSave scratch = SaveScratch(ty);

        GC_STOP();

        if (setjmp(jb) != 0) {
                GC_RESUME();
                RestoreScratch(ty, scratch);
                Stk.n = sp;
                if (t0 == T2_TYPE_INVALID) {
                        Throw(ty, input, Furthest - p.start, NULL);
                } else {
                        ThrowTyped(ty, input, Furthest - p.start, "failed to parse JSON as %s", t0);
                }
        }

        Value v;

        if (root == NULL) {
                dany(&p, &v);
        } else {
                dval(&p, root, &v);
        }

        space(&p);

        GC_RESUME();
        RestoreScratch(ty, scratch);

        if (p.s == p.end) {
                return v;
        }

        if (t0 == T2_TYPE_INVALID) {
                Throw(ty, input, p.s - p.start, "unexpected trailing data");
        }

        ThrowTyped(ty, input, p.s - p.start, "unexpected trailing data after parsing %s", t0);
}

Value
json_parse(Ty *ty, Value const *input)
{
        return parse(ty, input, T2_TYPE_INVALID, false);
}

Value
json_parse_xD(Ty *ty, Value const *input)
{
        return parse(ty, input, T2_TYPE_INVALID, true);
}

Value
json_parse_typed(Ty *ty, T2Type t0, Value const *input)
{
        return parse(ty, input, t0, true);
}

Value
json_encode(Ty *ty, Value const *v)
{
        str buf = {0};
        Value r = NIL;

        v0(Visiting);

        if (encode(ty, v, &buf)) {
                r = vSs(vv(buf), vN(buf));
                xvF(buf);
        }

        return r;
}


bool
json_dump(Ty *ty, Value const  *v, byte_vector *out)
{
        Visiting.count = 0;

        usize start = vN(*out);

        if (!encode(ty, v, out)) {
                out->count = start;
                return false;
        }

        return true;
}
