#include <limits.h>

#include "ty.h"
#include "blob.h"
#include "dict.h"
#include "str.h"
#include "value.h"
#include "vm.h"
#include "xd.h"
#include "ty.h"
#include "mmmm.h"

static Value
blob_clear(Ty *ty, Value *blob, int argc, Value *kwargs)
{
        ASSERT_ARGC("Blob.clear()", 0, 1, 2);

        isize start;
        isize n;

        switch (argc) {
        case 0:
                start = 0;
                n = vN(*blob->blob);
                break;

        case 1:
                start = INT_ARG(0);
                if (start < 0) {
                        start += vN(*blob->blob);
                }
                n = vN(*blob->blob) - start;
                break;

        case 2:
                start = INT_ARG(0);
                if (start < 0) {
                        start += vN(*blob->blob);
                }
                n = INT_ARG(1);
                break;
        }

        if (
                (start < 0)
             || (n < 0)
             || ((n + start) > vN(*blob->blob))
        ) {
                bP(
                        "invalid argument(s): start=%s, n=%s (size=%zu)",
                        (argc >= 1) ? SHOW(&ARG(0)) : "nil",
                        (argc >= 2) ? SHOW(&ARG(1)) : "nil",
                        vN(*blob->blob)
                );
        }

        memmove(
                vv(*blob->blob) + start,
                vv(*blob->blob) + start + n,
                vN(*blob->blob) - start - n
        );

        vN(*blob->blob) -= n;

        return *blob;
}

static Value
blob_search(Ty *ty, Value *blob, int argc, Value *kwargs)
{
        ASSERT_ARGC("Blob.search()", 1, 2);

        isize start;
        Value c;

        switch (argc) {
        case 1:
                start = 0;
                c = ARGx(0, VALUE_STRING, VALUE_BLOB, VALUE_INTEGER);
                break;

        case 2:
                start = INT_ARG(0);
                c = ARGx(1, VALUE_STRING, VALUE_BLOB, VALUE_INTEGER);
                break;
        }

        if (vN(*blob->blob) == 0) {
                return NIL;
        }

        isize n = vN(*blob->blob) - start;
        char const *haystack = (char const *)v_(*blob->blob, start);

        char const *s;

        switch (c.type) {
        case VALUE_STRING:
                s = mmmm(haystack, n, ss(c), sN(c));
                break;

        case VALUE_BLOB:
                s = mmmm(haystack, n, (char *)c.blob->items, c.blob->count);
                break;

        case VALUE_INTEGER:
                if (c.z < 0 || c.z > UCHAR_MAX)
                        zP("invalid integer passed to blob.search()");
                s = memchr(haystack, c.z, n);
                break;
        }

        return (s == NULL) ? NIL : INTEGER(s - haystack + start);
}

static Value
blob_searchr(Ty *ty, Value *blob, int argc, Value *kwargs)
{
        ASSERT_ARGC("Blob.searchr()", 1, 2);

        isize end;
        Value c;

        switch (argc) {
        case 1:
                end = vN(*blob->blob);
                c = ARGx(0, VALUE_STRING, VALUE_BLOB, VALUE_INTEGER);
                break;

        case 2:
                end = INT_ARG(0);
                c = ARGx(1, VALUE_STRING, VALUE_BLOB, VALUE_INTEGER);
                break;
        }

        if (end <= 0 || vN(*blob->blob) == 0) {
                return NIL;
        }

        if (end > vN(*blob->blob)) {
                end = vN(*blob->blob);
        }

        char const *haystack = (char const *)v_(*blob->blob, 0);

        char const *s;
        u8 byte;

        switch (c.type) {
        case VALUE_STRING:
                s = (char const *)mmmmr((u8 const *)haystack, end, (u8 const *)ss(c), sN(c));
                break;

        case VALUE_BLOB:
                s = (char const *)mmmmr((u8 const *)haystack, end, (u8 const *)c.blob->items, c.blob->count);
                break;

        case VALUE_INTEGER:
                if (c.z < 0 || c.z > UCHAR_MAX) {
                        bP("bad needle: %s", VSC(&c));
                }
                byte = c.z;
                s = (char const *)mmmmr((u8 const *)haystack, end, &byte, 1);
                break;
        }

        return (s == NULL) ? NIL : INTEGER(s - haystack);
}

static Value
blob_shrink(Ty *ty, Value *blob, int argc, Value *kwargs)
{
        mRE(blob->blob->items, vN(*blob->blob));
        blob->blob->capacity = vN(*blob->blob);
        return NIL;
}

Value
blob_push(Ty *ty, Value *blob, int argc, Value *kwargs)
{
        ASSERT_ARGC("Blob.push()", 1, 2, 3);

        isize index;
        Value arg;

        if (argc >= 2 && ARG_T(0) != VALUE_PTR) {
                index = INT_ARG(0);
                arg = ARG(1);
        } else {
                index = vN(*blob->blob);
                arg = ARG(0);
        }

        switch (arg.type) {
        case VALUE_INTEGER:
                if (arg.z < 0 || arg.z > UCHAR_MAX) {
                        bP("not an octet: %s", VSC(&arg));
                }
                vvI(*blob->blob, arg.z, index);
                break;

        case VALUE_BLOB:
                vvIn(*blob->blob, arg.blob->items, arg.blob->count, index);
                break;

        case VALUE_STRING:
                vvIn(*blob->blob, ss(arg), sN(arg), index);
                break;

        case VALUE_PTR:
                vvIn(*blob->blob, arg.ptr, INT_ARG(argc - 1), index);
                break;

        default:
                ARGx(!!argc, VALUE_INTEGER, VALUE_STRING, VALUE_BLOB, VALUE_PTR);
        }

        return *blob;
}

static Value
blob_size(Ty *ty, Value *blob, int argc, Value *kwargs)
{
        return INTEGER(vN(*blob->blob));
}

Value
blob_get(Ty *ty, Value *blob, int argc, Value *kwargs)
{
        ASSERT_ARGC("Blob.get()", 1);

        isize i = INT_ARG(0);
        if (i < 0) {
                i += vN(*blob->blob);
        }
        if (i < 0 || i >= vN(*blob->blob)) {
                bP("out of range: %zd", i);
        }

        return INTEGER(v__(*blob->blob, i));
}

static Value
blob_fill(Ty *ty, Value *blob, int argc, Value *kwargs)
{
        ASSERT_ARGC("Blob.fill()", 0);

        if (vv(*blob->blob) == NULL) {
                return NIL;
        }

        memset(
                vv(*blob->blob) + vN(*blob->blob),
                0,
                vC(*blob->blob) - vN(*blob->blob)
        );

        vN(*blob->blob) = blob->blob->capacity;

        return *blob;
}

static Value
blob_xor(Ty *ty, Value *blob, int argc, Value *kwargs)
{
        ASSERT_ARGC("Blob.xor()", 1, 2);

        if (argc == 1 && ARG_T(0) == VALUE_BLOB) {
                Blob *b = ARG(0).blob;
                if (vN(*b) > 0) {
                        for (usize i = 0; i < vN(*blob->blob); ++i) {
                                *v_(*blob->blob, i) ^= v__(*b, i % vN(*b));
                        }
                }
                return *blob;
        }

        if (argc != 2) {
                zP("blob.xor(): expected 2 arguments but got %d", argc);
        }

        (void)INT_ARG(0);
        u8 size = INT_ARG(1);

        u8  _u8;
        u16 _u16, *pu16;
        u32 _u32, *pu32;
        u64 _u64, *pu64;

        u8 r;

        switch (size) {
        case 1:
                _u8 = ARG(0).z;
                for (usize i = 0; i < vN(*blob->blob); ++i) {
                        *v_(*blob->blob, i) ^= _u8;
                }
                break;

        case 2:
                _u16 = ARG(0).z;
                pu16 = (void *)vv(*blob->blob);
                for (usize i = 0; i < vN(*blob->blob) / 2; ++i) {
                        pu16[i] ^= _u16;
                }
                r =  vN(*blob->blob) % 2;
                for (u8 i = 0; i < r; ++i) {
                        *v_(*blob->blob, vN(*blob->blob) - r + i) ^= ((_u16 >> (8 * i)) & 0xFF);
                }
                break;

        case 4:
                _u32 = ARG(0).z;
                pu32 = (void *)vv(*blob->blob);
                for (usize i = 0; i < vN(*blob->blob) / 4; ++i) {
                        pu32[i] ^= _u32;
                }
                r =  vN(*blob->blob) % 4;
                for (u8 i = 0; i < r; ++i) {
                        *v_(*blob->blob, vN(*blob->blob) - r + i) ^= ((_u32 >> (8 * i)) & 0xFF);
                }
                break;

        case 8:
                _u64 = ARG(0).z;
                pu64 = (void *)vv(*blob->blob);
                for (usize i = 0; i < vN(*blob->blob) / 8; ++i) {
                        pu64[i] ^= _u64;
                }
                r =  vN(*blob->blob) % 8;
                for (u8 i = 0; i < r; ++i) {
                        *v_(*blob->blob, vN(*blob->blob) - r + i) ^= ((_u64 >> (8 * i)) & 0xFF);
                }
                break;

        default:
                bP("invalid mask size: %hhu", size);
        }

        return *blob;
}


static void
blobspan(Ty *ty, Value *blob, int argc, char const *name, isize *pstart, isize *pn)
{
        ASSERT_ARGC(name, 0, 1, 2);

        isize start;
        isize n;

        switch (argc) {
        case 0:
                start = 0;
                n = vN(*blob->blob);
                break;

        case 1:
                start = INT_ARG(0);
                n = INT_MAX;
                break;

        case 2:
                start = INT_ARG(0);
                n = INT_ARG(1);
                break;
        }

        if (start < 0) {
                start += vN(*blob->blob);
        }

        n = max(0, min(n, vN(*blob->blob) - start));

        if (start < 0 || (n + start) > vN(*blob->blob)) {
                bP("invalid argument(s): start=%zd, n=%zd, size=%zu", start, n, vN(*blob->blob));
        }

        *pstart = start;
        *pn     = n;
}

static noreturn void
badutf8(Ty *ty, char const *name)
{
        Value exc = NewInstance(
                CLASS_VALUE_ERROR,
                xSz(name)
        );
        vmE(&exc);
}

Value
LossyString(Ty *ty, u8 const *s, isize n)
{
        u8 *str = value_string_alloc(ty, 3 * n);
        isize i = 0;
        isize j = 0;
        int st;

        while (i < n) {
                isize v = utf8valid(s + i, n - i);
                memcpy(str + j, s + i, v);
                i += v;
                j += v;
                if (i < n) {
                        i += utf8seq(s + i, n - i, &st);
                        str[j++] = 0xEF;
                        str[j++] = 0xBF;
                        str[j++] = 0xBD;
                }
        }

        return STRING(str, j);
}

static Value
blob_str(Ty *ty, Value *blob, int argc, Value *kwargs)
{
        char const *_name__ = "Blob.str()";
        isize start;
        isize n;

        Value lossy = KWARG("lossy", BOOLEAN);

        blobspan(ty, blob, argc, _name__, &start, &n);

        u8 const *s = vv(*blob->blob) + start;

        if (utf8ok(s, n)) {
                return vSs((char const *)s, n);
        }

        if (!IsNone(lossy) && lossy.boolean) {
                return LossyString(ty, s, n);
        }

        badutf8(ty, "Blob.str(): invalid UTF-8");
}

static Value
blob_is_utf8(Ty *ty, Value *blob, int argc, Value *kwargs)
{
        isize start;
        isize n;

        blobspan(ty, blob, argc, "Blob.utf8?()", &start, &n);

        return BOOLEAN(utf8ok(vv(*blob->blob) + start, n));
}

static Value
blob_utf8_valid(Ty *ty, Value *blob, int argc, Value *kwargs)
{
        isize start;
        isize n;

        blobspan(ty, blob, argc, "Blob.utf8-valid()", &start, &n);

        return INTEGER(utf8valid(vv(*blob->blob) + start, n));
}

static Value
blob_utf8_tail(Ty *ty, Value *blob, int argc, Value *kwargs)
{
        isize start;
        isize n;

        blobspan(ty, blob, argc, "Blob.utf8-tail()", &start, &n);

        return INTEGER(utf8tail(vv(*blob->blob) + start, n));
}

static Value
blob_take_str(Ty *ty, Value *blob, int argc, Value *kwargs)
{
        ASSERT_ARGC("Blob.take-str!()", 0);

        u8 const *s = vv(*blob->blob);
        isize n = vN(*blob->blob);
        isize v = utf8valid(s, n);
        int st;

        if (v < n) {
                utf8seq(s + v, n - v, &st);
                if (st != UTF8_SHORT) {
                        badutf8(ty, "Blob.take-str!(): invalid UTF-8");
                }
        }

        Value str = vSs((char const *)s, v);

        memmove(vv(*blob->blob), vv(*blob->blob) + v, n - v);
        vN(*blob->blob) -= v;

        return str;
}

static Value
blob_str_unsafe(Ty *ty, Value *blob, int argc, Value *kwargs)
{
        isize start;
        isize n;

        blobspan(ty, blob, argc, "Blob.str!()", &start, &n);

        return vSs((char const *)vv(*blob->blob) + start, n);
}

static Value
blob_reserve(Ty *ty, Value *blob, int argc, Value *kwargs)
{
        if (argc != 1)
                zP("blob.reserve() expects 1 argument but got %d", argc);

        Value n = ARG(0);
        if (n.type != VALUE_INTEGER)
                zP("the argument to blob.reserve() must be an integer");
        if (n.z < 0)
                zP("the argument to blob.reserve() must be non-negative");

        vvR(*blob->blob, n.z);

        return NIL;
}

static Value
blob_pad(Ty *ty, Value *blob, int argc, Value *kwargs)
{
        Value n;
        Value pad;

        switch (argc) {
        case 1:
                n = ARG(0);
                pad = INTEGER(0);
                break;
        case 2:
                n = ARG(0);
                pad = ARG(1);
                break;
        default:
                zP("Blob.pad(): expected 1 or 2 arguments but got %d", argc);
        }

        if (n.type != VALUE_INTEGER) {
                zP("Blob.pad(): expected arg0: Int but got: %s", VSC(&n));
        }

        usize goal = n.z;

        if (vN(*blob->blob) >= goal) {
                return BOOLEAN(false);
        }

        switch (pad.type) {
        case VALUE_INTEGER:
                vvR(*blob->blob, goal);
                memset(vZ(*blob->blob), (u8)pad.z, goal - vN(*blob->blob));
                vN(*blob->blob) = blob->blob->capacity;
                break;

        case VALUE_STRING:
                vvR(*blob->blob, goal + sN(pad));
                while (vN(*blob->blob) < goal) {
                        vvPn(*blob->blob, ss(pad), sN(pad));
                }
                break;

        default:
                zP("Blob.pad(): expected arg1: Int | String but got: %s", VSC(&pad));
        }

        return BOOLEAN(true);
}

static Value
blob_ptr(Ty *ty, Value *blob, int argc, Value *kwargs)
{
        ASSERT_ARGC("Blob.ptr()", 0, 1);

        if (argc == 0) {
                return PTR(vv(*blob->blob));
        } else {
                return PTR(vv(*blob->blob) + INT_ARG(0));
        }
}

static Value
blob_hex(Ty *ty, Value *blob, int argc, Value *kwargs)
{
        ASSERT_ARGC("Blob.hex()", 0);

        static char const digits[] = "0123456789abcdef";

        usize n = vN(*blob->blob);
        u8 *str = mAo(n*2, GC_STRING);

        for (int i = 0; i < n; ++i) {
                u8 b = v__(*blob->blob, i);
                str[2*i  ] = digits[b / 0x10];
                str[2*i+1] = digits[b & 0xF];
        }

        return STRING(str, n*2);
}

inline static isize
BlobWrap(isize i, isize n)
{
        return (i < 0) ? (i + n) : i;
}

static Value
BlobSlice3(Ty *ty, Blob const *b, Value const *_i, Value const *_j, Value const *_k)
{
        isize n = vN(*b);
        isize i = _i->z;
        isize k = (_k->type == VALUE_NIL) ? 1 : (_k->z + !_k->z);

        Blob *slice = value_blob_new(ty);

        if (k < 0) {
                isize j     = (_j->type == VALUE_NIL) ? 0 : _j->z;
                isize start = min(BlobWrap(i - 1, n), n - 1);
                isize stop  = max(BlobWrap(j, n), 0);
                for (isize ix = start; ix >= stop; ix += k) {
                        uvP(*slice, v__(*b, ix));
                }
        } else {
                isize j     = (_j->type == VALUE_NIL) ? n : _j->z;
                isize start = min(max(BlobWrap(i, n), 0), n);
                isize stop  = min(BlobWrap(j, n), n);
                if (k == 1) {
                        uvPn(*slice, v_(*b, start), max(stop - start, 0));
                        return BLOB(slice);
                }
                for (isize ix = start; ix < stop; ix += k) {
                        uvP(*slice, v__(*b, ix));
                }
        }

        return BLOB(slice);
}

static Value
blob_slice(Ty *ty, Value *blob, int argc, Value *kwargs)
{
        ASSERT_ARGC("Blob.slice()", 0, 1, 2, 3);

        if (argc == 3) {
                Value _i = ARGx(0, VALUE_INTEGER);
                Value _j = ARGx(1, VALUE_INTEGER, VALUE_NIL);
                Value _k = ARGx(2, VALUE_INTEGER, VALUE_NIL);
                return BlobSlice3(ty, blob->blob, &_i, &_j, &_k);
        }

        isize start;
        isize n;

        switch (argc) {
        case 0:
                start = 0;
                n = vN(*blob->blob);
                break;

        case 1:
                start = INT_ARG(0);
                n = vN(*blob->blob);
                break;

        case 2:
                start = INT_ARG(0);
                n = INT_ARG(1);
                break;
        }

        if (start < 0) {
                start += vN(*blob->blob);
        }
        if (start < 0 || start > vN(*blob->blob)) {
                bP("start index out of range: %zd", start);
        }

        if (n < 0) {
                n += vN(*blob->blob) - start;
        }
        if (n < 0) {
                zP("count d out of range: %zd", n);
        }
        n = min(n, vN(*blob->blob) - start);

        Blob *b = value_blob_new(ty);
        uvPn(*b, v_(*blob->blob, start), n);

        return BLOB(b);
}

static Value
blob_splice(Ty *ty, Value *blob, int argc, Value *kwargs)
{
        ASSERT_ARGC("Blob.splice()", 0, 1, 2);

        isize start;
        isize n;

        switch (argc) {
        case 0:
                start = 0;
                n = vN(*blob->blob);
                break;

        case 1:
                start = INT_ARG(0);
                n = vN(*blob->blob);
                break;

        case 2:
                start = INT_ARG(0);
                n = INT_ARG(1);
                break;
        }

        if (start < 0) {
                start += vN(*blob->blob);
        }
        if (start < 0 || start > vN(*blob->blob)) {
                bP("start index out of range: %zd", start);
        }

        if (n < 0) {
                n += vN(*blob->blob) - start;
        }
        if (n < 0) {
                bP("count out of range: %zd", n);
        }
        n = min(n, vN(*blob->blob) - start);

        Blob *b = value_blob_new(ty);
        uvPn(*b, vv(*blob->blob) + start, n);


        memmove(
                vv(*blob->blob) + start,
                vv(*blob->blob) + start + n,
                vN(*blob->blob) - start - n
        );

        vN(*blob->blob) -= n;

        return BLOB(b);
}

static u8 const PackedSize[] = { 8, 4, 8, 4, 4, 2, 2, 1, 1 };

static imax
packed_index(Ty *ty, Value const *blob, char const *who, int argc, Value *kwargs, imax *kind)
{
        if (argc < 2) {
                zP("Blob.%s(): expected at least 2 arguments but got %d", who, argc);
        }

        if (ARG(0).type != VALUE_INTEGER || ARG(1).type != VALUE_INTEGER) {
                zP("Blob.%s(): expected Int kind and index", who);
        }

        *kind = ARG(0).z;

        if (*kind < 0 || *kind >= (imax)countof(PackedSize)) {
                zP("Blob.%s(): invalid element kind %" PRIiMAX, who, *kind);
        }

        imax i = ARG(1).z;
        imax n = vN(*blob->blob) / PackedSize[*kind];

        if (i < 0 || i >= n) {
                zP("Blob.%s(): element %" PRIiMAX " is out of range for %" PRIiMAX " elements", who, i, n);
        }

        return i * PackedSize[*kind];
}

static Value
blob_peek(Ty *ty, Value *blob, int argc, Value *kwargs)
{
        imax kind;
        imax at = packed_index(ty, blob, "peek", argc, kwargs, &kind);
        u8  *p  = vv(*blob->blob) + at;

        switch (kind) {
        case 0: { double x;   memcpy(&x, p, sizeof x); return REAL(x);    }
        case 1: { float  x;   memcpy(&x, p, sizeof x); return REAL(x);    }
        case 2: { i64    x;   memcpy(&x, p, sizeof x); return INTEGER(x); }
        case 3: { i32    x;   memcpy(&x, p, sizeof x); return INTEGER(x); }
        case 4: { u32    x;   memcpy(&x, p, sizeof x); return INTEGER(x); }
        case 5: { i16    x;   memcpy(&x, p, sizeof x); return INTEGER(x); }
        case 6: { u16    x;   memcpy(&x, p, sizeof x); return INTEGER(x); }
        case 7: { i8     x;   memcpy(&x, p, sizeof x); return INTEGER(x); }
        default:                                       return INTEGER(*p);
        }
}

static Value
blob_poke(Ty *ty, Value *blob, int argc, Value *kwargs)
{
        if (argc != 3) {
                zP("Blob.poke(): expected 3 arguments but got %d", argc);
        }

        imax  kind;
        imax  at = packed_index(ty, blob, "poke", argc, kwargs, &kind);
        u8   *p  = vv(*blob->blob) + at;
        Value v  = ARG(2);
        bool  real = (kind <= 1);

        if (real ? (v.type != VALUE_REAL && v.type != VALUE_INTEGER) : (v.type != VALUE_INTEGER)) {
                zP("Blob.poke(): expected %s but got: %s", real ? "Float" : "Int", VSC(&v));
        }

        double f = (v.type == VALUE_REAL) ? v.real : (double)v.z;
        imax   z = (v.type == VALUE_INTEGER) ? v.z : 0;

        switch (kind) {
        case 0: { double x = f;      memcpy(p, &x, sizeof x); break; }
        case 1: { float  x = f;      memcpy(p, &x, sizeof x); break; }
        case 2: { i64    x = z;      memcpy(p, &x, sizeof x); break; }
        case 3: case 4: { u32 x = z; memcpy(p, &x, sizeof x); break; }
        case 5: case 6: { u16 x = z; memcpy(p, &x, sizeof x); break; }
        default:        { u8  x = z; memcpy(p, &x, sizeof x); break; }
        }

        return v;
}

DEFINE_METHOD_TABLE(
        blob,
        { .name = "clear",     .func = blob_clear      },
        { .name = "fill",      .func = blob_fill       },
        { .name = "get",       .func = blob_get        },
        { .name = "hex",       .func = blob_hex        },
        { .name = "pad",       .func = blob_pad        },
        { .name = "peek",      .func = blob_peek       },
        { .name = "poke",      .func = blob_poke       },
        { .name = "ptr",       .func = blob_ptr        },
        { .name = "push",      .func = blob_push       },
        { .name = "reserve",   .func = blob_reserve    },
        { .name = "search",    .func = blob_search     },
        { .name = "searchr",   .func = blob_searchr    },
        { .name = "shrink",    .func = blob_shrink     },
        { .name = "size",      .func = blob_size       },
        { .name = "slice",     .func = blob_slice      },
        { .name = "splice",    .func = blob_splice     },
        { .name = "str",       .func = blob_str        },
        { .name = "str!",      .func = blob_str_unsafe },
        { .name = "takeStr!",  .func = blob_take_str   },
        { .name = "utf8?",     .func = blob_is_utf8    },
        { .name = "utf8Tail",  .func = blob_utf8_tail  },
        { .name = "utf8Valid", .func = blob_utf8_valid },
        { .name = "xor",       .func = blob_xor        },
);

DEFINE_METHOD_LOOKUP(blob)
DEFINE_METHOD_TABLE_BUILDER(blob)
DEFINE_METHOD_COMPLETER(blob)
