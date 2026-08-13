#include <limits.h>
#include <utf8proc.h>

#include "ty.h"
#include "blob.h"
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
                n = vN(*V_BLOB(*blob));
                break;

        case 1:
                start = INT_ARG(0);
                if (start < 0) {
                        start += vN(*V_BLOB(*blob));
                }
                n = vN(*V_BLOB(*blob)) - start;
                break;

        case 2:
                start = INT_ARG(0);
                if (start < 0) {
                        start += vN(*V_BLOB(*blob));
                }
                n = INT_ARG(1);
                break;
        }

        if (
                (start < 0)
             || (n < 0)
             || ((n + start) > vN(*V_BLOB(*blob)))
        ) {
                bP(
                        "invalid argument(s): start=%s, n=%s (size=%zu)",
                        (argc >= 1) ? SHOW(&ARG(0)) : "nil",
                        (argc >= 2) ? SHOW(&ARG(1)) : "nil",
                        vN(*V_BLOB(*blob))
                );
        }

        memmove(
                vv(*V_BLOB(*blob)) + start,
                vv(*V_BLOB(*blob)) + start + n,
                vN(*V_BLOB(*blob)) - start - n
        );

        vN(*V_BLOB(*blob)) -= n;

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

        if (vN(*V_BLOB(*blob)) == 0) {
                return NIL;
        }

        isize n = vN(*V_BLOB(*blob)) - start;
        char const *haystack = (char const *)v_(*V_BLOB(*blob), start);

        char const *s;

        switch (V_TYPE(c)) {
        case VALUE_STRING:
                s = mmmm(haystack, n, ss(c), sN(c));
                break;

        case VALUE_BLOB:
                s = mmmm(haystack, n, (char *)V_BLOB(c)->items, V_BLOB(c)->count);
                break;

        case VALUE_INTEGER:
                if (V_Z(c) < 0 || V_Z(c) > UCHAR_MAX)
                        zP("invalid integer passed to blob.search()");
                s = memchr(haystack, V_Z(c), n);
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
                end = vN(*V_BLOB(*blob));
                c = ARGx(0, VALUE_STRING, VALUE_BLOB, VALUE_INTEGER);
                break;

        case 2:
                end = INT_ARG(0);
                c = ARGx(1, VALUE_STRING, VALUE_BLOB, VALUE_INTEGER);
                break;
        }

        if (end <= 0 || vN(*V_BLOB(*blob)) == 0) {
                return NIL;
        }

        if (end > vN(*V_BLOB(*blob))) {
                end = vN(*V_BLOB(*blob));
        }

        char const *haystack = (char const *)v_(*V_BLOB(*blob), 0);

        char const *s;
        u8 byte;

        switch (V_TYPE(c)) {
        case VALUE_STRING:
                s = (char const *)mmmmr((u8 const *)haystack, end, (u8 const *)ss(c), sN(c));
                break;

        case VALUE_BLOB:
                s = (char const *)mmmmr((u8 const *)haystack, end, (u8 const *)V_BLOB(c)->items, V_BLOB(c)->count);
                break;

        case VALUE_INTEGER:
                if (V_Z(c) < 0 || V_Z(c) > UCHAR_MAX) {
                        bP("bad needle: %s", VSC(&c));
                }
                byte = V_Z(c);
                s = (char const *)mmmmr((u8 const *)haystack, end, &byte, 1);
                break;
        }

        return (s == NULL) ? NIL : INTEGER(s - haystack);
}

static Value
blob_shrink(Ty *ty, Value *blob, int argc, Value *kwargs)
{
        mRE(V_BLOB(*blob)->items, vN(*V_BLOB(*blob)));
        V_BLOB(*(blob))->capacity = vN(*V_BLOB(*blob));
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
                index = vN(*V_BLOB(*blob));
                arg = ARG(0);
        }

        switch (V_TYPE(arg)) {
        case VALUE_INTEGER:
                if (V_Z(arg) < 0 || V_Z(arg) > UCHAR_MAX) {
                        bP("not an octet: %s", VSC(&arg));
                }
                vvI(*V_BLOB(*blob), V_Z(arg), index);
                break;

        case VALUE_BLOB:
                vvIn(*V_BLOB(*blob), V_BLOB(arg)->items, V_BLOB(arg)->count, index);
                break;

        case VALUE_STRING:
                vvIn(*V_BLOB(*blob), ss(arg), sN(arg), index);
                break;

        case VALUE_PTR:
                vvIn(*V_BLOB(*blob), V_PTR(arg), INT_ARG(argc - 1), index);
                break;

        default:
                ARGx(!!argc, VALUE_INTEGER, VALUE_STRING, VALUE_BLOB, VALUE_PTR);
        }

        return *blob;
}

static Value
blob_size(Ty *ty, Value *blob, int argc, Value *kwargs)
{
        return INTEGER(vN(*V_BLOB(*blob)));
}

Value
blob_get(Ty *ty, Value *blob, int argc, Value *kwargs)
{
        ASSERT_ARGC("Blob.get()", 1);

        isize i = INT_ARG(0);
        if (i < 0) {
                i += vN(*V_BLOB(*blob));
        }
        if (i < 0 || i >= vN(*V_BLOB(*blob))) {
                bP("out of range: %zd", i);
        }

        return INTEGER(v__(*V_BLOB(*blob), i));
}

static Value
blob_fill(Ty *ty, Value *blob, int argc, Value *kwargs)
{
        ASSERT_ARGC("Blob.fill()", 0);

        if (vv(*V_BLOB(*blob)) == NULL) {
                return NIL;
        }

        memset(
                vv(*V_BLOB(*blob)) + vN(*V_BLOB(*blob)),
                0,
                vC(*V_BLOB(*blob)) - vN(*V_BLOB(*blob))
        );

        vN(*V_BLOB(*blob)) = V_BLOB(*(blob))->capacity;

        return *blob;
}

static Value
blob_set(Ty *ty, Value *blob, int argc, Value *kwargs)
{
        if (argc != 2)
                zP("blob.set() expects 2 arguments but got %d", argc);

        Value i = ARG(0);
        if (V_TYPE(i) != VALUE_INTEGER)
                zP("the argument to blob.get() must be an integer");
        if (V_Z(i) < 0)
                i = INTEGER(V_Z(i) + vN(*V_BLOB(*blob)));
        if (V_Z(i) < 0 || V_Z(i) >= vN(*V_BLOB(*blob)))
                zP("invalid index passed to blob.get()");

        Value arg = ARG(1);
        if (V_TYPE(arg) != VALUE_INTEGER || V_Z(arg) < 0 || V_Z(arg) > UCHAR_MAX)
                zP("invalid integer passed to blob.set()");

        V_BLOB(*(blob))->items[V_Z(i)] = V_Z(arg);

        return arg;
}

static Value
blob_xor(Ty *ty, Value *blob, int argc, Value *kwargs)
{
        ASSERT_ARGC("Blob.xor()", 1, 2);

        if (argc == 1 && ARG_T(0) == VALUE_BLOB) {
                Blob *b = V_BLOB(ARG(0));
                if (vN(*b) > 0) {
                        for (usize i = 0; i < vN(*V_BLOB(*blob)); ++i) {
                                *v_(*V_BLOB(*blob), i) ^= v__(*b, i % vN(*b));
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
                _u8 = V_Z(ARG(0));
                for (usize i = 0; i < vN(*V_BLOB(*blob)); ++i) {
                        *v_(*V_BLOB(*blob), i) ^= _u8;
                }
                break;

        case 2:
                _u16 = V_Z(ARG(0));
                pu16 = (void *)vv(*V_BLOB(*blob));
                for (usize i = 0; i < vN(*V_BLOB(*blob)) / 2; ++i) {
                        pu16[i] ^= _u16;
                }
                r =  vN(*V_BLOB(*blob)) % 2;
                for (u8 i = 0; i < r; ++i) {
                        *v_(*V_BLOB(*blob), vN(*V_BLOB(*blob)) - r + i) ^= ((_u16 >> (8 * i)) & 0xFF);
                }
                break;

        case 4:
                _u32 = V_Z(ARG(0));
                pu32 = (void *)vv(*V_BLOB(*blob));
                for (usize i = 0; i < vN(*V_BLOB(*blob)) / 4; ++i) {
                        pu32[i] ^= _u32;
                }
                r =  vN(*V_BLOB(*blob)) % 4;
                for (u8 i = 0; i < r; ++i) {
                        *v_(*V_BLOB(*blob), vN(*V_BLOB(*blob)) - r + i) ^= ((_u32 >> (8 * i)) & 0xFF);
                }
                break;

        case 8:
                _u64 = V_Z(ARG(0));
                pu64 = (void *)vv(*V_BLOB(*blob));
                for (usize i = 0; i < vN(*V_BLOB(*blob)) / 8; ++i) {
                        pu64[i] ^= _u64;
                }
                r =  vN(*V_BLOB(*blob)) % 8;
                for (u8 i = 0; i < r; ++i) {
                        *v_(*V_BLOB(*blob), vN(*V_BLOB(*blob)) - r + i) ^= ((_u64 >> (8 * i)) & 0xFF);
                }
                break;

        default:
                bP("invalid mask size: %hhu", size);
        }

        return *blob;
}


static Value
blob_str(Ty *ty, Value *blob, int argc, Value *kwargs)
{
        ASSERT_ARGC("Blob.str()", 0, 1, 2);

        isize start;
        isize n;

        switch (argc) {
        case 0:
                start = 0;
                n = vN(*V_BLOB(*blob));
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
                start += vN(*V_BLOB(*blob));
        }

        n = max(0, min(n, vN(*V_BLOB(*blob)) - start));

        if (start < 0 || (n + start) > vN(*V_BLOB(*blob))) {
                bP("invalid argument(s): start=%zd, n=%zd, size=%zu", start, n, vN(*V_BLOB(*blob)));
        }


        u8 *str = value_string_alloc(ty, 2 * n);
        isize i = 0;

        i32 cp;

        while (n > 0) {
                i32 sz = utf8proc_iterate(vv(*V_BLOB(*blob)) + start, n, &cp);
                if (sz < 0) {
                        if (v__(*V_BLOB(*blob), start) < 0xC0) {
                                str[i++] = 0xC2;
                                str[i++] = v__(*V_BLOB(*blob), start);
                        }
                        start += 1;
                        n     -= 1;
                } else {
                        memcpy(str + i, vv(*V_BLOB(*blob)) + start, sz);
                        start += sz;
                        i     += sz;
                        n     -= sz;
                }
        }

        return STRING(ty, str, i);
}

static Value
blob_str_unsafe(Ty *ty, Value *blob, int argc, Value *kwargs)
{
        ASSERT_ARGC("Blob.str!()", 0, 1, 2);

        isize start;
        isize n;

        switch (argc) {
        case 0:
                start = 0;
                n = vN(*V_BLOB(*blob));
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
                start += vN(*V_BLOB(*blob));
        }

        n = max(0, min(n, vN(*V_BLOB(*blob)) - start));

        if (start < 0 || (n + start) > vN(*V_BLOB(*blob))) {
                bP("invalid argument(s): start=%d, n=%d, size=%zu", start, n, vN(*V_BLOB(*blob)));
        }

        return vSs((char const *)vv(*V_BLOB(*blob)) + start, n);
}

static Value
blob_reserve(Ty *ty, Value *blob, int argc, Value *kwargs)
{
        if (argc != 1)
                zP("blob.reserve() expects 1 argument but got %d", argc);

        Value n = ARG(0);
        if (V_TYPE(n) != VALUE_INTEGER)
                zP("the argument to blob.reserve() must be an integer");
        if (V_Z(n) < 0)
                zP("the argument to blob.reserve() must be non-negative");

        vvR(*V_BLOB(*blob), V_Z(n));

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

        if (V_TYPE(n) != VALUE_INTEGER) {
                zP("Blob.pad(): expected arg0: Int but got: %s", VSC(&n));
        }

        usize goal = V_Z(n);

        if (vN(*V_BLOB(*blob)) >= goal) {
                return BOOLEAN(false);
        }

        switch (V_TYPE(pad)) {
        case VALUE_INTEGER:
                vvR(*V_BLOB(*blob), goal);
                memset(vZ(*V_BLOB(*blob)), (u8)V_Z(pad), goal - vN(*V_BLOB(*blob)));
                vN(*V_BLOB(*blob)) = V_BLOB(*(blob))->capacity;
                break;

        case VALUE_STRING:
                vvR(*V_BLOB(*blob), goal + sN(pad));
                while (vN(*V_BLOB(*blob)) < goal) {
                        vvPn(*V_BLOB(*blob), ss(pad), sN(pad));
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
                return PTR(vv(*V_BLOB(*blob)));
        } else {
                return PTR(vv(*V_BLOB(*blob)) + INT_ARG(0));
        }
}

static Value
blob_hex(Ty *ty, Value *blob, int argc, Value *kwargs)
{
        ASSERT_ARGC("Blob.hex()", 0);

        static char const digits[] = "0123456789abcdef";

        usize n = vN(*V_BLOB(*blob));
        u8 *str = mAo(n*2, GC_STRING);

        for (int i = 0; i < n; ++i) {
                u8 b = v__(*V_BLOB(*blob), i);
                str[2*i  ] = digits[b / 0x10];
                str[2*i+1] = digits[b & 0xF];
        }

        return STRING(ty, str, n*2);
}

static Value
blob_slice(Ty *ty, Value *blob, int argc, Value *kwargs)
{
        ASSERT_ARGC("Blob.slice()", 0, 1, 2);

        isize start;
        isize n;

        switch (argc) {
        case 0:
                start = 0;
                n = vN(*V_BLOB(*blob));
                break;

        case 1:
                start = INT_ARG(0);
                n = vN(*V_BLOB(*blob));
                break;

        case 2:
                start = INT_ARG(0);
                n = INT_ARG(1);
                break;
        }

        if (start < 0) {
                start += vN(*V_BLOB(*blob));
        }
        if (start < 0 || start > vN(*V_BLOB(*blob))) {
                bP("start index out of range: %zd", start);
        }

        if (n < 0) {
                n += vN(*V_BLOB(*blob));
        }
        if (n < 0) {
                zP("count d out of range: %zd", n);
        }
        n = min(n, vN(*V_BLOB(*blob)) - start);

        Blob *b = value_blob_new(ty);
        uvPn(*b, V_BLOB(*blob)->items + start, n);

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
                n = vN(*V_BLOB(*blob));
                break;

        case 1:
                start = INT_ARG(0);
                n = vN(*V_BLOB(*blob));
                break;

        case 2:
                start = INT_ARG(0);
                n = INT_ARG(1);
                break;
        }

        if (start < 0) {
                start += vN(*V_BLOB(*blob));
        }
        if (start < 0 || start > vN(*V_BLOB(*blob))) {
                bP("start index out of range: %zd", start);
        }

        if (n < 0) {
                n += vN(*V_BLOB(*blob));
        }
        if (n < 0) {
                bP("count out of range: %zd", n);
        }
        n = min(n, vN(*V_BLOB(*blob)) - start);

        Blob *b = value_blob_new(ty);
        uvPn(*b, vv(*V_BLOB(*blob)) + start, n);


        memmove(
                vv(*V_BLOB(*blob)) + start,
                vv(*V_BLOB(*blob)) + start + n,
                vN(*V_BLOB(*blob)) - start - n
        );

        vN(*V_BLOB(*blob)) -= n;

        return BLOB(b);
}

DEFINE_METHOD_TABLE(
        blob,
        { .name = "clear",    .func = blob_clear        },
        { .name = "fill",     .func = blob_fill         },
        { .name = "get",      .func = blob_get          },
        { .name = "hex",      .func = blob_hex          },
        { .name = "pad",      .func = blob_pad          },
        { .name = "ptr",      .func = blob_ptr          },
        { .name = "push",     .func = blob_push         },
        { .name = "reserve",  .func = blob_reserve      },
        { .name = "search",   .func = blob_search       },
        { .name = "searchr",  .func = blob_searchr      },
        { .name = "set",      .func = blob_set          },
        { .name = "shrink",   .func = blob_shrink       },
        { .name = "size",     .func = blob_size         },
        { .name = "slice",    .func = blob_slice        },
        { .name = "splice",   .func = blob_splice       },
        { .name = "str",      .func = blob_str          },
        { .name = "str!",     .func = blob_str_unsafe   },
        { .name = "xor",      .func = blob_xor          },
);

DEFINE_METHOD_LOOKUP(blob)
DEFINE_METHOD_TABLE_BUILDER(blob)
DEFINE_METHOD_COMPLETER(blob)
