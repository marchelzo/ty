#include <limits.h>
#include <utf8proc.h>

#include "ty.h"
#include "blob.h"
#include "value.h"
#include "vm.h"
#include "xd.h"
#include "ty.h"

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

        Value start;
        Value c;

        switch (argc) {
        case 1:
                start = INTEGER(0);
                c = ARG(0);
                break;
        case 2:
                start = ARG(0);
                c = ARG(1);
                break;
        default:
                zP("blob.search() expects 1 or 2 arguments but got %d", argc);
        }

        if (start.type != VALUE_INTEGER)
                zP("the offset argument to blob.search() must be an integer");

        if (start.z < 0 || start.z > vN(*blob->blob))
                zP("invalid offset passed to blob.search()");

        if (vN(*blob->blob) == 0)
                return NIL;

        char const *haystack = (char const *)blob->blob->items + start.z;
        int n = vN(*blob->blob) - start.z;
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
        default:
                zP("invalid argument passed to blob.search()");
        }

        return (s == NULL) ? NIL : INTEGER(s - haystack + start.z);
}

static Value
blob_shrink(Ty *ty, Value *blob, int argc, Value *kwargs)
{
        mRE(blob->blob->items, vN(*blob->blob));
        blob->blob->capacity = vN(*blob->blob);
        return NIL;
}

static Value
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
blob_set(Ty *ty, Value *blob, int argc, Value *kwargs)
{
        if (argc != 2)
                zP("blob.set() expects 2 arguments but got %d", argc);

        Value i = ARG(0);
        if (i.type != VALUE_INTEGER)
                zP("the argument to blob.get() must be an integer");
        if (i.z < 0)
                i.z += vN(*blob->blob);
        if (i.z < 0 || i.z >= vN(*blob->blob))
                zP("invalid index passed to blob.get()");

        Value arg = ARG(1);
        if (arg.type != VALUE_INTEGER || arg.z < 0 || arg.z > UCHAR_MAX)
                zP("invalid integer passed to blob.set()");

        blob->blob->items[i.z] = arg.z;

        return arg;
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


static Value
blob_str(Ty *ty, Value *blob, int argc, Value *kwargs)
{
        ASSERT_ARGC("Blob.str()", 0, 1, 2);

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

        u8 *str = value_string_alloc(ty, 2 * n);
        isize i = 0;

        i32 cp;

        while (n > 0) {
                i32 sz = utf8proc_iterate(vv(*blob->blob) + start, n, &cp);
                if (sz < 0) {
                        start += 1;
                        n     -= 1;
                        if (v__(*blob->blob, start) < 0xC0) {
                                str[i++] = 0xC2;
                                str[i++] = v__(*blob->blob, start);
                        }
                } else {
                        memcpy(str + i, vv(*blob->blob) + start, sz);
                        start += sz;
                        i     += sz;
                        n     -= sz;
                }
        }

        return STRING(str, i);
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
                bP("invalid argument(s): start=%d, n=%d, size=%zu", start, n, vN(*blob->blob));
        }

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

static Value
blob_slice(Ty *ty, Value *blob, int argc, Value *kwargs)
{
        ASSERT_ARGC("Blob.slice()", 0, 1, 2);

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
                n += vN(*blob->blob);
        }
        if (n < 0) {
                zP("count d out of range: %zd", n);
        }
        n = min(n, vN(*blob->blob) - start);

        Blob *b = value_blob_new(ty);
        uvPn(*b, blob->blob->items + start, n);

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
                n += vN(*blob->blob);
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

DEFINE_METHOD_TABLE(
        { .name = "clear",    .func = blob_clear        },
        { .name = "fill",     .func = blob_fill         },
        { .name = "get",      .func = blob_get          },
        { .name = "hex",      .func = blob_hex          },
        { .name = "pad",      .func = blob_pad          },
        { .name = "ptr",      .func = blob_ptr          },
        { .name = "push",     .func = blob_push         },
        { .name = "reserve",  .func = blob_reserve      },
        { .name = "search",   .func = blob_search       },
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
