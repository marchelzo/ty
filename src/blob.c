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
        isize start;
        isize n;

        if (argc > 0 && ARG(0).type != VALUE_INTEGER)
                zP("the first argument to blob.clear() must be an integer");

        if (argc > 1 && ARG(1).type != VALUE_INTEGER)
                zP("the second argument to blob.clear() must be an integer");

        switch (argc) {
        case 0:
                start = 0;
                n = blob->blob->count;
                break;
        case 1:
                start = ARG(0).z;
                if (start < 0)
                        start += blob->blob->count;
                n = blob->blob->count - start;
                break;
        case 2:
                start = ARG(0).z;
                if (start < 0)
                        start += blob->blob->count;
                n = ARG(1).z;
                break;
        default:
                zP("blob.clear() expects 0, 1, or 2 arguments but got %d", argc);
        }

        if (start < 0 || n < 0 || (n + start) > blob->blob->count)
                zP("invalid arguments to blob.clear()");

        memmove(blob->blob->items + start, blob->blob->items + start + n, blob->blob->count - start - n);
        blob->blob->count -= n;

        return NIL;
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

        if (start.z < 0 || start.z > blob->blob->count)
                zP("invalid offset passed to blob.search()");

        if (blob->blob->count == 0)
                return NIL;

        char const *haystack = (char const *)blob->blob->items + start.z;
        int n = blob->blob->count - start.z;
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
        mRE(blob->blob->items, blob->blob->count);
        blob->blob->capacity = blob->blob->count;
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
        return INTEGER(blob->blob->count);
}

Value
blob_get(Ty *ty, Value *blob, int argc, Value *kwargs)
{
        if (argc != 1)
                zP("blob.get() expects 1 argument but got %d", argc);

        Value i = ARG(0);
        if (i.type != VALUE_INTEGER)
                zP("the argument to blob.get() must be an integer");
        if (i.z < 0)
                i.z += blob->blob->count;
        if (i.z < 0 || i.z >= blob->blob->count)
                zP("blob.get(): invalid index: %"PRIiMAX, i.z);

        return INTEGER(blob->blob->items[i.z]);
}

static Value
blob_fill(Ty *ty, Value *blob, int argc, Value *kwargs)
{
        if (argc != 0)
                zP("blob.fill() expects no arguments but got %d", argc);

        if (blob->blob->items == NULL)
                return NIL;

        memset(blob->blob->items + blob->blob->count, 0, blob->blob->capacity - blob->blob->count);
        blob->blob->count = blob->blob->capacity;

        return NIL;
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
                i.z += blob->blob->count;
        if (i.z < 0 || i.z >= blob->blob->count)
                zP("invalid index passed to blob.get()");

        Value arg = ARG(1);
        if (arg.type != VALUE_INTEGER || arg.z < 0 || arg.z > UCHAR_MAX)
                zP("invalid integer passed to blob.set()");

        blob->blob->items[i.z] = arg.z;

        return NIL;
}

static Value
blob_xor(Ty *ty, Value *blob, int argc, Value *kwargs)
{
        if (argc == 1 && ARG(0).type == VALUE_BLOB) {
                Blob *b = ARG(0).blob;
                if (b->count > 0) for (usize i = 0; i < blob->blob->count; ++i) {
                        blob->blob->items[i] ^= b->items[i % b->count];
                }
                return *blob;
        }

        if (argc != 2) {
                zP("blob.xor(): expected 2 arguments but got %d", argc);
        }

        if (ARG(0).type != VALUE_INTEGER) {
                zP("blob.xor(mask, _): expected integer but got: %s", value_show(ty, &ARG(0)));
        }

        if (ARG(1).type != VALUE_INTEGER) {
                zP("blob.xor(_, size): expected integer but got: %s", value_show(ty, &ARG(0)));
        }

        u8  _u8;
        u16 _u16, *pu16;
        u32 _u32, *pu32;
        u64 _u64, *pu64;

        u8 size = ARG(1).z;
        u8 r;

        switch (size) {
        case 1:
                _u8 = ARG(0).z;
                for (usize i = 0; i < blob->blob->count; ++i) {
                        blob->blob->items[i] ^= _u8;
                }
                break;

        case 2:
                _u16 = ARG(0).z;
                pu16 = (void *)blob->blob->items;
                for (usize i = 0; i < blob->blob->count / 2; ++i) {
                        pu16[i] ^= _u16;
                }
                r =  blob->blob->count % 2;
                for (int i = 0; i < r; ++i) {
                        blob->blob->items[blob->blob->count - r + i] ^= ((_u16 >> (8 * i)) & 0xFF);
                }
                break;

        case 4:
                _u32 = ARG(0).z;
                pu32 = (void *)blob->blob->items;
                for (usize i = 0; i < blob->blob->count / 4; ++i) {
                        pu32[i] ^= _u32;
                }
                r =  blob->blob->count % 4;
                for (int i = 0; i < r; ++i) {
                        blob->blob->items[blob->blob->count - r + i] ^= ((_u32 >> (8 * i)) & 0xFF);
                }
                break;

        case 8:
                _u64 = ARG(0).z;
                pu64 = (void *)blob->blob->items;
                for (usize i = 0; i < blob->blob->count / 8; ++i) {
                        pu64[i] ^= _u64;
                }
                r =  blob->blob->count % 8;
                for (int i = 0; i < r; ++i) {
                        blob->blob->items[blob->blob->count - r + i] ^= ((_u64 >> (8 * i)) & 0xFF);
                }
                break;

        default:
                zP("blob.xor(): invalid mask size: %"PRIiMAX, ARG(1).z);
        }

        return *blob;
}


static Value
blob_str(Ty *ty, Value *blob, int argc, Value *kwargs)
{
        int start;
        int n;

        if (argc > 0 && ARG(0).type != VALUE_INTEGER)
                zP("Blob.str(): expected integer but got: %s", VSC(&ARG(0)));

        if (argc > 1 && ARG(1).type != VALUE_INTEGER)
                zP("Blob.str(): expected integer but got: %s", VSC(&ARG(1)));

        switch (argc) {
        case 0:
                start = 0;
                n = blob->blob->count;
                break;
        case 1:
                start = ARG(0).z;
                n = INT_MAX;
                break;
        case 2:
                start = ARG(0).z;
                n = ARG(1).z;
                break;
        default:
                zP("blob.str() expects 0, 1, or 2 arguments but got %d", argc);
        }

        if (start < 0) {
                start += blob->blob->count;
        }

        n = max(0, min(n, blob->blob->count - start));

        if (start < 0 || (n + start) > blob->blob->count)
                zP("Blob.str(): invalid argument(s): start=%d, n=%d, size=%zu", start, n, blob->blob->count);

        char *s = value_string_alloc(ty, 2 * n);
        int i = 0;

        utf8proc_int32_t cp;
        while (n > 0) {
                int r = utf8proc_iterate((unsigned char *)blob->blob->items + start, n, &cp);
                if (r < 0) {
                        start += 1;
                        n -= 1;
                        if (blob->blob->items[start] < 0xC0) {
                                s[i++] = 0xC2;
                                s[i++] = blob->blob->items[start];
                        }
                } else {
                        memcpy(s + i, blob->blob->items + start, r);
                        i += r;
                        start += r;
                        n -= r;
                }
        }

        return STRING(s, i);
}

static Value
blob_str_unsafe(Ty *ty, Value *blob, int argc, Value *kwargs)
{
        ASSERT_ARGC("Blob.str!()", 0, 1, 2);

        int start;
        int n;

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

        default:
                zP("blob.str!() expects 0, 1, or 2 arguments but got %d", argc);
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
                blob->blob->count = blob->blob->capacity;
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
        if (argc == 0) {
                return PTR(blob->blob->items);
        }

        if (argc == 1) {
                if (ARG(0).type != VALUE_INTEGER) {
                        zP("blob.ptr() expects an integer but got %s", value_show(ty, &ARG(0)));
                }

                return PTR(blob->blob->items + ARG(0).z);
        }

        zP("blob.ptr() expects 0 or 1 arguments but got %d", argc);
}

static Value
blob_hex(Ty *ty, Value *blob, int argc, Value *kwargs)
{
        if (argc != 0)
                zP("blob.hex() expects no arguments but got %d", argc);

        static char const digits[] = "0123456789abcdef";

        int n = blob->blob->count;
        char *s = mAo(n*2, GC_STRING);

        for (int i = 0; i < n; ++i) {
                unsigned char b = blob->blob->items[i];
                s[2*i] = digits[b / 0x10];
                s[2*i+1] = digits[b & 0xF];
        }

        return STRING(s, n*2);
}

static Value
blob_slice(Ty *ty, Value *blob, int argc, Value *kwargs)
{
        int start = 0;
        int n = blob->blob->count;

        switch (argc) {
        case 2:
                if (ARG(1).type != VALUE_INTEGER)
                        zP("the second argument to blob.slice() must be an integer");
                n = ARG(1).z;
        case 1:
                if (ARG(0).type != VALUE_INTEGER)
                        zP("the first argument to blob.slice() must be an integer");
                start = ARG(0).z;
        case 0:
                break;
        default:
                zP("blob.slice() expects 0, 1, or 2 arguments but got %d", argc);
        }

        if (start < 0)
                start += blob->blob->count;
        if (start < 0 || start > blob->blob->count)
                zP("start index %d out of range in call to blob.slice()", start);

        if (n < 0)
                n += blob->blob->count;
        if (n < 0)
                zP("count %d out of range in call to blob.slice()", n);
        n = min(n, blob->blob->count - start);

        Blob *b = value_blob_new(ty);
        NOGC(b);
        vvPn(*b, blob->blob->items + start, n);
        OKGC(b);

        return BLOB(b);
}

static Value
blob_splice(Ty *ty, Value *blob, int argc, Value *kwargs)
{
        int start = 0;
        int n = blob->blob->count;

        switch (argc) {
        case 2:
                if (ARG(1).type != VALUE_INTEGER)
                        zP("the second argument to blob.splice() must be an integer");
                n = ARG(1).z;
        case 1:
                if (ARG(0).type != VALUE_INTEGER)
                        zP("the first argument to blob.splice() must be an integer");
                start = ARG(0).z;
        case 0:
                break;
        default:
                zP("blob.splice() expects 0, 1, or 2 arguments but got %d", argc);
        }

        if (start < 0)
                start += blob->blob->count;
        if (start < 0 || start > blob->blob->count)
                zP("start index %d out of range in call to blob.splice()", start);

        if (n < 0)
                n += blob->blob->count;
        if (n < 0)
                zP("count %d out of range in call to blob.splice()", n);
        n = min(n, blob->blob->count - start);

        Blob *b = value_blob_new(ty);
        NOGC(b);
        vvPn(*b, blob->blob->items + start, n);
        OKGC(b);


        memmove(blob->blob->items + start, blob->blob->items + start + n, blob->blob->count - start - n);
        blob->blob->count -= n;

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
