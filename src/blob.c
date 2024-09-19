#include <limits.h>
#include <utf8proc.h>

#include "ty.h"
#include "blob.h"
#include "value.h"
#include "vm.h"
#include "util.h"
#include "ty.h"

static struct value
blob_clear(Ty *ty, struct value *blob, int argc, struct value *kwargs)
{
        int start;
        int n;

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
                start = ARG(0).integer;
                if (start < 0)
                        start += blob->blob->count;
                n = blob->blob->count - start;
                break;
        case 2:
                start = ARG(0).integer;
                if (start < 0)
                        start += blob->blob->count;
                n = ARG(1).integer;
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

static struct value
blob_search(Ty *ty, struct value *blob, int argc, struct value *kwargs)
{

        struct value start;
        struct value c;

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

        if (start.integer < 0 || start.integer > blob->blob->count)
                zP("invalid offset passed to blob.search()");

        if (blob->blob->count == 0)
                return NIL;

        char const *haystack = (char const *) blob->blob->items + start.integer;
        int n = blob->blob->count - start.integer;
        char const *s;

        switch (c.type) {
        case VALUE_STRING:
                s = strstrn(haystack, n, c.string, c.bytes);
                break;
        case VALUE_BLOB:
                s = strstrn(haystack, n, (char *)c.blob->items, c.blob->count);
                break;
        case VALUE_INTEGER:
                if (c.integer < 0 || c.integer > UCHAR_MAX)
                        zP("invalid integer passed to blob.search()");
                s = memchr(haystack, c.integer, n);
                break;
        default:
                zP("invalid argument passed to blob.search()");
        }

        return (s == NULL) ? NIL : INTEGER(s - haystack + start.integer);
}

static struct value
blob_shrink(Ty *ty, struct value *blob, int argc, struct value *kwargs)
{
        mRE(blob->blob->items, blob->blob->count);
        blob->blob->capacity = blob->blob->count;
        return NIL;
}

static struct value
blob_push(Ty *ty, struct value *blob, int argc, struct value *kwargs)
{
        size_t index = blob->blob->count;
        struct value arg;

        if (argc >= 2 && ARG(0).type != VALUE_PTR) {
                arg = ARG(1);
                struct value idx = ARG(0);
                if (idx.type != VALUE_INTEGER)
                        zP("the index passed to blob.push() must be an integer");
                if (idx.integer < 0)
                        idx.integer += blob->blob->count;
                if (idx.integer < 0 || idx.integer > blob->blob->count)
                        zP("invalid index passed to blob.push()");
                index = idx.integer;
        } else {
                arg = ARG(0);
        }

        switch (arg.type) {
        case VALUE_INTEGER:
                if (arg.integer < 0 || arg.integer > UCHAR_MAX)
                        zP("integer passed to blob.push() out of byte range");
                vvI(*blob->blob, arg.integer, index);
                break;
        case VALUE_BLOB:
                vvIn(*blob->blob, arg.blob->items, arg.blob->count, index);
                break;
        case VALUE_STRING:
                vvIn(*blob->blob, arg.string, arg.bytes, index);
                break;
        case VALUE_PTR:
                if (ARG(argc - 1).type != VALUE_INTEGER) {
                        zP("blob.push(): expected integer length after pointer argument");
                }
                vvIn(*blob->blob, arg.ptr, ARG(argc - 1).integer, index);
                break;
        default:
                zP("invalid argument passed to blob.push()");
        }

        return *blob;
}

static struct value
blob_size(Ty *ty, struct value *blob, int argc, struct value *kwargs)
{
        return INTEGER(blob->blob->count);
}

static struct value
blob_get(Ty *ty, struct value *blob, int argc, struct value *kwargs)
{
        if (argc != 1)
                zP("blob.get() expects 1 argument but got %d", argc);

        struct value i = ARG(0);
        if (i.type != VALUE_INTEGER)
                zP("the argument to blob.get() must be an integer");
        if (i.integer < 0)
                i.integer += blob->blob->count;
        if (i.integer < 0 || i.integer >= blob->blob->count)
                zP("blob.get(): invalid index: %"PRIiMAX, i.integer);

        return INTEGER(blob->blob->items[i.integer]);
}

static struct value
blob_fill(Ty *ty, struct value *blob, int argc, struct value *kwargs)
{
        if (argc != 0)
                zP("blob.fill() expects no arguments but got %d", argc);

        if (blob->blob->items == NULL)
                return NIL;

        memset(blob->blob->items + blob->blob->count, 0, blob->blob->capacity - blob->blob->count);
        blob->blob->count = blob->blob->capacity;

        return NIL;
}

static struct value
blob_set(Ty *ty, struct value *blob, int argc, struct value *kwargs)
{
        if (argc != 2)
                zP("blob.set() expects 2 arguments but got %d", argc);

        struct value i = ARG(0);
        if (i.type != VALUE_INTEGER)
                zP("the argument to blob.get() must be an integer");
        if (i.integer < 0)
                i.integer += blob->blob->count;
        if (i.integer < 0 || i.integer >= blob->blob->count)
                zP("invalid index passed to blob.get()");

        struct value arg = ARG(1);
        if (arg.type != VALUE_INTEGER || arg.integer < 0 || arg.integer > UCHAR_MAX)
                zP("invalid integer passed to blob.set()");

        blob->blob->items[i.integer] = arg.integer;

        return NIL;
}

static struct value
blob_xor(Ty *ty, struct value *blob, int argc, struct value *kwargs)
{
        if (argc == 1 && ARG(0).type == VALUE_BLOB) {
                struct blob *b = ARG(0).blob;
                if (b->count > 0) for (size_t i = 0; i < blob->blob->count; ++i) {
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

        uint8_t u8;
        uint16_t u16, *pu16;
        uint32_t u32, *pu32;
        uint64_t u64, *pu64;

        uint8_t size = ARG(1).integer;
        uint8_t r;

        switch (size) {
        case 1:
                u8 = ARG(0).integer;
                for (size_t i = 0; i < blob->blob->count; ++i) {
                        blob->blob->items[i] ^= u8;
                }
                break;
        case 2:
                u16 = ARG(0).integer;
                pu16 = (void *)blob->blob->items;
                for (size_t i = 0; i < blob->blob->count / 2; ++i) {
                        pu16[i] ^= u16;
                }
                r =  blob->blob->count % 2;
                for (int i = 0; i < r; ++i) {
                        blob->blob->items[blob->blob->count - r + i] ^= ((u16 >> (8 * i)) & 0xFF);
                }
                break;
        case 4:
                u32 = ARG(0).integer;
                pu32 = (void *)blob->blob->items;
                for (size_t i = 0; i < blob->blob->count / 4; ++i) {
                        pu32[i] ^= u32;
                }
                r =  blob->blob->count % 4;
                for (int i = 0; i < r; ++i) {
                        blob->blob->items[blob->blob->count - r + i] ^= ((u32 >> (8 * i)) & 0xFF);
                }
                break;
        case 8:
                u64 = ARG(0).integer;
                pu64 = (void *)blob->blob->items;
                for (size_t i = 0; i < blob->blob->count / 8; ++i) {
                        pu64[i] ^= u64;
                }
                r =  blob->blob->count % 8;
                for (int i = 0; i < r; ++i) {
                        blob->blob->items[blob->blob->count - r + i] ^= ((u64 >> (8 * i)) & 0xFF);
                }
                break;
        default:
                zP("blob.xor(): invalid mask size: %"PRIiMAX, ARG(1).integer);
        }

        return *blob;
}


static struct value
blob_str(Ty *ty, struct value *blob, int argc, struct value *kwargs)
{
        int start;
        int n;

        if (argc > 0 && ARG(0).type != VALUE_INTEGER)
                zP("the first argument to blob.str() must be an integer");

        if (argc > 1 && ARG(1).type != VALUE_INTEGER)
                zP("the second argument to blob.str() must be an integer");

        switch (argc) {
        case 0:
                start = 0;
                n = blob->blob->count;
                break;
        case 1:
                start = ARG(0).integer;
                n = blob->blob->count - start;
                break;
        case 2:
                start = ARG(0).integer;
                n = ARG(1).integer;
                break;
        default:
                zP("blob.str() expects 0, 1, or 2 arguments but got %d", argc);
        }

        if (start < 0 || n < 0 || (n + start) > blob->blob->count)
                zP("invalid arguments to blob.str()");

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

static struct value
blob_str_unsafe(Ty *ty, struct value *blob, int argc, struct value *kwargs)
{
        int start;
        int n;

        if (argc > 0 && ARG(0).type != VALUE_INTEGER)
                zP("the first argument to blob.str() must be an integer");

        if (argc > 1 && ARG(1).type != VALUE_INTEGER)
                zP("the second argument to blob.str() must be an integer");

        switch (argc) {
        case 0:
                start = 0;
                n = blob->blob->count;
                break;
        case 1:
                start = ARG(0).integer;
                n = blob->blob->count - start;
                break;
        case 2:
                start = ARG(0).integer;
                n = ARG(1).integer;
                break;
        default:
                zP("blob.str() expects 0, 1, or 2 arguments but got %d", argc);
        }

        if (start < 0 || n < 0 || (n + start) > blob->blob->count)
                zP("invalid arguments to blob.str()");

        return vSc((char const *)blob->blob->items + start, n);
}

static struct value
blob_reserve(Ty *ty, struct value *blob, int argc, struct value *kwargs)
{
        if (argc != 1)
                zP("blob.reserve() expects 1 argument but got %d", argc);

        struct value n = ARG(0);
        if (n.type != VALUE_INTEGER)
                zP("the argument to blob.reserve() must be an integer");
        if (n.integer < 0)
                zP("the argument to blob.reserve() must be non-negative");

        vvR(*blob->blob, n.integer);

        return NIL;
}

static struct value
blob_ptr(Ty *ty, struct value *blob, int argc, struct value *kwargs)
{
        if (argc == 0) {
                return PTR(blob->blob->items);
        }

        if (argc == 1) {
                if (ARG(0).type != VALUE_INTEGER) {
                        zP("blob.ptr() expects an integer but got %s", value_show(ty, &ARG(0)));
                }

                return PTR(blob->blob->items + ARG(0).integer);
        }

        zP("blob.ptr() expects 0 or 1 arguments but got %d", argc);
}

static struct value
blob_hex(Ty *ty, struct value *blob, int argc, struct value *kwargs)
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

static struct value
blob_slice(Ty *ty, struct value *blob, int argc, struct value *kwargs)
{
        int start = 0;
        int n = blob->blob->count;

        switch (argc) {
        case 2:
                if (ARG(1).type != VALUE_INTEGER)
                        zP("the second argument to blob.slice() must be an integer");
                n = ARG(1).integer;
        case 1:
                if (ARG(0).type != VALUE_INTEGER)
                        zP("the first argument to blob.slice() must be an integer");
                start = ARG(0).integer;
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

        struct blob *b = value_blob_new(ty);
        NOGC(b);
        vvPn(*b, blob->blob->items + start, n);
        OKGC(b);

        return BLOB(b);
}

static struct value
blob_splice(Ty *ty, struct value *blob, int argc, struct value *kwargs)
{
        int start = 0;
        int n = blob->blob->count;

        switch (argc) {
        case 2:
                if (ARG(1).type != VALUE_INTEGER)
                        zP("the second argument to blob.splice() must be an integer");
                n = ARG(1).integer;
        case 1:
                if (ARG(0).type != VALUE_INTEGER)
                        zP("the first argument to blob.splice() must be an integer");
                start = ARG(0).integer;
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

        struct blob *b = value_blob_new(ty);
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
DEFINE_METHOD_COMPLETER(blob)
