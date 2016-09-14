#include <limits.h>

#include "blob.h"
#include "value.h"
#include "vm.h"
#include "util.h"
#include "utf8.h"

static struct value
blob_clear(struct value *blob, value_vector *args)
{
        int start;
        int n;

        if (args->count > 0 && args->items[0].type != VALUE_INTEGER)
                vm_panic("the first argument to blob.clear() must be an integer");

        if (args->count > 1 && args->items[1].type != VALUE_INTEGER)
                vm_panic("the second argument to blob.clear() must be an integer");

        switch (args->count) {
        case 0:
                start = 0;
                n = blob->blob->count;
                break;
        case 1:
                start = args->items[0].integer;
                n = blob->blob->count - start;
                break;
        case 2:
                start = args->items[0].integer;
                n = args->items[1].integer;
                break;
        default:
                vm_panic("blob.clear() expects 0, 1, or 2 arguments but got %zu", args->count);
        }

        if (start < 0 || n < 0 || (n + start) > blob->blob->count)
                vm_panic("invalid arguments to blob.clear()");

        memmove(blob->blob->items + start, blob->blob->items + start + n, blob->blob->count - start - n);
        blob->blob->count -= n;

        return NIL;
}

static struct value
blob_search(struct value *blob, value_vector *args)
{

        struct value start;
        struct value c;

        switch (args->count) {
        case 1:
                start = INTEGER(0);
                c = args->items[0];
                break;
        case 2:
                start = args->items[0];
                c = args->items[1];
                break;
        default:
                vm_panic("blob.search() expects 1 or 2 arguments but got %zu", args->count);
        }

        if (start.type != VALUE_INTEGER)
                vm_panic("the offset argument to blob.search() must be an integer");

        if (start.integer < 0 || start.integer > blob->blob->count)
                vm_panic("invalid offset passed to blob.search()");

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
                        vm_panic("invalid integer passed to blob.search()");
                s = memchr(haystack, c.integer, n);
                break;
        default:
                vm_panic("invalid argument passed to blob.search()");
        }

        return (s == NULL) ? NIL : INTEGER(s - haystack + start.integer);
}

static struct value
blob_shrink(struct value *blob, value_vector *args)
{
        resize(blob->blob->items, blob->blob->count);
        blob->blob->capacity = blob->blob->count;
        return NIL;
}

static struct value
blob_push(struct value *blob, value_vector *args)
{
        size_t index = blob->blob->count;
        struct value arg;

        if (args->count == 2) {
                arg = args->items[1];
                struct value idx = args->items[0];
                if (idx.type != VALUE_INTEGER)
                        vm_panic("the index passed to blob.push() must be an integer");
                if (idx.integer < 0)
                        idx.integer += blob->blob->count;
                if (idx.integer < 0 || idx.integer > blob->blob->count)
                        vm_panic("invalid index passed to blob.push()");
                index = idx.integer;
        } else {
                arg = args->items[0];
        }

        switch (arg.type) {
        case VALUE_INTEGER:
                if (arg.integer < 0 || arg.integer > UCHAR_MAX)
                        vm_panic("integer passed to blob.push() out of byte range");
                vec_insert(*blob->blob, arg.integer, index);
                break;
        case VALUE_BLOB:
                vec_insert_n(*blob->blob, arg.blob->items, arg.blob->count, index);
                break;
        case VALUE_STRING:
                vec_insert_n(*blob->blob, arg.string, arg.bytes, index);
                break;
        default:
                vm_panic("invalid argument passed to blob.push()");
        }

        return NIL;
}

static struct value
blob_size(struct value *blob, value_vector *args)
{
        return INTEGER(blob->blob->count);
}

static struct value
blob_get(struct value *blob, value_vector *args)
{
        if (args->count != 1)
                vm_panic("blob.get() expects 1 argument but got %zu", args->count);

        struct value i = args->items[0];
        if (i.type != VALUE_INTEGER)
                vm_panic("the argument to blob.get() must be an integer");
        if (i.integer < 0)
                i.integer += blob->blob->count;
        if (i.integer < 0 || i.integer >= blob->blob->count)
                vm_panic("invalid index passed to blob.get()");

        return INTEGER(blob->blob->items[i.integer]);
}

static struct value
blob_str(struct value *blob, value_vector *args)
{
        int start;
        int n;

        if (args->count > 0 && args->items[0].type != VALUE_INTEGER)
                vm_panic("the first argument to blob.str() must be an integer");

        if (args->count > 1 && args->items[1].type != VALUE_INTEGER)
                vm_panic("the second argument to blob.str() must be an integer");

        switch (args->count) {
        case 0:
                start = 0;
                n = blob->blob->count;
                break;
        case 1:
                start = args->items[0].integer;
                n = blob->blob->count - start;
                break;
        case 2:
                start = args->items[0].integer;
                n = args->items[1].integer;
                break;
        default:
                vm_panic("blob.str() expects 0, 1, or 2 arguments but got %zu", args->count);
        }

        if (start < 0 || n < 0 || (n + start) > blob->blob->count)
                vm_panic("invalid arguments to blob.str()");

        if (!utf8_valid((char *)blob->blob->items + start, n))
                return NIL;

        return STRING_CLONE((char *)blob->blob->items + start, n);
}

static struct value
blob_reserve(struct value *blob, value_vector *args)
{
        if (args->count != 1)
                vm_panic("blob.reserve() expects 1 argument but got %zu", args->count);

        struct value n = args->items[0];
        if (n.type != VALUE_INTEGER)
                vm_panic("the argument to blob.reserve() must be an integer");
        if (n.integer < 0)
                vm_panic("the argument to blob.reserve() must be non-negative");

        vec_reserve(*blob->blob, n.integer);

        return NIL;
}

DEFINE_METHOD_TABLE(
        { .name = "clear",    .func = blob_clear     },
        { .name = "get",      .func = blob_get       },
        { .name = "push",     .func = blob_push      },
        { .name = "reserve",  .func = blob_reserve   },
        { .name = "search",   .func = blob_search    },
        { .name = "shrink",   .func = blob_shrink    },
        { .name = "size",     .func = blob_size      },
        { .name = "str",      .func = blob_str       },
);

DEFINE_METHOD_LOOKUP(blob)
