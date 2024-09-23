#include <string.h>
#include <math.h>

#include <ffi.h>

#include "alloc.h"
#include "value.h"
#include "operators.h"
#include "class.h"
#include "dict.h"
#include "vm.h"
#include "gc.h"

typedef struct {
        vec(int) refs;
        vec(uint64_t) keys;
        int64_t t;
} DispatchCache;

typedef struct {
        uint32_t t1;
        uint32_t t2;
        int ref;
} OperatorSpec;

typedef vec(OperatorSpec) DispatchList;

typedef vec(DispatchList) DispatchTable;

static DispatchTable OpTable;
static vec(DispatchCache) OpCache;

inline static uint64_t
forge_key(int t1, int t2)
{
        return (((uint64_t)t1) << 32) | ((uint32_t)t2);
}

inline static int
check_cache(DispatchCache const *c, uint64_t key)
{
        _Static_assert(CHAR_BIT * sizeof (int) <= 32, "this isn't gonna work");

        int lo = 0,
            hi = c->keys.count - 1;

        while (lo <= hi) {
                int m = (lo + hi) / 2;
                if      (key < c->keys.items[m]) hi = m - 1;
                else if (key > c->keys.items[m]) lo = m + 1;
                else                             return c->refs.items[m];
        }

        return -1;
}

inline static bool
are_ordered(OperatorSpec const *a, OperatorSpec const *b)
{
        return (
                class_is_subclass(&MainTy, a->t1, b->t1) &&
                class_is_subclass(&MainTy, a->t2, b->t2) &&
                (
                        a->t1 != b->t1 ||
                        a->t2 != b->t2
                )
        );
}

inline static int
check_slow(DispatchList const *list, int t1, int t2)
{
        OperatorSpec const *match = NULL;

        for (int i = 0; i < list->count; ++i) {
                OperatorSpec const *op = &list->items[i];
                if (t1 == op->t1 && t2 == op->t2) {
                        return op->ref;
                }
                if (
                        class_is_subclass(&MainTy, t1, op->t1) &&
                        class_is_subclass(&MainTy, t2, op->t2) &&
                        (
                                (match == NULL) ||
                                are_ordered(op, match)
                        )
                ) {
                        match = op;
                }
        }

        return (match != NULL) ? match->ref : -1;
}

void
op_add(int op, int t1, int t2, int ref)
{
        static DispatchList EmptyDispatchList;
        static DispatchCache EmptyDispatchCache;

        while (OpTable.count <= op) {
                xvP(OpTable, EmptyDispatchList);
                xvP(OpCache, EmptyDispatchCache);
        }

        xvP(
                OpTable.items[op],
                ((OperatorSpec){
                        .t1  = t1,
                        .t2  = t2,
                        .ref = ref
                })
        );
}

int
op_dispatch(int op, int t1, int t2)
{
        if (OpTable.count <= op)
                return -1;

        DispatchList *list = &OpTable.items[op];
        DispatchCache *cache = &OpCache.items[op];

        uint64_t key = forge_key(t1, t2);

        if (cache->t != list->count) {
                cache->keys.count = 0;
                cache->refs.count = 0;
                cache->t = list->count;
        } else {
                int ref = check_cache(cache, key);
                if (ref != -1) {
                        return ref;
                }
        }

        int ref = check_slow(list, t1, t2);

        xvP(cache->keys, key);
        xvP(cache->refs, ref);

        return ref;
}
