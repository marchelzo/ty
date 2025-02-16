#include <string.h>
#include <math.h>
#include <inttypes.h>

#include <ffi.h>

#include "alloc.h"
#include "class.h"
#include "dict.h"
#include "gc.h"
#include "operators.h"
#include "tthread.h"
#include "value.h"
#include "vec.h"
#include "vm.h"

enum {
        OP_CACHE_MISS = -2,
        OP_NO_IMPL    = -1
};

typedef struct {
        uint32_t t1;
        uint32_t t2;
        int      ref;
} OperatorSpec;

typedef struct {
        uint64_t key;
        int      ref;
} CacheEntry;

typedef vec(OperatorSpec) DispatchList;
typedef vec(CacheEntry)   DispatchCache;

typedef struct {
        TyRwLock      lock;
        DispatchCache cache;
        DispatchList  defs;
} DispatchGroup;


static struct {
        TyRwLock             lock;
        vec(DispatchGroup *) ops;
} _2 = {
        .lock = TY_RWLOCK_INIT
};

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
            hi = c->count - 1;

        while (lo <= hi) {
                int m = (lo + hi) / 2;
                if      (key < c->items[m].key) hi = m - 1;
                else if (key > c->items[m].key) lo = m + 1;
                else                            return c->items[m].ref;
        }

        return OP_CACHE_MISS;
}


inline static void
update_cache(DispatchCache *c, uint64_t key, int ref)
{
        xvP(*c, ((CacheEntry) { .key = key, .ref = ref }));

        for (int i = c->count - 1; i > 0 && c->items[i - 1].key > key; --i) {
                SWAP(CacheEntry, c->items[i], c->items[i - 1]);
        }
}

inline static bool
are_ordered(OperatorSpec const *a, OperatorSpec const *b)
{
        return (
                class_is_subclass(ty, a->t1, b->t1) &&
                class_is_subclass(ty, a->t2, b->t2) &&
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
                        class_is_subclass(ty, t1, op->t1) &&
                        class_is_subclass(ty, t2, op->t2) &&
                        (
                                (match == NULL) ||
                                are_ordered(op, match)
                        )
                ) {
                        match = op;
                }
        }

        return (match != NULL) ? match->ref : OP_NO_IMPL;
}

void
op_add(int op, int t1, int t2, int ref)
{
        dont_printf(
                "op_add(): %20s %4s   %-20s\n",
                class_name(ty, t1),
                intern_entry(&xD.b_ops, op)->name,
                class_name(ty, t2)
        );

        if (op >= _2.ops.count) {
                TyRwLockWrLock(&_2.lock);

                do {
                        DispatchGroup *group = mrealloc(NULL, sizeof *group);
                        *group = (DispatchGroup) { .lock = TY_RWLOCK_INIT };
                        xvP(_2.ops, group);

                } while (_2.ops.count <= op || _2.ops.count < _2.ops.capacity);

                TyRwLockWrUnlock(&_2.lock);
        }

        DispatchGroup *group = _2.ops.items[op];

        TyRwLockWrLock(&group->lock);

        xvP(
                group->defs,
                ((OperatorSpec) {
                        .t1  = t1,
                        .t2  = t2,
                        .ref = ref
                })
        );

        group->cache.count = 0;

        TyRwLockWrUnlock(&group->lock);
}

int
op_dispatch(int op, int t1, int t2)
{
        uint64_t key = forge_key(t1, t2);

        TyRwLockRdLock(&_2.lock);

        if (_2.ops.count <= op) {
                TyRwLockRdUnlock(&_2.lock);
                return OP_NO_IMPL;
        }

        DispatchGroup *group = _2.ops.items[op];

        TyRwLockRdUnlock(&_2.lock);
        TyRwLockRdLock(&group->lock);

        int ref = check_cache(&group->cache, key);

        TyRwLockRdUnlock(&group->lock);

        if (ref == OP_CACHE_MISS) {
                TyRwLockWrLock(&group->lock);

                ref = check_slow(&group->defs, t1, t2);
                update_cache(&group->cache, key, ref);

                TyRwLockWrUnlock(&group->lock);
        }

        return ref;
}

void
op_dump(int op)
{
        // TODO
}
