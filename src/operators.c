#include <string.h>
#include <math.h>
#include <inttypes.h>

#include <ffi.h>

#include "alloc.h"
#include "ast.h"
#include "class.h"
#include "dict.h"
#include "gc.h"
#include "operators.h"
#include "tthread.h"
#include "value.h"
#include "vec.h"
#include "types.h"
#include "vm.h"

enum {
        OP_CACHE_MISS = -2,
        OP_NO_IMPL    = -1
};

typedef struct {
        i32   t1;
        i32   t2;
        i32   ref;
        Expr *expr;
} OperatorSpec;

typedef vec(OperatorSpec) DispatchList;

typedef struct {
        TyRwLock      lock;
        DispatchCache cache;
        DispatchList  defs;
        Type *op0;
} DispatchGroup;

static struct {
        TyRwLock             lock;
        vec(DispatchGroup *) ops;
} _2 = {
        .lock = TY_RWLOCK_INIT
};

inline static u64
key_for(i32 t1, i32 t2)
{
        return (((u64)t1) << 32) | ((u32)t2);
}

inline static i32
check_cache(DispatchCache const *c, u64 key)
{
        _Static_assert(CHAR_BIT * sizeof (i32) <= 32, "this isn't gonna work");

        i32 lo = 0,
            hi = c->count - 1;

        while (lo <= hi) {
                i32 m = (lo + hi) / 2;
                if      (key < c->items[m].key) hi = m - 1;
                else if (key > c->items[m].key) lo = m + 1;
                else    return c->items[m].ref;
        }

        return OP_CACHE_MISS;
}


inline static void
update_cache(DispatchCache *c, u64 key, i32 ref)
{
        xvP(*c, ((CacheEntry) { .key = key, .ref = ref }));

        for (i32 i = vN(*c) - 1; i > 0 && v_(*c, i - 1)->key > key; --i) {
                SWAP(
                        CacheEntry,
                        v__(*c, i),
                        v__(*c, i - 1)
                );
        }
}

inline static bool
are_ordered(OperatorSpec const *a, OperatorSpec const *b)
{
        return (
                class_is_subclass(&vvv, a->t1, b->t1)
             && class_is_subclass(&vvv, a->t2, b->t2)
             && (
                        (a->t1 != b->t1)
                     || (a->t2 != b->t2)
                )
        );
}

inline static i32
check_slow(DispatchList const *list, i32 t1, i32 t2)
{
        OperatorSpec const *match = NULL;

        for (i32 i = 0; i < list->count; ++i) {
                OperatorSpec const *op = &list->items[i];
                if (op->ref == -1) {
                        continue;
                }
                if (t1 == op->t1 && t2 == op->t2) {
                        return op->ref;
                }
                if (
                        class_is_subclass(&vvv, t1, op->t1)
                     && class_is_subclass(&vvv, t2, op->t2)
                     && (
                                (match == NULL)
                             || are_ordered(op, match)
                        )
                ) {
                        match = op;
                }
        }

        return (match != NULL) ? match->ref : OP_NO_IMPL;
}

inline static Expr *
find_op_fun(DispatchList const *list, i32 t1, i32 t2)
{
        OperatorSpec const *match = NULL;

        for (i32 i = 0; i < list->count; ++i) {
                OperatorSpec const *op = &list->items[i];
                if (t1 == op->t1 && t2 == op->t2) {
                        return op->expr;
                }
                if (
                        class_is_subclass(&vvv, t1, op->t1)
                     && class_is_subclass(&vvv, t2, op->t2)
                     && (
                                match == NULL
                             || are_ordered(op, match)
                        )
                ) {
                        match = op;
                }
        }

        return (match == NULL) ? NULL : match->expr;
}

void
op_add(i32 op, i32 t1, i32 t2, i32 ref, Expr *expr)
{
        dont_printf(
                "op_add(): %20s %4s   %-20s\n",
                class_name(&vvv, t1),
                intern_entry(&xD.b_ops, op)->name,
                class_name(&vvv, t2)
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
                        .t1   = t1,
                        .t2   = t2,
                        .ref  = ref,
                        .expr = expr
                })
        );

        v0(group->cache);
        group->op0 = NULL;

        TyRwLockWrUnlock(&group->lock);
}

static i32
op_xdispatch(i32 op, i32 t1, i32 t2)
{
        u64 key = key_for(t1, t2);

        TyRwLockRdLock(&_2.lock);

        if (_2.ops.count <= op) {
                TyRwLockRdUnlock(&_2.lock);
                return OP_NO_IMPL;
        }

        DispatchGroup *group = _2.ops.items[op];

        TyRwLockRdUnlock(&_2.lock);
        TyRwLockRdLock(&group->lock);

        i32 ref = check_cache(&group->cache, key);

        TyRwLockRdUnlock(&group->lock);

        if (ref == OP_CACHE_MISS) {
                TyRwLockWrLock(&group->lock);

                ref = check_slow(&group->defs, t1, t2);
                update_cache(&group->cache, key, ref);

                TyRwLockWrUnlock(&group->lock);
        }

        return ref;
}

i32
op_dispatch(Ty *ty, i32 op, i32 t1, i32 t2)
{
        u64 key = key_for(t1, t2);

        if (op >= vN(ty->_2op_cache)) {
                goto SlowPath;
        }

        DispatchCache *cache = v_(ty->_2op_cache, op);
        i32 ref = check_cache(cache, key);

        if (ref != OP_CACHE_MISS) {
                return ref;
        }

SlowPath:
        ref = op_xdispatch(op, t1, t2);

        while (vN(ty->_2op_cache) <= op) {
                xvP(ty->_2op_cache, ((DispatchCache) {0}));
        }

        update_cache(v_(ty->_2op_cache, op), key, ref);

        return ref;
}

Expr *
op_fun_info(i32 op, i32 t1, i32 t2)
{
        TyRwLockRdLock(&_2.lock);

        if (_2.ops.count <= op) {
                TyRwLockRdUnlock(&_2.lock);
                return NULL;
        }

        DispatchGroup *group = _2.ops.items[op];
        TyRwLockRdUnlock(&_2.lock);

        TyRwLockWrLock(&group->lock);
        Expr *expr = find_op_fun(&group->defs, t1, t2);
        TyRwLockWrUnlock(&group->lock);

        return expr;
}

i32
op_defs_for(i32 op, i32 c, bool left, ExprVec *defs)
{
        Ty *ty = &vvv;

        TyRwLockRdLock(&_2.lock);

        if (_2.ops.count <= op) {
                TyRwLockRdUnlock(&_2.lock);
                puts("none");
                return 0;
        }

        i32 n = 0;

        DispatchGroup *group = _2.ops.items[op];
        TyRwLockRdUnlock(&_2.lock);

        TyRwLockWrLock(&group->lock);
        for (i32 i = 0; i < vN(group->defs); ++i) {
                Expr *fun = v_(group->defs, i)->expr;
                i32 t1 = v_(group->defs, i)->t1;
                i32 t2 = v_(group->defs, i)->t2;
                if (
                        fun->_type != NULL
                     && class_is_subclass(&vvv, c, (left ? t1 : t2))
                ) {
                        avP(*defs, fun);
                        n += 1;
                }
        }
        TyRwLockWrUnlock(&group->lock);

        return n;
}

i32
op_defs_for_l(i32 op, i32 c, ExprVec *defs)
{
        return op_defs_for(op, c, true, defs);
}

i32
op_defs_for_r(i32 op, i32 c, ExprVec *defs)
{
        return op_defs_for(op, c, false, defs);
}

Type *
op_member_type(i32 op, i32 c, bool left)
{
        TyRwLockRdLock(&_2.lock);

        if (_2.ops.count <= op) {
                TyRwLockRdUnlock(&_2.lock);
                return NULL;
        }

        Type *t0 = NULL;

        DispatchGroup *group = _2.ops.items[op];
        TyRwLockRdUnlock(&_2.lock);

        TyRwLockWrLock(&group->lock);
        for (i32 i = 0; i < vN(group->defs); ++i) {
                Expr const *fun = v_(group->defs, i)->expr;
                i32 t1 = v_(group->defs, i)->t1;
                i32 t2 = v_(group->defs, i)->t2;
                if (
                        (fun->_type != NULL)
                     && ((left ? t1 : t2) == c)
                ) {
                        t0 = type_both(&vvv, t0, fun->_type);
                }
        }
        TyRwLockWrUnlock(&group->lock);

        return t0;
}

Type *
op_member_type_l(i32 op, i32 c)
{
        return op_member_type(op, c, true);
}

Type *
op_member_type_r(i32 op, i32 c)
{
        return op_member_type(op, c, false);
}

Type *
op_type(Ty *ty, i32 op)
{
        Type *t0 = NULL;
        TypeVector types = {0};
        DispatchGroup *group;

        TyRwLockRdLock(&_2.lock);
        if (_2.ops.count <= op) {
                TyRwLockRdUnlock(&_2.lock);
                return NULL;
        }
        group = _2.ops.items[op];
        TyRwLockRdUnlock(&_2.lock);

        SCRATCH_SAVE();

        TyRwLockRdLock(&group->lock);
        dont_printf("op_type(%s)  (%u defs):\n", intern_entry(&xD.b_ops, op)->name, vN(group->defs));
        if (group->op0 == NULL) {
                /*
                 * Snapshot the type pointers while holding the lock.
                 */
                for (i32 i = 0; i < vN(group->defs); ++i) {
                        Expr const *fun = v_(group->defs, i)->expr;
                        if (fun->_type != NULL && fun->return_type != NULL) {
                                svP(types, fun->_type);
                        }
                }
                TyRwLockRdUnlock(&group->lock);

                /*
                 * Build the intersection incrementally outside the lock.
                 * Update group->op0 after each step so that recursive
                 * op_type calls (via type_both -> Reduce -> BindConstraint)
                 * see the progressively-built result and terminate.
                 */
                for (i32 i = 0; i < vN(types); ++i) {
                        t0 = type_both(ty, t0, v__(types, i));
                        TyRwLockWrLock(&group->lock);
                        group->op0 = t0;
                        TyRwLockWrUnlock(&group->lock);
                }
        } else {
                t0 = group->op0;
                TyRwLockRdUnlock(&group->lock);
        }

        SCRATCH_RESTORE();

        dont_printf("op_type(%s): %s\n", intern_entry(&xD.b_ops, op)->name, type_show(ty, t0));

        return t0;
}

void
op_dump(i32 op)
{
        // TODO
}
