#ifndef HTAB_H_INCLUDED
#define HTAB_H_INCLUDED

#if !defined(HT) || !defined(HT_ITEM) || !defined(HT_PAYLOAD)
#error "htab.h needs HT, HT_ITEM and HT_PAYLOAD"
#endif

#include "ty.h"
#include "value.h"
#include "alloc.h"

#define HT_INITIAL_SIZE 8
#define HT_NONE         SIZE_MAX

#define HT_EMPTY(it) ((it)->k.type == VALUE_ZERO)
#define HT_TOMB(it)  ((it)->k.type == VALUE_TOMBSTONE)
#define HT_LIVE(t, i)                          \
        (                                      \
                ((i) != HT_NONE)               \
             && !HT_EMPTY(&(t)->items[i])      \
             && !HT_TOMB(&(t)->items[i])       \
        )

#define HT_ENSURE(t) do {               \
        if ((t)->size == 0) {           \
                ht_init(ty, (t));       \
        }                               \
} while (0)

#define htfor(it, t) for (HT_ITEM *it = (t)->first; it != NULL; it = it->next)

#define htfor_del(it, t)                                                 \
        for (                                                            \
                HT_ITEM *it = (t)->first, *it##_next;                    \
                (it != NULL) && ((it##_next = it->next), true);          \
                it = it##_next                                           \
        )

inline static void
ht_init(Ty *ty, HT *t)
{
        NOGC(t);
        t->items = mA0(sizeof (HT_ITEM) * HT_INITIAL_SIZE);
        t->size  = HT_INITIAL_SIZE;
        OKGC(t);
}

inline static bool
ht_crowded(HT const *t)
{
        return (4 * (t->count + t->tombs) >= 3 * t->size);
}

inline static usize
ht_find(Ty *ty, usize size, HT_ITEM const *items, u64 h, Value const *k)
{
        if (size == 0) {
                return HT_NONE;
        }

        usize mask = size - 1;
        usize i    = h & mask;
        usize tomb = HT_NONE;

        while (!HT_EMPTY(&items[i])) {
                if (items[i].h == h && v_eq(&items[i].k, k)) {
                        return i;
                }
                if (tomb == HT_NONE && HT_TOMB(&items[i])) {
                        tomb = i;
                }
                i = (i + 1) & mask;
        }

        return (tomb != HT_NONE) ? tomb : i;
}

inline static usize
ht_seek(Ty *ty, HT const *t, HT_ITEM const *it)
{
        return ht_find(ty, t->size, t->items, it->h, &it->k);
}

inline static usize
ht_lookup(Ty *ty, HT const *t, Value const *k)
{
        if (t->size == 0) {
                return HT_NONE;
        }

        usize i = ht_find(ty, t->size, t->items, value_hash(ty, k), k);

        return HT_LIVE(t, i) ? i : HT_NONE;
}

inline static bool
ht_holds(Ty *ty, HT const *t, HT_ITEM const *it)
{
        return HT_LIVE(t, ht_seek(ty, t, it));
}

inline static void
ht_link(HT *t, HT_ITEM *it)
{
        if (it->next != NULL) {
                it->next->prev = it;
        } else {
                t->last = it;
        }

        if (it->prev != NULL) {
                it->prev->next = it;
        } else {
                t->first = it;
        }
}

inline static void
ht_swap(HT *t, usize i, usize j)
{
        HT_ITEM *a = &t->items[i];
        HT_ITEM *b = &t->items[j];

        SWAP(HT_ITEM, *a, *b);

        if (a->next == a) { a->next = b; }
        if (a->prev == a) { a->prev = b; }
        if (b->next == b) { b->next = a; }
        if (b->prev == b) { b->prev = a; }

        ht_link(t, a);
        ht_link(t, b);
}

inline static usize
ht_robinhood(HT *t, usize i)
{
        usize size = t->size;
        usize mask = size - 1;
        HT_ITEM *items = t->items;

        usize lo = items[i].h & mask;
        usize hi = i;

        while (lo != hi) {
                usize lo_dist = (lo + size - (items[lo].h & mask)) & mask;
                usize hi_dist = (hi + size - (items[hi].h & mask)) & mask;

                if (hi_dist > lo_dist) {
                        ht_swap(t, lo, hi);
                        if (hi == i) {
                                i = lo;
                        }
                }

                lo = (lo + 1) & mask;
        }

        return i;
}

inline static HT_ITEM *
ht_fill(Ty *ty, usize size, HT_ITEM *items, HT_ITEM const *it, HT_ITEM **first)
{
        HT_ITEM *last = NULL;

        *first = NULL;

        for (; it != NULL; it = it->next) {
                HT_ITEM *slot = &items[ht_find(ty, size, items, it->h, &it->k)];

                *slot      = *it;
                slot->prev = last;
                slot->next = NULL;

                if (last != NULL) {
                        last->next = slot;
                } else {
                        *first = slot;
                }

                last = slot;
        }

        return last;
}

inline static void
ht_rehash(Ty *ty, HT *t, usize size)
{
        HT_ITEM *items = mA0(size * sizeof (HT_ITEM));

        t->last = ht_fill(ty, size, items, t->first, &t->first);

        mF(t->items);

        t->items = items;
        t->tombs = 0;
        t->size  = size;
}

inline static void
ht_copy(Ty *ty, HT *dst, HT const *src)
{
        if (src->count == 0) {
                return;
        }

        dst->items = mA0(src->size * sizeof (HT_ITEM));
        dst->size  = src->size;
        dst->count = src->count;
        dst->last  = ht_fill(ty, src->size, dst->items, src->first, &dst->first);
}

inline static usize
ht_delete(HT *t, usize i)
{
        HT_ITEM *it = &t->items[i];

        if (it->next != NULL) {
                it->next->prev = it->prev;
        } else {
                t->last = it->prev;
        }

        if (it->prev != NULL) {
                it->prev->next = it->next;
        } else {
                t->first = it->next;
        }

        m0(*it);
        it->k.type = VALUE_TOMBSTONE;

        t->count -= 1;
        t->tombs += 1;

        return i;
}

inline static usize
ht_claim(Ty *ty, HT *t, usize i, u64 h, Value const *k)
{
        if (ht_crowded(t)) {
                ht_rehash(ty, t, t->size * 2);
                i = ht_find(ty, t->size, t->items, h, k);
        }

        HT_ITEM *it = &t->items[i];

        t->tombs -= HT_TOMB(it);

        it->k    = *k;
        it->h    = h;
        it->prev = t->last;
        it->next = NULL;

        if (t->last != NULL) {
                t->last->next = it;
        } else {
                t->first = it;
        }

        t->last   = it;
        t->count += 1;

        return i;
}

inline static usize
ht_put(Ty *ty, HT *t, usize i, HT_ITEM const *src)
{
        i = ht_claim(ty, t, i, src->h, &src->k);
        HT_PAYLOAD(&t->items[i], src);
        return ht_robinhood(t, i);
}

inline static void
ht_clear(HT *t)
{
        if (t->items != NULL) {
                memset(t->items, 0, sizeof (HT_ITEM) * t->size);
        }

        t->first = NULL;
        t->last  = NULL;
        t->count = 0;
        t->tombs = 0;
}

inline static HT_ITEM *
ht_nth(HT const *t, isize i)
{
        HT_ITEM *it;

        if (i < t->count / 2) {
                for (it = t->first; i --> 0;) {
                        it = it->next;
                }
        } else {
                i = t->count - i - 1;
                for (it = t->last; i --> 0;) {
                        it = it->prev;
                }
        }

        return it;
}

inline static bool
ht_same_keys(Ty *ty, HT const *t, HT const *u)
{
        if (t->count != u->count) {
                return false;
        }

        htfor(it, t) {
                if (!ht_holds(ty, u, it)) {
                        return false;
                }
        }

        return true;
}

inline static bool
ht_covered(Ty *ty, HT const *t, HT const *u)
{
        if (t->count > u->count) {
                return false;
        }

        htfor(it, t) {
                if (!ht_holds(ty, u, it)) {
                        return false;
                }
        }

        return true;
}

inline static bool
ht_disjoint(Ty *ty, HT const *t, HT const *u)
{
        if (t->count > u->count) {
                SWAP(HT const *, t, u);
        }

        htfor(it, t) {
                if (ht_holds(ty, u, it)) {
                        return false;
                }
        }

        return true;
}

inline static void
ht_retain(Ty *ty, HT *t, HT const *u)
{
        htfor_del(it, t) {
                if (!ht_holds(ty, u, it)) {
                        ht_delete(t, it - t->items);
                }
        }
}

inline static void
ht_discard(Ty *ty, HT *t, HT const *u)
{
        if (t == u) {
                ht_clear(t);
                return;
        }

        if (t->count == 0) {
                return;
        }

        htfor(it, u) {
                usize i = ht_seek(ty, t, it);
                if (HT_LIVE(t, i)) {
                        ht_delete(t, i);
                }
        }
}

inline static void
ht_absorb(Ty *ty, HT *t, HT const *u)
{
        if (u->count == 0) {
                return;
        }

        HT_ENSURE(t);

        htfor(it, u) {
                usize i = ht_seek(ty, t, it);
                if (!HT_LIVE(t, i)) {
                        ht_put(ty, t, i, it);
                }
        }
}

inline static void
ht_unique(Ty *ty, HT *out, HT const *t, HT const *u)
{
        HT_ENSURE(out);

        htfor(it, t) {
                if (!ht_holds(ty, u, it)) {
                        ht_put(ty, out, ht_seek(ty, out, it), it);
                }
        }
}

#endif
