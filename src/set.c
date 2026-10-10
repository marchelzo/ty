#include <string.h>
#include <stdbool.h>

#include "ty.h"
#include "alloc.h"
#include "xd.h"
#include "value.h"
#include "set.h"
#include "vm.h"
#include "gc.h"
#include "vec.h"

#define HT                 Set
#define HT_ITEM            SetItem
#define HT_PAYLOAD(it, src) ((void)(it), (void)(src))
#include "htab.h"

inline static SetItem
item(Ty *ty, Value const *x)
{
        return (SetItem) { .k = *x, .h = value_hash(ty, x) };
}

inline static bool
add(Ty *ty, Set *s, SetItem const *it)
{
        HT_ENSURE(s);

        usize i = ht_seek(ty, s, it);

        if (HT_LIVE(s, i)) {
                return false;
        }

        ht_put(ty, s, i, it);

        return true;
}

bool
set_add(Ty *ty, Set *s, Value x)
{
        gP(&x);
        SetItem it = item(ty, &x);
        bool added = add(ty, s, &it);
        gX();

        return added;
}

void
set_add_all(Ty *ty, Set *s, Value xs)
{
        Value x;

        switch (xs.type) {
        case VALUE_SET:
                ht_absorb(ty, s, xs.set);
                break;

        case VALUE_ARRAY:
                for (usize i = 0; i < vN(*xs.array); ++i) {
                        set_add(ty, s, v__(*xs.array, i));
                }
                break;

        case VALUE_TUPLE:
                for (int i = 0; i < xs.count; ++i) {
                        set_add(ty, s, xs.items[i]);
                }
                break;

        case VALUE_DICT:
                for (DictItem *it = xs.dict->first; it != NULL; it = it->next) {
                        add(ty, s, &(SetItem) { .k = it->k, .h = it->h });
                }
                break;

        default:
                vm_iter_begin(ty, xs);
                while (vm_iter_next(ty, &x)) {
                        set_add(ty, s, x);
                }
        }
}

bool
set_has(Ty *ty, Set const *s, Value const *x)
{
        return ht_lookup(ty, s, x) != HT_NONE;
}

bool
set_has_hashed(Ty *ty, Set const *s, u64 h, Value const *x)
{
        return HT_LIVE(s, ht_find(ty, s->size, s->items, h, x));
}

bool
set_remove(Ty *ty, Set *s, Value const *x)
{
        usize i = ht_lookup(ty, s, x);

        if (i == HT_NONE) {
                return false;
        }

        ht_delete(s, i);

        return true;
}

Set *
SetClone(Ty *ty, Set const *s)
{
        Set *new = set_new(ty);

        NOGC(new);
        ht_copy(ty, new, s);
        OKGC(new);

        return new;
}

Set *
SetAbsorb(Ty *ty, Set *s, Set const *t)
{
        ht_absorb(ty, s, t);
        return s;
}

Set *
SetRetain(Ty *ty, Set *s, Set const *t)
{
        ht_retain(ty, s, t);
        return s;
}

Set *
SetDiscard(Ty *ty, Set *s, Set const *t)
{
        ht_discard(ty, s, t);
        return s;
}

Set *
SetToggle(Ty *ty, Set *s, Set const *t)
{
        if (s == t) {
                ht_clear(s);
                return s;
        }

        htfor(it, t) {
                HT_ENSURE(s);
                usize i = ht_seek(ty, s, it);
                if (HT_LIVE(s, i)) {
                        ht_delete(s, i);
                } else {
                        ht_put(ty, s, i, it);
                }
        }

        return s;
}

Set *
SetUnion(Ty *ty, Set const *s, Set const *t)
{
        Set *new = SetClone(ty, s);

        NOGC(new);
        ht_absorb(ty, new, t);
        OKGC(new);

        return new;
}

Set *
SetIntersect(Ty *ty, Set const *s, Set const *t)
{
        Set *new = set_new(ty);

        if (s->count > t->count) {
                SWAP(Set const *, s, t);
        }

        NOGC(new);
        htfor(it, s) {
                if (ht_holds(ty, t, it)) {
                        add(ty, new, it);
                }
        }
        OKGC(new);

        return new;
}

Set *
SetSubtract(Ty *ty, Set const *s, Set const *t)
{
        Set *new = set_new(ty);

        NOGC(new);
        ht_unique(ty, new, s, t);
        OKGC(new);

        return new;
}

Set *
SetSymDiff(Ty *ty, Set const *s, Set const *t)
{
        Set *new = set_new(ty);

        NOGC(new);
        ht_unique(ty, new, s, t);
        ht_unique(ty, new, t, s);
        OKGC(new);

        return new;
}

bool
set_equal(Ty *ty, Set const *s, Set const *t)
{
        return (s == t) || ht_same_keys(ty, s, t);
}

bool
set_equal_x(Ty *ty, Set const *s, Set const *t, ValueEqFn *eq, void *ctx)
{
        if (s == t) {
                return true;
        }

        if (s->count != t->count) {
                return false;
        }

        htfor(it, s) {
                if (ht_find_x(ty, t, it->h, &it->k, eq, ctx) == HT_NONE) {
                        return false;
                }
        }

        return true;
}

int
set_order(Ty *ty, Set const *s, Set const *t)
{
        if (s->count == t->count) {
                return ht_same_keys(ty, s, t) ? SET_EQUAL : SET_UNRELATED;
        }

        return (s->count < t->count)
             ? (ht_covered(ty, s, t) ? SET_SUBSET   : SET_UNRELATED)
             : (ht_covered(ty, t, s) ? SET_SUPERSET : SET_UNRELATED);
}

u64
set_hash(Set const *s)
{
        u64 h = hash64(s->count ^ 0x5E75E75E75E75E7ULL);

        htfor(it, s) {
                h += hash64(it->h);
        }

        return h;
}

void
set_mark(Ty *ty, Set *s)
{
        if (MARKED(s)) return;

        MARK(s);

#if defined(TY_TRACE_GC)
        if (s->size > 0) {
                ADD_REACHED(ALLOC_OF(s->items)->size);
        }
#endif

        htfor(it, s) {
                xvP(ty->marking, &it->k);
        }
}

void
set_free(Ty *ty, Set *s)
{
        mF(s->items);
}

inline static Set *
set_arg(Ty *ty, int argc, int i)
{
        Value xs = ARG(i);

        if (xs.type == VALUE_SET) {
                return xs.set;
        }

        Value s = SET(set_new(ty));

        gP(&s);
        set_add_all(ty, s.set, xs);
        gX();

        ARG(i) = s;

        return s.set;
}

Value
builtin_set(Ty *ty, int argc, Value *kwargs)
{
        ASSERT_ARGC("Set()", 0, 1);

        Value s = SET(set_new(ty));

        if (argc == 1) {
                gP(&s);
                set_add_all(ty, s.set, ARG(0));
                gX();
        }

        return s;
}

static Value
set_add_m(Ty *ty, Value *self, int argc, Value *kwargs)
{
        ASSERT_ARGC_MIN("Set.add()", 1);

        for (int i = 0; i < argc; ++i) {
                set_add(ty, self->set, ARG(i));
        }

        return *self;
}

static Value
set_insert(Ty *ty, Value *self, int argc, Value *kwargs)
{
        ASSERT_ARGC("Set.insert()", 1);
        return BOOLEAN(set_add(ty, self->set, ARG(0)));
}

static Value
set_remove_m(Ty *ty, Value *self, int argc, Value *kwargs)
{
        ASSERT_ARGC("Set.remove()", 1);
        return BOOLEAN(set_remove(ty, self->set, &ARG(0)));
}

static Value
set_contains(Ty *ty, Value *self, int argc, Value *kwargs)
{
        ASSERT_ARGC("Set.contains?()", 1);
        return BOOLEAN(set_has(ty, self->set, &ARG(0)));
}

static Value
set_len(Ty *ty, Value *self, int argc, Value *kwargs)
{
        ASSERT_ARGC("Set.len()", 0);
        return INTEGER(self->set->count);
}

static Value
set_clear(Ty *ty, Value *self, int argc, Value *kwargs)
{
        ASSERT_ARGC("Set.clear()", 0);
        ht_clear(self->set);
        return *self;
}

static Value
set_clone(Ty *ty, Value *self, int argc, Value *kwargs)
{
        ASSERT_ARGC("Set.clone()", 0);
        return SET(SetClone(ty, self->set));
}

static Value
set_pop(Ty *ty, Value *self, int argc, Value *kwargs)
{
        ASSERT_ARGC("Set.pop()", 0, 1);

        Set  *s = self->set;
        isize i = (argc == 1) ? INT_ARG(0) : -1;

        if (i < 0) {
                i += s->count;
        }
        if (i < 0 || i >= s->count) {
                bP("index %jd out of range [0, %zu)", i, s->count);
        }

        SetItem *it = ht_nth(s, i);
        Value popped = it->k;

        ht_delete(s, it - s->items);

        return popped;
}

static Value
set_to_array(Ty *ty, Value *self, int argc, Value *kwargs)
{
        ASSERT_ARGC("Set.toArray()", 0);

        Array *xs = vAn(self->set->count);
        htfor(it, self->set) {
                vPx(*xs, it->k);
        }

        return ARRAY(xs);
}

static Value
set_keep(Ty *ty, Value *self, int argc, Value *kwargs)
{
        ASSERT_ARGC("Set.keep()", 1);

        Value f   = ARG(0);
        Value new = SET(set_new(ty));

        gP(&new);
        htfor(it, self->set) {
                Value keep = vm_call1(ty, &f, &it->k);
                if (value_truthy(ty, &keep)) {
                        add(ty, new.set, it);
                }
        }
        gX();

        return new;
}

static Value
set_keep_mut(Ty *ty, Value *self, int argc, Value *kwargs)
{
        ASSERT_ARGC("Set.keep!()", 1);

        Value f = ARG(0);
        Set  *s = self->set;

        htfor_del(it, s) {
                Value keep = vm_call1(ty, &f, &it->k);
                if (!value_truthy(ty, &keep)) {
                        ht_delete(s, it - s->items);
                }
        }

        return *self;
}

static Value
set_update(Ty *ty, Value *self, int argc, Value *kwargs)
{
        ASSERT_ARGC_MIN("Set.update()", 1);

        for (int i = 0; i < argc; ++i) {
                set_add_all(ty, self->set, ARG(i));
        }

        return *self;
}

static Value
set_intersect(Ty *ty, Value *self, int argc, Value *kwargs)
{
        ASSERT_ARGC("Set.intersect()", 1);
        SetRetain(ty, self->set, set_arg(ty, argc, 0));
        return *self;
}

static Value
set_subtract(Ty *ty, Value *self, int argc, Value *kwargs)
{
        ASSERT_ARGC("Set.subtract()", 1);
        SetDiscard(ty, self->set, set_arg(ty, argc, 0));
        return *self;
}

static Value
set_diff(Ty *ty, Value *self, int argc, Value *kwargs)
{
        ASSERT_ARGC("Set.diff()", 1);
        return SET(SetSymDiff(ty, self->set, set_arg(ty, argc, 0)));
}

static Value
set_subset(Ty *ty, Value *self, int argc, Value *kwargs)
{
        ASSERT_ARGC("Set.subset?()", 1);
        return BOOLEAN(ht_covered(ty, self->set, set_arg(ty, argc, 0)));
}

static Value
set_superset(Ty *ty, Value *self, int argc, Value *kwargs)
{
        ASSERT_ARGC("Set.superset?()", 1);
        return BOOLEAN(ht_covered(ty, set_arg(ty, argc, 0), self->set));
}

static Value
set_disjoint(Ty *ty, Value *self, int argc, Value *kwargs)
{
        ASSERT_ARGC("Set.disjoint?()", 1);
        return BOOLEAN(ht_disjoint(ty, self->set, set_arg(ty, argc, 0)));
}

static Value
set_ptr(Ty *ty, Value *self, int argc, Value *kwargs)
{
        ASSERT_ARGC("Set.ptr()", 0);
        return PTR(self->set);
}

DEFINE_METHOD_TABLE(
        set,
        { .name = "add",       .func = set_add_m     },
        { .name = "clear",     .func = set_clear     },
        { .name = "clone",     .func = set_clone     },
        { .name = "contains?", .func = set_contains  },
        { .name = "diff",      .func = set_diff      },
        { .name = "disjoint?", .func = set_disjoint  },
        { .name = "insert",    .func = set_insert    },
        { .name = "intersect", .func = set_intersect },
        { .name = "keep",      .func = set_keep      },
        { .name = "keep!",     .func = set_keep_mut  },
        { .name = "len",       .func = set_len       },
        { .name = "pop",       .func = set_pop       },
        { .name = "ptr",       .func = set_ptr       },
        { .name = "remove",    .func = set_remove_m  },
        { .name = "subset?",   .func = set_subset    },
        { .name = "subtract",  .func = set_subtract  },
        { .name = "superset?", .func = set_superset  },
        { .name = "toArray",   .func = set_to_array  },
        { .name = "update",    .func = set_update    },
);

DEFINE_METHOD_LOOKUP(set);
DEFINE_METHOD_TABLE_BUILDER(set);
DEFINE_METHOD_COMPLETER(set);
