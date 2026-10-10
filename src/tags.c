#include <stdbool.h>
#include <string.h>

#include "ty.h"
#include "value.h"
#include "alloc.h"
#include "log.h"
#include "xd.h"
#include "vec.h"
#include "itable.h"

#include "ty/thread.h"

typedef struct class Class;
struct tags;

struct link {
        int tag;
        struct tags *t;
};

struct links {
        int n;
        struct links *prev;
        struct link items[];
};

struct tags {
        int n;
        int tag;
        struct tags *next;
        _Atomic(struct links *) links;
};

static struct links nil;

static TyMutex lock;
static u32 nlists;
static _Atomic(struct tags *) lists[1 << (8 * sizeof ((Value){0}).tags)];

static u32 next_id = 0;

static vec(char const *) names;
static vec(struct itable) tables;
static vec(struct itable) statics;
static vec(Class *) classes;

[[gnu::always_inline]]
inline static struct tags *
L(int n)
{
        return atomic_load_explicit(&lists[n], memory_order_acquire);
}

static struct tags *
mklist(int tag, struct tags *next)
{
        struct tags *t = alloc0(sizeof *t);

        t->n     = nlists++;
        t->tag   = tag;
        t->next  = next;
        t->links = &nil;

        atomic_store_explicit(&lists[t->n], t, memory_order_release);

        return t;
}

[[gnu::always_inline]]
inline static struct tags *
follow(struct links const *ls, int tag)
{
        for (int i = 0; i < ls->n; ++i) {
                if (ls->items[i].tag == tag) {
                        return ls->items[i].t;
                }
        }

        return NULL;
}

static struct links *
snoc(struct links *old, struct link link)
{
        int n = old->n;
        struct links *new = alloc0(sizeof *new + (n + 1) * sizeof new->items[0]);

        memcpy(new->items, old->items, n * sizeof new->items[0]);

        new->n        = n + 1;
        new->prev     = old;
        new->items[n] = link;

        return new;
}

static struct tags *
extend(Ty *ty, struct tags *list, int tag)
{
        struct links *ls;
        struct tags *t;

        TyMutexLock(&lock);

        ls = atomic_load_explicit(&list->links, memory_order_relaxed);
        t  = follow(ls, tag);

        if (UNLIKELY(t == NULL) && UNLIKELY(nlists < countof(lists))) {
                t = mklist(tag, list);
                atomic_store_explicit(
                        &list->links,
                        snoc(ls, (struct link) { .tag = tag, .t = t }),
                        memory_order_release
                );
        }

        TyMutexUnlock(&lock);

        if (t == NULL) {
                zP("too many distinct tag chains (limit is %zu)", countof(lists));
        }

        return t;
}

void
tags_init(Ty *ty)
{
        TyMutexInit(&lock);

        next_id = 0;
        nlists  = 0;

        v0(names);
        v0(tables);
        v0(statics);
        v0(classes);

        mklist(next_id++, NULL);
}

void
tags_set_class(Ty *ty, int tag, Class *c)
{
        *v_(classes, tag - 1) = c;
}

Class *
tags_get_class(Ty *ty, int tag)
{
        if (tag < 1 || tag > vN(classes)) {
                return NULL;
        }

        return v__(classes, tag - 1);
}

int
tags_new(Ty *ty, char const *tag)
{
        LOG("making new tag: %s -> %d", tag, next_id);

        TyMutexLock(&lock);

        xvP(names, tag);

        struct itable table;

        itable_init(ty, &table);
        xvP(tables, table);

        itable_init(ty, &table);
        xvP(statics, table);

        xvP(classes, NULL);

        mklist(next_id, L(0));

        int id = next_id++;

        TyMutexUnlock(&lock);

        return id;
}

bool
tags_same(Ty *ty, int t1, int t2)
{
        return L(t1)->tag == L(t2)->tag;
}

int
tags_push(Ty *ty, int tags, int tag)
{
        struct tags *list = L(tags);
        struct tags *t = follow(
                atomic_load_explicit(&list->links, memory_order_acquire),
                tag
        );

        return (t ?: extend(ty, list, tag))->n;
}

int
tags_pop(Ty *ty, int tags)
{
        return L(tags)->next->n;
}

bool
tags_try_pop(Ty *ty, u16 *tags, int tag)
{
        struct tags *list = L(*tags);

        if (list->tag == tag) {
                *tags = list->next->n;
                return true;
        } else {
                return false;
        }
}

int
tags_first(Ty *ty, int tags)
{
        return L(tags)->tag;
}

/*
 * Wraps a string in the tag labels specified by 'tags'.
 */
char *
tags_wrap(Ty *ty, char const *s, int tags, bool color)
{
        byte_vector cs = {0};

        struct tags *list = L(tags);

        if (color && list->tag != 0) {
                svPn(cs, TERM(94), strlen(TERM(94)));
        }

        i32 n = 0;
        while (list->tag != 0) {
                char const *name = names.items[list->tag - 1];
                svPn(cs, name, strlen(name));
                svP(cs, '(');
                list = list->next;
                n += 1;
        }

        if (color && n > 0) {
                svPn(cs, TERM(0), strlen(TERM(0)));
        }

        svPn(cs, s, strlen(s));

        if (color && n > 0) {
                svPn(cs, TERM(94), strlen(TERM(94)));
        }

        for (i32 i = 0; i < n; ++i) {
                svP(cs, ')');
        }

        if (color && n > 0) {
                svPn(cs, TERM(0), strlen(TERM(0)));
        }

        svP(cs, '\0');

        return vv(cs);
}

char *
tags_open(Ty *ty, int tags, bool color)
{
        byte_vector cs = {0};

        struct tags *list = L(tags);

        if (color && list->tag != 0) {
                svPn(cs, TERM(94), strlen(TERM(94)));
        }

        while (list->tag != 0) {
                char const *name = names.items[list->tag - 1];
                svPn(cs, name, strlen(name));
                svP(cs, '(');
                list = list->next;
        }

        if (color && vN(cs) > 0) {
                svPn(cs, TERM(0), strlen(TERM(0)));
        }

        svP(cs, '\0');

        return vv(cs);
}

char *
tags_close(Ty *ty, int tags, bool color)
{
        byte_vector cs = {0};

        struct tags *list = L(tags);

        i32 n = 0;
        while (list->tag != 0) {
                list = list->next;
                n += 1;
        }

        if (n > 0) {
                if (color) {
                        svPn(cs, TERM(94), strlen(TERM(94)));
                }

                for (i32 i = 0; i < n; ++i) {
                        svP(cs, ')');
                }

                if (color) {
                        svPn(cs, TERM(0), strlen(TERM(0)));
                }
        }

        svP(cs, '\0');

        return vv(cs);
}

int
tags_count(Ty *ty)
{
        return names.count;
}

char const *
tags_name(Ty *ty, int tag)
{
        if (tag < 1 || tag > vN(names)) {
                return NULL;
        }

        return names.items[tag - 1];
}

void
tags_add_method(Ty *ty, int tag, char const *name, struct value f)
{
        LOG("tag = %d", tag);
        LOG("adding method %s to tag %s", name, names.items[tag - 1]);
        itable_put(ty, &tables.items[tag - 1], name, f);
}

void
tags_add_static(Ty *ty, int tag, char const *name, Value f)
{
        LOG("tag = %d", tag);
        LOG("adding method %s to tag %s", name, names.items[tag - 1]);
        itable_put(ty, &statics.items[tag - 1], name, f);
}

void
tags_copy_methods(Ty *ty, int dst, int src)
{
        struct itable *dt = &tables.items[dst - 1];
        struct itable const *st = &tables.items[src - 1];
        itable_copy(ty, dt, st);

        dt = &statics.items[dst - 1];
        st = &statics.items[src - 1];
        itable_copy(ty, dt, st);
}

Value *
tags_lookup_method_i(Ty *ty, int tag, int i)
{
        struct itable const *t = &tables.items[tag - 1];
        return itable_lookup(ty, t, i);
}

Value *
tags_lookup_static(Ty *ty, int tag, int i)
{
        struct itable const *t = &statics.items[tag - 1];
        return itable_lookup(ty, t, i);
}
