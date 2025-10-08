#include <stdbool.h>
#include <string.h>

#include "ty.h"
#include "value.h"
#include "alloc.h"
#include "log.h"
#include "util.h"
#include "vec.h"
#include "itable.h"

typedef struct class Class;
struct tags;

struct link {
        int tag;
        struct tags *t;
};

struct tags {
        int n;
        int tag;
        struct tags *next;
        vec(struct link) links;
};

static int tagcount = 0;
static vec(struct tags *) lists;
static vec(char const *) names;
static vec(struct itable) tables;
static vec(struct itable) statics;
static vec(Class *) classes;

static struct tags *
mklist(int tag, struct tags *next)
{
        struct tags *t = NULL;
        resize_nogc(t, sizeof *t);

        vec_init(t->links);
        t->n = lists.count;
        t->tag = tag;
        t->next = next;

        vec_nogc_push(lists, t);

        return t;
}

void
tags_init(Ty *ty)
{
        mklist(tagcount++, NULL);
}

void
tags_set_class(Ty *ty, int tag, Class *c)
{
        *v_(classes, tag - 1) = c;
}

Class *
tags_get_class(Ty *ty, int tag)
{
        return v__(classes, tag - 1);
}

int
tags_new(Ty *ty, char const *tag)
{
        LOG("making new tag: %s -> %d", tag, tagcount);

        vec_nogc_push(names, tag);

        struct itable table;

        itable_init(ty, &table);
        xvP(tables, table);

        itable_init(ty, &table);
        xvP(statics, table);

        xvP(classes, NULL);

        mklist(tagcount, lists.items[0]);
        return tagcount++;
}

bool
tags_same(Ty *ty, int t1, int t2)
{
        return (lists.items[t1]->tag == lists.items[t2]->tag);
}

int
tags_push(Ty *ty, int n, int tag)
{

        LOG("tags_push: n = %d, tag = %d", n, tag);

        struct tags *t = lists.items[n];

        for (int i = 0; i < t->links.count; ++i)
                if (t->links.items[i].tag == tag)
                        return t->links.items[i].t->n;

        struct tags *new = mklist(tag, t);
        vec_nogc_push(t->links, ((struct link){ .t = new, .tag = tag }));

        return new->n;
}

int
tags_pop(Ty *ty, int n)
{
        return lists.items[n]->next->n;
}

int
tags_first(Ty *ty, int tags)
{
        return lists.items[tags]->tag;
}

/*
 * Wraps a string in the tag labels specified by 'tags'.
 */
char *
tags_wrap(Ty *ty, char const *s, int tags, bool color)
{
        vec(char) cs = {0};

        struct tags *list = lists.items[tags];

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

int
tags_lookup(Ty *ty, char const *name)
{
        for (int i = 0; i < names.count; ++i)
                if (strcmp(names.items[i], name) == 0)
                        return i + 1;

        return -1;
}

char const *
tags_name(Ty *ty, int tag)
{
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
