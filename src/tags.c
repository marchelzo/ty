#include <stdbool.h>
#include <string.h>

#include "value.h"
#include "alloc.h"
#include "log.h"
#include "util.h"
#include "vec.h"
#include "table.h"

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
static vec(struct table) tables;

static struct tags *
mklist(int tag, struct tags *next)
{
        struct tags *t = alloc(sizeof *t);

        vec_init(t->links);
        t->n = lists.count;
        t->tag = tag;
        t->next = next;

        vec_push(lists, t);

        return t;
}

void
tags_init(void)
{
        mklist(tagcount++, NULL);
}

int
tags_new(char const *tag)
{
        LOG("making new tag: %s -> %d", tag, tagcount);

        vec_push(names, tag);

        struct table table;
        table_init(&table);
        vec_push(tables, table);

        mklist(tagcount, lists.items[0]);
        return tagcount++;
}

bool
tags_same(int t1, int t2)
{
        return (lists.items[t1]->tag == lists.items[t2]->tag);
}

int
tags_push(int n, int tag)
{

        LOG("tags_push: n = %d, tag = %d", n, tag);

        struct tags *t = lists.items[n];

        for (int i = 0; i < t->links.count; ++i)
                if (t->links.items[i].tag == tag)
                        return t->links.items[i].t->n;

        struct tags *new = mklist(tag, t);
        vec_push(t->links, ((struct link){ .t = new, .tag = tag }));

        return new->n;
}

int
tags_pop(int n)
{
        return lists.items[n]->next->n;
}

int
tags_first(int tags)
{
        return lists.items[tags]->tag;
}

/*
 * Wraps a string in the tag labels specified by 'tags'.
 */
char *
tags_wrap(char const *s, int tags)
{
        vec(char) cs = {0};

        struct tags *list = lists.items[tags];
        int n = 0;
        while (list->tag != 0) {
                char const *name = names.items[list->tag - 1];
                vec_push_n(cs, name, strlen(name));
                vec_push(cs, '(');
                list = list->next;
                ++n;
        }

        vec_push_n(cs, s, strlen(s));

        while (n --> 0)
                vec_push(cs, ')');

        vec_push(cs, '\0');

        return cs.items;
}

int
tags_lookup(char const *name)
{
     for (int i = 0; i < names.count; ++i)
          if (strcmp(names.items[i], name) == 0)
               return i + 1;

     return -1;
}

char const *
tags_name(int tag)
{
        return names.items[tag - 1];
}

void
tags_add_method(int tag, char const *name, struct value f)
{
        LOG("tag = %d", tag);
        LOG("adding method %s to tag %s", name, names.items[tag - 1]);
        table_add(&tables.items[tag - 1], name, strhash(name), f);
}

void
tags_copy_methods(int dst, int src)
{
        struct table *dt = &tables.items[dst - 1];
        struct table const *st = &tables.items[src - 1];
        table_copy(dt, st);
}

struct value *
tags_lookup_method(int tag, char const *name, unsigned h)
{
        struct table const *t = &tables.items[tag - 1];
        return table_lookup(t, name, h);
}
