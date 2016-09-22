#include <stdbool.h>
#include <string.h>

#include "value.h"
#include "alloc.h"
#include "log.h"
#include "util.h"
#include "vec.h"

enum {
        METHOD_TABLE_SIZE = 16
};

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

struct method_bucket {
        vec(uint64_t) hashes;
        vec(char const *) names;
        vec(struct value) methods;
};

struct method_table {
        struct method_bucket buckets[METHOD_TABLE_SIZE];
};

static int tagcount = 0;
static vec(struct tags *) lists;
static vec(char const *) names;
static vec(struct method_table) method_tables;

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
        vec_init(lists);
        vec_init(names);
        tagcount = 0;
        mklist(tagcount++, NULL);
}

int
tags_new(char const *tag)
{
        LOG("making new tag: %s -> %d", tag, tagcount);

        vec_push(names, tag);

        struct method_table table;
        vec_push(method_tables, table);

        for (int i = 0; i < METHOD_TABLE_SIZE; ++i) {
                vec_init(method_tables.items[tagcount - 1].buckets[i].hashes);
                vec_init(method_tables.items[tagcount - 1].buckets[i].names);
                vec_init(method_tables.items[tagcount - 1].buckets[i].methods);
        }

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
char const *
tags_wrap(char const *s, int tags)
{
        static vec(char) cs;

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

        cs.count = 0;

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
        uint64_t h = strhash(name);
        int i = h % METHOD_TABLE_SIZE;

        struct value *m = tags_lookup_method(tag, name);
        if (m != NULL) {
                *m = f;
                return;
        }

        vec_push(method_tables.items[tag - 1].buckets[i].hashes, h);
        vec_push(method_tables.items[tag - 1].buckets[i].names, name);
        vec_push(method_tables.items[tag - 1].buckets[i].methods, f);
}

void
tags_copy_methods(int dst, int src)
{
        struct method_bucket *dt = method_tables.items[dst - 1].buckets;
        struct method_bucket *st = method_tables.items[src - 1].buckets;

        for (int i = 0; i < METHOD_TABLE_SIZE; ++i) {
                if (st[i].hashes.count == 0)
                        continue;
                vec_push_n(
                        dt[i].hashes,
                        st[i].hashes.items,
                        st[i].hashes.count
                );
                vec_push_n(
                        dt[i].names,
                        st[i].names.items,
                        st[i].names.count
                );
                vec_push_n(
                        dt[i].methods,
                        st[i].methods.items,
                        st[i].methods.count
                );
        }
}

struct value *
tags_lookup_method(int tag, char const *name)
{
        uint64_t h = strhash(name);
        int i = h % METHOD_TABLE_SIZE;

        struct method_bucket const *b = &method_tables.items[tag - 1].buckets[i];

        for (int i = 0; i < b->hashes.count; ++i) {
                if (b->hashes.items[i] != h)
                        continue;
                if (strcmp(b->names.items[i], name) == 0)
                        return &b->methods.items[i];
        }

        return NULL;
}
