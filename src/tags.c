#include <stdbool.h>
#include <string.h>

#include "alloc.h"
#include "log.h"
#include "vec.h"

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

        for (int i = 0; i < t->links.count; ++i) {
                if (t->links.items[i].tag == tag) {
                        return t->links.items[i].t->n;
                }
        }

        struct tags *new = mklist(tag, t);
        vec_push(t->links, ((struct link){ .t = new, .tag = tag }));

        return new->n;
}

int
tags_pop(int n)
{
        LOG("trying to pop with n = %d", n);
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
        static vec(char) cs = { .items = 0, .count = 0, .capacity = 0 };

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

        while (n --> 0) {
                vec_push(cs, ')');
        }

        vec_push(cs, '\0');

        cs.count = 0;

        return cs.items;
}

char const *
tags_name(int tag)
{
        return names.items[tag - 1];
}
