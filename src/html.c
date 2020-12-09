#include <gumbo.h>

#include "value.h"
#include "alloc.h"
#include "vec.h"
#include "vm.h"
#include "table.h"
#include "object.h"

static struct value
convert_node(GumboNode const *n, struct table *p);

inline static struct value
S(char const *s)
{
        return STRING_CLONE(s, strlen(s));
}

inline static struct value
convert_text(GumboText const *t)
{
        return S(t->text);
}

inline static struct value
convert_attr(GumboAttribute const *a)
{
        struct table *t = object_new();
        NOGC(t);

        table_add(t, "name", S(a->name));
        table_add(t, "value", S(a->value));

        OKGC(t);

        return OBJECT(t, 0);
}

static struct value
convert_elem(GumboElement const *e, struct table *n)
{
        struct table *t = object_new();
        NOGC(t);

        struct array *cs = value_array_new();
        NOGC(cs);

        for (int i = 0; i < e->children.length; ++i) {
                value_array_push(cs, convert_node(e->children.data[i], n));
        }


        table_add(t, "children", ARRAY(cs));
        table_add(t, "t", S(gumbo_normalized_tagname(e->tag)));

        struct array *as = value_array_new();
        NOGC(as);

        for (int i = 0; i < e->attributes.length; ++i) {
                value_array_push(as, convert_attr(e->attributes.data[i]));
        }

        table_add(t, "attributes", ARRAY(as));

        OKGC(as);
        OKGC(cs);
        OKGC(t);

        return OBJECT(t, 0);
}

static struct value
convert_doc(GumboDocument const *d)
{
        struct table *t = object_new();
        NOGC(t);

        table_add(t, "has_doctype", BOOLEAN(!!d->has_doctype));
        table_add(t, "name", S(d->name));
        table_add(t, "public_id", S(d->public_identifier));
        table_add(t, "system_id", S(d->system_identifier));

        OKGC(t);
        return OBJECT(t, 0);
}

static struct value
convert_node(GumboNode const *n, struct table *p)
{
        struct table *t = object_new();
        NOGC(t);
        table_add(t, "type", INTEGER(n->type));
        table_add(t, "parent", (p == NULL) ? NIL : OBJECT(p, 0));
        table_add(t, "index", INTEGER(n->index_within_parent));

        switch (n->type) {
        case GUMBO_NODE_DOCUMENT:
                table_add(t, "document", convert_doc(&n->v.document));
                break;
        case GUMBO_NODE_ELEMENT:
                table_add(t, "element", convert_elem(&n->v.element, t));
                break;
        default:
                table_add(t, "text", convert_text(&n->v.text));
        }

        OKGC(t);
        return OBJECT(t, 0);
}

static struct value
convert(GumboOutput const *out)
{
        struct table *t = object_new();
        NOGC(t);

        table_add(t, "root", convert_node(out->root, NULL));
        table_add(t, "document", convert_node(out->document, NULL));

        OKGC(t);

        return OBJECT(t, 0);
}

struct value
html_parse(value_vector *args)
{
        if (args->count != 1) {
                vm_panic("gumbo::parse() expects 1 argument but got %zu", args->count);
        }

        struct value s = args->items[0];
        vec(char) b = {0};

        if (s.type == VALUE_STRING) {
                vec_push_n(b, s.string, s.bytes);
        } else if (s.type == VALUE_BLOB) {
                vec_push_n(b, s.blob->items, s.blob->count);
        } else {
                vm_panic("the argument to gumbo::parse() must be a string or a blob");
        }

        vec_push(b, '\0');
        GumboOutput *out = gumbo_parse(b.items);

        if (out == NULL) {
                vec_empty(b);
                return NIL;
        } else {
                struct value v = convert(out);
                vec_empty(b);
                gumbo_destroy_output(&kGumboDefaultOptions, out);
                return v;
        }
}
