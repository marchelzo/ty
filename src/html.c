#include <gumbo.h>

#include "value.h"
#include "alloc.h"
#include "vec.h"
#include "vm.h"
#include "itable.h"
#include "object.h"
#include "util.h"
#include "gc.h"

static struct value
convert_node(Ty *ty, GumboNode const *n, struct itable *p);

inline static struct value
convert_text(Ty *ty, GumboText const *t)
{
        return vSsz(t->text);
}

inline static struct value
convert_attr(Ty *ty, GumboAttribute const *a)
{
        struct itable *t = object_new(ty, 0);
        NOGC(t);

        itable_put(ty, t, "name", vSsz(a->name));
        itable_put(ty, t, "value", vSsz(a->value));

        OKGC(t);

        return OBJECT(t, 0);
}

static struct value
convert_elem(Ty *ty, GumboElement const *e, struct itable *n)
{
        struct itable *t = object_new(ty, 0);
        NOGC(t);

        struct array *cs = vA();
        NOGC(cs);

        for (int i = 0; i < e->children.length; ++i) {
                vAp(cs, convert_node(ty, e->children.data[i], n));
        }


        itable_put(ty, t, "children", ARRAY(cs));
        itable_put(ty, t, "t", vSsz(gumbo_normalized_tagname(e->tag)));

        struct array *as = vA();
        NOGC(as);

        for (int i = 0; i < e->attributes.length; ++i) {
                vAp(as, convert_attr(ty, e->attributes.data[i]));
        }

        itable_put(ty, t, "attributes", ARRAY(as));

        OKGC(as);
        OKGC(cs);
        OKGC(t);

        return OBJECT(t, 0);
}

static struct value
convert_doc(Ty *ty, GumboDocument const *d)
{
        struct itable *t = object_new(ty, 0);
        NOGC(t);

        itable_put(ty, t, "has_doctype", BOOLEAN(!!d->has_doctype));
        itable_put(ty, t, "name", vSsz(d->name));
        itable_put(ty, t, "public_id", vSsz(d->public_identifier));
        itable_put(ty, t, "system_id", vSsz(d->system_identifier));

        OKGC(t);
        return OBJECT(t, 0);
}

static struct value
convert_node(Ty *ty, GumboNode const *n, struct itable *p)
{
        struct itable *t = object_new(ty, 0);
        NOGC(t);
        itable_put(ty, t, "type", INTEGER(n->type));
        itable_put(ty, t, "parent", (p == NULL) ? NIL : OBJECT(p, 0));
        itable_put(ty, t, "index", INTEGER(n->index_within_parent));

        switch (n->type) {
        case GUMBO_NODE_DOCUMENT:
                itable_put(ty, t, "document", convert_doc(ty, &n->v.document));
                break;
        case GUMBO_NODE_ELEMENT:
                itable_put(ty, t, "element", convert_elem(ty, &n->v.element, t));
                break;
        default:
                itable_put(ty, t, "text", convert_text(ty, &n->v.text));
        }

        OKGC(t);
        return OBJECT(t, 0);
}

static struct value
convert(Ty *ty, GumboOutput const *out)
{
        struct itable *t = object_new(ty, 0);
        NOGC(t);

        itable_put(ty, t, "root", convert_node(ty, out->root, NULL));
        itable_put(ty, t, "document", convert_node(ty, out->document, NULL));

        OKGC(t);

        return OBJECT(t, 0);
}

struct value
html_parse(Ty *ty, int argc, struct value *kwargs)
{
        if (argc != 1) {
                zP("gumbo::parse(ty) expects 1 argument but got %d", argc);
        }

        struct value s = ARG(0);
        vec(char) b = {0};

        if (s.type == VALUE_STRING) {
                vvPn(b, s.string, s.bytes);
        } else if (s.type == VALUE_BLOB) {
                vvPn(b, s.blob->items, s.blob->count);
        } else {
                zP("the argument to gumbo::parse(ty) must be a string or a blob");
        }

        vvP(b, '\0');
        GumboOutput *out = gumbo_parse(b.items);

        if (out == NULL) {
                vec_empty(b);
                return NIL;
        } else {
                GC_STOP();
                struct value v = convert(ty, out);
                GC_RESUME();
                vec_empty(b);
                gumbo_destroy_output(&kGumboDefaultOptions, out);
                return v;
        }
}
