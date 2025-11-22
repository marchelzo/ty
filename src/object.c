#include <string.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdbool.h>

#include "alloc.h"
#include "xd.h"
#include "value.h"
#include "object.h"
#include "itable.h"
#include "class.h"
#include "gc.h"

struct itable *
object_new(Ty *ty, int class)
{
        struct itable *t =  mAo0(sizeof *t, GC_OBJECT);

        NOGC(t);
        class_init_object(ty, class, t);
        OKGC(t);

        return t;
}

void
object_mark(Ty *ty, struct itable *o)
{
        if (MARKED(o)) return;

        MARK(o);

        for (int i = 0; i < vN(o->values); ++i) {
                xvP(ty->marking, v_(o->values, i));
        }
}

/* vim: set sts=8 sw=8 expandtab: */
