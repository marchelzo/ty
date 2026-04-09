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

void
object_mark(Ty *ty, TyObject *o)
{
        if (MARKED(o)) return;

        MARK(o);

        for (int i = 0; i < o->nslot; ++i) {
                _value_mark_xd(ty, &o->slots[i]);
        }

        if (o->dynamic != NULL) {
                for (int i = 0; i < vN(o->dynamic->values); ++i) {
                        _value_mark_xd(ty, v_(o->dynamic->values, i));
                }
        }
}

/* vim: set sts=8 sw=8 expandtab: */
