#ifndef OBJECT_H_INCLUDED
#define OBJECT_H_INCLUDED

#include "value.h"
#include "table.h"

struct table *
object_new(Ty *ty, int class);

void
object_mark(Ty *ty, struct table *obj);

#endif
