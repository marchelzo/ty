#ifndef OBJECT_H_INCLUDED
#define OBJECT_H_INCLUDED

#include "value.h"
#include "table.h"

struct table *
object_new(void);

void
object_mark(struct table *obj);

#endif
