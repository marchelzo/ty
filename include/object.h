#ifndef OBJECT_H_INCLUDED
#define OBJECT_H_INCLUDED

#include "value.h"
#include "itable.h"

struct itable *
object_new(Ty *ty, int class);

void
object_mark(Ty *ty, struct itable *obj);

#endif
