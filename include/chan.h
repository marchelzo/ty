#ifndef CHAN_H_INCLUDED
#define CHAN_H_INCLUDED

#include "ty.h"
#include "value.h"

void
chan_send(Ty *ty, Channel *chan, Value v);

bool
chan_recv(Ty *ty, Channel *chan, Value *v);

bool
chan_try_recv(Ty *ty, Channel *chan, Value *v, i64 timeout);

void
chan_destroy(Ty *ty, Channel *chan);

#endif
/* vim: set sw=8 sts=8 expandtab: */
