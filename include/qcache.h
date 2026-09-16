#ifndef QCACHE_H_INCLUDED
#define QCACHE_H_INCLUDED

#include "defs.h"

void *queue_cache_take(void);
bool queue_cache_put(void *p);
u32 queue_cpu_hint(u32 fallback);

#endif
