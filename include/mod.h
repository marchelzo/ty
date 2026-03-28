#ifndef MOD_H_INCLUDED
#define MOD_H_INCLUDED

#include "defs.h"

typedef struct table PackageCache;

void
mod_init(TY *ty);

char const *
mod_root(Ty *ty, char const *path);

#endif

/* vim: set sts=8 sw=8 expandtab: */
