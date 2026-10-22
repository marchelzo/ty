#ifndef MOD_H_INCLUDED
#define MOD_H_INCLUDED

#include "defs.h"

typedef struct table PackageCache;

enum {
        PKG_IMPLICIT,
        PKG_LIBRARY,
        PKG_DECLARED
};

typedef struct package {
        char const *dir;
        char const *manifest;
        ConstStringVector roots;
        ConstStringVector deps;
        u64 gen;
        u8 kind;
        bool read;
        bool reading;
} Package;

void
mod_init(TY *ty);

Package *
mod_package(Ty *ty, char const *from);

char const *
mod_root(Ty *ty, char const *path);

char const *
mod_resolve(Ty *ty, char const *name, char const *from, bool library, ConstStringVector *tried);

char *
mod_name(Ty *ty, char const *dotted);

char const *
mod_kind_name(Package const *pkg);

#endif

/* vim: set sts=8 sw=8 expandtab: */
