#ifndef DYNLIB_H_INCLUDED
#define DYNLIB_H_INCLUDED

#include <stdlib.h>

#include "polyfill_dlfcn.h"

inline static void *
DynOpen(char const *env, char const *const *names)
{
        char const *path = (env != NULL) ? getenv(env) : NULL;

        if (path != NULL && *path != '\0') {
                return dlopen(path, RTLD_NOW | RTLD_GLOBAL);
        }

        for (char const *const *name = names; *name != NULL; ++name) {
                void *lib = dlopen(*name, RTLD_NOW | RTLD_GLOBAL);
                if (lib != NULL) {
                        return lib;
                }
        }

        return NULL;
}

inline static bool
DynBind(void *lib, void **slots, char const *const *names, char const **missing)
{
        for (int i = 0; names[i] != NULL; ++i) {
                slots[i] = dlsym(lib, names[i]);
                if (slots[i] == NULL) {
                        *missing = names[i];
                        return false;
                }
        }

        return true;
}

#endif
/* vim: set sts=8 sw=8 expandtab: */
