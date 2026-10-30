#ifndef DIRS_H_INCLUDED
#define DIRS_H_INCLUDED

#include "defs.h"

#define TY_DIRS(X)        \
        X(HOME)           \
        X(CACHE)          \
        X(CONFIG)         \
        X(CONFIG_LOCAL)   \
        X(DATA)           \
        X(DATA_LOCAL)     \
        X(PREFERENCES)    \
        X(EXECUTABLES)    \
        X(RUNTIME)        \
        X(STATE)          \
        X(AUDIO)          \
        X(DESKTOP)        \
        X(DOCUMENTS)      \
        X(DOWNLOADS)      \
        X(FONTS)          \
        X(PICTURES)       \
        X(PUBLIC)         \
        X(TEMPLATES)      \
        X(VIDEOS)

enum {
#define X(d) DIR_##d,
        TY_DIRS(X)
#undef X
        DIR_COUNT
};

extern char const *const DirNames[DIR_COUNT];

char const *
dirs_get(int which);

Bytes
dirs_tmp(void);

bool
dirs_affected(char const *var);

void
dirs_reload(void);

bool
dirs_path(char *out, usize n, int which, char const *fmt, ...);

#endif

/* vim: set sts=8 sw=8 expandtab: */
