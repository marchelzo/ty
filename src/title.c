#include <stdio.h>

#include "title.h"
#include "ty.h"

extern char **environ;

char **TyArgv;
int    TyArgc;
usize  TyTitleSize;

typedef struct {
        char *data;
        usize idx;
} EnvironEntry;

static int
entrycmp(const void *_a, const void *_b)
{
        uptr a = (uptr)((EnvironEntry *)_a)->data;
        uptr b = (uptr)((EnvironEntry *)_b)->data;
        return (a < b) ? -1 : (a > b);
}

void
TyTitleInit(
        int argc
      , char **argv
#ifdef __APPLE__
      , char const *env_end
#endif
)
{
#ifdef __APPLE__
        char ***_NSGetArgv();

        char **clone = xtA(char *, argc + 1);
        for (int i = 0; i < argc; ++i) {
                clone[i] = S2(argv[i]);
        }
        clone[argc] = NULL;

        *_NSGetArgv() = clone;
#else
        FILE *stat = fopen("/proc/self/stat", "r");
        if (stat == NULL) {
                return;
        }

        uptr addr = 0;
        for (int i = 0; i < 51; ++i) {
                fscanf(stat, "%ju", &addr);
        }

        char *env_end = (char *)addr;
#endif
        TyArgc = argc;
        TyArgv = argv;

        uptr beg = (uptr)argv[0];
        uptr end = (uptr)env_end;

        TyTitleSize = (end - beg) + 1;

        for (usize i = 0; environ[i] != NULL; ++i) {
                uptr env_addr = (uptr)environ[i];
                if (env_addr >= beg && env_addr < end) {
                        environ[i] = S2(environ[i]);
                }
        }
}
/* vim: set sts=8 sw=8 expandtab: */
