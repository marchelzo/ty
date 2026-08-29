#include "title.h"
#include "ty.h"

char **TyArgv;
int    TyArgc;
usize  TyTitleSize;

void
TyTitleInit(int argc, char **argv)
{
#ifdef __APPLE__
        char ***_NSGetArgv();

        char **clone = xtA(char *, argc + 1);
        for (int i = 0; i < argc; ++i) {
                clone[i] = S2(argv[i]);
        }
        clone[argc] = NULL;

        *_NSGetArgv() = clone;
#endif
        TyArgc = argc;
        TyArgv = argv;
        TyTitleSize = strlen(argv[0]) + 1;

        for (int i = 1; argv[i] == argv[0] + TyTitleSize; ++i) {
                TyTitleSize += strlen(argv[i]) + 1;
        }
}
/* vim: set sts=8 sw=8 expandtab: */
