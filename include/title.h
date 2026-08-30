#ifndef TITLE_H_INCLUDED
#define TITLE_H_INCLUDED

#include "defs.h"

extern char **TyArgv;
extern int    TyArgc;
extern usize  TyTitleSize;

#if defined(__APPLE__)
void
TyTitleInit(int argc, char **argv, char const *env_end);
#else
void
TyTitleInit(int argc, char **argv);
#endif

#endif
/* vim: set sts=8 sw=8 expandtab: */
