#ifndef TITLE_H_INCLUDED
#define TITLE_H_INCLUDED

#include "defs.h"

extern char **TyArgv;
extern int    TyArgc;
extern usize  TyTitleSize;

void
TyTitleInit(int argc, char **argv);

#endif
/* vim: set sts=8 sw=8 expandtab: */
