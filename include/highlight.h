#ifndef HIGHLIGHT_H_INCLUDED
#define HIGHLIGHT_H_INCLUDED

#include "ty.h"

void
syntax_highlight(Ty *ty, byte_vector *out, Module const *mod, usize start, usize end, char const *attr, char const *theme);

#endif

/* vim: set sts=8 sw=8 expandtab: */
