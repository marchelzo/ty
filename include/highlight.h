#ifndef HIGHLIGHT_H_INCLUDED
#define HIGHLIGHT_H_INCLUDED

#include "ty.h"

typedef struct literal_style {
        char const *text;
        char const *escape;
        char const *invalid;
} LiteralStyle;

void
highlight_string(Ty *ty, byte_vector *out, Bytes string, LiteralStyle style);

void
highlight_regex(Ty *ty, byte_vector *out, Regex const *regex, LiteralStyle style);

bool
syntax_highlight(
        Ty *ty,
        byte_vector *out,
        char const *source,
        TokenVector const *tokens,
        usize start,
        usize end,
        char const *attr,
        char const *theme
);

#endif

/* vim: set sts=8 sw=8 expandtab: */
