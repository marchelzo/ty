#ifndef UTIL_H_INCLUDED
#define UTIL_H_INCLUDED

#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <inttypes.h>
#include <stdbool.h>

uintmax_t
umax(uintmax_t a, uintmax_t b);

uintmax_t
umin(uintmax_t a, uintmax_t b);

intmax_t
max(intmax_t a, intmax_t b);

intmax_t
min(intmax_t a, intmax_t b);

char *
sclone(char const *s);

bool
contains(char const *s, char c);

char *slurp(char const *path);

/* memmem. maybe change this to Knuth-Morris-Pratt or Boyer-Moore at some point */
inline static char const *
strstrn(char const *haystack, int hn, char const *needle, int nn)
{
        for (int i = 0; i < hn - nn; ++i) {
                if (memcmp(haystack + i, needle, nn) == 0)
                        return haystack + i;
        }

        return NULL;
}

#endif
