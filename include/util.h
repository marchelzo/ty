#ifndef UTIL_H_INCLUDED
#define UTIL_H_INCLUDED

#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <inttypes.h>
#include <stdbool.h>
#include <unistd.h>

#define TERM(n) (isatty(2) ? ("\x1b[" #n "m") : "")
#define ERR_SIZE 4096

#define P_ALIGN (_Alignof (uintptr_t))

extern char ERR[ERR_SIZE];

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

inline static unsigned long
strhash(char const *s)
{
        unsigned long hash = 5381;

        while (*s != '\0')
                hash = ((hash << 5) + hash) + *s++; /* hash * 33 + c */

        return hash;
}

inline static int
gcd(int a, int b)
{
        while (b != 0) {
                int t = b;
                b = a % b;
                a = t;
        }

        return a;
}

#endif
