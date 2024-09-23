#ifndef UTIL_H_INCLUDED
#define UTIL_H_INCLUDED

#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <inttypes.h>
#include <stdbool.h>
#include "polyfill_unistd.h"
#include <pcre.h>

#include "value.h"

#ifdef max
#undef max
#endif

#ifdef min
#undef min
#endif

#define PTERM(n) \
        ( \
                ( \
                        (ProfileOut == stderr && isatty(2)) || \
                        (ProfileOut == stdout && isatty(1)) \
                ) \
                ? ("\x1b[" #n "m") : "" \
        )
#define TERM(n) (isatty(2) ? ("\x1b[" #n "m") : "")
#define ERR_SIZE 4096

#define SWAP(t, a, b) do { t tmp = a; a = b; b = tmp; } while (0)

#define P_ALIGN (_Alignof (uintptr_t))

#ifdef TY_UNSAFE
#define FALSE_OR(x) if (false)
#define TRUE_OR(x) if (true)
#else
#define FALSE_OR(x) if (x)
#define TRUE_OR(x) if (!(x))
#endif

extern _Thread_local char ERR[ERR_SIZE];

extern pcre_jit_stack *JITStack;
enum {
        JIT_STACK_START = 1 << 10,
        JIT_STACK_MAX   = 1 << 22
};

static inline uintmax_t
umax(uintmax_t a, uintmax_t b)
{
        return (a > b) ? a : b;
}

static inline uintmax_t
umin(uintmax_t a, uintmax_t b)
{
        return (a < b) ? a : b;
}

static inline intmax_t
max(intmax_t a, intmax_t b)
{
        return (a > b) ? a : b;
}

static inline intmax_t
min(intmax_t a, intmax_t b)
{
        return (a < b) ? a : b;
}

char *
sclone(Ty *ty, char const *s);

char *
sclonea(Ty *ty, char const *s);

char *
sclone_malloc(char const *s);

bool
contains(char const *s, char c);

char *
slurp(Ty *ty, char const *path);

char *
fslurp(Ty *ty, FILE *f);

/* memmem. maybe change this to Knuth-Morris-Pratt or Boyer-Moore at some point */
inline static char const *
strstrn(char const *haystack, int hn, char const *needle, int nn)
{
        for (int i = 0; i <= hn - nn; ++i) {
                if (memcmp(haystack + i, needle, nn) == 0)
                        return haystack + i;
        }

        return NULL;
}

inline static unsigned long
strhash(char const *s)
{
        unsigned long hash = 2166136261UL;

        while (*s != '\0')
                hash = (hash ^ *s++) * 16777619UL;

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

inline static unsigned long
StrHash(char const *s)
{
        unsigned long hash = 2166136261UL;

        while (*s != '\0')
                hash = (hash ^ *s++) * 16777619UL;

        return hash;
}

Value
this_executable(Ty *ty);

#endif
