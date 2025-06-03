#ifndef UTIL_H_INCLUDED
#define UTIL_H_INCLUDED

#include <stdarg.h>
#include <stddef.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>
#include <inttypes.h>
#include <stdbool.h>

#include <utf8proc.h>

#include "ty.h"
#include "alloc.h"
#include "intern.h"
#include "polyfill_unistd.h"

#ifdef max
#undef max
#endif

#ifdef min
#undef min
#endif

#define PTERM(n) (ColorProfile ? ("\x1b[" #n "m") : "")
#define TERM1(n) (ColorStdout  ? ("\x1b[" #n "m") : "")
#define TERM(n)  (ColorStderr  ? ("\x1b[" #n "m") : "")

#define ERR_SIZE 4096

#define SWAP(t, a, b) do { t _swap_tmp_ = a; a = b; b = _swap_tmp_; } while (0)

#define SAVE_(t, x) t x##_; memcpy(&(x##_), &(x), sizeof (x))
#define RESTORE_(x) memcpy(&(x), &(x##_), sizeof (x))

#define countof(x) (sizeof (x) / sizeof ((x)[0]))

#define afmt(...) ((afmt)(ty, __VA_ARGS__))
#define adump(...) ((adump)(ty, __VA_ARGS__))

inline static size_t
P_ALIGN(void const *p)
{
        return ((uintptr_t)p & 7)[(size_t []) {
                [0] = 8,
                [1] = 1,
                [2] = 2,
                [3] = 1,
                [4] = 4,
                [5] = 1,
                [6] = 2,
                [7] = 1,
        }];
}

inline static void *
ALIGNED_TO(void const *p, size_t align)
{
        return (void *)(((uintptr_t)p + (align - 1)) & ~(align - 1));
}

inline static bool
IS_ALIGNED_TO(void const *p, size_t align)
{
        return ((uintptr_t)p & (align - 1)) == 0;
}

#define ALIGNED_FOR(T, p) (ALIGNED_TO((p), _Alignof (T)))
#define IS_ALIGNED_FOR(T, p) (IS_ALIGNED_TO((p), _Alignof (T)))

#ifdef TY_UNSAFE
#define FALSE_OR(x) if (false)
#define TRUE_OR(x) if (true)
#else
#define FALSE_OR(x) if (x)
#define TRUE_OR(x) if (!(x))
#endif

static inline int
load_int(void const *p)
{
        return *(int const *)memcpy(&(int){0}, p, sizeof (int));
}

static inline umax
zmaxu(umax a, umax b)
{
        return (a > b) ? a : b;
}

static inline umax
zminu(umax a, umax b)
{
        return (a < b) ? a : b;
}

static inline imax
max(imax a, imax b)
{
        return (a > b) ? a : b;
}

static inline imax
min(imax a, imax b)
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

inline static uint64_t
splitmix64(uint64_t *state)
{
        uint64_t z = (*state += 0x9e3779b97f4a7c15);
        z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9;
        z = (z ^ (z >> 27)) * 0x94d049bb133111eb;
        return z ^ (z >> 31);
}

inline static unsigned long
StrHash(char const *s)
{
        unsigned long hash = 2166136261UL;

        while (*s != '\0')
                hash = (hash ^ *s++) * 16777619UL;

        return hash;
}

inline static bool
search_str(StringVector const *ss, char const *s)
{
        for (size_t i = 0; i < ss->count; ++i) {
                if (strcmp(ss->items[i], s) == 0) {
                        return true;
                }
        }

        return false;
}

static int
vdump(byte_vector *b, char const *fmt, va_list ap)
{
        va_list ap_;

        for (;;) {
                int avail = b->capacity - b->count;
                int need;

                va_copy(ap_, ap);
                need = vsnprintf(b->items + b->count, avail, fmt, ap_);
                va_end(ap_);

                if (1 + need >= avail) {
                        xvR(*b, max(b->capacity * 2, 256));
                        continue;
                }

                b->count += need;
                vvL(*b)[1] = '\0';

                return need;
        }
}

static int
dump(byte_vector *b, char const *fmt, ...)
{
        va_list ap;

        for (;;) {
                int avail = b->capacity - b->count;
                int need;

                va_start(ap, fmt);
                need = vsnprintf(b->items + b->count, avail, fmt, ap);
                va_end(ap);

                if (1 + need >= avail) {
                        xvR(*b, max(b->capacity * 2, 256));
                        continue;
                }

                b->count += need;
                vvL(*b)[1] = '\0';

                return need;
        }
}

static int
avdump(Ty *ty, byte_vector *str, char const *fmt, va_list ap)
{
        va_list ap_;

        for (;;) {
                int avail = vC(*str) - vN(*str);
                int need;

                va_copy(ap_, ap);
                need = vsnprintf(vZ(*str), avail, fmt, ap_);
                va_end(ap_);

                if (1 + need >= avail) {
                        avR(*str, max(vC(*str) * 2, 256));
                        continue;
                }

                str->count += need;
                *vZ(*str) = '\0';

                return need;
        }
}

static int
(adump)(Ty *ty, byte_vector *str, char const *fmt, ...)
{
        int bytes;
        va_list ap;

        va_start(ap, fmt);
        bytes = avdump(ty, str, fmt, ap);
        va_end(ap);

        return bytes;
}

static int
scvdump(Ty *ty, byte_vector *str, char const *fmt, va_list ap)
{
        va_list ap_;

        for (;;) {
                int avail = vC(*str) - vN(*str);
                int need;

                va_copy(ap_, ap);
                need = vsnprintf(vZ(*str), avail, fmt, ap_);
                va_end(ap_);

                if (1 + need >= avail) {
                        svR(*str, max(vC(*str) * 2, 256));
                        continue;
                }

                str->count += need;
                *vZ(*str) = '\0';

                return need;
        }
}

static const char *
ifmt(char const *fmt, ...)
{
        char const *str;
        byte_vector buf = {0};
        va_list ap;

        SCRATCH_SAVE();
        va_start(ap, fmt);
        scvdump(ty, &buf, fmt, ap);
        va_end(ap);
        str = intern(&xD.members, vv(buf))->name;
        SCRATCH_RESTORE();

        return str;
}

static char *
(xfmt)(Ty *ty, char const *fmt, ...)
{
        char *str;
        byte_vector buf = {0};
        va_list ap;

        SCRATCH_SAVE();
        va_start(ap, fmt);
        scvdump(ty, &buf, fmt, ap);
        str = sclone_malloc(vv(buf));
        va_end(ap);
        SCRATCH_RESTORE();

        return str;
}

static char *
(afmt)(Ty *ty, char const *fmt, ...)
{
        char *str;
        byte_vector buf = {0};
        va_list ap;

        SCRATCH_SAVE();
        va_start(ap, fmt);
        scvdump(ty, &buf, fmt, ap);
        str = sclonea(ty, v_(buf, 0));
        va_end(ap);
        SCRATCH_RESTORE();

        return str;
}

static int
term_width(char const *s, int n)
{
        if (n == -1) {
                n = strlen(s);
        }

        int width = 0;
        int ret;
        int cp;

        for (int i = 0; i < n;) {
                if (s[i] == 0x1b) {
                        while (++i < n && s[i] != 'm') {
                                ;
                        }
                        i += 1;
                } else if ((ret = utf8proc_iterate((uint8_t const *)s + i, n - i, &cp)) > 0) {
                        width += utf8proc_charwidth(cp);
                        i += ret;
                } else {
                        i += 1;
                }
        }

        return width;
}
inline static i32
u8_rune_sz(u8 const *str)
{
	i32 cp;
	i32 n = utf8proc_iterate(str, 8, &cp);
        return n + !n;
}

bool
get_directory_where_chad_looks_for_runtime_dependencies(char *buffer);

#endif

/* vim: set sts=8 sw=8 expandtab: */
