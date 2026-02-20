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
#include <xxhash.h>

#include "defs.h"
#include "panic.h"
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

#define SWAP(t, a, b) do { t _swap_tmp_ = a; a = b; b = _swap_tmp_; } while (0)

#define SAVE_(t, x) t x##_; memcpy(&(x##_), &(x), sizeof (x))
#define RESTORE_(x) memcpy(&(x), &(x##_), sizeof (x))

#define countof(x) (sizeof (x) / sizeof ((x)[0]))

inline static usize
P_ALIGN(void const *p)
{
        return ((uptr)p & 7)[(usize []) {
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
ALIGNED_TO(void const *p, usize align)
{
        return (void *)(((uptr)p + (align - 1)) & ~(align - 1));
}

inline static bool
IS_ALIGNED_TO(void const *p, usize align)
{
        return ((uptr)p & (align - 1)) == 0;
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

static inline i32
load_i32(void const *p)
{
        return *(i32 const *)memcpy(&(i32){0}, p, sizeof (i32));
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

inline static int
s_eq(char const *a, char const *b)
{
        return strcmp(a, b) == 0;
}

char *
sclone(Ty *ty, char const *s);

char *
sclonea(Ty *ty, char const *s);

static inline char *
S2(char const *s)
{
        usize n = strlen(s);
        char *new = ty_malloc(n + 1);

        if (new == NULL) {
                panic("out of memory");
        }

        memcpy(new, s, n + 1);

        return new;
}

bool
contains(char const *s, char c);

char *
slurp(Ty *ty, char const *path);

char *
fslurp(Ty *ty, FILE *f);

inline static u64
HashCombine(u64 seed, u64 hash)
{
        return seed ^ (hash + 0x9E3779B97F4A7C15ULL + (seed << 6) + (seed >> 2));
}

inline static u64
hash64z(char const *s)
{
        return XXH3_64bits(s, strlen(s));
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

inline static u64
splitmix64(u64 *state)
{
        u64 z = (*state += 0x9e3779b97f4a7c15);
        z = (z ^ (z >> 30)) * 0xbf58476d1ce4e5b9;
        z = (z ^ (z >> 27)) * 0x94d049bb133111eb;
        return z ^ (z >> 31);
}

inline static bool
search_str(StringVector const *ss, char const *s)
{
        for (usize i = 0; i < vN(*ss); ++i) {
                if (s_eq(v__(*ss, i), s)) {
                        return true;
                }
        }

        return false;
}

static isize
term_fit_cols(void const *_s, isize n, int cols)
{
        isize width = 0;
        u8 const *s = _s;
        bool zwj = false;

        if (n == -1) {
                n = strlen(_s);
        }

        for (isize i = 0; i < n;) {
                if (
                        (i + 1 < n)
                     && (s[i    ] == 0x1b)
                     && (s[i + 1] == '[')
                ) {
                        while (++i < n && s[i] != 'm') {
                                ;
                        }

                        i += 1;
                        zwj = false;

                        continue;
                }

                i32 cp;
                isize ret = utf8proc_iterate(s + i, n - i, &cp);

                if (ret <= 0) {
                        i += 1;
                        continue;
                }

                width += !zwj * utf8proc_charwidth(cp);
                i += ret;

                if (width >= cols) {
                        return i;
                }

                zwj = (cp == 0x200d);
        }

        return n;
}

static isize
term_width(void const *_s, isize n)
{
        if (n == -1) {
                n = strlen(_s);
        }

        isize width = 0;
        u8 const *s = _s;
        bool zwj = false;

        for (isize i = 0; i < n;) {
                if (
                        (i + 1 < n)
                     && (s[i    ] == 0x1b)
                     && (s[i + 1] == '[')
                ) {
                        while (++i < n && s[i] != 'm') {
                                ;
                        }

                        i += 1;
                        zwj = false;

                        continue;
                }

                i32 cp;
                isize ret = utf8proc_iterate(s + i, n - i, &cp);

                if (ret <= 0) {
                        i += 1;
                        continue;
                }

                width += !zwj * utf8proc_charwidth(cp);
                i += ret;

                zwj = (cp == 0x200d);
        }

        return width;
}

inline static i32
u8_rune_sz(u8 const *str)
{
	i32 cp;
	i32 n = utf8proc_iterate(str, 8, &cp);
        return (n > 0) ? n : 1;
}

inline static isize
rune_count(u8 const *s, isize n)
{
        isize count = 0;

        while (n != 0) {
                i32 rune;
                isize bytes = utf8proc_iterate(s, n, &rune);
                if (bytes <= 0) {
                        n -= 1;
                        s += 1;
                } else {
                        count += 1;
                        n -= bytes;
                        s += bytes;
                }
        }

        return count;
}

inline static isize
vec_search_i32(i32Vector const *v, i32 x)
{
        for (usize i = 0; i < vN(*v); ++i) {
                if (v__(*v, i) == x) {
                        return (isize)i;
                }
        }

        return -1;
}

bool
get_directory_where_chad_looks_for_runtime_dependencies(char *buffer);

char *
directory_of(char const *path, char *buf);

bool
get_terminal_size(int fd, int *rows, int *cols);

int
vdump(byte_vector *b, char const *fmt, va_list ap);

int
dump(byte_vector *b, char const *fmt, ...);

int
avdump(Ty *ty, byte_vector *str, char const *fmt, va_list ap);

int
(adump)(Ty *ty, byte_vector *str, char const *fmt, ...);

int
scvdump(Ty *ty, byte_vector *str, char const *fmt, va_list ap);

int
(sxdf)(Ty *ty, byte_vector *str, char const *fmt, ...);

char *
(sfmt)(Ty *ty, char const *fmt, ...);

const char *
(ifmt)(char const *fmt, ...);

char *
xfmt(char const *fmt, ...);

char *
(afmt)(Ty *ty, char const *fmt, ...);

#endif

/* vim: set sts=8 sw=8 expandtab: */
