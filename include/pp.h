#ifndef PP_H_INCLUDED
#define PP_H_INCLUDED

#ifdef _WIN32
#  define UNLIKELY(x)  (x)
#  define LIKELY(x)    (x)
#  define EXPECT(x, y) (x)
#  ifndef TY_RELEASE
#    define UNREACHABLE(msg) assert(! "" msg)
#  else
#    define UNREACHABLE(msg) __assume(0)
#  endif
#else
#  define UNLIKELY(x)  __builtin_expect((x), 0)
#  define LIKELY(x)    __builtin_expect((x), 1)
#  define EXPECT(x, y) __builtin_expect((x), (y))
#  ifndef TY_RELEASE
#    define UNREACHABLE(msg) assert(! "" msg)
#  else
#    define UNREACHABLE(msg) __builtin_unreachable()
#  endif
#endif

#define CAT(a, b) a ## b

#define countof(x) (sizeof (x) / sizeof ((x)[0]))

#define VA_COUNT_INNER(_1, _2, _3, _4, _5, _6, _7, _8, COUNT, ...) COUNT
#define VA_COUNT(...) VA_COUNT_INNER(__VA_ARGS__, 8, 7, 6, 5, 4, 3, 2, 1, 0)

#define VA_SELECT_INNER(f, i) CAT(f##_, i)
#define VA_SELECT(f, ...) VA_SELECT_INNER(f, VA_COUNT(__VA_ARGS__))(__VA_ARGS__)

#endif
/* vim: set sts=8 sw=8 expandtab: */

