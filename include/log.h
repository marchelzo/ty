#ifndef LOG_H_INCLUDED
#define LOG_H_INCLUDED

#include "polyfill_unistd.h"
#include <stdio.h>

#ifdef _WIN32
#define flockfile(f) _lock_file(f)
#define funlockfile(f) _unlock_file(f)
#endif

extern int EnableLogging;

#define XLOG(...) if (EnableLogging > 0) do {                \
                        GC_STOP();                           \
                        flockfile(stderr),                   \
                        fprintf(stderr, "(%d) ", getpid()),  \
                        fprintf(stderr, "(%4lld) ", TID),    \
                        fprintf(stderr, __VA_ARGS__),        \
                        fprintf(stderr, "\n"),               \
                        funlockfile(stderr);                 \
                        GC_RESUME();                         \
                } while (0)

#define XLOGX(...) if (EnableLogging > 0) do {               \
                        GC_STOP();                           \
                        flockfile(stderr);                   \
                        fprintf(stderr, "(%d) ", getpid());  \
                        fprintf(stderr, "(%4lld) ", TID);    \
                        fprintf(stderr, __VA_ARGS__);        \
                        funlockfile(stderr);                 \
                        GC_RESUME();                         \
                } while (0)

#define XXLOG(...)                              \
        if (EnableLogging >= 0) do {            \
                fprintf(stdout, __VA_ARGS__);   \
                fprintf(stdout, "\n");          \
        } while (0)

#define XXXLOG(...)                             \
        do {                                    \
                fprintf(stdout, __VA_ARGS__);   \
                fprintf(stdout, "\n");          \
        } while (0)

#define XXX(fmt, ...) fprintf(stderr, fmt "\n" __VA_OPT__(,) __VA_ARGS__)

#if !defined(TY_NO_LOG)
#define LOG(...) if (EnableLogging > 0) do {                 \
                        GC_STOP();                           \
                        flockfile(stderr),                   \
                        fprintf(stderr, "(%d) ", getpid()),  \
                        fprintf(stderr, "(%4lld) ", TID),    \
                        fprintf(stderr, __VA_ARGS__),        \
                        fprintf(stderr, "\n"),               \
                        funlockfile(stderr);                 \
                        GC_RESUME();                         \
                } while (0)
#else
#define LOG(...) ;
#endif

#define TID (long long)MyThreadId(ty)

#if 0
#define GCLOG(...) if (EnableLogging > 0) do {                           \
                        flockfile(stderr),                               \
                        fprintf(stderr, "[%d](%4lld) ", I_AM_TDB, TID),  \
                        fprintf(stderr, __VA_ARGS__),                    \
                        fprintf(stderr, "\n"),                           \
                        funlockfile(stderr);                             \
                } while (0)
#else
#define GCLOG LOG
#endif

#endif

/* vim: set sts=8 sw=8 expandtab: */
