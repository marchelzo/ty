#ifndef LOG_H_INCLUDED
#define LOG_H_INCLUDED

#include "polyfill_unistd.h"
#include <stdio.h>

#ifdef _WIN32
#define flockfile(f) _lock_file(f)
#define funlockfile(f) _unlock_file(f)
#endif

extern int EnableLogging;

#if 0
extern _Atomic(uint64_t) LogCounter;
#define XxLOG(...) if (true) do {                                          \
                        GC_STOP();                                         \
                        flockfile(stderr),                                 \
                        fprintf(                                           \
                                stderr,                                    \
                                "[%7llu] (ty=%-4lld, real=%-4lld) ",       \
                                ++LogCounter,                              \
                                TID,                                       \
                                RealThreadId()                             \
                        ),                                                 \
                        fprintf(stderr, __VA_ARGS__),                      \
                        fprintf(stderr, "\n"),                             \
                        funlockfile(stderr);                               \
                        GC_RESUME();                                       \
                } while (0)
#else
#define XxLOG(...) GCLOG(__VA_ARGS__)
#endif

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
        if (EnableLogging >= 0) {                \
                fprintf(stdout, __VA_ARGS__);   \
                fprintf(stdout, "\n");          \
        } else if (0)

#define XXXLOG(...)                             \
        do {                                    \
                fprintf(stdout, __VA_ARGS__);   \
                fprintf(stdout, "\n");          \
        } while (0)

#define XXX(fmt, ...)  fprintf(stderr, fmt "\n" __VA_OPT__(,) __VA_ARGS__)
#define LOGX(fmt, ...) fprintf(stderr, fmt "\n" __VA_OPT__(,) __VA_ARGS__)
#define XXXX(fmt, ...) fprintf(stderr, fmt __VA_OPT__(,) __VA_ARGS__)

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

#define TID (long long)TyThreadId(ty)

#if 0
#define GCLOG(...) if (EnableLogging > 0) do {                           \
                        flockfile(stderr),                               \
                        fprintf(stderr, "[%d](%4lld) ", I_AM_TDB, TID),  \
                        fprintf(stderr, __VA_ARGS__),                    \
                        fprintf(stderr, "\n"),                           \
                        funlockfile(stderr);                             \
                } while (0)
#else
#define GCLOG(...) LOG(__VA_ARGS__)
#endif

#if 0
#define CO_LOG(...) XXX(__VA_ARGS__)
#else
#define CO_LOG(...)
#endif

#endif

/* vim: set sts=8 sw=8 expandtab: */
