#ifndef LOG_H_INCLUDED
#define LOG_H_INCLUDED

#include "polyfill_unistd.h"
#include <stdio.h>

#ifdef _WIN32
#define flockfile(f) _lock_file(f)
#define funlockfile(f) _unlock_file(f)
#endif

extern unsigned EnableLogging;

#define XLOG(...) if (EnableLogging) do {                    \
                        GC_STOP();                           \
                        flockfile(stderr),                   \
                        fprintf(stderr, "(%d) ", getpid()),  \
                        fprintf(stderr, "(%4lld) ", TID),    \
                        fprintf(stderr, __VA_ARGS__),        \
                        fprintf(stderr, "\n"),               \
                        funlockfile(stderr);                 \
                        GC_RESUME();                         \
                } while (0)

#define XLOGX(...) if (EnableLogging) do {                   \
                        GC_STOP();                           \
                        flockfile(stderr),                   \
                        fprintf(stderr, "(%d) ", getpid()),  \
                        fprintf(stderr, "(%4lld) ", TID),    \
                        fprintf(stderr, __VA_ARGS__),        \
                        funlockfile(stderr);                 \
                        GC_RESUME();                         \
                } while (0)

#define XXLOG(...) if (EnableLogging) do {                   \
                        Ty *ty = ty;                         \
                        GC_STOP();                           \
                        flockfile(stderr),                   \
                        fprintf(stderr, "(%d) ", getpid()),  \
                        fprintf(stderr, "(%4lld) ", TID),    \
                        fprintf(stderr, __VA_ARGS__),        \
                        fprintf(stderr, "\n"),               \
                        funlockfile(stderr);                 \
                        GC_RESUME();                         \
                } while (0)

#if !defined(TY_NO_LOG)
#define LOG(...) if (EnableLogging) do {                     \
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
#define GCLOG(...) if (EnableLogging) do {                   \
                        flockfile(stderr),                   \
                        fprintf(stderr, "(%4lld) ", TID),    \
                        fprintf(stderr, __VA_ARGS__),        \
                        fprintf(stderr, "\n"),               \
                        funlockfile(stderr);                 \
                } while (0)
#else
#define GCLOG LOG
#endif

#endif

/* vim: set sts=8 sw=8 expandtab: */
