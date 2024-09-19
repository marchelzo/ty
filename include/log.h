#ifndef LOG_H_INCLUDED
#define LOG_H_INCLUDED

#include "polyfill_unistd.h"
#include <stdio.h>

#ifdef _WIN32
#define flockfile(f) _lock_file(f)
#define funlockfile(f) _unlock_file(f)
#endif

extern _Bool EnableLogging;

#define XLOG(...) if (EnableLogging) do { \
                        GC_STOP(); \
                        flockfile(stderr), \
                        fprintf(stderr, "(%d) ", getpid()), \
                        fprintf(stderr, "(%14llu) ", TID), \
                        fprintf(stderr, __VA_ARGS__), \
                        fprintf(stderr, "\n"), \
                        funlockfile(stderr); \
                        GC_RESUME(); \
                } while (0)

#if !defined(TY_NO_LOG)
#define LOG(...) if (EnableLogging) do { \
                        GC_STOP(); \
                        flockfile(stderr), \
                        fprintf(stderr, "(%d) ", getpid()), \
                        fprintf(stderr, __VA_ARGS__), \
                        fprintf(stderr, "\n"), \
                        funlockfile(stderr); \
                        GC_RESUME(); \
                } while (0)
#else
#define LOG(...) ;
#endif

#define TID MyThreadId(ty)

#if 0
#define GCLOG(...) if (EnableLogging) do { \
                        flockfile(stderr), \
                        fprintf(stderr, "(%14llu) ", TID), \
                        fprintf(stderr, __VA_ARGS__), \
                        fprintf(stderr, "\n"), \
                        funlockfile(stderr); \
                } while (0)
#else
#define GCLOG LOG
#endif

#endif

/* vim: set sts=8 sw=8 expandtab: */
