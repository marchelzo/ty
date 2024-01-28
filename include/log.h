#ifndef LOG_H_INCLUDED
#define LOG_H_INCLUDED

#include <unistd.h>
#include <sys/file.h>
#include <stdio.h>

extern _Bool EnableLogging;

#define XLOG(...) if (EnableLogging) do { \
                        GC_OFF_COUNT += 1; \
                        flockfile(stderr), \
                        fprintf(stderr, "(%d) ", getpid()), \
                        fprintf(stderr, "(%14llu) ", TID), \
                        fprintf(stderr, __VA_ARGS__), \
                        fprintf(stderr, "\n"), \
                        funlockfile(stderr); \
                        GC_OFF_COUNT -= 1; \
                } while (0)

#if !defined(TY_NO_LOG)
#define LOG(...) if (EnableLogging) do { \
                        GC_OFF_COUNT += 1; \
                        flockfile(stderr), \
                        fprintf(stderr, "(%d) ", getpid()), \
                        fprintf(stderr, __VA_ARGS__), \
                        fprintf(stderr, "\n"), \
                        funlockfile(stderr); \
                        GC_OFF_COUNT -= 1; \
                } while (0)
#else
#define LOG(...) ;
#endif

#define TID ((unsigned long long)pthread_self())

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
