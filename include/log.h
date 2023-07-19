#ifndef LOG_H_INCLUDED
#define LOG_H_INCLUDED

#include <unistd.h>
#include <sys/file.h>
#include <stdio.h>

#define XLOG(...) do { \
                        flockfile(stderr), \
                        fprintf(stderr, "(%d) ", getpid()), \
                        fprintf(stderr, __VA_ARGS__), \
                        fprintf(stderr, "\n"), \
                        funlockfile(stderr); \
                } while (0)

#ifndef TY_NO_LOG
#define LOG(...) do { \
                        flockfile(stderr), \
                        fprintf(stderr, "(%d) ", getpid()), \
                        fprintf(stderr, __VA_ARGS__), \
                        fprintf(stderr, "\n"), \
                        funlockfile(stderr); \
                } while (0)
#else
#define LOG(...) ;
#endif

#define TID ((unsigned long long)pthread_self())

#if 0
#define GCLOG(...) do { \
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
