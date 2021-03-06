#ifndef LOG_H_INCLUDED
#define LOG_H_INCLUDED

#include <unistd.h>
#include <sys/file.h>
#include <stdio.h>

#ifndef TY_NO_LOG
#define LOG(...) do { \
                        flock(2, LOCK_EX), \
                        fprintf(stderr, "(%d) ", getpid()), \
                        fprintf(stderr, __VA_ARGS__), \
                        fprintf(stderr, "\n"), \
                        flock(2, LOCK_UN); \
                } while (0)
#else
#define LOG(...) ;
#endif

#endif
