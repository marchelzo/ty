#ifndef NSYNC_COMPAT_COSMO_H_
#define NSYNC_COMPAT_COSMO_H_

#include <errno.h>
#include <limits.h>
#include <pthread.h>
#include <sched.h>
#include <stdalign.h>
#include <stdarg.h>
#include <stdatomic.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdint.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <unistd.h>

#ifdef __cplusplus
#define COSMOPOLITAN_C_START_ extern "C" {
#define COSMOPOLITAN_C_END_   }
#else
#define COSMOPOLITAN_C_START_
#define COSMOPOLITAN_C_END_
#endif

#define forceinline        static inline __attribute__((__always_inline__))
#define wontreturn         __attribute__((__noreturn__))
#define relegated          __attribute__((__cold__))
#define dontinline         __attribute__((__noinline__))
#define paramsnonnull(...)
#define libcesque
#define __static_yoink(s)

#define BEGIN_CANCELATION_POINT ((void)0)
#define END_CANCELATION_POINT   ((void)0)
#define BLOCK_CANCELATION       ((void)0)
#define ALLOW_CANCELATION       ((void)0)

#define STRACE(...)    ((void)0)
#define LOCKTRACE(...) ((void)0)

#define unassert(x) ((x) ? (void)0 : nsync_panic_("assertion failed: " #x "\n"))

typedef int errno_t;

COSMOPOLITAN_C_START_

void nsync_panic_(const char *s) __attribute__((__noreturn__));

int cosmo_futex_wait(atomic_int *w, int expect, char pshare, int clock, const struct timespec *abstime);
int cosmo_futex_wake(atomic_int *w, int count, char pshare);

unsigned pthread_delay_np(const void *symbol, unsigned attempts);

static inline int
pthread_yield_np(void)
{
        return sched_yield();
}

#define timespec_max  ((struct timespec){ INT64_MAX, 999999999 })
#define timespec_zero ((struct timespec){ 0, 0 })

static inline struct timespec
timespec_add(struct timespec x, struct timespec y)
{
        x.tv_sec  += y.tv_sec;
        x.tv_nsec += y.tv_nsec;

        if (x.tv_nsec >= 1000000000) {
                x.tv_nsec -= 1000000000;
                x.tv_sec  += 1;
        }

        return x;
}

static inline struct timespec
timespec_sub(struct timespec a, struct timespec b)
{
        a.tv_sec  -= b.tv_sec;
        a.tv_nsec -= b.tv_nsec;

        if (a.tv_nsec < 0) {
                a.tv_nsec += 1000000000;
                a.tv_sec  -= 1;
        }

        return a;
}

static inline int
timespec_cmp(struct timespec a, struct timespec b)
{
        return (a.tv_sec  != b.tv_sec)  ? ((a.tv_sec  < b.tv_sec)  ? -1 : 1)
             : (a.tv_nsec != b.tv_nsec) ? ((a.tv_nsec < b.tv_nsec) ? -1 : 1)
             :                            0;
}

static inline struct timespec
timespec_fromnanos(int64_t x)
{
        struct timespec ts = { x / 1000000000, x % 1000000000 };

        if (ts.tv_nsec < 0) {
                ts.tv_nsec += 1000000000;
                ts.tv_sec  -= 1;
        }

        return ts;
}

static inline struct timespec
timespec_frommicros(int64_t x)
{
        return timespec_fromnanos(x * 1000);
}

static inline struct timespec
timespec_frommillis(int64_t x)
{
        return timespec_fromnanos(x * 1000000);
}

static inline struct timespec
timespec_real(void)
{
        struct timespec ts;
        clock_gettime(CLOCK_REALTIME, &ts);
        return ts;
}

static inline struct timespec
timespec_mono(void)
{
        struct timespec ts;
        clock_gettime(CLOCK_MONOTONIC, &ts);
        return ts;
}

static inline int
timespec_sleep_until(int clock, struct timespec abstime)
{
#ifdef __APPLE__
        struct timespec now;
        clock_gettime(clock, &now);
        if (timespec_cmp(abstime, now) <= 0) {
                return 0;
        }
        abstime = timespec_sub(abstime, now);
        return nanosleep(&abstime, NULL) ? errno : 0;
#else
        return clock_nanosleep(clock, TIMER_ABSTIME, &abstime, NULL);
#endif
}

static inline struct timespec
timespec_sleep(int clock, struct timespec delay)
{
        struct timespec now;
        clock_gettime(clock, &now);
        timespec_sleep_until(clock, timespec_add(now, delay));
        return timespec_zero;
}

COSMOPOLITAN_C_END_

#endif
