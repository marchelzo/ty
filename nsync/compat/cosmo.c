#include "cosmo.h"

#if defined(__linux__)
#include <linux/futex.h>
#include <sys/syscall.h>
#elif defined(__APPLE__)
#define UL_COMPARE_AND_WAIT 1
#define ULF_WAKE_ALL        0x00000100
#define ULF_NO_ERRNO        0x01000000

int __ulock_wait2(uint32_t op, void *addr, uint64_t value, uint64_t timeout_ns, uint64_t value2);
int __ulock_wake(uint32_t op, void *addr, uint64_t wake_value);
#endif

static inline void
SpinPause(void)
{
#if defined(__x86_64__) || defined(__i386__)
        __builtin_ia32_pause();
#elif defined(__aarch64__)
        __asm__ volatile ("yield");
#endif
}

unsigned
pthread_delay_np(const void *symbol, unsigned attempts)
{
        (void)symbol;

        if (attempts < 12) {
                for (unsigned i = 1u << attempts; i > 0; --i) {
                        SpinPause();
                }
                return attempts + 1;
        }

        sched_yield();

        return attempts;
}

static struct timespec
Remaining(int clock, struct timespec const *abstime)
{
        struct timespec now;

        clock_gettime(clock, &now);

        return (timespec_cmp(*abstime, now) <= 0) ? timespec_zero
             :                                      timespec_sub(*abstime, now);
}

#if defined(__linux__)

int
cosmo_futex_wait(atomic_int *w, int expect, char pshare, int clock, struct timespec const *abstime)
{
        int             op = FUTEX_WAIT_BITSET;
        struct timespec ts;
        long            rc;

        if (pshare == PTHREAD_PROCESS_PRIVATE) {
                op |= FUTEX_PRIVATE_FLAG;
        }

        if (abstime != NULL && clock == CLOCK_REALTIME) {
                op |= FUTEX_CLOCK_REALTIME;
        } else if (abstime != NULL && clock != CLOCK_MONOTONIC) {
                ts      = timespec_add(timespec_mono(), Remaining(clock, abstime));
                abstime = &ts;
        }

        rc = syscall(SYS_futex, w, op, expect, abstime, NULL, FUTEX_BITSET_MATCH_ANY);

        return (rc < 0) ? -errno : 0;
}

int
cosmo_futex_wake(atomic_int *w, int count, char pshare)
{
        int  op = FUTEX_WAKE;
        long rc;

        if (pshare == PTHREAD_PROCESS_PRIVATE) {
                op |= FUTEX_PRIVATE_FLAG;
        }

        rc = syscall(SYS_futex, w, op, count);

        return (rc < 0) ? -errno : (int)rc;
}

#elif defined(__APPLE__)

int
cosmo_futex_wait(atomic_int *w, int expect, char pshare, int clock, struct timespec const *abstime)
{
        struct timespec left;
        uint64_t        ns = 0;
        int             rc;

        (void)pshare;

        if (abstime != NULL) {
                left = Remaining(clock, abstime);
                ns   = (uint64_t)left.tv_sec * 1000000000u + (uint64_t)left.tv_nsec;
                if (ns == 0) {
                        return -ETIMEDOUT;
                }
        }

        rc = __ulock_wait2(UL_COMPARE_AND_WAIT | ULF_NO_ERRNO, w, (uint32_t)expect, ns, 0);

        return (rc < 0) ? rc : 0;
}

int
cosmo_futex_wake(atomic_int *w, int count, char pshare)
{
        int rc;

        (void)pshare;

        rc = __ulock_wake(UL_COMPARE_AND_WAIT | ULF_NO_ERRNO | ((count > 1) ? ULF_WAKE_ALL : 0), w, 0);

        return (rc == -ENOENT) ? 0 : rc;
}

#else

enum { BUCKETS = 64 };

static struct {
        pthread_mutex_t mu;
        pthread_cond_t  cv;
} Buckets[BUCKETS];

static pthread_once_t BucketsOnce = PTHREAD_ONCE_INIT;

static void
BucketsInit(void)
{
        for (int i = 0; i < BUCKETS; ++i) {
                pthread_mutex_init(&Buckets[i].mu, NULL);
                pthread_cond_init(&Buckets[i].cv, NULL);
        }
}

static int
Bucket(atomic_int *w)
{
        pthread_once(&BucketsOnce, BucketsInit);
        return (int)(((uintptr_t)w >> 2) % BUCKETS);
}

int
cosmo_futex_wait(atomic_int *w, int expect, char pshare, int clock, struct timespec const *abstime)
{
        int             b  = Bucket(w);
        int             rc = 0;
        struct timespec deadline;

        (void)pshare;

        if (abstime != NULL) {
                deadline = timespec_add(timespec_real(), Remaining(clock, abstime));
        }

        pthread_mutex_lock(&Buckets[b].mu);

        if (atomic_load(w) != expect) {
                rc = EAGAIN;
        } else if (abstime == NULL) {
                rc = pthread_cond_wait(&Buckets[b].cv, &Buckets[b].mu);
        } else {
                rc = pthread_cond_timedwait(&Buckets[b].cv, &Buckets[b].mu, &deadline);
        }

        pthread_mutex_unlock(&Buckets[b].mu);

        return -rc;
}

int
cosmo_futex_wake(atomic_int *w, int count, char pshare)
{
        int b = Bucket(w);

        (void)count;
        (void)pshare;

        pthread_mutex_lock(&Buckets[b].mu);
        pthread_cond_broadcast(&Buckets[b].cv);
        pthread_mutex_unlock(&Buckets[b].mu);

        return 0;
}

#endif
