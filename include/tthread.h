#ifndef INCLUDED_THREAD_H_
#define INCLUDED_THREAD_H_

#include <stdint.h>
#include <stdbool.h>
#include <time.h>
#include <stdio.h>

#include "defs.h"

#define TY_1e3 1000UL
#define TY_1e6 1000000UL
#define TY_1e9 1000000000ULL

inline static u64
TyThreadGetTime(void)
{
#ifdef _WIN32
        LARGE_INTEGER counter;
        LARGE_INTEGER frequency;
        QueryPerformanceCounter(&counter);
        QueryPerformanceFrequency(&frequency);
        return (u64)(counter.QuadPart * 1000000000ULL / frequency.QuadPart);
#else
        struct timespec t;
        clock_gettime(CLOCK_REALTIME, &t);
        return 1000000000ULL * t.tv_sec + t.tv_nsec;
#endif
}

/*
 * Waitable object tags (matching TGCPTR extra tags in builtins)
 */
#define TY_WAITABLE_MUTEX    1
#define TY_WAITABLE_SPINLOCK 2
#define TY_WAITABLE_CONDVAR  3
#define TY_WAITABLE_NOTE     4
#define TY_WAITABLE_COUNTER  5

typedef struct {
        void *obj;
        int   tag;
} TyWaitable;

#ifdef TY_USE_NSYNC
#define TY_WAIT_SCRATCH(n) ((n) * (sizeof (struct nsync_waitable_s) + sizeof (struct nsync_waitable_s *)))
#else
#define TY_WAIT_SCRATCH(n) (0)
#endif

#ifdef _WIN32

#include <windows.h>
#include <process.h>

#define TY_THREAD_OK 0
#define TY_RWLOCK_INIT SRWLOCK_INIT

typedef HANDLE                  TyThread;
typedef CRITICAL_SECTION        TyMutex;
typedef CONDITION_VARIABLE      TyCondVar;
typedef SRWLOCK                 TyRwLock;
typedef SYNCHRONIZATION_BARRIER TyBarrier;
typedef unsigned                TyThreadFunc(void *);
typedef unsigned                TyThreadReturnValue;

inline static int
TyThreadCreate(TyThread *t, TyThreadFunc *f, void *arg)
{
        unsigned tid;

        *t = (HANDLE)_beginthreadex(
                NULL,
                0,
                f,
                arg,
                0,
                &tid
        );

        return 0;
}

inline static void
TyThreadJoin(TyThread t)
{
        WaitForSingleObject(t, INFINITE);
}

inline static bool
TyThreadDetach(TyThread t)
{
        return CloseHandle(t);
}

inline static bool
TyThreadKill(TyThread t, int code)
{
        return TerminateThread(t, code) && CloseHandle(t);
}

inline static TyThread
TyThreadSelf(void)
{
        return GetCurrentThread();
}

inline static bool
TyThreadEqual(TyThread t1, TyThread t2)
{
        return GetThreadId(t1) == GetThreadId(t2);
}

inline static void
TyMutexInit(TyMutex* m)
{
        InitializeCriticalSection(m);
}

inline static void
TyMutexInitRecursive(TyMutex *m)
{
        InitializeCriticalSection(m);
}

inline static bool
TyMutexDestroy(TyMutex* m)
{
        DeleteCriticalSection(m);
        return true;
}

inline static bool
TyMutexLock(TyMutex* m)
{
        EnterCriticalSection(m);
        return true;
}

inline static bool
TyMutexTryLock(TyMutex *m)
{
        return TryEnterCriticalSection(m);
}

inline static bool
TyMutexUnlock(TyMutex *m)
{
        LeaveCriticalSection(m);
        return true;
}

inline static void
TyCondVarInit(TyCondVar *cv)
{
        InitializeConditionVariable(cv);
}

inline static bool
TyCondVarWait(TyCondVar *cv, TyMutex *m)
{
        return SleepConditionVariableCS(cv, m, INFINITE);
}

inline static bool
TyCondVarTimedWaitRelative(TyCondVar *cv, TyMutex *m, u64 nMs)
{
        return SleepConditionVariableCS(cv, m, nMs);
}

inline static bool
TyCondVarSignal(TyCondVar *cv)
{
        WakeConditionVariable(cv);
        return true;
}

inline static bool
TyCondVarBroadcast(TyCondVar *cv)
{
        WakeAllConditionVariable(cv);
        return true;
}

inline static bool
TyCondVarDestroy(TyCondVar *cv)
{
        return true;
}

inline static void
TyRwLockInit(TyRwLock *m)
{
        InitializeSRWLock(m);
}

inline static bool
TyRwLockDestroy(TyRwLock* m)
{
        return true;
}

inline static bool
TyRwLockRdLock(TyRwLock *m)
{
        AcquireSRWLockShared(m);
        return true;
}

inline static bool
TyRwLockTryRdLock(TyRwLock *m)
{
        return TryAcquireSRWLockShared(m);
}

inline static bool
TyRwLockWrLock(TyRwLock *m)
{
        AcquireSRWLockExclusive(m);
        return true;
}

inline static bool
TyRwLockTryWrLock(TyRwLock *m)
{
        return TryAcquireSRWLockExclusive(m);
}

inline static bool
TyRwLockRdUnlock(TyRwLock *m)
{
        ReleaseSRWLockShared(m);
        return true;
}

inline static bool
TyRwLockWrUnlock(TyRwLock *m)
{
        ReleaseSRWLockExclusive(m);
        return true;
}

inline static void
TyBarrierInit(TyBarrier *b, int n)
{
        InitializeSynchronizationBarrier(b, n, -1);
}

inline static bool
TyBarrierWait(TyBarrier *b)
{
        return EnterSynchronizationBarrier(b, 0);
}

typedef void *TyNote;
typedef void *TyCounter;

inline static TyNote
TyNoteNew(void) { return NULL; }

inline static void
TyNoteFree(TyNote n) { (void)n; }

inline static void
TyNoteNotify(TyNote n) { (void)n; }

inline static bool
TyNoteIsNotified(TyNote n) { (void)n; return false; }

inline static bool
TyNoteWait(TyNote n, u64 ms) { (void)n; (void)ms; return false; }

inline static TyCounter
TyCounterNew(u32 v) { (void)v; return NULL; }

inline static void
TyCounterFree(TyCounter c) { (void)c; }

inline static u32
TyCounterAdd(TyCounter c, i32 d) { (void)c; (void)d; return 0; }

inline static u32
TyCounterValue(TyCounter c) { (void)c; return 0; }

inline static u32
TyCounterWait(TyCounter c, u64 ms) { (void)c; (void)ms; return 0; }

inline static int
TyWaitAny(TyWaitable *items, int count, u64 timeout_ms, void *scratch,
          TyMutex **locks, int nlocks)
{
        (void)items; (void)count; (void)timeout_ms; (void)scratch;
        (void)locks; (void)nlocks;
        return count;
}

#else /* !_WIN32 */

#include <pthread.h>
#include <signal.h>

typedef pthread_t            TyThread;
typedef void                *TyThreadFunc(void *);
typedef void                *TyThreadReturnValue;

#ifdef TY_USE_NSYNC

#include <nsync.h>

typedef nsync_counter        TyBarrier;
typedef nsync_mu             TyMutex;
typedef nsync_mu             TyRwLock;
typedef nsync_cv             TyCondVar;
typedef nsync_note           TyNote;
typedef nsync_counter        TyCounter;

#define TY_RWLOCK_INIT NSYNC_MU_INIT

#else /* !TY_USE_NSYNC */

#include "barrier.h"

typedef pthread_barrier_t    TyBarrier;

typedef pthread_mutex_t      TyMutex;
typedef pthread_cond_t       TyCondVar;
typedef pthread_rwlock_t     TyRwLock;
typedef void                *TyNote;
typedef void                *TyCounter;

#define TY_RWLOCK_INIT PTHREAD_RWLOCK_INITIALIZER

#endif /* TY_USE_NSYNC */

#define TY_THREAD_OK   NULL

#if defined(__APPLE__)
  #include <os/lock.h>
  typedef os_unfair_lock TySpinLock;
#elif defined(TY_USE_NSYNC)
  typedef TyMutex TySpinLock;
#elif defined(__linux__)
  typedef pthread_spinlock_t TySpinLock;
#else
  #error "TODO"
#endif

/*
 * Thread functions (always pthreads)
 */

inline static int
TyThreadCreate(TyThread *t, TyThreadFunc *f, void *arg)
{
#if !defined(TY_RELEASE)
        pthread_attr_t attr;
        pthread_attr_init(&attr);
        int r = pthread_attr_setstacksize(&attr, 1ULL << 24);
        if (r != 0)
                return r;
        return pthread_create(t, &attr, f, arg);
#else
        return pthread_create(t, NULL, f, arg);
#endif
}

inline static void
TyThreadJoin(TyThread t)
{
        pthread_join(t, NULL);
}

inline static bool
TyThreadDetach(TyThread t)
{
        return pthread_detach(t) == 0;
}

inline static bool
TyThreadKill(TyThread t, int code)
{
        return pthread_kill(t, code) == 0;
}

inline static TyThread
TyThreadSelf(void)
{
#ifdef _WIN32
        HANDLE hSelf;

        DuplicateHandle(
                GetCurrentProcess(),
                TyThreadSelf(),
                GetCurrentProcess(),
                &hSelf,
                0,
                FALSE,
                DUPLICATE_SAME_ACCESS
        );

        return hSelf;
#else
        return pthread_self();
#endif
}

inline static bool
TyThreadEqual(TyThread t1, TyThread t2)
{
        return pthread_equal(t1, t2);
}

#ifdef TY_USE_NSYNC

/*
 * Barrier functions (nsync counter)
 */

inline static void
TyBarrierInit(TyBarrier *b, int n)
{
        if (*b != NULL) {
                nsync_counter_free(*b);
        }
        *b = nsync_counter_new(n);
}

inline static bool
TyBarrierWait(TyBarrier *b)
{
        nsync_counter_add(*b, -1);
        return nsync_counter_wait(*b, nsync_time_no_deadline) == 0;
}

/*
 * Mutex functions (nsync)
 */

inline static bool
TyMutexInit(TyMutex *m)
{
        nsync_mu_init(m);
        return true;
}

inline static bool
TyMutexInitRecursive(TyMutex *m)
{
        /* nsync_mu does not support recursive locking */
        nsync_mu_init(m);
        return true;
}

inline static bool
TyMutexDestroy(TyMutex *m)
{
        (void)m;
        return true;
}

inline static bool
TyMutexLock(TyMutex *m)
{
        nsync_mu_lock(m);
        return true;
}

inline static bool
TyMutexTryLock(TyMutex *m)
{
        return nsync_mu_trylock(m) != 0;
}

inline static bool
TyMutexUnlock(TyMutex *m)
{
        nsync_mu_unlock(m);
        return true;
}

/*
 * Condition variable functions (nsync)
 */

inline static void
TyCondVarInit(TyCondVar *cv)
{
        nsync_cv_init(cv);
}

inline static bool
TyCondVarWait(TyCondVar *cv, TyMutex *m)
{
        nsync_cv_wait(cv, m);
        return true;
}

inline static bool
TyCondVarTimedWaitRelative(TyCondVar *cv, TyMutex *m, u64 nMs)
{
        nsync_time abs_deadline = nsync_time_add(
                nsync_time_now(),
                nsync_time_ms((unsigned)nMs)
        );
        return nsync_cv_wait_with_deadline(cv, m, abs_deadline, NULL) == 0;
}

inline static bool
TyCondVarSignal(TyCondVar *cv)
{
        nsync_cv_signal(cv);
        return true;
}

inline static bool
TyCondVarBroadcast(TyCondVar *cv)
{
        nsync_cv_broadcast(cv);
        return true;
}

inline static bool
TyCondVarDestroy(TyCondVar *cv)
{
        (void)cv;
        return true;
}

/*
 * Read-write lock functions (nsync_mu in reader/writer mode)
 */

inline static void
TyRwLockInit(TyRwLock *m)
{
        nsync_mu_init(m);
}

inline static bool
TyRwLockDestroy(TyRwLock *m)
{
        (void)m;
        return true;
}

inline static bool
TyRwLockRdLock(TyRwLock *m)
{
        nsync_mu_rlock(m);
        return true;
}

inline static bool
TyRwLockTryRdLock(TyRwLock *m)
{
        return nsync_mu_rtrylock(m) != 0;
}

inline static bool
TyRwLockWrLock(TyRwLock *m)
{
        nsync_mu_lock(m);
        return true;
}

inline static bool
TyRwLockTryWrLock(TyRwLock *m)
{
        return nsync_mu_trylock(m) != 0;
}

inline static bool
TyRwLockRdUnlock(TyRwLock *m)
{
        nsync_mu_runlock(m);
        return true;
}

inline static bool
TyRwLockWrUnlock(TyRwLock *m)
{
        nsync_mu_unlock(m);
        return true;
}

/*
 * Note functions (nsync)
 */

inline static TyNote
TyNoteNew(void)
{
        return nsync_note_new(NULL, nsync_time_no_deadline);
}

inline static void
TyNoteFree(TyNote n)
{
        nsync_note_free(n);
}

inline static void
TyNoteNotify(TyNote n)
{
        nsync_note_notify(n);
}

inline static bool
TyNoteIsNotified(TyNote n)
{
        return nsync_note_is_notified(n) != 0;
}

inline static bool
TyNoteWait(TyNote n, u64 ms)
{
        nsync_time deadline = (ms == (u64)-1)
                ? nsync_time_no_deadline
                : nsync_time_add(nsync_time_now(), nsync_time_ms((unsigned)ms));
        return nsync_note_wait(n, deadline) != 0;
}

/*
 * Counter functions (nsync)
 */

inline static TyCounter
TyCounterNew(u32 v)
{
        return nsync_counter_new(v);
}

inline static void
TyCounterFree(TyCounter c)
{
        nsync_counter_free(c);
}

inline static u32
TyCounterAdd(TyCounter c, i32 d)
{
        return nsync_counter_add(c, d);
}

inline static u32
TyCounterValue(TyCounter c)
{
        return nsync_counter_value(c);
}

inline static u32
TyCounterWait(TyCounter c, u64 ms)
{
        nsync_time deadline = (ms == (u64)-1)
                ? nsync_time_no_deadline
                : nsync_time_add(nsync_time_now(), nsync_time_ms((unsigned)ms));
        return nsync_counter_wait(c, deadline);
}

/*
 * Wait for any of several objects (nsync)
 */

typedef struct {
        TyMutex *mu[16];
        int      n;
} TyWaitMuSet;

static void
TyWaitMuSetLock(void *v)
{
        TyWaitMuSet *s = v;
        for (int i = 0; i < s->n; i++) {
                TyMutexLock(s->mu[i]);
        }
}

static void
TyWaitMuSetUnlock(void *v)
{
        TyWaitMuSet *s = v;
        for (int i = s->n - 1; i >= 0; i--) {
                TyMutexUnlock(s->mu[i]);
        }
}

static void
TyWaitMuLock(void *v)
{
        TyMutexLock(v);
}

static void
TyWaitMuUnlock(void *v)
{
        TyMutexUnlock(v);
}

inline static int
TyWaitAny(TyWaitable *items, int count, u64 timeout_ms, void *scratch,
          TyMutex **locks, int nlocks)
{
        struct nsync_waitable_s *w = scratch;
        struct nsync_waitable_s **pw = (struct nsync_waitable_s **)((char *)scratch + count * sizeof *w);

        for (int i = 0; i < count; i++) {
                switch (items[i].tag) {
                case TY_WAITABLE_NOTE:
                        w[i].v = (void *)*(TyNote *)items[i].obj;
                        w[i].funcs = &nsync_note_waitable_funcs;
                        break;

                case TY_WAITABLE_COUNTER:
                        w[i].v = (void *)*(TyCounter *)items[i].obj;
                        w[i].funcs = &nsync_counter_waitable_funcs;
                        break;

                case TY_WAITABLE_CONDVAR:
                        w[i].v = items[i].obj;
                        w[i].funcs = &nsync_cv_waitable_funcs;
                        break;

                default:
                        return -1;
                }
                pw[i] = &w[i];
        }

        nsync_time deadline = (timeout_ms == (u64)-1)
                ? nsync_time_no_deadline
                : nsync_time_add(nsync_time_now(), nsync_time_ms((u32)timeout_ms));

        if (nlocks == 1) {
                return nsync_wait_n(locks[0], &TyWaitMuLock, &TyWaitMuUnlock,
                                    deadline, count, pw);
        } else if (nlocks > 1) {
                TyWaitMuSet mus;
                mus.n = nlocks > 16 ? 16 : nlocks;
                for (int i = 0; i < mus.n; i++) {
                        mus.mu[i] = locks[i];
                }
                return nsync_wait_n(&mus, &TyWaitMuSetLock, &TyWaitMuSetUnlock,
                                    deadline, count, pw);
        } else {
                return nsync_wait_n(NULL, NULL, NULL, deadline, count, pw);
        }
}

#else /* !TY_USE_NSYNC */

/*
 * Barrier functions (pthreads)
 */

inline static void
TyBarrierInit(TyBarrier *b, int n)
{
        pthread_barrier_init(b, NULL, n);
}

inline static bool
TyBarrierWait(TyBarrier *b)
{
        return pthread_barrier_wait(b) == 0;
}

/*
 * Mutex functions (pthreads)
 */

inline static bool
TyMutexInit(TyMutex *m)
{
        return pthread_mutex_init(m, NULL) == 0;
}

inline static bool
TyMutexInitRecursive(TyMutex *m)
{
        pthread_mutexattr_t attr;
        int err;

        pthread_mutexattr_init(&attr);
        pthread_mutexattr_settype(&attr, PTHREAD_MUTEX_RECURSIVE);

        err = pthread_mutex_init(m, &attr);
        pthread_mutexattr_destroy(&attr);

        return (err == 0);
}

inline static bool
TyMutexDestroy(TyMutex* m)
{
        return pthread_mutex_destroy(m) == 0;
}

inline static bool
TyMutexLock(TyMutex *m)
{
        return pthread_mutex_lock(m) == 0;
}

inline static bool
TyMutexTryLock(TyMutex *m)
{
        return pthread_mutex_trylock(m) == 0;
}

inline static bool
TyMutexUnlock(TyMutex *m)
{
        return pthread_mutex_unlock(m) == 0;
}

/*
 * Condition variable functions (pthreads)
 */

inline static void
TyCondVarInit(TyCondVar *cv)
{
        pthread_cond_init(cv, NULL);
}

inline static bool
TyCondVarWait(TyCondVar *cv, TyMutex *m)
{
        return pthread_cond_wait(cv, m) == 0;
}

inline static bool
TyCondVarTimedWaitRelative(TyCondVar *cv, TyMutex *m, u64 nMs)
{
        u64 t0 = TyThreadGetTime();
        u64 end = t0 + (TY_1e6 * nMs);

        struct timespec deadline = {
                .tv_sec = end / TY_1e9,
                .tv_nsec = end % TY_1e9
        };

        return pthread_cond_timedwait(cv, m, &deadline) == 0;
}

inline static bool
TyCondVarSignal(TyCondVar *cv)
{
        return pthread_cond_signal(cv) == 0;
}

inline static bool
TyCondVarBroadcast(TyCondVar *cv)
{
        return pthread_cond_broadcast(cv) == 0;
}

inline static bool
TyCondVarDestroy(TyCondVar *cv)
{
        return pthread_cond_destroy(cv) == 0;
}

/*
 * Read-write lock functions (pthreads)
 */

inline static void
TyRwLockInit(TyRwLock *m)
{
        pthread_rwlock_init(m, NULL);
}

inline static bool
TyRwLockDestroy(TyRwLock* m)
{
        return pthread_rwlock_destroy(m) == 0;
}

inline static bool
TyRwLockRdLock(TyRwLock *m)
{
        return pthread_rwlock_rdlock(m) == 0;
}

inline static bool
TyRwLockTryRdLock(TyRwLock *m)
{
        return pthread_rwlock_tryrdlock(m) == 0;
}

inline static bool
TyRwLockWrLock(TyRwLock *m)
{
        return pthread_rwlock_wrlock(m) == 0;
}

inline static bool
TyRwLockTryWrLock(TyRwLock *m)
{
        return pthread_rwlock_trywrlock(m) == 0;
}

inline static bool
TyRwLockRdUnlock(TyRwLock *m)
{
        return pthread_rwlock_unlock(m) == 0;
}

inline static bool
TyRwLockWrUnlock(TyRwLock *m)
{
        return pthread_rwlock_unlock(m) == 0;
}

/*
 * Note functions (pthreads stub)
 */

inline static TyNote
TyNoteNew(void) { return NULL; }

inline static void
TyNoteFree(TyNote n) { (void)n; }

inline static void
TyNoteNotify(TyNote n) { (void)n; }

inline static bool
TyNoteIsNotified(TyNote n) { (void)n; return false; }

inline static bool
TyNoteWait(TyNote n, u64 ms) { (void)n; (void)ms; return false; }

/*
 * Counter functions (pthreads stub)
 */

inline static TyCounter
TyCounterNew(u32 v) { (void)v; return NULL; }

inline static void
TyCounterFree(TyCounter c) { (void)c; }

inline static u32
TyCounterAdd(TyCounter c, i32 d) { (void)c; (void)d; return 0; }

inline static u32
TyCounterValue(TyCounter c) { (void)c; return 0; }

inline static u32
TyCounterWait(TyCounter c, u64 ms) { (void)c; (void)ms; return 0; }

/*
 * Wait for any (pthreads stub)
 */

inline static int
TyWaitAny(TyWaitable *items, int count, u64 timeout_ms, void *scratch,
          TyMutex **locks, int nlocks)
{
        (void)items; (void)count; (void)timeout_ms; (void)scratch;
        (void)locks; (void)nlocks;
        return count;
}
#endif /* TY_USE_NSYNC */

#ifdef __APPLE__
inline static bool
TySpinLockInit(TySpinLock *spin)
{
        *spin = OS_UNFAIR_LOCK_INIT;
        return true;
}

inline static bool
TySpinLockTryLock(TySpinLock *spin)
{
        return os_unfair_lock_trylock(spin);
}

inline static bool
TySpinLockLock(TySpinLock *spin)
{
        os_unfair_lock_lock(spin);
        return true;
}

inline static bool
TySpinLockUnlock(TySpinLock *spin)
{
        os_unfair_lock_unlock(spin);
        return true;
}

inline static bool
TySpinLockDestroy(TySpinLock *spin)
{
        return true;
}
#elif defined(TY_USE_NSYNC)
  #define TySpinLockInit TyMutexInit
  #define TySpinLockTryLock TyMutexTryLock
  #define TySpinLockLock    TyMutexLock
  #define TySpinLockUnlock  TyMutexUnlock
  #define TySpinLockDestroy TyMutexDestroy
#else
inline static bool
TySpinLockInit(TySpinLock *spin)
{
        return pthread_spin_init(spin, PTHREAD_PROCESS_PRIVATE) == 0;
}

inline static bool
TySpinLockTryLock(TySpinLock *spin)
{
        return pthread_spin_trylock(spin) == 0;
}

inline static bool
TySpinLockLock(TySpinLock *spin)
{
        return pthread_spin_lock(spin) == 0;
}

inline static bool
TySpinLockUnlock(TySpinLock *spin)
{
        return pthread_spin_unlock(spin) == 0;
}

inline static bool
TySpinLockDestroy(TySpinLock *spin)
{
        return pthread_spin_destroy(spin) == 0;
}
#endif

#endif /* _WIN32 */

#endif

/* vim: set sw=8 sts=8 expandtab: */
