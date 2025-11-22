#ifndef INCLUDED_THREAD_H_
#define INCLUDED_THREAD_H_

#include <stdint.h>
#include <stdbool.h>
#include <time.h>
#include <stdio.h>

typedef uint64_t u64;

#define TY_1e3 1000UL
#define TY_1e6 1000000UL
#define TY_1e9 1000000000ULL

inline static u64
TyThreadGetTime()
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
TyCondVarTimedWaitRelative(TyCondVar *cv, TyMutex *m, uint64_t nMs)
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

#else

#include <pthread.h>
#include <signal.h>
#include "barrier.h"

typedef pthread_t            TyThread;
typedef pthread_mutex_t      TyMutex;
typedef pthread_cond_t       TyCondVar;
typedef pthread_rwlock_t     TyRwLock;
typedef pthread_barrier_t    TyBarrier;
typedef void                *TyThreadFunc(void *);
typedef void                *TyThreadReturnValue;

#if defined(__linux__)
typedef pthread_spinlock_t   TySpinLock;
#elif defined(__APPLE__)
#include <os/lock.h>
typedef os_unfair_lock TySpinLock;
#else
#error "TODO"
#endif


#define TY_THREAD_OK   NULL
#define TY_RWLOCK_INIT PTHREAD_RWLOCK_INITIALIZER

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

#endif

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
#else // __APPLE__
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
#endif // __APPLE__

#endif

/* vim: set sw=8 sts=8 expandtab: */
