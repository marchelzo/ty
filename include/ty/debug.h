#ifndef DEBUG_H_INCLUDED
#define DEBUG_H_INCLUDED

#include <signal.h>
#include <stdatomic.h>

#include "ty.h"
#include "ty/thread.h"

enum {
        DBG_RUNNING,
        DBG_BLOCKED,
        DBG_GCWAIT,
        DBG_PARKED
};

enum {
        STEP_NONE,
        STEP_IN,
        STEP_OVER,
        STEP_OUT,
        STEP_INSN
};

typedef struct debug_job DebugJob;

typedef struct ty_debug_thread {
        Ty *ty;
        u64 id;
        TyThread thread;

        atomic_int state;
        int suppress;
        bool agent;
        bool registered;

        int step;
        co_state *step_st;
        isize step_depth;
        Expr const *step_expr;
        char const *skip_trap;
        char *rearm;

        char const *stop_ip;
        u64 stop_gen;

        DebugJob *job;
} TyDebugThread;

typedef struct {
        Ty *ty;
        co_state *st;
        isize index;
        char const *ip;
        Value fun;
        bool has_fun;
        isize fp;
        isize nslot;
} DebugFrame;

extern volatile sig_atomic_t DebugInterrupt;
extern volatile sig_atomic_t DebugJitOff;

void
DebugInit(Ty *ty);

void
DebugShutdown(void);

void
DebugThreadStart(Ty *ty, TyThread self);

void
DebugThreadExit(Ty *ty);

void
DebugSafepoint(Ty *ty);

void
DebugReacquire(Ty *ty);

void
DebugTrap(Ty *ty, char *ip);

void
DebugRearm(Ty *ty);

u8
DebugOriginalOp(char const *ip);

void
DebugSanitizeCode(char const *src, char *dst, usize n);

void
DebugOnThrow(Ty *ty);

void
DebugCodeLoaded(Ty *ty);

void
DebugMarkRoots(Ty *ty);

void
DebugLockLocations(void);

void
DebugUnlockLocations(void);

bool
DebugCanDeopt(Ty *ty);

Expr const *
DebugEvalContext(Ty *ty);

bool
DebugHandlesSignal(int sig);

void
DebugSetSignalDisposition(int sig, int disposition);

void
DebugWaitForClient(Ty *ty);

inline static void
DebugOnRelease(Ty *ty, bool blocked)
{
        ty->dbg->state = blocked ? DBG_BLOCKED : DBG_GCWAIT;

        if (UNLIKELY(ty->dbg->rearm != NULL) && ty->ip != ty->dbg->rearm) {
                DebugRearm(ty);
        }
}

inline static void
DebugOnLock(Ty *ty)
{
        if (UNLIKELY(DebugInterrupt) && ty->dbg != NULL) {
                DebugReacquire(ty);
        }
}

#endif

/* vim: set sts=8 sw=8 expandtab: */
