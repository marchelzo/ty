#ifdef _WIN32
#include <winsock2.h>
#include <ws2tcpip.h>
#endif

#include "ty.h"
#include "prof.h"

#include <ctype.h>
#include <errno.h>
#include <locale.h>
#include <setjmp.h>
#include <stdarg.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <stdnoreturn.h>
#include <string.h>
#include <time.h>

#include <pcre2.h>

#include <fcntl.h>
#include <signal.h>
#include <unistd.h>

#include "polyfill_unistd.h"
#include "polyfill_stdatomic.h"
#include "barrier.h"
#include "ty/thread.h"

#ifdef __linux__
#include <sys/epoll.h>
#include <sys/mount.h>
#include <linux/mount.h>
#include <linux/sched.h>
#endif

#ifdef _WIN32
#include <windows.h>
#define PATH_MAX MAX_PATH
#define NAME_MAX MAX_PATH
#define O_DIRECTORY 0
#define O_ASYNC 0
#define O_NONBLOCK 0
#define SHUT_RD SD_RECEIVE
#define SHUT_WR SD_SEND
#define SHUT_RDWR SD_BOTH
#define CLOCK_REALTIME 0
#define CLOCK_MONOTONIC 0
#else
#include <dirent.h>
#include <net/if.h>
#include <netdb.h>
#include <netdb.h>
#include <netinet/ip.h>
#include <poll.h>
#include <pthread.h>
#include <sys/ioctl.h>
#include <sys/mman.h>
#include <sys/resource.h>
#include <sys/socket.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <sys/un.h>
#include <sys/wait.h>
#include <termios.h>
#endif

#if defined(__FreeBSD__)
#include <netinet/ip_mroute.h>
#endif

#if defined(__APPLE__)
#include <mach/task_policy.h>
#include <sys/qos.h>
#endif

#include "alloc.h"
#include "array.h"
#include "blob.h"
#include "queue.h"
#include "cffi.h"
#include "class.h"
#include "compiler.h"
#include "parse.h"
#include "diag.h"
#include "dict.h"
#include "dirs.h"
#include "set.h"
#include "heap.h"
#include "functions.h"
#include "gc.h"
#include "intern.h"
#include "istat.h"
#include "log.h"
#include "object.h"
#include "operators.h"
#include "sqlite.h"
#include "str.h"
#include "tags.h"
#include "types2.h"
#include "utf8.h"
#include "xd.h"
#include "value.h"
#include "jit/jit.h"
#include "vm.h"
#include "ty/debug.h"
#include "bundle.h"

#define TY_LOG_VERBOSE 1

#define SKIPSTR()    (IP += strlen(IP) + 1)
#define READSTR(s)   do { (s) = IP; SKIPSTR(); } while (0)
#define READVALUE(s) (__builtin_memcpy(&s, IP, sizeof s), (IP += sizeof s))
#define READJUMP(c)  (((c) = IP), (IP += sizeof (int)))
#define DOJUMP(c)    (IP = (c) + load_int((c)) + sizeof (int))

static _Thread_local Expr *expr;

#if defined(TY_LOG_VERBOSE) && !defined(TY_NO_LOG)
static Ty *ty = &vvv;
#define CASE(i)                                          \
        case INSTR_##i:                                  \
        if (EnableLogging > 0) {                         \
                expr = compiler_find_expr(ty, IP - 1);   \
        }                                                \
        LOG(                                             \
                "[%3zu -> %ld(%zu)] %s:%d:%d: " #i,      \
                vN(STACK),                               \
                vN(SP_STACK) ? v_L(SP_STACK) : (long)-1, \
                vN(SP_STACK),                            \
                expr ? GetExpressionModule(expr) : "",   \
                (expr ? expr->start.line : 0) + 1,       \
                (expr ? expr->start.col : 0) + 1         \
        );
#define XCASE(i)                                         \
        case INSTR_##i:                                  \
        expr = compiler_find_expr(ty, IP - 1);           \
        XXX(                                             \
                "[%3zu -> %ld(%zu)] %s:%d:%d: " #i,      \
                vN(STACK),                               \
                vN(SP_STACK) ? v_L(SP_STACK) : (long)-1, \
                vN(SP_STACK),                            \
                expr ? GetExpressionModule(expr) : "",   \
                (expr ? expr->start.line : 0) + 1,       \
                (expr ? expr->start.col : 0) + 1         \
        );
#else
#define ZCASE(i)                                            \
        case INSTR_##i:                                     \
                fprintf(                                    \
                        stderr,                             \
                        "[f=%zu fp=%zu sp=%zu]: %s   %s\n", \
                        vN(FRAMES), \
                        vN(FRAMES) ? vvL(FRAMES)->fp : 0, \
                        vN(STACK), \
                        GetInstructionName(IP[-1]), \
                        vN(STACK) ? SHOW(top()) : "--" \
                );
#define YCASE(i) case INSTR_##i:
#define CASE(i) \
        case INSTR_##i: \
                CO_LOG(#i, TERM(93), "");
#endif

#define MatchError do {                                          \
        top()->tags = tags_push(ty, top()->tags, TAG_MATCH_ERR); \
        top()->type |= VALUE_TAGGED;                             \
        RaiseException(ty);                                      \
        goto NextInstruction;                                    \
} while (0)

#define X(i) #i
static char const *InstructionNames[] = {
        TY_INSTRUCTIONS
};
#undef X

/* ======/ RVL Section /============================/ TVSL Types /=========== */
static char halt = INSTR_HALT;
static char next_fix[] = { INSTR_NONE_IF_NIL, INSTR_RETURN_PRESERVE_CTX };
static char iter_fix[] = { INSTR_SENTINEL, INSTR_GET_NEXT, INSTR_RETURN_PRESERVE_CTX };
static char hook_fix[] = { INSTR_POP, INSTR_RETURN_PRESERVE_CTX };
static char unapply[]  = { INSTR_RETURN_PRESERVE_CTX };
static char pop_ret[]  = { INSTR_POP, INSTR_RETURN_PRESERVE_CTX };

InternedNames NAMES;
ValueVector Globals;

static int  DirSlots[DIR_COUNT];
static bool DirsBound = false;

Value LOTS_OF_NILS[2048];
/* ========================================================================== */

#define FRAME(n, fn, from) ((Frame){ .fp = (n), .f = (fn), .ip = (from) })

#define TY_INSTR_INLINE

#define IP             (ty->ip)
#define CO_THREADS     (ty->cothreads)
#define JB             (ty->jb)
#define THREAD_LOCALS  (ty->tls)
#define THROW_STACK    (ty->throw_stack)

#define CALLS         (ty->st->calls)
#define DROP_STACK    (ty->st->to_drop)
#define EXEC_DEPTH    (ty->st->exec_depth)
#define FRAMES        (ty->st->frames)
#define SP_STACK      (ty->st->sps)
#define TARGETS       (ty->st->targets)
#define TRY_STACK     (ty->st->try_stack)
#define VISITING      (ty->visiting)

#define top()    ((top)(ty))
#define topN(i)  ((topN)(ty, i))
#define pop()    ((pop)(ty))
#define peek()   ((peek)(ty))
#define push(x)  ((push)(ty, (x)))
#define xpush(x) ((xpush)(ty, (x)))
#define put(x)   ((put)(ty, (x)))
#define swap()   ((swap)(ty))

#define poptarget()      ((poptarget)(ty))
#define peektarget()     ((peektarget)(ty))
#define pushtarget(t, g) ((pushtarget)(ty, (t), (g)))

#define GC_IS_WAITING \
        atomic_load_explicit(&ty->group->WantGC, memory_order_relaxed)

#if defined(TY_GC_STATS)
static u64 GCTimeTotal  = 0;
static u64 GCTimeWait   = 0;
static u64 GCTimeMark   = 0;
static u64 GCTimeSweep  = 0;
static u64 GCMaxHeap    = 0;
static u64 GCRunCount   = 0;
#endif


#if !defined(TY_RELEASE)
volatile bool GC_EVERY_ALLOC = false;
#endif


bool PrintResult = false;
FILE *DisassemblyOut = NULL;

typedef struct {
        atomic_bool *created;
        Value *ctx;
        Value *name;
        Thread *t;
        ThreadGroup *group;
        Ty *ty;
        bool isolated;
} NewThreadCtx;

static ThreadGroup MainGroup;


static TySpinLock GroupIdLock;
static bool       GroupIdUsed[GC_OWNER_MAX + 1] = { [0] = true, [1] = true };

static _Thread_local Ty *co_ty;

static _Thread_local Ty *MyTy;
static _Thread_local u64 MyId;

bool DyingOfError;

// ==========/ Signal Handling /========================================
ValueVector                  SignalGCRoots;
static Value                 SignalHandlers[NSIG];
static volatile u8           SignalStates[NSIG];
static volatile sig_atomic_t AnySignalPending;
static volatile u8           AttachPending;
volatile sig_atomic_t        JitInterruptFlag;
static pthread_rwlock_t      SignalLock = PTHREAD_RWLOCK_INITIALIZER;

void
vm_do_signal(int sig, siginfo_t *info, void *ctx)
{
        SignalStates[sig] = 1;
        AnySignalPending  = 1;
        JitInterruptFlag  = 1;
}

void
vm_attach_request(void)
{
        AttachPending    = 1;
        AnySignalPending = 1;
        JitInterruptFlag = 1;
}
// =====================================================================

void
MarkStorage(Ty *ty);

static TyThreadReturnValue
vm_run_thread(void *p);

inline static void
DoUnaryOp(Ty *ty, int op, bool exec);

static VPool Slabs = VPOOL(TY_SLAB_SIZE, 1ULL << 36, false);

static void
InitializeTy(Ty *ty, ThreadGroup *group)
{
        m0(*ty);

        ty->slab = VPoolTake(&Slabs);

        if (ty->slab != NULL) {
                ScratchAttach(
                        &ty->scratch,
                        ty->slab + TY_TMP_BUF_COUNT * TY_TMP_SLOT,
                        ty->slab + TY_SLAB_SIZE
                );
        }

        ExpandScratch(ty);
        ty->memory_limit = GC_INITIAL_LIMIT;

        ty->st = alloc0(sizeof *ty->st);
        ty->st->ctx = NIL;
        ty->co_top = co_active();

        u64 seed = random();
        ty->prng[0] = splitmix64(&seed);
        ty->prng[1] = splitmix64(&seed);
        ty->prng[2] = splitmix64(&seed);
        ty->prng[3] = splitmix64(&seed);

        ty->pcre2.ctx = pcre2_match_context_create(NULL);
        if (UNLIKELY(ty->pcre2.ctx == NULL)) {
                panic("out of memory!");
        }

        ty->pcre2.match = pcre2_match_data_create(128, NULL);
        if (UNLIKELY(ty->pcre2.match == NULL)) {
                panic("out of memory!");
        }

        ty->pcre2.stack = pcre2_jit_stack_create(4096, 4096 * 64, NULL);
        if (UNLIKELY(ty->pcre2.stack == NULL)) {
                panic("out of memory!");
        }

        pcre2_jit_stack_assign(ty->pcre2.ctx, NULL, ty->pcre2.stack);

        ty->lock = mrealloc(NULL, sizeof *ty->lock);
        TySpinLockInit(ty->lock);
        TySpinLockLock(ty->lock);
        ty->locked = true;
        ty->blocked = alloc0(sizeof *ty->blocked);
        ty->group   = group;
        ty->ty      = &xD;

        ty->gc_owner = ((group == &MainGroup) ? 1 : group->id) << 1;

        xvR(STACK, 4096);
}

static void
InitializeTY(TY *ty0, Ty *ty)
{
#define X(op, id) intern(&ty0->b_ops, id)
        TY_BINARY_OPERATORS;
#undef X

#define X(op, id) intern(&ty0->members, id)
        TY_UNARY_OPERATORS;
#undef X

        intern(&ty0->strings, "");

        for (int i = 0; i < countof(LOTS_OF_NILS); ++i) {
                LOTS_OF_NILS[i] = NIL;
        }

        srandom(TyRealTime() & 0xFFFFFFFF);

        InitializeTy(ty, &MainGroup);

        mod_init(ty0);
        jit_init(ty);

        ty0->ty = ty;
        ty->ty  = ty0;
}

Ty *
get_my_ty(void)
{
        return MyTy;
}

inline static void
UnlockThreads(Ty *ty, int *threads, int n)
{
        for (int i = 0; i < n; ++i) {
                TySpinLockUnlock(ty->group->ThreadLocks.items[threads[i]]);
        }
}

inline static void
SetState(Ty *ty, bool blocking)
{
        *ty->blocked = blocking;
}

inline static bool
TryFlipTo(TyThreadState *state, bool blocking)
{
        bool expected = !blocking;
#ifdef _WIN32
        return InterlockedCompareExchange(state, blocking, expected) == expected;
#else
        return atomic_compare_exchange_strong(state, &expected, blocking);
#endif
}

void
Forget(Ty *ty, Value *v, AllocList *allocs)
{
        isize n = vN(ty->allocs);

        value_mark(ty, v);
        GCForget(ty, &ty->allocs, &ty->memory_used);

        for (usize i = vN(ty->allocs); i < n; ++i) {
                xvP(*allocs, v__(ty->allocs, i));
        }
}

static ThreadGroup *
InitThreadGroup(ThreadGroup *group, u8 id, ThreadGroup *parent)
{
        m0(*group);
        group->id     = id;
        group->parent = parent;
        TySpinLockInit(&group->Lock);
        TySpinLockInit(&group->GCLock);
        TySpinLockInit(&group->DLock);
        TyMutexInit(&group->GCPhaseLock);
        TyCondVarInit(&group->GCPhaseCond);
        group->GCPhase = GC_PHASE_NONE;
        return group;
}

static u8
TakeGroupId(void)
{
        u8 id = 0;

        TySpinLockLock(&GroupIdLock);
        for (u8 i = 2; i <= GC_OWNER_MAX; ++i) {
                if (!GroupIdUsed[i]) {
                        GroupIdUsed[i] = true;
                        id = i;
                        break;
                }
        }
        TySpinLockUnlock(&GroupIdLock);

        return id;
}

static void
ReleaseGroupId(u8 id)
{
        TySpinLockLock(&GroupIdLock);
        GroupIdUsed[id] = false;
        TySpinLockUnlock(&GroupIdLock);
}

inline static ThreadGroup *
NewThreadGroup(ThreadGroup *parent)
{
        u8 id = TakeGroupId();

        if (id == 0) {
                return NULL;
        }

        return InitThreadGroup(mrealloc(NULL, (sizeof (ThreadGroup))), id, parent);
}

static void
BequeathAllocs(ThreadGroup *group)
{
        ThreadGroup *heir = group->parent;

        while (heir->dead) {
                heir = heir->parent;
        }

        u8 bits = heir->id << 1;

        TySpinLockLock(&heir->GCLock);
        TySpinLockLock(&heir->DLock);

        for (usize i = 0; i < vN(group->DeadAllocs); ++i) {
                atomic_store_explicit(&v__(group->DeadAllocs, i)->mark, bits, memory_order_relaxed);
        }

        xvPv(heir->DeadAllocs, group->DeadAllocs);
        xvPv(heir->DeadFinalizable, group->DeadFinalizable);
        heir->DeadUsed += group->DeadUsed;

        TySpinLockUnlock(&heir->DLock);
        TySpinLockUnlock(&heir->GCLock);
}

inline static int
WaitForGCPhase(Ty *ty, int bits)
{
        int phase;

        GCLOG("Waiting for GC phase %d", bits);

        TyMutexLock(&ty->group->GCPhaseLock);
        while (((phase = ty->group->GCPhase) & bits) == 0) {
                TyCondVarWait(&ty->group->GCPhaseCond, &ty->group->GCPhaseLock);
        }
        TyMutexUnlock(&ty->group->GCPhaseLock);

        //GCLOG("Finished waiting for GC phase %d on thread %llu: current phase is %d", bits, TID, phase);

        return phase;
}

inline static void
StartGC(Ty *ty)
{
        TyMutexLock(&ty->group->GCPhaseLock);
        ty->group->GCReadyCount = 0;
        ty->group->GCPhase = GC_PHASE_MARK;
        TyMutexUnlock(&ty->group->GCPhaseLock);
        TyCondVarBroadcast(&ty->group->GCPhaseCond);
}

inline static void
EndGC(Ty *ty)
{
        TyMutexLock(&ty->group->GCPhaseLock);
        ty->group->GCPhase = GC_PHASE_NONE;
        TyMutexUnlock(&ty->group->GCPhaseLock);
        TyCondVarBroadcast(&ty->group->GCPhaseCond);
}

inline static void
NextGCPhase(Ty *ty, int phase, int n_running)
{
        while (ty->group->GCReadyCount < n_running) {
                ;
        }
        TyMutexLock(&ty->group->GCPhaseLock);
        ty->group->GCReadyCount = 0;
        ty->group->GCPhase = phase;
        TyMutexUnlock(&ty->group->GCPhaseLock);
        GCLOG("Starting GC phase %d", phase);
        TyCondVarBroadcast(&ty->group->GCPhaseCond);
}

static void
MarkPendingFFIAutoValues(Ty *marker, AllocList const *allocs)
{
        for (usize i = 0; i < vN(*allocs); ++i) {
                struct alloc *a = v__(*allocs, i);
                if (a->type == GC_FFI_AUTO && !(a->mark & 1) && a->hard == 0) {
                        Value *values = (Value *)a->data;
                        value_mark(marker, &values[0]);
                        value_mark(marker, &values[1]);
                }
        }
}

static void
RunFinalizers(Ty *ty)
{
        for (;;) {
                Value o = NIL;
                Value f;
                GC_STOP();
                TySpinLockLock(&ty->group->DLock);
                if (vN(ty->group->Finalize) > 0) {
                        o = vXx(ty->group->Finalize);
                }
                TySpinLockUnlock(&ty->group->DLock);
                if (o.type == VALUE_NIL) {
                        GC_RESUME();
                        break;
                }
                f = class_get_finalizer(ty, o.class);
                vm_call_method(ty, &o, &f, 0);
                GC_RESUME();
        }
}

inline static void
TakeLockRaw(Ty *ty);

#ifdef TY_HAVE_USDT
__attribute__((noinline, cold))
static void
ProbeFunction(Ty *ty, Value const *f, bool entry)
{
        Expr const *e = from_eval(f) ? NULL : expr_of(f);
        char const *file = (e != NULL && e->mod != NULL && e->mod->path != NULL) ? e->mod->path : "";
        char const *name = name_of(f);
        int line = (e != NULL) ? (int)LocLine(e->start) + 1 : 0;
        int depth = vN(FRAMES);

        if (entry) {
                TY_PROBE(function__entry, file, name, line, depth);
        } else {
                TY_PROBE(function__return, file, name, line, depth);
        }
}
#endif

static void
WaitGC(Ty *ty)
{
        GCLOG("Waiting for GC");

        PROF_ENTER(PS_GC_WAIT);

        ReleaseLock(ty, false);
        int phase = WaitForGCPhase(ty, GC_PHASE_MARK | GC_PHASE_DONE);
        TakeLockRaw(ty);

        if (phase == GC_PHASE_DONE) {
                GCLOG("Finished waiting: %llu", TID);
                PROF_LEAVE();
                return;
        }

        MarkStorage(ty);
        MarkPendingFFIAutoValues(ty, &ty->allocs);
        ty->group->GCReadyCount += 1;

        WaitForGCPhase(ty, GC_PHASE_SWEEP);
        GCSweepTy(ty);
        ScratchTrim(&ty->scratch, TY_SCRATCH_KEEP);
        ty_collect(false);
        ty->group->GCReadyCount += 1;

        WaitForGCPhase(ty, GC_PHASE_DONE | GC_PHASE_NONE);

        PROF_LEAVE();

        dont_printf("Thread %-3llu: %lluus\n", TID, (TyThreadTime() - start) / 1000);
}

void
DoGC(Ty *ty)
{
        GCLOG("Trying to do GC. Used = %zu, DeadUsed = %zu", MemoryUsed, ty->group->DeadUsed);

        if (!TySpinLockTryLock(&ty->group->GCLock)) {
                GCLOG("Waiting for GC lock on thread %llu", TID);
                UnlockTy();
                TySpinLockLock(&ty->group->GCLock);
                TySpinLockUnlock(&ty->group->GCLock);
                LockTy();
                return;
        }

        PROF_ENTER(PS_GC);

#if defined(TY_GC_STATS)
        u64 start = TyMonotonicTime();
        u64 heap  = MemoryUsed;
#endif

        TY_PROBE_IF(gc__start, (unsigned long)MemoryUsed);

#if defined(TY_HAVE_USDT) || defined(TY_HAVE_SAMPLER)
        u64 probe_t0 = TyMonotonicTime();
        u64 probe_heap = MemoryUsed;
#endif

        CO_LOG("GC", TERM(91), "========== Starting GC on thread %llu ============", TID);
        GCLOG("Doing GC: ty->group = %p, (%zu threads)", ty->group, ty->group->ThreadList.count);

        TySpinLockLock(&ty->group->Lock);

        GCLOG("Took threads lock on thread %llu to do GC", TID);
        GCLOG("Storing true in WantGC on thread %llu", TID);

        ty->group->WantGC = true;
        JitInterruptFlag  = 1;

        usize nThreads = vN(ty->group->ThreadList);
        if (nThreads > ty->group->GCThreadCapacity) {
                ty->group->GCBlockedThreads = mrealloc(
                        ty->group->GCBlockedThreads,
                        nThreads * sizeof *ty->group->GCBlockedThreads
                );
                ty->group->GCThreadCapacity = nThreads;
        }
        int *blockedThreads = ty->group->GCBlockedThreads;

        int nBlocked = 0;
        int nRunning = 0;

        for (int i = 0; i < vN(ty->group->ThreadList); ++i) {
                if (ty->lock == v__(ty->group->ThreadLocks, i)) {
                        continue;
                }
                GCLOG("Trying to take lock for thread %llu: %p", (long long unsigned)ty->group->ThreadList.items[i], (void *)ty->group->ThreadLocks.items[i]);
                TySpinLockLock(v__(ty->group->ThreadLocks, i));
#if defined(TY_GC_STATS)
                heap += v__(ty->group->TyList, i)->memory_used;
#endif
                if (TryFlipTo(v__(ty->group->ThreadStates, i), true)) {
                        GCLOG("Thread %llu is running", ty->group->TyList.items[i]->id);
                        nRunning += 1;
                        TySpinLockUnlock(v__(ty->group->ThreadLocks, i));
                } else {
                        GCLOG("Thread %llu is blocked", ty->group->TyList.items[i]->id);
                        blockedThreads[nBlocked++] = i;
                }
        }

        GCLOG("nBlocked = %d, nRunning = %d on thread %llu", nBlocked, nRunning, TID);

        StartGC(ty);

#if defined(TY_GC_STATS)
        if (heap > GCMaxHeap) {
                GCMaxHeap = heap;
        }
        u64 mark = TyMonotonicTime();
#endif

        for (int i = 0; i < nBlocked; ++i) {
                GCLOG("Marking thread %d storage from thread %llu", blockedThreads[i], TID);
                MarkStorage(v__(ty->group->TyList, blockedThreads[i]));
        }

        GCLOG("Marking own storage on thread %llu", TID);
        MarkStorage(ty);

        for (int i = 0; i < nBlocked; ++i) {
                MarkPendingFFIAutoValues(ty, &v__(ty->group->TyList, blockedThreads[i])->allocs);
        }
        MarkPendingFFIAutoValues(ty, &ty->allocs);

        TySpinLockLock(&ty->group->DLock);
        MarkPendingFFIAutoValues(ty, &ty->group->DeadAllocs);
        for (int i = 0; i < vN(ty->group->Finalize); ++i) {
                value_mark(ty, v_(ty->group->Finalize, i));
        }
        TySpinLockUnlock(&ty->group->DLock);

        if (ty->group == &MainGroup) {
                GCLOG("Marking %zu global roots on thread %llu", vN(Globals), TID);
                RESET_TOTAL_REACHED();
                for (int i = 0; i < vN(Globals); ++i) {
                        value_mark(ty, v_(Globals, i));
                }
                LOG_REACHED(" => globals reached %llu", TotalReached);

                class_mark_refs(ty);

                RESET_TOTAL_REACHED();
                GCRootSet *immortal = GCImmortalSet(ty);
                for (int i = 0; i < vN(*immortal); ++i) {
                        value_mark(ty, v_(*immortal, i));
                }
                LOG_REACHED(" => immortal reached %llu", TotalReached);

                for (int i = 0; i < vN(SignalGCRoots); ++i) {
                        value_mark(ty, v_(SignalGCRoots, i));
                }

                DebugMarkRoots(ty);
        }

        while (ty->group->GCReadyCount < nRunning) {
                ;
        }

        GCQueueFinalizers(ty, &ty->group->Finalize);

        NextGCPhase(ty, GC_PHASE_SWEEP, nRunning);

#if defined(TY_GC_STATS)
        u64 sweep = TyMonotonicTime();
#endif

        GCLOG("Storing false in WantGC on thread %llu", TID);
        ty->group->WantGC = false;

        for (int i = 0; i < nBlocked; ++i) {
                Ty *other = v__(ty->group->TyList, blockedThreads[i]);
                GCLOG("Sweeping thread %llu storage from thread %llu", other->id, TID);
                GCSweepTy(other);
        }

        GCLOG("Sweeping own storage on thread %llu", TID);
        GCSweepTy(ty);
        ScratchTrim(&ty->scratch, TY_SCRATCH_KEEP);
        ty_collect(false);

        GCLOG("Sweeping objects from dead threads on thread %llu", TID);
        TySpinLockLock(&ty->group->DLock);
        GCSweep(ty, &ty->group->DeadAllocs, &ty->group->DeadUsed);
        TySpinLockUnlock(&ty->group->DLock);

        NextGCPhase(ty, GC_PHASE_DONE, nRunning);
        EndGC(ty);

        TySpinLockUnlock(&ty->group->GCLock);

        UnlockThreads(ty, blockedThreads, nBlocked);
        GCLOG("Unlocking ThreadsLock and GCLock. Used = %lld, DeadUsed = %lld", MemoryUsed, ty->group->DeadUsed);

        TySpinLockUnlock(&ty->group->Lock);

        GCLOG("Unlocked ThreadsLock and GCLock on thread %llu", TID);

        RunFinalizers(ty);

#if defined(TY_GC_STATS)
        u64 end = TyMonotonicTime();
        GCTimeTotal += end - start;
        GCTimeWait += mark - start;
        GCTimeMark += sweep - mark;
        GCTimeSweep += end - sweep;
        GCRunCount += 1;
#endif

#ifdef TY_HAVE_SAMPLER
        prof_gc_done(probe_heap, MemoryUsed, TyMonotonicTime() - probe_t0);
#endif

#ifdef TY_HAVE_USDT
        if (TY_PROBING(gc__done)) {
                TY_PROBE(
                        gc__done,
                        (unsigned long)probe_heap,
                        (unsigned long)MemoryUsed,
                        (unsigned long)(TyMonotonicTime() - probe_t0)
                );
        }
#endif

        PROF_LEAVE();

        dont_printf("Thread %-3llu: %.6fs\n", TID, (t1 - t0) / 1.0e9);
}

//====/ Builtin Values /======================================================================
#define TY_GENERATED_BUILTIN(f) { .type = VALUE_BUILTIN_FUNCTION, .builtin_function = (f), .tags = 0 }
#define FLOAT(x)      { .type = VALUE_REAL,             .real             = (x), .tags = 0 }
#define INT(k)        { .type = VALUE_INTEGER,          .z                = (k), .tags = 0 }
#define BOOL_(b)      { .type = VALUE_BOOLEAN,          .boolean          = (b), .tags = 0 }
#define POINTER(p)    { .type = VALUE_PTR,              .ptr              = (p), .tags = 0 }
#ifdef __linux__
#include <sys/eventfd.h>
#include <sys/inotify.h>
#include <sys/signalfd.h>
#include <sys/timerfd.h>
#endif
#include "builtins.h"
#undef INT
#undef FLOAT
#undef TY_GENERATED_BUILTIN
#undef BOOL_
#undef POINTER
//============================================================================================

enum { GLOBALS_MAX = 1 << 20 };

static void
ReserveGlobals(void)
{
        usize size = GLOBALS_MAX * sizeof (Value);

#ifdef _WIN32
        void *p = VirtualAlloc(NULL, size, MEM_RESERVE | MEM_COMMIT, PAGE_READWRITE);
        if (p == NULL) {
                panic("cannot reserve the global table");
        }
#else
        void *p = mmap(NULL, size, PROT_READ | PROT_WRITE, MAP_PRIVATE | MAP_ANONYMOUS | MAP_NORESERVE, -1, 0);
        if (p == MAP_FAILED) {
                panic("cannot reserve the global table");
        }
#endif

        Globals.items    = p;
        Globals.count    = 0;
        Globals.capacity = GLOBALS_MAX;
}

void
vm_global_added(Ty *ty, Symbol const *sym)
{
        if (UNLIKELY(sym->i >= GLOBALS_MAX - 1)) {
                panic("too many globals (at most %d)", GLOBALS_MAX - 1);
        }

        while (vN(Globals) <= sym->i) {
                xvP(Globals, NIL);
        }

        *v_(Globals, sym->i) = IsTopLevel(sym) ? UNINITIALIZED(sym) : NIL;
}

inline static void
PopulateGlobals(Ty *ty)
{
        usize n = compiler_global_count(ty);

        while (vN(Globals) < n) {
                Symbol *sym = compiler_global_sym(ty, vN(Globals));
                xvP(
                        Globals,
                        IsTopLevel(sym) ? UNINITIALIZED(sym) : NIL
                );
        }
}

Module *
vm_caller_module(Ty *ty)
{
        Frame const *top = (vN(FRAMES) > 0) ? vvL(FRAMES) : NULL;
        char const *ip = (IP == NULL) ? NULL : jit_frame_ip(top, IP);
        Expr const *e = (ip == NULL) ? NULL : compiler_find_expr(ty, ip - 1);

        return (e == NULL) ? NULL : e->mod;
}

Module *
vm_foreign_caller_module(Ty *ty)
{
        co_state st = *ty->st;
        char const *ip = IP;
        Module *home = NULL;

        while (ip != NULL) {
                Frame const *frame = (vN(st.frames) > 0) ? vvL(st.frames) : NULL;
                Expr const *e = compiler_find_expr(ty, jit_frame_ip(frame, ip) - 1);
                Module *mod = (e == NULL) ? NULL : e->mod;

                if (home == NULL) {
                        home = mod;
                } else if (mod != NULL && mod != home) {
                        return mod;
                }

                if (vN(st.frames) == 0) {
                        break;
                }

                ip = vXx(st.frames).ip;
        }

        return NULL;
}

static void
AddSearchDir(Ty *ty, char const *dir)
{
        Array *search = v_(Globals, NAMES.path)->array;

        for (int i = 0; i < vN(*search); ++i) {
                Value const *v = v_(*search, i);
                if (v->type == VALUE_STRING && vs_eq_z(*v, dir)) {
                        return;
                }
        }

        vAp(search, vSzz(dir));
}

static void
AddSearchDirs(Ty *ty, char const *dirs)
{
#ifdef _WIN32
        char const *sep = ";";
#else
        char const *sep = ":";
#endif
        char dir[PATH_MAX + 1];
        char real[PATH_MAX + 1];

        for (char const *p = dirs; *p != '\0'; p += (p[0] != '\0')) {
                usize n = strcspn(p, sep);
                if (
                        (n > 0)
                     && (n < sizeof dir)
                ) {
                        memcpy(dir, p, n);
                        dir[n] = '\0';
                        if (realpath(dir, real) != NULL) {
                                AddSearchDir(ty, real);
                        }
                }
                p += n;
        }
}

static void
add_builtins(Ty *ty, int ac, char **av)
{
        GC_STOP();

        for (int i = CLASS_OBJECT; i < CLASS_BUILTIN_END; ++i) {
                xvP(Globals, CLASS(i));
        }

        for (int i = 0; i < countof(builtins); ++i) {
                Value *v = &builtins[i].value;
                bool fn = (v->type == VALUE_BUILTIN_FUNCTION);
                Symbol *sym = compiler_introduce_symbol(
                        ty,
                        builtins[i].module,
                        builtins[i].name,
                        builtins[i].sig,
                        fn
                );
                sym->doc = builtins[i].doc;
                if (fn) {
                        v->name = M_ID(builtins[i].name);
                        v->module = builtins[i].module;
                        sym->flags |= SYM_FUNCTION;
                        sym->flags |= SYM_CONST;
                }
                xvP(Globals, builtins[i].value);
                switch (ClassOf(v)) {
                case CLASS_INT:
                        sym->type = t2_literal_int(t2_global_universe(), v->z);
                        sym->flags |= SYM_CONST;
                        break;

                case CLASS_STRING:
                        sym->type = t2_literal_string_n(
                                t2_global_universe(),
                                (char const *)ss(*v),
                                sN(*v)
                        );
                        sym->flags |= SYM_CONST;
                        break;

                case CLASS_BOOL:
                        sym->type = t2_literal_bool(t2_global_universe(), v->boolean);
                        sym->flags |= SYM_CONST;
                        break;

                case CLASS_FLOAT:
                case CLASS_PTR:
                        sym->type = t2_object_type(ty, class_get(ty, ClassOf(v)));
                        sym->flags |= SYM_CONST;
                        break;
                }
        }

        Array *args = vA();

        for (int i = 0; i < ac; ++i) {
                vAp(args, vSsz(av[i]));
        }

        compiler_introduce_symbol(ty, NULL, "argv", "Array[String]", false);
        xvP(Globals, ARRAY(args));

        for (int i = 0; i < DIR_COUNT; ++i) {
                char const *dir = dirs_get(i);
                Symbol *sym = compiler_introduce_symbol(ty, "dirs", DirNames[i], "String", false);
                sym->flags |= SYM_CONST;
                DirSlots[i] = vN(Globals);
                xvP(Globals, vSsz(dir));
        }

        DirsBound = true;

        Dict *env = dict_new(ty);

        extern char **environ;
        for (char **envp = environ; *envp != NULL; ++envp) {
                u32 len = strlen(*envp);
                char const *eq = strchr(*envp, '=');
                if (eq == NULL) {
                        Value key = vSs(*envp, len);
                        Value val = NIL;
                        dict_put_value(ty, env, key, val);
                } else {
                        Value key = vSs(*envp, eq - *envp);
                        Value val = vSsz(eq + 1);
                        dict_put_value(ty, env, key, val);
                }
        }

        Value version = vTn(
                "string", xSz(TY_VERSION_STRING),
                "date",   xSz(TY_VERSION_DATE)
        );

//===========================================================================
#define BUILTIN_VAR(m, t, type)                           \
        compiler_introduce_symbol(ty, m, t, type, false); \
        *xvP(Globals, NIL)

#define BUILTIN_NAMED_VAR(m, t, c, type)                  \
        compiler_introduce_symbol(ty, m, t, type, false); \
        NAMES.c = vN(Globals);                            \
        *xvP(Globals, NIL)
//---------------------------------------------------------------------------
        BUILTIN_NAMED_VAR(NULL, "__env",          env,         "Dict[String, String]"                          ) = DICT(env);
        BUILTIN_NAMED_VAR(NULL, "__EXIT_HOOKS__", exit_hooks,  NULL                                            ) = ARRAY(vA());
        BUILTIN_NAMED_VAR(NULL, "__FORK_HOOKS__", fork_hooks,  NULL                                            ) = ARRAY(vA());
        BUILTIN_NAMED_VAR(NULL, "_readln",        _readln,     NULL                                            ) = NIL;
        BUILTIN_NAMED_VAR(NULL, "pretty",         pretty,      NULL                                            ) = NIL;
        BUILTIN_NAMED_VAR(NULL, "pp",             pp,          NULL                                            ) = NIL;
        BUILTIN_NAMED_VAR("ty", "path",           path,        "prelude.Array[prelude.String]"                 ) = ARRAY(vA());
        BUILTIN_NAMED_VAR("ty", "q",              q,           "prelude.Bool"                                  ) = BOOLEAN(!CheckTypes);
        BUILTIN_NAMED_VAR("ty", "jit",            jit,         "prelude.Bool"                                  ) = BOOLEAN(!NoJIT);
        BUILTIN_NAMED_VAR("ty", "TEST",           TEST,        "prelude.Bool"                                  ) = BOOLEAN(RunningTests);
        BUILTIN_NAMED_VAR("ty", "version",        version,     "{string: prelude.String, date: prelude.String}") = version;
        BUILTIN_NAMED_VAR("ty", "interactive",    interactive, "prelude.Bool"                                  ) = BOOLEAN(false);

#ifdef TY_EMBED_LIB
        BUILTIN_VAR("ty",  "executable", "prelude.String") = (bundle_ty() != NULL) ? vSsz(bundle_ty()) : this_executable(ty);
        BUILTIN_VAR("ty",  "bundle",     "prelude.String | nil") = (bundle_dir() != NULL) ? vSsz(bundle_dir()) : NIL;
#else
        BUILTIN_VAR("ty",  "executable", "prelude.String") = this_executable(ty);
        BUILTIN_VAR("ty",  "bundle",     "prelude.String | nil") = NIL;
#endif
        BUILTIN_VAR("ty",  "platform",   "prelude.String") = xSz(TY_PLATFORM_NAME);
        BUILTIN_VAR("ty",  "arch",       "prelude.String") = xSz(TY_PLATFORM_ARCH);
        BUILTIN_VAR("ty",  "color",      "prelude.String") = xSz(COLOR_MODE_NAMES[ColorMode]);
#if defined(_WIN32)
        BUILTIN_VAR("os",  "PAGE_SIZE",  "Int") = INTEGER(4096);
#else
        BUILTIN_VAR("os",  "PAGE_SIZE",  "Int") = INTEGER(sysconf(_SC_PAGESIZE));
#endif
#if defined(__linux__)
        BUILTIN_VAR("os",  "SIGRTMIN",   "Int") = INTEGER(SIGRTMIN);
        BUILTIN_VAR("os",  "SIGRTMAX",   "Int") = INTEGER(SIGRTMAX);
#endif
        BUILTIN_VAR("stdio", "stdin",  "Ptr[Any]") = PTR(stdin);
        BUILTIN_VAR("stdio", "stdout", "Ptr[Any]") = PTR(stdout);
        BUILTIN_VAR("stdio", "stderr", "Ptr[Any]") = PTR(stderr);
//---------------------------------------------------------------------------
#undef BUILTIN_VAR
//===========================================================================


//===========================================================================
// Add default module directories to the module search path
//---------------------------------------------------------------------------
#define add(dir) do {                                             \
        if (realpath(dir, real) != NULL) {                        \
                AddSearchDir(ty, real);                           \
        }                                                         \
} while (0)
//---------------------------------------------------------------------------
{
        char path[PATH_MAX + 1];
        char chad[PATH_MAX + 1];
        char real[PATH_MAX + 1];

        char const *env_path = getenv("TY_LIBRARY_PATH");

#ifdef TY_EMBED_LIB
        char const *bundle = bundle_dir();
        if (bundle != NULL) {
                char const *const *extra;
                int nextra = bundle_paths(&extra);
                ty_snprintf(path, sizeof path, "%s/lib", bundle);
                add(path);
                for (int i = 0; i < nextra; ++i) {
                        add(extra[i]);
                }
                if (embedded_lib_dir(path, sizeof path)) {
                        add(path);
                }
                if (env_path != NULL) {
                        AddSearchDirs(ty, env_path);
                }
                goto SearchPathReady;
        }
#endif

        if (env_path != NULL) {
                AddSearchDirs(ty, env_path);
        }

        if (dirs_path(path, sizeof path, DIR_DATA, "ty/lib")) {
                add(path);
        }

        if (get_directory_where_chad_looks_for_runtime_dependencies(chad)) {
                ty_snprintf(path, sizeof path, "%s/lib", chad);
                add(path);
                ty_snprintf(path, sizeof path, "%s/../lib/ty", chad);
                add(path);
        }

#ifdef TY_EMBED_LIB
        if (embedded_lib_dir(path, sizeof path)) {
                add(path);
        }
SearchPathReady:
        ;
#endif
}
//---------------------------------------------------------------------------
#undef add
//===========================================================================


//===========================================================================
/* Add FFI types here because they aren't constant expressions on Windows. */
//---------------------------------------------------------------------------
#define BUILTIN_FFI_TYPE(name, ffi_type_ptr, t)                         \
        compiler_introduce_symbol(ty, "ffi", name, "CType[" t "]", false); \
        xvP(Globals, PTR(ffi_type_ptr))
//---------------------------------------------------------------------------
        BUILTIN_FFI_TYPE("char",   &ffi_type_schar,   "Int"     );
        BUILTIN_FFI_TYPE("short",  &ffi_type_sshort,  "Int"     );
        BUILTIN_FFI_TYPE("int",    &ffi_type_sint,    "Int"     );
        BUILTIN_FFI_TYPE("long",   &ffi_type_slong,   "Int"     );
        BUILTIN_FFI_TYPE("uchar",  &ffi_type_uchar,   "Int"     );
        BUILTIN_FFI_TYPE("ushort", &ffi_type_ushort,  "Int"     );
        BUILTIN_FFI_TYPE("uint",   &ffi_type_uint,    "Int"     );
        BUILTIN_FFI_TYPE("ulong",  &ffi_type_ulong,   "Int"     );
        BUILTIN_FFI_TYPE("u8",     &ffi_type_uint8,   "Int"     );
        BUILTIN_FFI_TYPE("u16",    &ffi_type_uint16,  "Int"     );
        BUILTIN_FFI_TYPE("u32",    &ffi_type_uint32,  "Int"     );
        BUILTIN_FFI_TYPE("u64",    &ffi_type_uint64,  "Int"     );
        BUILTIN_FFI_TYPE("i8",     &ffi_type_sint8,   "Int"     );
        BUILTIN_FFI_TYPE("i16",    &ffi_type_sint16,  "Int"     );
        BUILTIN_FFI_TYPE("i32",    &ffi_type_sint32,  "Int"     );
        BUILTIN_FFI_TYPE("i64",    &ffi_type_sint64,  "Int"     );
        BUILTIN_FFI_TYPE("float",  &ffi_type_float,   "Float"   );
        BUILTIN_FFI_TYPE("double", &ffi_type_double,  "Float"   );
        BUILTIN_FFI_TYPE("ptr",    &ffi_type_pointer, "Ptr[Any]");
        BUILTIN_FFI_TYPE("void",   &ffi_type_void,    "nil"     );
//---------------------------------------------------------------------------
#undef BUILTIN_FFI_TYPE
//===========================================================================


//====/ AST Enum /===========================================================
#define X(name)                                       \
        compiler_introduce_tag(ty, "ty", #name, -1);  \
        xvP(Globals, TAG(Ty ## name));                \

        TY_AST_NODES
#undef X
//===========================================================================




        GC_RESUME();
}

char const *
vm_builtin_type(char const *module, char const *name)
{
        for (int i = 0; i < countof(builtins); ++i) {
                if (
                        s_eq(builtins[i].name, name)
                     && (
                                (builtins[i].module == module)
                             || (
                                        (builtins[i].module != NULL)
                                     && (module != NULL)
                                     && s_eq(builtins[i].module, module)
                                )
                        )
                ) {
                        return builtins[i].sig;
                }
        }

        return NULL;
}

char const *
vm_builtin_source(Value const *f, char const **file, int *line)
{
        for (int i = 0; i < countof(builtins); ++i) {
                if (
                        (builtins[i].value.type == VALUE_BUILTIN_FUNCTION)
                     && (builtins[i].value.builtin_function == f->builtin_function)
                     && (builtins[i].src != NULL)
                ) {
                        *file = builtins[i].file;
                        *line = builtins[i].line;
                        return builtins[i].src;
                }
        }

        return NULL;
}

static struct {
        int class;
        char const *name;
        char const *src;
        char const *file;
        int line;
} builtin_methods[] = {
#include "gen/builtin_method_src.h"
};

char const *
vm_builtin_method_source(int class, char const *name, char const **file, int *line)
{
        for (int i = 0; i < countof(builtin_methods); ++i) {
                if (
                        (builtin_methods[i].class == class)
                     && s_eq(builtin_methods[i].name, name)
                ) {
                        *file = builtin_methods[i].file;
                        *line = builtin_methods[i].line;
                        return builtin_methods[i].src;
                }
        }

        return NULL;
}

void
vm_load_c_module(Ty *ty, char const *name, void *p)
{
        struct {
                char const *name;
                Value value;
        } *mod = p;

        for (isize i = 0; mod[i].name != NULL; ++i) {
                compiler_introduce_symbol(ty, name, mod[i].name, NULL, false);
                xvP(Globals, mod[i].value);
        }
}

inline static Value *
(topN)(Ty *ty, int n)
{
        return vZ(STACK) - n;
}

inline static Value *
(top)(Ty *ty)
{
        return topN(1);
}

void
xprint_stack(Ty *ty, int n)
{
        fprintf(stderr, "STACK: (%zu)\n", vN(STACK));
        for (int i = 0; i < zminu(n, vN(STACK)); ++i) {
                if (vN(FRAMES) == 0) {
                        fprintf(stderr, "      %s\n", VSC(top() - i));
                        continue;
                }

                int i_abs = vN(STACK) - (i + 1);
                int off = i_abs - vvL(FRAMES)->fp;

                Expr const *func = compiler_find_func(ty, IP);
                char const *name = (func != NULL && vN(func->fn->scope->owned) > off)
                                 ? v_(func->fn->scope->owned, off)[0]->identifier
                                 : NULL;

                if (off == 0) {
                        fprintf(
                                stderr,
                                "%s%8.8s%s --> %s%8.8s%s = %s\n",
                                TERM(95;1),
                                (func == NULL ? "???" : func->fn->name),
                                TERM(0;92),
                                TERM(33),
                                name,
                                TERM(0),
                                VSC(top() - i)
                        );
                } else if (name != NULL) {
                        fprintf(
                                stderr,
                                "   %s%18.18s%s = %s\n",
                                TERM(33),
                                name,
                                TERM(0),
                                VSC(top() - i)
                        );
                } else {
                        fprintf(
                                stderr,
                                "%24s%s\n",
                                "",
                                VSC(top() - i)
                        );
                }
        }
}

#define print_stack(ty, n)

inline static Value
(pop)(Ty *ty)
{
        return vXx(STACK);
}

inline static Value
(peek)(Ty *ty)
{
        return *top();
}

inline static void
(push)(Ty *ty, Value v)
{
        xvP(STACK, v);

}

inline static void
(xpush)(Ty *ty, Value v)
{
        vPx(STACK, v);
}

inline static void
(put)(Ty *ty, Value v)
{
        *top() = v;
}

inline static void
(swap)(Ty *ty)
{
        SWAP(Value, top()[-1], top()[0]);
}

inline static Value *
local(Ty *ty, int i)
{
        return v_(STACK, vvL(FRAMES)->fp + i);
}

inline static Value *
FrameLocals(Ty *ty)
{
        return (vN(FRAMES) > 0) ? local(ty, 0) : NULL;
}

inline static Value **
FrameEnv(Ty *ty)
{
        return (vN(FRAMES) > 0) ? ActiveFun(ty)->env : NULL;
}

inline static Value *
(poptarget)(Ty *ty)
{
        return vXx(TARGETS).t;
}

inline static Value *
(peektarget)(Ty *ty)
{
        return vvL(TARGETS)->t;
}

inline static void
(pushtarget)(Ty *ty, Value *v, void *gc)
{
        xvP(TARGETS, ((Target) { .t = v, .gc = gc }));
}

inline static bool
SpecialTarget(Ty *ty)
{
        return pT(vvL(TARGETS)->t) != 0;
}

inline static Value
GetSelf(Ty *ty)
{
        Value const *fun = ActiveFun(ty);
        u32 np = param_count_of(fun);

        usize i = vvL(FRAMES)->fp + np;
        Value v = v__(STACK, i);

        while (v.type == VALUE_REF) {
                v = *v.ref;
        }

        return v;
}

static void
HandlePendingSignals(Ty *ty)
{
        bool interrupted = false;

        GC_STOP();

#ifdef TY_HAVE_SAMPLER
        if (__sync_bool_compare_and_swap(&AttachPending, 1, 0)) {
                prof_attach_toggle(ty);
        }
#endif

        for (int sig = 0; sig < NSIG; sig++) {
                if (!__sync_bool_compare_and_swap(&SignalStates[sig], 1, 0)) {
                        continue;
                }

                pthread_rwlock_rdlock(&SignalLock);
                Value fn = SignalHandlers[sig];
                pthread_rwlock_unlock(&SignalLock);

                if (!IsZero(fn)) {
                        push(INTEGER(sig));
                        vm_call(ty, &fn, 1);
                } else if (sig == SIGINT && InteractiveSession) {
                        interrupted = true;
                }
        }

        GC_RESUME();

        if (interrupted) {
                zP("Interrupted");
        }
}

inline static bool
TakePendingSignals(void)
{
        return (
                UNLIKELY(AnySignalPending)
            && __sync_bool_compare_and_swap(&AnySignalPending, 1, 0)
        );
}

inline static void
CheckPendingSignals(Ty *ty)
{
        if (UNLIKELY(TakePendingSignals())) {
                HandlePendingSignals(ty);
        }
}

__attribute__((always_inline))
inline static void
CheckFlags(Ty *ty, char const *ip)
{
        bool signaled = TakePendingSignals();

        if (UNLIKELY(GC_IS_WAITING | signaled | (VmPoll.any != 0))) {
                if (GC_IS_WAITING & (ty->GC_OFF_COUNT == 0)) {
                        WaitGC(ty);
                }
                if (UNLIKELY(signaled)) {
                        HandlePendingSignals(ty);
                }
                if (UNLIKELY(VmPoll.debug)) {
                        DebugSafepoint(ty);
                }
                if (VmPoll.prof && ip != NULL) {
                        PROF_OP(ty, ip);
                        PROF_POLL(ty);
                        atomic_signal_fence(memory_order_seq_cst);
                }
        }
}

Value *
vm_get_self(Ty *ty)
{
        Value const *fun = ActiveFun(ty);
        u32 np = param_count_of(fun);

        usize i = vvL(FRAMES)->fp + np;
        Value *v = v_(STACK, i);

        while (v->type == VALUE_REF) {
                v = v->ref;
        }

        return v;
}

inline static Value
BindMethod(Ty *ty, Value *f, Value *v)
{
        Value meth = *f;

        if (class_of(f) != -1) {
                Value *this = memcpy(mAo(sizeof *this, GC_VALUE), v, sizeof *v);
                int    nEnv = f->info[FUN_INFO_CAPTURES];
                Value **env = uAo0((nEnv + 1) * sizeof (Value *), GC_ENV);
                memcpy(env, f->env, nEnv * sizeof (Value *));
                env[nEnv] = this;
                meth.env = env;
                meth.type = VALUE_BOUND_FUNCTION;
        }

        return meth;
}

// JIT helpers
void
vm_jit_push_target(Ty *ty, Value *v)
{
        pushtarget(v, NULL);
}

Value *
vm_jit_pop_target(Ty *ty)
{
        return poptarget();
}

Value
vm_jit_bind_method(Ty *ty, Value *f, Value *v)
{
        return BindMethod(ty, f, v);
}

void
vm_jit_fail(Ty *ty, Value *top, char *ip)
{
        vN(STACK) = top - vv(STACK);
        vm_exec(ty, ip);
        UNREACHABLE();
}

static bool
co_yield_value(Ty *ty);

char *
co_colored(Ty *ty)
{
        static char buf[64];
        void *co = co_active();
        u64 hash = XXH3_64bits(&co, sizeof co);
        if (ColorOutput) {
                u8 r = 80 + (hash % 176);
                u8 g = 80 + ((hash >> 8) % 176);
                u8 b = 80 + ((hash >> 16) % 176);
                u8 max = r > g ? (r > b ? r : b) : (g > b ? g : b);
                u8 min = r < g ? (r < b ? r : b) : (g < b ? g : b);
                if (max - min < 60) {
                        u64 h2 = hash ^ (hash >> 32);
                        switch (h2 % 3) {
                        case 0: r = 200 + (h2 >> 3) % 56; g = 70 + (h2 >> 9) % 90; b = 70 + (h2 >> 15) % 64; break;
                        case 1: g = 200 + (h2 >> 3) % 56; b = 70 + (h2 >> 9) % 90; r = 70 + (h2 >> 15) % 64; break;
                        case 2: b = 200 + (h2 >> 3) % 56; r = 70 + (h2 >> 9) % 90; g = 70 + (h2 >> 15) % 64; break;
                        }
                }
                ty_snprintf(buf, sizeof buf, "\033[38;2;%d;%d;%dm%p\033[0m", r, g, b, co);
        } else {
                ty_snprintf(buf, sizeof buf, "%p", co);
        }
        return buf;
}

#ifdef __has_feature
#if __has_feature(address_sanitizer)
#define ASAN_ENABLED
#endif
#endif

#ifdef __SANITIZE_ADDRESS__
#define ASAN_ENABLED
#endif

#ifdef ASAN_ENABLED
void __sanitizer_start_switch_fiber(void** fake_stack_save,
                                     const void* bottom,
                                     size_t size);
void __sanitizer_finish_switch_fiber(void* fake_stack_save,
                                      const void** bottom_old,
                                      size_t* size_old);

void __asan_unpoison_memory_region(void const *addr, size_t size);

static void
xco_switch(cothread_t co)
{
        co_switch(co);
}
#else
#define __sanitizer_start_switch_fiber(...)
#define __sanitizer_finish_switch_fiber(...)
#define __asan_unpoison_memory_region(...)
static void
xco_switch(cothread_t co)
{
        co_switch(co);
}
#endif

inline static co_state *
GetFreeCoState(Ty *ty)
{
        co_state *st;
        if (vN(ty->co_states) > 0) {
                st = vXx(ty->co_states);
                v0(st->stack);
                v0(st->calls);
                v0(st->frames);
                v0(st->targets);
                v0(st->sps);
                v0(st->to_drop);
                v0(st->gc_roots);
                v0(st->try_stack);
                st->ctx = NIL;
                st->exec_depth = 0;
        } else {
                st = alloc0(sizeof *st);
        }
        return st;
}

inline static void
DestroyCoState(co_state *st)
{
        xvF(st->stack);
        xvF(st->calls);
        xvF(st->frames);
        xvF(st->targets);
        xvF(st->sps);
        xvF(st->to_drop);
        xvF(st->gc_roots);
        for (int i = 0; i < vC(st->try_stack); ++i) {
                xvF(v__(st->try_stack, i)->defer);
                xmF(v__(st->try_stack, i));
        }
        xvF(st->try_stack);
        xmF(st);
}

inline static bool
GeneratorIsSuspended(Generator *gen)
{
        return (gen->ip != NULL);
}

inline static Generator *
GetCurrentGenerator(Ty *ty)
{
        if (UNLIKELY(vN(FRAMES) == 0 || vN(STACK) == 0)) {
                return NULL;
        }

        if (UNLIKELY(vv(STACK)->type != VALUE_GENERATOR)) {
                return NULL;
        }

        return vv(STACK)->gen;
}

static Generator *
NewGenerator(Ty *ty, Value fun)
{
        Generator *gen = mAo0(sizeof (Generator), GC_GENERATOR);
        gen->f = fun;
        gen->ip = code_of(&fun);
        gen->st = GetFreeCoState(ty);
        gen->st->ctx = ty->st->ctx;

        xvP(gen->st->stack, GENERATOR(gen));

        return gen;
}

static char const *
co_up(Ty *ty, co_state *st)
{
        if (
                (vN(st->frames) == 0)
             || (vN(st->stack)  == 0)
             || (vv(st->stack)->type != VALUE_GENERATOR)
        ) {
                return NULL;
        }

        Generator *gen = vv(st->stack)->gen;
        *st = *gen->st;
        return gen->ip;
}

static void
DoDrop(Ty *ty);

static ThrowCtx *
PopThrowCtx(Ty *ty);

inline static bool
IsCloseSignal(Value const *exc)
{
        return (exc->type == VALUE_GENERATOR) && exc->gen->closing;
}

static noreturn void
co_finish_close(Ty *ty)
{
        Generator *gen = vv(STACK)->gen;

        PopThrowCtx(ty);

        while (vN(DROP_STACK) > 0) {
                DoDrop(ty);
        }

        ty->st->stack = STACK;
        SWAP(co_state *, gen->st, ty->st);
        STACK = ty->st->stack;

        vN(STACK) = vXx(FRAMES).fp;
        IP = vXx(CALLS);

        put(None);

        xvP(ty->co_states, gen->st);
        gen->st = NULL;

        cothread_t co = gen->co;
        gen->co = NULL;

        xvP(CO_THREADS, co_active());
        co_switch(co);

        UNREACHABLE();
}

static bool
co_abort(Ty *ty)
{
        if (vN(FRAMES) == 0 || vN(STACK) == 0) {
                return false;
        }

        usize n = v_0(FRAMES).fp;

        if (n == 0 || v_(STACK, n - 1)->type != VALUE_GENERATOR) {
                return false;
        }

        Generator *gen = v_(STACK, n - 1)->gen;
        STACK.count = n - 1;

        ty->st->stack = STACK;
        SWAP(co_state *, gen->st, ty->st);
        STACK = ty->st->stack;

        vXx(FRAMES);
        IP = vXx(CALLS);

        return true;
}

_Thread_local Generator *InterruptedGenerator;

static bool
co_yield_value(Ty *ty)
{
        if (UNLIKELY((vN(FRAMES) == 0) | (vN(STACK) == 0))) {
                return false;
        }

        if (UNLIKELY(vv(STACK)->type != VALUE_GENERATOR)) {
                return false;
        }

        Generator *gen = vv(STACK)->gen;
        gen->ip = IP;

        Value v = pop();

        ty->st->stack = STACK;
        SWAP(co_state *, gen->st, ty->st);
        STACK = ty->st->stack;

        vN(STACK) = vXx(FRAMES).fp;
        IP = vXx(CALLS);

        put(v);

        cothread_t co = gen->co;

        if (gen->st->exec_depth > 1 || vN(gen->st->try_stack) > 0) {
                CO_LOG("co_yield()", TERM(91;1), "switch to [%p] (RECURSED): %s", gen->co, VSC(top()));
                gen->co = co_active();
        } else {
                CO_LOG("co_yield()", TERM(91;1), "switch to [%p]: %s", gen->co, VSC(top()));
                gen->co = NULL;
                gen->st->exec_depth = 0;
                xvP(CO_THREADS, co_active());
        }

        co_switch(co);

        CO_LOG("co_yield()", TERM(92;1), "resume with: %s", VSC(top()));

        return true;
}

static void
co_retire(Ty *ty)
{
        Generator *gen = GetCurrentGenerator(ty);

        if (
                (gen == NULL)
             || (vN(FRAMES) != 1)
             || (vN(ty->st->try_stack) > 0)
             || (vN(DROP_STACK) > 0)
        ) {
                push(None);
                DoYield(ty);
                return;
        }

        gen->ip = code_of(&gen->f);

        ty->st->stack = STACK;
        SWAP(co_state *, gen->st, ty->st);
        STACK = ty->st->stack;

        vN(STACK) = vXx(FRAMES).fp;
        IP = vXx(CALLS);

        put(None);

        xvP(ty->co_states, gen->st);
        gen->st = NULL;

        cothread_t co = gen->co;
        gen->co = NULL;

        xvP(CO_THREADS, co_active());
        co_switch(co);

        UNREACHABLE();
}

static _Thread_local isize DeoptTryBase = -1;

enum { REENTRIES = 4 };

static void
DeoptFrame(Ty *ty, char *ip)
{
        char *ret = v_L(CALLS);
        isize k = vN(TRY_STACK);

        while (k > 0 && v__(TRY_STACK, k - 1)->fs >= vN(FRAMES)) {
                k -= 1;
        }

        DeoptTryBase = (k < vN(TRY_STACK)) ? k : -1;

        v_L(CALLS) = &halt;
        vm_exec(ty, ip);
        IP = ret;
}

inline static i32
xjit_finish(Ty *ty, isize depth, i32 rc);

inline static JitFn *
frame_jit(Frame const *frame)
{
        if (frame->jit_code != NULL && !jit_pending(frame->jit_code)) {
                return (JitFn *)frame->jit_code;
        }

        void *jit = jit_of(&frame->f);

        if (jit != NULL && !jit_pending(jit)) {
                return jit;
        }

        LirCode const *code = jit_code_of(&frame->f);

        return (code != NULL) ? (JitFn *)code->body : NULL;
}

inline static i32
xjit(Ty *ty, isize depth, JitFn *func, i32 resume_idx, Value *args, Value **env)
{
        if (UNLIKELY(vN(STACK) + 256 > vC(STACK))) {
                isize ai = args - vv(STACK);
                xvR(STACK, vN(STACK) + 256);
                args = v_(STACK, ai);
        }

        IP = &JIT;

        ++EXEC_DEPTH;
        ++EXEC_DEPTH;
        v_(FRAMES, depth)->jit_code = func;
        i32 rc = (*func)(ty, resume_idx, args, env, &v_(FRAMES, depth)->jit_pc);
        --EXEC_DEPTH;

        return xjit_finish(ty, depth, rc);
}

__attribute__((noinline, cold))
static void
NoteDeopt(Ty *ty, Frame const *top)
{
        Value          fn = top->f;
        LirCode const *lc = jit_code_of(&fn);

        fn.type = VALUE_FUNCTION;

        if (
                (lc != NULL)
             && (lc->body == (void *)frame_jit(top))
             && (__atomic_add_fetch((u32 *)&lc->deopts, 1, __ATOMIC_RELAXED) == JIT_DEOPT_LIMIT)
        ) {
                if (ProfMode) {
                        prof_jit_despecialize(&fn, JIT_DEOPT_LIMIT);
                }
                jit_despecialize(ty, &fn);
        }
}

static bool
TierFrame(Ty *ty, isize depth, i32 resume)
{
        Frame *frame = v_(FRAMES, depth);
        Value  fn    = frame->f;
        isize  k     = vN(TRY_STACK);

        fn.type = VALUE_FUNCTION;

        if (k > 0 && v__(TRY_STACK, k - 1)->fs >= vN(FRAMES)) {
                return false;
        }

        JitFn *jit = jit_promote(ty, &fn);

        if (jit == NULL) {
                return false;
        }

        i32 entry = 0;

        if (resume > 0) {
                LirCode const *lc     = jit_code_of(&fn);
                u32            offset = resume - 1;

                if (lc == NULL || lc->body != (void *)jit) {
                        return false;
                }

                entry = -1;

                for (u32 i = 0; i < lc->nosr; ++i) {
                        if (lc->osr[2 * i] == offset) {
                                entry = lc->osr[2 * i + 1];
                                break;
                        }
                }

                if (entry < 0) {
                        return false;
                }
        }

        xjit(ty, depth, jit, entry, v_(STACK, frame->fp), frame->f.env);

        while (vN(FRAMES) > depth) {
                isize  i   = vN(FRAMES) - 1;
                Frame *top = vvL(FRAMES);
                xjit(ty, i, frame_jit(top), top->jit_resume, v_(STACK, top->fp), top->f.env);
        }

        return true;
}

inline static i32
xjit_finish(Ty *ty, isize depth, i32 rc)
{
        v_(FRAMES, depth)->jit_pc = NULL;

        i32 next_resume = JIT_RESUME(rc);
        Frame *top = v_(FRAMES, depth);
        Value v;

        switch (JIT_REASON(rc)) {
        case JIT_RETURN:
JitReturn:
                CO_LOG("jit_return", TERM(93;1), "ret = %s", SHOW(vvL(STACK), BASIC));
                IP = vXx(CALLS);
                v = v_L(STACK);
                vN(STACK) = vXx(FRAMES).fp + 1;
                v_L(STACK) = v;
                CO_LOG("jit_return", TERM(92;1), "ret = %s", SHOW(vvL(STACK), BASIC));
                break;

        case JIT_CALL:
                CO_LOG("jit_trampoline_call", TERM(94;1), "suspend with resume_idx = %d", next_resume);
                top->jit_resume = next_resume;
                break;

        case JIT_YIELD_SOME:
                CO_LOG("jit_yield_some", TERM(91;1), "yielding: %s, resume=%d", VSC(vvL(STACK)), next_resume);
                top->jit_resume = next_resume;
                v_L(STACK) = Some(v_L(STACK));
                DoYield(ty);
                CheckInterrupt(ty);
                break;

        case JIT_YIELD:
                CO_LOG("jit_yield", TERM(91;1), "yielding: %s", VSC(vvL(STACK)));
                top->jit_resume = next_resume;
                DoYield(ty);
                CheckInterrupt(ty);
                break;

        case JIT_YIELD_NONE:
                if (vN(FRAMES) > 1) {
                        push(NIL);
                        goto JitReturn;
                }
                top->jit_resume = next_resume;
                CO_LOG("jit_yield_none", TERM(91;1), "retiring");
                co_retire(ty);
                CheckInterrupt(ty);
                break;

        case JIT_DEOPT:
                if (ProfMode) {
                        prof_jit_deopt(ty, top, next_resume);
                }
                TY_PROBE_IF(jit__deopt, name_of(&top->f), (long)next_resume);
                NoteDeopt(ty, top);
                top->jit_resume = 0;
                top->deopts += 1;
                DeoptFrame(ty, (char *)code_of(&top->f) + next_resume);
                break;

        case JIT_OSR:
                top->jit_resume = 0;
                if (!TierFrame(ty, depth, next_resume)) {
                        DeoptFrame(ty, (char *)code_of(&top->f) + (next_resume > 0 ? next_resume - 1 : 0));
                }
                break;
        }

        --EXEC_DEPTH;

        return rc;
}

inline static void
go_jit(Ty *ty)
{
        isize depth0 = vN(FRAMES) - 1;

        while (vN(FRAMES) > depth0) {
                isize depth = vN(FRAMES) - 1;
                Frame *top = vvL(FRAMES);

                usize cfp = top->fp;
                Value *args = v_(STACK, cfp);

                i32 resume_idx = top->jit_resume;

                CO_LOG("go()", TERM(34;1), "%s => resume%s: %d", TERM(92;1), TERM(0), resume_idx);

                xjit(ty, depth, frame_jit(top), resume_idx, args, top->f.env);
        }

        CO_LOG("go()", TERM(34;1), "%s => end%s", TERM(91;1), TERM(0));
}

static bool
vm_osr(Ty *ty)
{
        if (vN(FRAMES) == 0) {
                return false;
        }
        Frame *frame = vvL(FRAMES);
        Value fn = frame->f;
        if (fn.type != VALUE_FUNCTION || DebugJitOff || frame->deopts >= REENTRIES) {
                return false;
        }
        char const *code = code_of(&fn);
        if (IP < code || IP >= code + code_size_of(&fn)) {
                return false;
        }
        uptr state = (uptr)jit_of(&fn);
        JitFn *jit;
        if (state == 0) {
                return false;
        }
        if (jit_pending((void *)state)) {
                if (state == JIT_UNSEEN) {
                        state = jit_eager() == 1 ? JIT_UNSEEN + 1 : JIT_UNSEEN + jit_budget(&fn);
                }
                if (state > JIT_UNSEEN + 1) {
                        set_jit_of(&fn, (void *)(state - 1));
                        return false;
                }
                jit = try_jit_now(ty, &fn);
        } else {
                jit = (JitFn *)state;
        }
        LirCode const *lc = jit == NULL ? NULL : jit_code_of(&fn);
        if (lc == NULL) {
                return false;
        }
        u32 offset = IP - code;
        i32 entry = -1;
        for (u32 i = 0; i < lc->nosr; ++i) {
                if (lc->osr[2 * i] == offset) {
                        entry = lc->osr[2 * i + 1];
                        break;
                }
        }
        if (entry < 0) {
                return false;
        }
        usize f0 = vN(FRAMES) - 1;
        frame->jit_resume = 0;
        xjit(ty, f0, jit, entry, v_(STACK, frame->fp), fn.env);
        while (vN(FRAMES) > f0) {
                isize i = vN(FRAMES) - 1;
                Frame *top = vvL(FRAMES);
                xjit(ty, i, frame_jit(top), top->jit_resume, v_(STACK, top->fp), top->f.env);
        }
        return true;
}

inline static bool
call_jit(Ty *ty, Value const *f)
{
        JitFn *func = try_jit(ty, f);
        if (func == NULL) {
                return false;
        }

        char *ip = IP;

        CO_LOG("call_jit()", TERM(93;1), "call %s", VSC(f));

        usize fp = vvL(FRAMES)->fp;
        usize f0 = vN(FRAMES) - 1;

        v_(FRAMES, f0)->jit_resume = 0;

        xjit(ty, f0, func, 0, v_(STACK, fp), f->env);

        if (LIKELY(vN(FRAMES) == f0)) {
                IP = ip;
                return true;
        }

        while (vN(FRAMES) != f0) {
                isize i = vN(FRAMES) - 1;
                Frame *top = vvL(FRAMES);

                usize cfp = top->fp;
                Value *args = v_(STACK, cfp);

                i32 resume_idx = top->jit_resume;

                CO_LOG("call_jit()", TERM(34;1), "%s => resume%s: %d", TERM(92;1), TERM(0), resume_idx);

                xjit(ty, i, frame_jit(top), resume_idx, args, top->f.env);
        }

        CO_LOG("call_jit()", TERM(34;1), "%s => return%s", TERM(91;1), TERM(0));

        IP = ip;

        return true;
}

noreturn static void
do_co(void)
{
        Ty *ty = co_ty;

        CO_LOG("do_co()", TERM(94), "%s: %s", SHOW(ActiveFun(ty), BASIC), vN(STACK) > 1 ? SHOW(local(ty, 0), BASIC) : "--");

        Generator *gen = vv(STACK)->gen;

        if (UNLIKELY(IP == code_of(&gen->f))) {
                call_jit(ty, &gen->f);
        }

        while (IP == &JIT) {
                go_jit(ty);
        }

        vm_exec(ty, IP);

        UNREACHABLE();
}

#if !defined(TY_RELEASE)
__attribute__((optnone, noinline))
#endif
inline static void
xcall(Ty *ty, Value const *f, Value const *pSelf, int argc, Value const *pKwargs, char *whence)
{
        if (UNLIKELY(vN(FRAMES) >= TY_MAX_CALL_DEPTH)) {
                zP("maximum call depth exceeded");
        }

        int   np      = f->info[FUN_INFO_PARAM_COUNT];
        int   bound   = f->info[FUN_INFO_BOUND];

        int   irest   = rest_idx_of(f);
        int   ikwargs = kwargs_idx_of(f);
        Value kwargs  = (pKwargs != NULL) ? *pKwargs : NIL;

        Value self;
        int   class   = f->info[FUN_INFO_CLASS];

        int   fp      = vN(STACK) - argc;
        int   fz      = fp + bound;

        if (class != -1) {
                self = ((pSelf != NULL) && !IsNone(*pSelf)) ? *pSelf : self_of(f);
        } else {
                self = ZERO;
        }

        CO_LOG("xcall", TERM(91;1), "call %s: bound=%d, argc=%d", VSC(f), bound, argc);

        LOG(
                "Calling %s with %d args, bound = %d, self = %s, env size = %d",
                VSC(f), argc, bound, SHOW(&self, BASIC), f->info[2]
        );

        xvR(STACK, fz);

        if (UNLIKELY(irest != ikwargs)) {
                if (irest != -1) {
                        int nExtra = max(argc - irest, 0);
                        Array *extra = vAun(nExtra);

                        memcpy(v_(*extra, 0), vv(STACK) + fp + irest, nExtra * sizeof (Value));
                        memset(vv(STACK) + fp + irest, 0, nExtra * sizeof (Value));
                        extra->count = nExtra;

                        argc = min(argc, irest + 1);

                        if (LIKELY(fp + argc < fz)) {
                                NilStackRange(ty, fp + argc, bound - argc);
                        }

                        *v_(STACK, fp + irest) = ARRAY(extra);
                } else if (LIKELY(fp + argc < fz)) {
                        NilStackRange(ty, fp + argc, bound - argc);
                }
                if (ikwargs != -1) {
                        // FIXME: don't allocate a dict when there are no kwargs
                        *v_(STACK, fp + ikwargs) = !IsNil(kwargs) ? kwargs : DICT(dict_xnew(ty));
                }
        } else if (LIKELY(fp + argc < fz)) {
                NilStackRange(ty, fp + argc, bound - argc);
        }

        vN(STACK) = fz;

        if (class != -1) {
                *v_(STACK, fp + np) = self;
        }

        xvP(FRAMES, FRAME(fp, *f, IP));
        xvP(CALLS, whence);

#ifdef TY_HAVE_USDT
        if (TY_PROBING(function__entry)) {
                ProbeFunction(ty, f, true);
        }
#endif

        // Fill in kwargs (overwriting positional args)
        if (UNLIKELY(!IsNil(kwargs))) {
                char const *name = ((char *)f->info) + FUN_PARAM_NAMES;
                for (int i = 0; i < np; ++i, name += strlen(name) + 1) {
                        if (i == irest || i == ikwargs) {
                                continue;
                        }

                        Value *arg = dict_get_member(ty, kwargs.dict, name);

                        if (arg != NULL) {
                                *local(ty, i) = *arg;
                        }
                }
        }

        CheckUsed(ty);
}

inline static void
SetupGenerator(Ty *ty, Value const *f, Value const *pSelf, int argc, Value const *pKwargs)
{
        GC_STOP();

        Value v = GENERATOR(NewGenerator(ty, *f));

        count_call(f);

        xvPn(v.gen->st->stack, topN(argc), argc);
        vN(STACK) -= argc;

        ty->st->stack = STACK;
        SWAP(co_state *, ty->st, v.gen->st);
        STACK = ty->st->stack;

        xcall(ty, &v.gen->f, pSelf, argc, pKwargs, IP);

        CO_LOG("SetupGenerator()", TERM(95), "initial frame for %s with: %s (self=%s)", VSC(&v.gen->f), VSC(top()), pSelf ? VSC(pSelf) : "--");

        ty->st->stack = STACK;
        SWAP(co_state *, ty->st, v.gen->st);
        STACK = ty->st->stack;

        GC_RESUME();

        push(v);
}

inline static FnExpr const *
arm_fn(Expr const *arm)
{
        return IsStmt(arm) ? ((Stmt const *)arm)->value->fn : arm->fn;
}

static bool
plain_arm(FnExpr const *fn)
{
        if (fn->rest != -1 || fn->ikwargs != -1 || (fn->name != NULL && IsPrivateMember(fn->name))) {
                return false;
        }

        for (int i = 0; i < vN(fn->dflts); ++i) {
                Expr const *dflt = v__(fn->dflts, i);
                if (dflt != NULL && dflt->type != EXPRESSION_NIL) {
                        return false;
                }
        }

        return true;
}

static bool
arm_fits(FnExpr const *fn, int argc)
{
        int required = 0;

        for (int i = 0; i < vN(fn->params); ++i) {
                required += (v__(fn->dflts, i) == NULL);
        }

        return (argc >= required) && (argc <= vN(fn->params));
}

inline static bool
dispatcher(Value const *f)
{
        return (f->type == VALUE_FUNCTION)
            && (rest_idx_of(f) != -1)
            && (kwargs_idx_of(f) != -1)
            && (expr_of(f)->type == EXPRESSION_MULTI_FUNCTION);
}

static bool
dispatch(Ty *ty, Value const *f, Value const *pSelf, int argc, Value const *pKwargs)
{
        Expr const *e      = expr_of(f);
        bool        method = is_method(e);
        Value       self   = NIL;
        usize       base   = vN(STACK) - argc;

        if ((pKwargs != NULL && !IsNil(*pKwargs)) || (e->fn->mtype & MT_SET)) {
                return false;
        }

        if (method) {
                self = (pSelf != NULL && !IsNone(*pSelf)) ? *pSelf : self_of(f);
                if (self.type != VALUE_OBJECT) {
                        return false;
                }
        }

        for (int i = 0; i < vN(e->fn->functions); ++i) {
                if (!plain_arm(arm_fn(v__(e->fn->functions, i)))) {
                        return false;
                }
        }

        gP(&self);

        for (int i = 0; i < vN(e->fn->functions); ++i) {
                Expr const   *arm = v__(e->fn->functions, i);
                FnExpr const *fn  = arm_fn(arm);
                Value const  *g   = method
                                  ? class_lookup_method_i(ty, self.class, M_ID(fn->name))
                                  : v_(Globals, ((Stmt const *)arm)->target->symbol->i);

                if (!arm_fits(fn, argc)) {
                        continue;
                }

                if (g == NULL || g->type != VALUE_FUNCTION) {
                        break;
                }

                for (int j = 0; j < argc; ++j) {
                        push(*v_(STACK, base + j));
                }

                Value r = method ? vm_call_method(ty, &self, g, argc) : vm_call(ty, g, argc);

                if (r.type != VALUE_NONE) {
                        gX();
                        vN(STACK) = base;
                        push(r);
                        return true;
                }
        }

        gX();

        return false;
}

static bool
call(Ty *ty, Value const *f, Value const *pSelf, int argc, Value const *pKwargs)
{
        if (UNLIKELY(is_starred(f))) {
                SetupGenerator(ty, f, pSelf, argc, pKwargs);
                return false;
        }

        if (UNLIKELY(dispatcher(f)) && dispatch(ty, f, pSelf, argc, pKwargs)) {
                return false;
        }

        if (
                is_overload(f)
             && (param_count_of(f) < argc)
             && (rest_idx_of(f) == -1)
        ) {
                STACK.count -= argc;
                push(NONE);
                return false;
        }

        xcall(ty, f, pSelf, argc, pKwargs, IP);

        if (call_jit(ty, f)) {
                return false;
        }

        count_call(f);

        IP = code_of(f);

        return true;
}

static void
call6t(Ty *ty, Value const *f, Value const *pSelf, int argc, Value const *pKwargs, char *whence)
{
        xvP(CALLS, IP);

        if (UNLIKELY(is_starred(f))) {
                SetupGenerator(ty, f, pSelf, argc, pKwargs);
                IP = whence;
                return;
        }

        xcall(ty, f, pSelf, argc, pKwargs, whence);
        count_call(f);
        IP = code_of(f);
}

void
vm_xcall(Ty *ty, Value const *f, Value const *pSelf, int argc, Value const *pKwargs)
{
        xcall(ty, f, pSelf, argc, pKwargs, IP);
}

void
vm_trampoline(Ty *ty)
{
        go_jit(ty);
}

void
vm_trampoline_resume(Ty *ty, i32 rc)
{
        isize depth0 = vN(FRAMES) - 1;

        while (v_(FRAMES, depth0)->jit_pc == NULL) {
                depth0 -= 1;
        }

        --EXEC_DEPTH;
        xjit_finish(ty, depth0, rc);

        while (vN(FRAMES) > depth0) {
                isize depth = vN(FRAMES) - 1;
                Frame *top = vvL(FRAMES);
                xjit(ty, depth, frame_jit(top), top->jit_resume, v_(STACK, top->fp), top->f.env);
        }
}

void
vm_trampoline_linked(Ty *ty, JitFn *func, Value **env)
{
        isize depth0 = vN(FRAMES) - 1;
        Frame *frame = vvL(FRAMES);

        if (LIKELY(vN(STACK) + 256 <= vC(STACK))) {
                IP = &JIT;
                EXEC_DEPTH += 2;
                i32 rc = (*func)(ty, 0, v_(STACK, frame->fp), env, &frame->jit_pc);
                --EXEC_DEPTH;
                if (LIKELY(JIT_REASON(rc) == JIT_RETURN)) {
                        v_(FRAMES, depth0)->jit_pc = NULL;
                        IP = vXx(CALLS);
                        Value v = v_L(STACK);
                        vN(STACK) = vXx(FRAMES).fp + 1;
                        v_L(STACK) = v;
                        --EXEC_DEPTH;
                        return;
                }
                xjit_finish(ty, depth0, rc);
        } else {
                xjit(ty, depth0, func, 0, v_(STACK, frame->fp), env);
        }

        while (vN(FRAMES) > depth0) {
                isize depth = vN(FRAMES) - 1;
                Frame *top = vvL(FRAMES);
                xjit(ty, depth, frame_jit(top), top->jit_resume, v_(STACK, top->fp), top->f.env);
        }
}

inline static bool
plain_call(Ty *ty, Value const *f, int argc)
{
        JitFn *jit   = jit_of(f);
        i32    bound = f->info[FUN_INFO_BOUND];

        if (
                UNLIKELY(DebugJitOff)
             || (jit == NULL)
             || jit_pending(jit)
             || (f->type != VALUE_FUNCTION)
             || (f->info[FUN_INFO_CLASS] != -1)
             || (rest_idx_of(f) != -1)
             || (kwargs_idx_of(f) != -1)
             || (argc > bound)
             || (vN(FRAMES) >= TY_MAX_CALL_DEPTH)
             || TY_PROBING(function__entry)
        ) {
                return false;
        }

        char  *ip = IP;
        usize  fp = vN(STACK) - argc;
        isize  f0 = vN(FRAMES);

        xvR(STACK, fp + bound + 256);
        NilStackRange(ty, fp + argc, bound - argc);
        vN(STACK) = fp + bound;

        xvP(FRAMES, FRAME(fp, *f, ip));
        xvP(CALLS, ip);

        CheckUsed(ty);

        v_(FRAMES, f0)->jit_resume = 0;

        xjit(ty, f0, jit, 0, v_(STACK, fp), f->env);

        while (vN(FRAMES) != f0) {
                isize  i   = vN(FRAMES) - 1;
                Frame *top = vvL(FRAMES);
                xjit(ty, i, frame_jit(top), top->jit_resume, v_(STACK, top->fp), top->f.env);
        }

        IP = ip;

        return true;
}

static void
exec_fn(Ty *ty, Value const *f, Value const *pSelf, int argc, Value const *pKwargs)
{
        if (UNLIKELY(is_starred(f))) {
                SetupGenerator(ty, f, pSelf, argc, pKwargs);
                return;
        }

        if (pSelf == NULL && pKwargs == NULL && plain_call(ty, f, argc)) {
                return;
        }

        if (UNLIKELY(dispatcher(f)) && dispatch(ty, f, pSelf, argc, pKwargs)) {
                return;
        }

        xcall(ty, f, pSelf, argc, pKwargs, IP);

        if (LIKELY(call_jit(ty, f))) {
                return;
        }

        v_L(CALLS) = &halt;
        vm_exec(ty, code_of(f));
}

#ifndef _WIN32
static VPool CoStacks = VPOOL(CO_STACK_SIZE, 1ULL << 32, true);

static void *
CoStackTake(void)
{
        void *base = VPoolTake(&CoStacks);

        if (base == NULL) {
                panic("out of memory: couldn't map a %zu-byte coroutine stack", (usize)CO_STACK_SIZE);
        }

        return base;
}

#define CoStackPut(p)  VPoolPut(&CoStacks, (p))
#else
#define CoStackTake()  xmA(CO_STACK_SIZE)
#define CoStackPut(p)  xmF(p)
#endif

inline static cothread_t
GetFreeCoThread(Ty *ty)
{
        void *base = (vN(CO_THREADS) == 0) ? CoStackTake() : vXx(CO_THREADS);
        return co_derive(base, CO_STACK_SIZE, do_co);
}

TY_INSTR_INLINE static void
call_co_ex(Ty *ty, Value *v, int n, char *whence)
{
        Generator *gen = v->gen;

        if (UNLIKELY(gen->st == NULL)) {
                push(None);
                return;
        }

        if (UNLIKELY(!GeneratorIsSuspended(gen))) {
                zP("attempt to invoke an already-active coroutine");
        }

        if (UNLIKELY(n == 0)) {
                if (LIKELY(gen->ip != code_of(&gen->f))) {
                        CO_LOG("co_call()", TERM(95), "pushing to gen frame: nil");
                        xvP(gen->st->stack, NIL);
                }
                push(*v);
        } else {
                if (LIKELY(gen->ip != code_of(&gen->f))) {
                        CO_LOG("co_call()", TERM(95), "pushing to gen frame: %s", VSC(top()));
                        xvP(gen->st->stack, peek());
                }
                put(*v);
        }

        xvP(FRAMES, FRAME(vN(STACK), gen->f, whence));
        xvP(CALLS, whence);
        v_(gen->st->frames, 0)->ip = whence;

        ty->st->stack = STACK;
        SWAP(co_state *, gen->st, ty->st);
        STACK = ty->st->stack;

        IP = gen->ip;
        gen->ip = NULL;

        if (gen->co != NULL) {
                cothread_t co = gen->co;
                gen->co = co_active();
                CO_LOG("co_call()", TERM(95), "switch BACK to %s with: %s", name_of(&gen->f), VSC(top()));
                xco_switch(co);
        } else {
                cothread_t co = GetFreeCoThread(ty);
                gen->co = co_active();
                CO_LOG("co_call()", TERM(95), "switch to FRESH %s with: %s", name_of(&gen->f), VSC(top()));
                co_ty = ty;
                xco_switch(co);

        }

        CO_LOG("co_call()", TERM(96), "back from %s with: %s", name_of(&gen->f), VSC(top()));
}

static void
call_co(Ty *ty, Value *v, int n)
{
        call_co_ex(ty, v, n, IP);
}

static ThrowCtx *
PushThrowCtx(Ty *ty)
{
        ThrowCtx *ctx;
        usize n = vN(THROW_STACK);

        if (UNLIKELY(n == vC(THROW_STACK))) {
                do {
                        ctx = alloc0(sizeof *ctx);
                        xvP(THROW_STACK, ctx);
                } while (vN(THROW_STACK) != vC(THROW_STACK));
                vN(THROW_STACK) = n;
        }

        ctx = *vZ(THROW_STACK);
        vN(THROW_STACK) += 1;

        //== (in case it's recycled) ==============
        vN(*ctx) = 0;
        ctx->traced = false;

        for (int i = 0; i < vN(ctx->locals); ++i) {
                vN(v__(ctx->locals, i)) = 0;
        }

        vN(ctx->locals) = 0;
        //=========================================

        ty->st->stack = STACK;

        if (DetailedExceptions) {
                CaptureContextEx(ty, ctx);
        } else {
                CaptureContext(ty, ctx);
        }

        return ctx;
}

inline static ThrowCtx *
CurrentThrowCtx(Ty *ty)
{
        return v_L(THROW_STACK);
}

static ThrowCtx *
PopThrowCtx(Ty *ty)
{
        return vXx(THROW_STACK);
}

inline static void
DropPendingThrow(Ty *ty)
{
        usize     n = vN(THROW_STACK);
        ThrowCtx *old;

        if (n < 2) {
                return;
        }

        old = v__(THROW_STACK, n - 2);

        v__(THROW_STACK, n - 2) = v__(THROW_STACK, n - 1);
        v__(THROW_STACK, n - 1) = old;

        vN(THROW_STACK) -= 1;
}

u64
TyThreadId(Ty *ty)
{
        return ty->id;
}

u64
RealThreadId(void)
{
        return MyId;
}

inline static void
TakeLockRaw(Ty *ty)
{
        TySpinLockLock(ty->lock);
        ty->locked = true;
        if (ty->dbg != NULL) {
                ty->dbg->state = DBG_RUNNING;
        }
}

void
TakeLock(Ty *ty)
{
        TySpinLockLock(ty->lock);
        ty->locked = true;
        DebugOnLock(ty);
}

void
vm_take_lock_raw(Ty *ty)
{
        TakeLockRaw(ty);
}

bool
MaybeTakeLock(Ty *ty)
{
        return ty->locked ? false : (TakeLock(ty), true);
}

void
ReleaseLock(Ty *ty, bool blocked)
{
        *ty->blocked = blocked;
        ty->locked = false;
        if (ty->dbg != NULL) {
                DebugOnRelease(ty, blocked);
        }
        TySpinLockUnlock(ty->lock);
}

bool
HoldingLock(Ty *ty)
{
        return ty->locked;
}

void
NewThread(Ty *ty, Thread *t, Value *call, Value *name, bool isolated)
{
        atomic_bool created = false;
        Value thread = THREAD(t);
        ThreadGroup *group = isolated ? NewThreadGroup(ty->group) : ty->group;

        if (group == NULL) {
                zP("too many isolated thread groups (at most %d at once)", GC_OWNER_MAX - 1);
        }

        NewThreadCtx *ctx = mrealloc(NULL, sizeof *ctx);

        *ctx = (NewThreadCtx) {
                .ty = ty,
                .ctx = call,
                .name = name,
                .created = &created,
                .t = t,
                .group = group,
                .isolated = isolated
        };

        t->ctx = call;
        TyMutexInit(&t->mutex);
        TyCondVarInit(&t->cond);
        t->alive = true;

        gP(&thread);
        UnlockTy();

        int r = TyThreadCreate(&t->t, vm_run_thread, ctx);
        if (r != 0) {
                zP("TyThreadCreate(): %s", strerror(r));
        }

        while (!created) {
                continue;
        }

        LockTy();
        gX();
}

static void
AddThread(Ty *ty, TyThread self)
{
        GC_STOP();
        GCLOG("AddThread(): %llu: taking lock", TID);
        TySpinLockLock(&ty->group->Lock);
        GCLOG("AddThread(): %llu: took lock", TID);
        xvP(ty->group->TyList, ty);
        xvP(ty->group->ThreadList, self);
        xvP(ty->group->ThreadLocks, ty->lock);
        xvP(ty->group->ThreadStates, ty->blocked);
        TySpinLockUnlock(&ty->group->Lock);
        GCLOG("AddThread(): %llu: finished", TID);
        GC_RESUME();

        DebugThreadStart(ty, self);
}

static void
CleanupThread(void *ctx)
{
        Ty *ty = ctx;

        GCLOG("Cleaning up thread: %zu bytes in use. DeadUsed = %zu", MemoryUsed, ty->group->DeadUsed);

#ifdef TY_HAVE_SAMPLER
        prof_thread_stop(ty);
#else
        TY_PROBE_IF(thread__stop, (long)ty->id);
#endif

        DebugThreadExit(ty);

        TySpinLockLock(&ty->group->DLock);
        if (ty->group->DeadUsed + MemoryUsed > MemoryLimit) {
                TySpinLockUnlock(&ty->group->DLock);
                DoGC(ty);
                TySpinLockLock(&ty->group->DLock);
        }
        xvPv(ty->group->DeadAllocs, ty->allocs);
        xvPv(ty->group->DeadFinalizable, ty->finalizable);
        ty->group->DeadUsed += MemoryUsed;
        v0(ty->allocs);
        v0(ty->finalizable);
        TySpinLockUnlock(&ty->group->DLock);

        UnlockTy();

        TySpinLockLock(&ty->group->Lock);

        GCLOG("Got threads lock on thread: %llu -- ready to clean up. Group size = %zu", TID, vN(ty->group->ThreadList));

        for (int i = 0; i < vN(ty->group->ThreadList); ++i) {
                if (ty->lock == v__(ty->group->ThreadLocks, i)) {
                        *v_(ty->group->ThreadList,   i) = vXx(ty->group->ThreadList);
                        *v_(ty->group->TyList,       i) = vXx(ty->group->TyList);
                        *v_(ty->group->ThreadLocks,  i) = vXx(ty->group->ThreadLocks);
                        *v_(ty->group->ThreadStates, i) = vXx(ty->group->ThreadStates);
                        break;
                }
        }

        usize group_remaining = vN(ty->group->ThreadList);

        TySpinLockUnlock(&ty->group->Lock);

        if (group_remaining == 0 && ty->group != &MainGroup) {
                LockTy();
                if (ty->result != NULL) {
                        value_mark(ty, ty->result);
                }
                GCDropFinalizable(ty);
                GCSweep(ty, &ty->group->DeadAllocs, &ty->group->DeadUsed);
                UnlockTy();
        }

        for (int i = 0; i < vC(THROW_STACK); ++i) {
                ThrowCtx *ctx = v__(THROW_STACK, i);
                xvF(*ctx);
                xvF(ctx->locals);
                xmF(ctx);
        }

        for (int i = 0; i < vN(ty->_2op_cache); ++i) {
                xvF(v__(ty->_2op_cache, i));
        }

        for (int i = 0; i < vN(CO_THREADS); ++i) {
                CoStackPut(v__(CO_THREADS, i));
        }

        for (int i = 0; i < vN(ty->co_states); ++i) {
                DestroyCoState(v__(ty->co_states, i));
        }

        for (int i = 0; i < TY_TMP_BUF_COUNT; ++i) {
                if (ty->tmp[i].p != TyTmpSlot(ty, i)) {
                        xmF(ty->tmp[i].p);
                }
        }

        ScratchFree(&ty->scratch);

        if (ty->slab != NULL) {
                VPoolPut(&Slabs, ty->slab);
        }

        ty->st->stack = STACK;
        DestroyCoState(ty->st);

        TySpinLockDestroy(ty->lock);
        xmF((void *)ty->lock);
        xmF((void *)ty->blocked);
        xvF(THREAD_LOCALS);
        xvF(THROW_STACK);
        xvF(CO_THREADS);
        xvF(ty->co_states);
        xvF(ty->allocs);
        xvF(ty->finalizable);
        xvF(ty->_2op_cache);
        xvF(ty->err);
        xvF(ty->marking);
        xvF(ty->visiting);
        FreeArena(&ty->arena);
        pcre2_match_data_free(ty->pcre2.match);
        pcre2_match_context_free(ty->pcre2.ctx);
        pcre2_jit_stack_free(ty->pcre2.stack);
        GlobCacheFree(ty);

        TyValueCleanup();
        TyFunctionsCleanup();

        if (group_remaining == 0 && ty->group != &MainGroup) {
                GCLOG("Cleaning up group %p", (void*)ty->group);
                BequeathAllocs(ty->group);
                ReleaseGroupId(ty->group->id);
                ty->group->dead = true;
                TySpinLockDestroy(&ty->group->Lock);
                TySpinLockDestroy(&ty->group->GCLock);
                TySpinLockDestroy(&ty->group->DLock);
                TyMutexDestroy(&ty->group->GCPhaseLock);
                TyCondVarDestroy(&ty->group->GCPhaseCond);
                xvF(ty->group->TyList);
                xvF(ty->group->ThreadList);
                xvF(ty->group->ThreadLocks);
                xvF(ty->group->ThreadStates);
                xvF(ty->group->DeadAllocs);
                xvF(ty->group->DeadFinalizable);
                xmF(ty->group->GCBlockedThreads);
        }

        GCLOG("Finished cleaning up on thread: %llu -- releasing threads lock", TID);
}

/*
 * An isolated thread's GC cannot keep allocations owned by the launching
 * thread group alive.  In particular, the function Value copied into the new
 * thread still points at the launching group's environment and capture cells.
 * Clone that scaffolding while the launcher is waiting in NewThread(), so the
 * isolated frame owns the storage it uses for LOAD_CAPTURED.
 *
 * Captured Values are intentionally copied shallowly.  Heap objects referenced
 * by those Values still obey the isolated-thread rule and must be transferred
 * through Channel when their owning group does not otherwise retain them.
 */
static Value
CloneThreadEnvironment(Ty *ty, Value const *src)
{
        Value f = *src;
        int type = f.type & ~VALUE_TAGGED;

        if (
                type != VALUE_FUNCTION
             && type != VALUE_BOUND_FUNCTION
             && type != VALUE_NATIVE_FUNCTION
        ) {
                return f;
        }

        int n = f.info[FUN_INFO_CAPTURES]
              + (type == VALUE_BOUND_FUNCTION);

        if (n == 0 || f.env == NULL) {
                return f;
        }

        Value **old = f.env;
        Value **env = uAo0(n * sizeof *env, GC_ENV);

        for (int i = 0; i < n; ++i) {
                if (old[i] == NULL) {
                        continue;
                }

                for (int j = 0; j < i; ++j) {
                        if (old[i] == old[j]) {
                                env[i] = env[j];
                                goto NextCapture;
                        }
                }

                env[i] = uAo(sizeof *env[i], GC_VALUE);
                *env[i] = *old[i];

NextCapture:
                continue;
        }

        /* Preserve references between cells in the cloned environment. */
        for (int i = 0; i < n; ++i) {
                if (env[i] == NULL || env[i]->type != VALUE_REF) {
                        continue;
                }
                for (int j = 0; j < n; ++j) {
                        if (env[i]->ref == old[j]) {
                                env[i]->ref = env[j];
                                break;
                        }
                }
        }

        f.env = env;
        return f;
}

static TyThreadReturnValue
vm_run_thread(void *p)
{
        NewThreadCtx *ctx = p;
        Value *call = ctx->ctx;
        Value *name = ctx->name;
        Thread *t = ctx->t;

        Ty *ty = mrealloc(NULL, sizeof *ty);
        InitializeTy(ty, ctx->group);

        if (ctx->isolated) {
                call[0] = CloneThreadEnvironment(ty, &call[0]);
        }

        MyTy = ty;
        MyId = ty->id = t->i;

        int argc = 0;

        GCLOG("New thread: %llu", TID);

        while (call[argc + 1].type != VALUE_NONE) {
                push(call[++argc]);
        }

        ty->group = ctx->group;

        AddThread(ty, t->t);

#ifdef TY_HAVE_SAMPLER
        prof_thread_start(ty);
#else
        TY_PROBE_IF(thread__start, (long)ty->id, 0L);
#endif

        gP(&call[0]);

        if (name != NULL) {
                push(*name);
                builtin_thread_setname(ty, 1, NULL);
                pop();
        }

#ifndef _WIN32
        pthread_cleanup_push(CleanupThread, ty);
#endif

        *ctx->created = true;

        if (TY_CATCH_ERROR()) {
                char *trace = FormatTrace(ty, NULL, NULL);
                t->v = TY_CATCH();
                fprintf(
                        stderr,
                        "Thread %lld dying with error: %s\n%s\n",
                        TID,
                        trace,
                        VSC(&t->v)
                );
                xmF(trace);
        } else {
                t->v = vmC(call, argc);
                TY_CATCH_END();
        }

        xmF(ctx);
        t->ctx = NULL;
        mF(call);

        ty->result = &t->v;

#ifndef _WIN32
        pthread_cleanup_pop(1);
#else
        CleanupThread(ty);
#endif

        TyMutexLock(&t->mutex);
        t->alive = false;
        TyMutexUnlock(&t->mutex);
        TyCondVarSignal(&t->cond);

        OKGC(t);

        return TY_THREAD_OK;
}

inline static void
FixSignalGCRoots(Ty *ty)
{
        v0(SignalGCRoots);

        for (int sig = 0; sig < NSIG; sig++) {
                Value *fn = &SignalHandlers[sig];
                if (!IsZero(*fn)) {
                        xvP(SignalGCRoots, *fn);
                }
        }
}

void
vm_del_sigfn(Ty *ty, int sig)
{
#ifndef _WIN32
        pthread_rwlock_wrlock(&SignalLock);
        m0(SignalHandlers[sig]);
        FixSignalGCRoots(ty);
        pthread_rwlock_unlock(&SignalLock);
#endif
}

void
vm_set_sigfn(Ty *ty, int sig, Value const *f)
{
#ifndef _WIN32
        pthread_rwlock_wrlock(&SignalLock);
        SignalHandlers[sig] = *f;
        FixSignalGCRoots(ty);
        pthread_rwlock_unlock(&SignalLock);
#endif
}

Value
vm_get_sigfn(Ty *ty, int sig)
{
        pthread_rwlock_rdlock(&SignalLock);
        Value f = SignalHandlers[sig];
        pthread_rwlock_unlock(&SignalLock);
        return IsZero(f) ? NIL : f;
}

int
vm_jit_handle_interrupt(Ty *ty, Value *top, JitDeopt const *info)
{
        vN(STACK) = (top - vv(STACK));

        if (GC_IS_WAITING & (ty->GC_OFF_COUNT == 0)) {
                WaitGC(ty);
        }

        JitInterruptFlag = DebugJitOff;

        if (TakePendingSignals()) {
                HandlePendingSignals(ty);
        }

        if (
                !DebugJitOff
             || (info == NULL)
             || !DebugCanDeopt(ty)
        ) {
                return 0;
        }

        isize base = vN(STACK) - info->sp;

        for (int i = 0; i < info->nsave; ++i) {
                xvP(SP_STACK, base + info->save[i]);
        }

        return 1;
}

void
vm_check_flags(Ty *ty)
{
        CheckFlags(ty, NULL);
}

static void
xdrop(Ty *ty, Value const *v)
{
        Value *f;

        switch (v->type) {
        case VALUE_ARRAY:
                for (usize i = 0; i < vN(*v->array); ++i) {
                        xdrop(ty, v_(*v->array, i));
                }
                break;

        case VALUE_TUPLE:
                for (usize i = 0; i < v->count; ++i) {
                        xdrop(ty, &v->items[i]);
                }
                break;

        case VALUE_OBJECT:
                f = class_lookup_method_i(ty, v->class, NAMES._drop_);
                if (f != NULL) {
                        vm_call_method(ty, v, f, 0);
                }
                break;

        case VALUE_GENERATOR:
                vm_close_generator(ty, v->gen);
                break;
        }
}

inline static void
DoDrop(Ty *ty)
{
        Array *group = vvL(DROP_STACK)->array;

        while (vN(*group) > 0) {
                Value v = vXx(*group);
                gP(&v);
                xdrop(ty, &v);
                gX();
        }

        vXx(DROP_STACK);
}

inline static Value *
SuperMember(Ty *ty, Value *f, int class, i32 z, char const *kind)
{
        if (f == NULL) {
                zP(
                        "super: %s%s%s has no %s %s'%s'%s",
                        TERM(97),
                        class_name(ty, class),
                        TERM(39),
                        kind,
                        TERM(34),
                        KebabName(ty, M_NAME(z)),
                        TERM(39)
                );
        }

        return f;
}

inline static struct try *
GetCurrentTry(Ty *ty)
{
        return *vvL(TRY_STACK);
}

inline static struct try *
GetDeferTry(Ty *ty)
{
        for (usize i = vN(TRY_STACK); i > 0; --i) {
                if (v__(TRY_STACK, i - 1)->clean) {
                        return v__(TRY_STACK, i - 1);
                }
        }

        zP("no active defer group");
}

inline static noreturn void
BadFieldAccess(Ty *ty, Value const *val, i32 z)
{
        if (val->type == VALUE_TUPLE) {
                zP(
                        "attempt to access non-existent field %s'%s'%s of %s%s%s",
                        TERM(34),
                        KebabName(ty, M_NAME(z)),
                        TERM(39),
                        TERM(97),
                        VSC(val),
                        TERM(39)
                );
        } else {
                zP(
                        "attempt to access non-existent member %s'%s'%s of %s%s%s",
                        TERM(34),
                        KebabName(ty, M_NAME(z)),
                        TERM(39),
                        TERM(97),
                        VSC(val),
                        TERM(39)
                );
        }
}

static struct try *
PushTry(Ty *ty)
{
        struct try *t;
        usize ntry = vN(TRY_STACK);

        if (UNLIKELY(ntry == vC(TRY_STACK))) {
                do {
                        t = alloc0(sizeof *t);
                        xvP(TRY_STACK, t);
                } while (vN(TRY_STACK) != vC(TRY_STACK));
                vN(TRY_STACK) = ntry;
        }

        t = *vZ(TRY_STACK);
        vN(TRY_STACK) += 1;

        t->flags  = ty->flags;
        t->sp     = vN(STACK);
        t->gc     = vN(RootSet);
        t->cs     = vN(CALLS);
        t->ts     = vN(TARGETS);
        t->ds     = vN(DROP_STACK);
        t->fs     = vN(FRAMES);
        t->nsp    = vN(SP_STACK);
        t->vs     = vN(VISITING);
        t->ed     = EXEC_DEPTH;
        t->off    = ty->GC_OFF_COUNT;
        t->ss     = SaveScratch(ty);
        t->state  = TRY_TRY;
        t->native = false;
        t->clean  = false;
        v0(t->defer);

        return t;
}

static void
TraceThrow(Ty *ty)
{
        ThrowCtx *ctx = CurrentThrowCtx(ty);

        if (ctx->traced) {
                return;
        }

        ctx->traced = true;

        byte_vector trace = {0};
        byte_vector brief = {0};

        FormatTrace(ty, ctx, &trace);
        TyErrorBrief(ty, &ty->exc, &brief);

        fprintf(
                stderr,
                "%s[throw]%s (try depth %zu, throw depth %zu) %s\n%s",
                TERM(95;1),
                TERM(0),
                (usize)vN(TRY_STACK),
                (usize)vN(THROW_STACK),
                vv(brief),
                (vN(trace) > 0) ? vv(trace) : ""
        );

        xvF(brief);

        if (CompilationDepth(ty) > 0) {
                byte_vector where = {0};
                CompilationTrace(ty, &where);
                if (vN(where) > 0) {
                        fprintf(stderr, "%s[compiling]%s%s\n", TERM(95), TERM(0), vv(where));
                }
                xvF(where);
        }

        xvF(trace);
}

TY_INSTR_INLINE static void
DoThrow(Ty *ty)
{
        ty->exc = CurrentThrowCtx(ty)->exc;

        if (ProfMode) {
                prof_throw(ty, IP);
        }

#ifdef TY_HAVE_USDT
        if (TY_PROBING(throw)) {
                Expr const *where = compiler_find_expr(ty, jit_frame_ip(vN(FRAMES) > 0 ? vvL(FRAMES) : NULL, IP) - 1);
                TY_PROBE(
                        throw,
                        (ty->exc.type == VALUE_OBJECT) ? class_name(ty, ty->exc.class) : "(value)",
                        (where != NULL && where->mod != NULL) ? where->mod->path : "",
                        (where != NULL) ? (int)LocLine(where->start) + 1 : 0
                );
        }
#endif

        if (UNLIKELY(TraceThrows)) {
                TraceThrow(ty);
        }

        for (;;) {
                while (
                        (vN(TRY_STACK) > 0)
                     && (vvL(TRY_STACK)[0]->state == TRY_FINALLY)
                ) {
                        vXx(TRY_STACK);
                }

                if (vN(TRY_STACK) > 0) {
                        struct try *t = v_L(TRY_STACK);

                        switch (t->state) {
                        case TRY_TRY:
                                t->state = TRY_THROW;

                                while (vN(DROP_STACK) > t->ds) {
                                        DoDrop(ty);
                                }

                                bool closing = IsCloseSignal(&ty->exc) && !t->native;

                                EXEC_DEPTH    = t->ed;
                                vN(STACK)     = t->sp;
                                vN(SP_STACK)  = t->nsp;
                                vN(FRAMES)    = t->fs;
                                vN(TARGETS)   = t->ts;
                                vN(CALLS)     = t->cs;
                                vN(RootSet)   = min(vN(RootSet), t->gc);
                                vN(VISITING)  = t->vs;
                                IP            = t->catch;

                                ty->GC_OFF_COUNT = t->off;

                                RestoreScratch(ty, t->ss);

                                push(SENTINEL);
                                push(ty->exc);

                                if (closing) {
                                        IP     = t->finally;
                                        t->end = NULL;
                                        longjmp(t->jb, 2);
                                }

                                t->state = TRY_CATCH;

                                longjmp(t->jb, 1);
                                ////////////////////////////////////////////////

                        case TRY_CATCH:
                                DropPendingThrow(ty);
                                t->state = TRY_THROW;
                                t->end = NULL;
                                IP = t->finally;
                                return;

                        case TRY_THROW:
                                vXx(TRY_STACK);
                                DropPendingThrow(ty);
                                continue;
                        }
                }
                if (IsCloseSignal(&ty->exc)) {
                        co_finish_close(ty);
                }
                if (UNLIKELY(!co_abort(ty))) {
                        UNREACHABLE("DoThrow(): no handler at top level");
                }
        }
}

TY_INSTR_INLINE static void
RaiseException(Ty *ty)
{
        ThrowCtx *ctx = PushThrowCtx(ty);
        Value exc = pop();
        if (
                (vN(THROW_STACK) > 1)
             && (exc.type == VALUE_OBJECT)
             && class_is_subclass(ty, exc.class, CLASS_RUNTIME_ERROR)
        ) {
                ThrowCtx *prev = vvL(THROW_STACK)[-1];
                PutMember(exc, NAMES._cause, prev->exc);
        }
        ctx->exc = exc;
        if (UNLIKELY(VmPoll.debug | DebugJitOff)) {
                DebugOnThrow(ty);
        }
        DoThrow(ty);
}

__attribute__((noinline, cold))
void
vm_interrupt(Ty *ty)
{
        Generator *gen = vv(STACK)->gen;

        if (gen != InterruptedGenerator) {
                return;
        }

        InterruptedGenerator = NULL;

        if (gen->closing) {
                vm_throw(ty, &GENERATOR(gen));
        }

        Value exc = pop();
        vm_throw(ty, &exc);
}

static void
DiscardGenerator(Ty *ty, Generator *gen)
{
        co_state *st = gen->st;
        gen->st = NULL;

        while (vN(st->to_drop) > 0) {
                Array *group = vvL(st->to_drop)->array;
                while (vN(*group) > 0) {
                        Value v = vXx(*group);
                        gP(&v);
                        xdrop(ty, &v);
                        gX();
                }
                vXx(st->to_drop);
        }

        xvP(ty->co_states, st);
}

void
vm_close_generator(Ty *ty, Generator *gen)
{
        if (gen->st == NULL || gen->closing) {
                return;
        }

        if (UNLIKELY(!GeneratorIsSuspended(gen))) {
                zP("attempt to close an active generator");
        }

        if (gen->ip != code_of(&gen->f) && gen->co != NULL) {
                Value v = GENERATOR(gen);
                gen->closing     = true;
                InterruptedGenerator = gen;
                gP(&v);
                call_co(ty, &v, 0);
                pop();
                gX();
                if (UNLIKELY(gen->st != NULL)) {
                        if (
                                (vN(THROW_STACK) > 0)
                             && IsCloseSignal(&CurrentThrowCtx(ty)->exc)
                        ) {
                                PopThrowCtx(ty);
                        }
                        DiscardGenerator(ty, gen);
                        zP("generator yielded while being closed");
                }
                return;
        }

        DiscardGenerator(ty, gen);
}

Value
vm_raise_generator(Ty *ty, Generator *gen, Value const *exc)
{
        Value e = *exc;
        Value v = GENERATOR(gen);

        if (UNLIKELY(gen->closing)) {
                zP("attempt to raise into a closing generator");
        }

        if (gen->st == NULL) {
                vm_throw(ty, &e);
        }

        if (UNLIKELY(!GeneratorIsSuspended(gen))) {
                zP("attempt to raise into an active generator");
        }

        gP(&e);
        gP(&v);

        if (gen->ip == code_of(&gen->f) || gen->co == NULL) {
                DiscardGenerator(ty, gen);
                vm_throw(ty, &e);
        }

        push(e);
        InterruptedGenerator = gen;
        call_co(ty, &v, 1);

        gX();
        gX();

        return pop();
}

static void
YieldFix(Ty *ty)
{
        if (TryUnwrap(top(), TAG_SOME)) {
                return;
        }

        if (UNLIKELY((top()->type != VALUE_TAG) || (top()->tag != TAG_NONE))) {
                zP(
                        "iterator returned invalid type. "
                        "Expected None or Some(...) but got %s",
                        VSC(top())
                );
        }

        *top() = NONE;
}

inline static bool
WrapIndex(imax *i, isize n)
{
        if (*i < 0) {
                *i += n;
        }

        return (*i >= 0) && (*i < n);
}

inline static bool
ArrayPick(Ty *ty, Array const *a, imax i, IndexMode mode, Value *out)
{
        if (!WrapIndex(&i, vN(*a))) {
                *out = (mode == INDEX_OPTIONAL) ? None : NIL;
                return (mode != INDEX_STRICT);
        }

        *out = (mode == INDEX_OPTIONAL) ? Some(v__(*a, i)) : v__(*a, i);

        return true;
}

Value
ArraySubscript(Ty *ty, Value container, Value subscript, IndexMode mode)
{
        char *ip;
        Value *vp;
        Array *a;
        Value err;
        Value x;

Start:
        switch (EXPECT(subscript.type, VALUE_INTEGER)) {
        case VALUE_GENERATOR:
                gP(&subscript);
                gP(&container);
                a = vA();
                NOGC(a);
                ip = IP;
                for (;;) {
                        call_co(ty, &subscript, 0);
                        YieldFix(ty);
                        Value r = pop();
                        if (r.type == VALUE_NONE) {
                                break;
                        }
                        if (UNLIKELY(r.type != VALUE_INTEGER)) {
                                zP(
                                        "iterator yielded non-integer array index"
                                        " in subscript expression: %s",
                                        VSC(&r)
                                );
                        }
                        if (!ArrayPick(ty, container.array, r.z, mode, &x)) {
                                goto Error;
                        }
                        vAp(a, x);
                }

                OKGC(a);
                gX();
                gX();

                IP = ip;
                return ARRAY(a);

        case VALUE_OBJECT:
                gP(&subscript);
                gP(&container);

                vp = class_lookup_method_i(ty, subscript.class, NAMES._next_);

                if (UNLIKELY(vp == NULL)) {
                        vp = class_lookup_method_i(ty, subscript.class, NAMES._iter_);
                        if (UNLIKELY(vp == NULL)) {
                                zP("non-iterable object used in subscript expression");
                        }
                        exec_fn(ty, vp, &subscript, 0, NULL);
                        subscript = pop();
                        gX();
                        gX();
                        goto Start;
                }

                a = vA();
                NOGC(a);

                for (int i = 0; ; ++i) {
                        push(INTEGER(i));
                        exec_fn(ty, vp, &subscript, 1, NULL);
                        YieldFix(ty);
                        Value r = pop();
                        if (r.type == VALUE_NONE) {
                                break;
                        }
                        if (UNLIKELY(r.type != VALUE_INTEGER)) {
                                zP(
                                        "iterator yielded non-integer array index"
                                        " in subscript expression: %s",
                                        VSC(&r)
                                );
                        }
                        if (!ArrayPick(ty, container.array, r.z, mode, &x)) {
                                goto Error;
                        }
                        vAp(a, x);
                }

                OKGC(a);
                gX();
                gX();
                return ARRAY(a);

        case VALUE_INTEGER:
                if (!ArrayPick(ty, container.array, subscript.z, mode, &x)) {
                        goto Error;
                }
                return x;

        default:
                zP(
                        "non-integer array index used in subscript expression: %s",
                        VSC(&subscript)
                );
        }

Error:
        err = TAGGED(TAG_INDEX_ERR, container, subscript);
        vm_throw(ty, &err);
}

TY_INSTR_INLINE static void
AddTupleEntry(
        Ty *ty,
        i32Vector *ids,
        ValueVector *values,
        int id,
        Value const *v
)
{
        for (int i = 0; i < ids->count; ++i) {
                if (ids->items[i] == id) {
                        values->items[i] = *v;
                        return;
                }
        }

        svP(*ids, id);
        svP(*values, *v);
}

inline static bool
search_i32(i32 const *zs, i32 z)
{
        while (*zs != -1) {
                if (*zs++ == z) return true;
        }

        return false;
}

TY_INSTR_INLINE static void
DoTag(Ty *ty, int tag, int n, Value *kws)
{
        if (
                (n == 1)
             && ((kws == NULL) || IsNil(*kws))
        ) {
                top()->tags = tags_push(ty, top()->tags, tag);
                top()->type |= VALUE_TAGGED;
        } else {
                GC_STOP();
                Value v = builtin_tuple(ty, n, kws);
                STACK.count -= n;
                v.type |= VALUE_TAGGED;
                v.tags = tags_push(ty, v.tags, tag);
                push(v);
                GC_RESUME();
        }
}


Value
BuildKwargsDict(Ty *ty, char **ip, int nkw)
{
        if (nkw == 0) {
                return NIL;
        }

        if (nkw == 1) {
                Value v = *top();
                if (
                        IsNone(v)
                     || (
                                (**ip == '*')
                             && (
                                        ((v.type == VALUE_DICT ) && (v.dict->count == 0))
                                     || ((v.type == VALUE_TUPLE) && (v.count       == 0))
                                )
                        )
                ) {
                        *ip += strlen(*ip) + 1;
                        pop();
                        return NIL;
                }
        }

        GC_STOP();
        Dict *kwargs = dict_new(ty);
        for (int i = 0; i < nkw; ++i, *ip += strlen(*ip) + 1) {
                Value v = vZ(STACK)[-(nkw - i)];
                if (IsNone(v)) {
                        continue;
                }
                if (**ip == '*') {
                        if (v.type == VALUE_DICT) {
                                dfor(v.dict, {
                                        if (UNLIKELY(key->type != VALUE_STRING)) {
                                                zP(
                                                        "splatted Dict argument contains non-string key: %s%s%s%s%s",
                                                        TERM(34),
                                                        TERM(1),
                                                        VSC(&v),
                                                        TERM(22),
                                                        TERM(39)
                                                );
                                        }
                                        dict_put_value(ty, kwargs, *key, *val);
                                });
                        } else if (
                                LIKELY(
                                        (v.type == VALUE_TUPLE)
                                     && (v.count == 0 || v.ids != NULL)
                                )
                        ) {
                                for (int i = 0; i < v.count; ++i) {
                                        if (v.ids[i] != -1) {
                                                dict_put_member(
                                                        ty,
                                                        kwargs,
                                                        intern_entry(&xD.members, v.ids[i])->name,
                                                        v.items[i]
                                                );
                                        }
                                }
                        } else {
                                zP(
                                        "attempt to splat invalid value in function call: %s%s%s%s%s",
                                        TERM(34),
                                        TERM(1),
                                        VSC(top()),
                                        TERM(22),
                                        TERM(39)
                                );
                        }
                } else {
                        dict_put_member(ty, kwargs, *ip, v);
                }
        }
        vN(STACK) -= nkw;
        GC_RESUME();

        return DICT(kwargs);
}

inline static bool
InertInit(Value const *init, int argc, Value const *kwargs)
{
        return (argc == 0)
            && ((kwargs == NULL) || IsNil(*kwargs))
            && (init->type == VALUE_FUNCTION)
            && expr_of(init)->fn->inert;
}

static Value
jfun_call(Ty *ty, Value const *f, int argc, Value *kwargs)
{
        Value fn = *f;
        Value out = ZERO;
        if (kwargs != NULL && kwargs->type == VALUE_DICT && kwargs->dict->count != 0) {
                zP("jit: keyword arguments are not supported");
        }
        if (fn.jit_entry == NULL) {
                zP("jit: function has no entry thunk");
        }
        gP(&fn);
        fn.jit_entry(ty, &out, ty->stack.items + ty->stack.count - argc, argc);
        gX();
        return out;
}

bool
DoCallEx(Ty *ty, Value const *f, int n, Value const *_kwargs, bool exec)
{
        Value v = *f;
        Value *vp;
        Value value;
        Value subscript;
        Value a, b;
        imax k;

        bool new_frame = false;

        /* TODO: optimize more tail calls */
#if 0
        if (tco) {
                vvX(FRAMES);
                IP = *vvX(CALLS);
                tco = false;
        }
#endif

        Value kwargs = *_kwargs;

        switch (v.type) {
        case VALUE_FUNCTION:
        case VALUE_BOUND_FUNCTION:
                if (exec) {
                        exec_fn(ty, &v, NULL, n, &kwargs);
                        new_frame = false;
                } else {
                        new_frame = call(ty, &v, NULL, n, &kwargs);
                }
                return new_frame;

        case VALUE_BUILTIN_FUNCTION:
                /*
                 * Builtin functions may not preserve the stack size, so instead
                 * of subtracting `n` after calling the builtin function, we compute
                 * the desired final stack size in advance.
                 *
                 * XXX: ??
                 */
                gP(&kwargs);
                k = vN(STACK) - n;
                v = (*v.builtin_function)(ty, n, &kwargs);
                gX();
                STACK.count = k;
                push(v);
                CheckPendingSignals(ty);
                return false;

        case VALUE_FOREIGN_FUNCTION:
                k = vN(STACK) - n;
                v = cffi_fast_call(ty, &v, n, NULL);
                STACK.count = k;
                push(v);
                CheckPendingSignals(ty);
                return false;

        case VALUE_JIT_FUNCTION:
                k = vN(STACK) - n;
                v = jfun_call(ty, &v, n, &kwargs);
                STACK.count = k;
                push(v);
                CheckPendingSignals(ty);
                return false;

        case VALUE_GENERATOR:
                call_co(ty, &v, n);
                return false;

        case VALUE_OPERATOR:
                switch (n) {
                case 1:
                        DoUnaryOp(ty, v.uop, exec);
                        return !exec;

                case 2:
                        b = pop();
                        a = pop();
                        xpush(vm_2op(ty, v.bop, &a, &b));
                        return false;

                default:
                        push(TAG(TAG_DISPATCH_ERR));
                        RaiseException(ty);
                }
                break;

        case VALUE_TAG:
                gP(&kwargs);
                DoTag(ty, v.tag, n, &kwargs);
                gX();
                return false;

        case VALUE_OBJECT:
                vp = class_lookup_method_i(ty, v.class, NAMES.call);
                if (vp == NULL) {
                        goto NotCallable;
                }
                if (exec) {
                        exec_fn(ty, vp, &v, n, &kwargs);
                        return false;
                } else {
                        new_frame = call(ty, vp, &v, n, &kwargs);
                        return new_frame;
                }

        case VALUE_CLASS:
                gP(&kwargs);
                if (v.class <= CLASS_PRIMITIVE) {
                        k = vN(STACK) - n;
                        value = ConstructPrimitive(ty, v.class, n, &kwargs);
                        vN(STACK) = k;
                        xpush(value);
                        gX();
                        return false;
                }
                vp = class_ctor(ty, v.class);
                value = RawObject(v.class);
                if (UNLIKELY(IsZero(*vp)) || InertInit(vp, n, &kwargs)) {
                        vN(STACK) -= n;
                        push(value);
                        gX();
                        return false;
                }
                if (exec) {
                        gP(&value);
                        exec_fn(ty, vp, &value, n, &kwargs);
                        gX();
                        put(value);
                        gX();
                        return false;
                } else {
                        usize i = vN(STACK) - n;
                        xvI(STACK, value, i);
                        call6t(ty, vp, &value, n, &kwargs, pop_ret);
                        gX();
                        return true;
                }
                UNREACHABLE();

        case VALUE_METHOD:
                if (v.name == NAMES.method_missing) {
                        push(NIL);
                        memmove(top() - (n - 1), top() - n, n * sizeof (Value));
                        top()[-n++] = v.this[1];
                }
                if (exec) {
                        exec_fn(ty, v.method, v.this, n, &kwargs);
                        return false;
                } else {
                        new_frame = call(ty, v.method, v.this, n, &kwargs);
                        return new_frame;
                }

        case VALUE_REGEX:
                if (UNLIKELY(n != 1)) {
                        zP("Regex.__call__(): too many arguments (%d given, 1 expected)", n);
                }
                value = peek();
                if (UNLIKELY(value.type != VALUE_STRING)) {
                        zP("Regex.__call__(): expected String but got: %s", VSC(&value));
                }
                push(v);
                v = string_match(ty, &value, 1, NULL);
                pop();
                put(v);
                return false;

        case VALUE_BUILTIN_METHOD:
                gP(&kwargs);
                v = v.builtin_method(ty, v.this, n, &kwargs);
                gX();
                STACK.count -= n;
                push(v);
                return false;

        case VALUE_NIL:
                STACK.count -= n;
                push(NIL);
                return false;

        case VALUE_DICT:
                value = peek();
                push(v);
                vp = dict_get_value(ty, v.dict, &value);
                STACK.count -= (n + 1);
                if (vp == NULL) {
                        xpush(None);
                } else {
                        xpush(Some(*vp));
                }
                return false;

        case VALUE_SET:
                if (UNLIKELY(n != 1)) {
                        zP("Set.__call__(): expected 1 argument but got %d", n);
                }
                value = peek();
                push(v);
                value = BOOLEAN(set_has(ty, v.set, &value));
                STACK.count -= (n + 1);
                xpush(value);
                return false;

        case VALUE_ARRAY:
                subscript = peek();
                push(v);
                value = ArraySubscript(ty, v, subscript, INDEX_OPTIONAL);
                STACK.count -= (n + 1);
                xpush(value);
                return false;

        NotCallable:
        default:
                zP("attempt to call non-callable value %s", VSC(&v));
        }

        return false;
}

inline static bool
DoCall(Ty *ty, Value const *f, int n, int nkw, bool exec)
{
        if (n == -1) {
                n = vN(STACK) - vXx(SP_STACK) - nkw;
        }

        Value kwargs = BuildKwargsDict(ty, &IP, nkw);

        return DoCallEx(ty, f, n, &kwargs, exec);
}

inline static u16
FastReadOffset(Ty *ty, Value const *v, i32 id)
{
        if (v->type != VALUE_OBJECT) {
                return OFF_NOT_FOUND;
        }

        Class *class = class_get(ty, v->class);

        if (id >= vN(class->offsets_r)) {
                return OFF_NOT_FOUND;
        }

        return v__(class->offsets_r, id);
}

inline static u16
FastWriteOffset(Ty *ty, Value const *v, i32 id)
{
        if (v->type != VALUE_OBJECT) {
                return OFF_NOT_FOUND;
        }

        Class *class = class_get(ty, v->class);

        if (id >= vN(class->offsets_w)) {
                return OFF_NOT_FOUND;
        }

        return v__(class->offsets_w, id);
}

inline static bool
TargetFieldFast(Ty *ty, Value *v, i32 id)
{
        u16 off = FastWriteOffset(ty, v, id);
        if (off == OFF_NOT_FOUND) {
                return false;
        }

        u8 type = (off >> OFF_SHIFT);
        off &= OFF_MASK;

        Value *_set = NULL;
        Value *_get = NULL;

        switch (type) {
        case OFF_FIELD:
                pushtarget(&v->object->slots[off], v->object);
                return true;

        case OFF_SETTER: {
                Class *class = class_get(ty, v->class);
                _set = v_(class->setters.values, off);
                _get = class_lookup_getter_i(ty, v->class, id);
                if (_get == NULL) {
                        return false;
                }
                pushtarget(_get, NULL);
                pushtarget((Value *)(uptr)v->class, v->object);
                pushtarget((Value *)(((uptr)_set) | 2), NULL);
                return true;
        }

        case OFF_SETTER_X:
                _set = &v->object->slots[off];
                _get = class_lookup_getter_i(ty, v->class, id);
                if (_get == NULL) {
                        return false;
                }
                pushtarget(_get, NULL);
                pushtarget((Value *)(uptr)v->class, v->object);
                pushtarget((Value *)(((uptr)_set) | 2), NULL);
                return true;

        default:
                return false;
        }
}

inline static Value
LoadFieldFast(Ty *ty, i32 id)
{
        Value v = peek();

        u16 off = FastReadOffset(ty, &v, id);
        if (off == OFF_NOT_FOUND) {
                return NONE;
        }

        u8 type = (off >> OFF_SHIFT);
        off &= OFF_MASK;

        Value *vp;
        Value *this;

        switch (type) {
        case OFF_FIELD:
                pop();
                return v.object->slots[off];

        case OFF_GETTER:
                vp = v_(class_get(ty, v.class)->getters.values, off);
                pop();
                call(ty, vp, &v, 0, NULL);
                return BREAK;

        case OFF_GETTER_X:
                vp = &v.object->slots[off];
                pop();
                call(ty, vp, &v, 0, NULL);
                return BREAK;

        case OFF_METHOD:
                vp = v_(class_get(ty, v.class)->methods.values, off);
                this = uAo(sizeof *this, GC_VALUE);
                *this = v;
                pop();
                return METHOD(id, vp, this);

        default:
                return NONE;
        }
}

inline static bool
DispatchMethodFast(Ty *ty, Value self, i32 id, int argc, int nkw, bool exec)
{
        Value *v = &self;

        u16 off = FastReadOffset(ty, v, id);
        if (off == OFF_NOT_FOUND) {
                return false;
        }

        u8 type = (off >> OFF_SHIFT);
        off &= OFF_MASK;

        Value *vp;
        Value fn;
        Value kwargs;

        switch (type) {
        case OFF_FIELD:
                pop();
                DoCall(ty, &v->object->slots[off], argc, nkw, exec);
                break;

        case OFF_GETTER:
                vp = v_(class_get(ty, v->class)->getters.values, off);
                exec_fn(ty, vp, v, 0, NULL);
                fn = pop();
                pop();
                DoCall(ty, &fn, argc, nkw, exec);
                break;

        case OFF_GETTER_X:
                vp = &v->object->slots[off];
                exec_fn(ty, vp, v, 0, NULL);
                fn = pop();
                pop();
                DoCall(ty, &fn, argc, nkw, exec);
                break;

        case OFF_METHOD:
                vp = v_(class_get(ty, v->class)->methods.values, off);
                pop();
                kwargs = BuildKwargsDict(ty, &IP, nkw);
                if (exec) {
                        exec_fn(ty, vp, v, argc, &kwargs);
                } else {
                        call(ty, vp, v, argc, &kwargs);
                }
                break;

        case OFF_METHOD_X:
                vp = &v->object->slots[off];
                pop();
                kwargs = BuildKwargsDict(ty, &IP, nkw);
                if (exec) {
                        exec_fn(ty, vp, v, argc, &kwargs);
                } else {
                        call(ty, vp, v, argc, &kwargs);
                }
                break;

        default:
                UNREACHABLE();
        }

        return true;
}

Value
GetMember(Ty *ty, int member, bool try_missing, bool exec)
{
        int n;
        Value *this;
        Value *vp = NULL;
        Value meta;
        BuiltinMethod *func;

        Value v = peek();

        if (v.type & VALUE_TAGGED) {
                Class *class = tags_get_class(ty, tags_first(ty, v.tags));
                if (class != NULL) {
                        vp = class_lookup_getter_i(ty, class->i, member);
                        if (vp != NULL) {
                                v = unwrap(ty, &v);
                                goto Getter;
                        }
                }
                vp = tags_lookup_method_i(ty, tags_first(ty, v.tags), member);
                if (vp != NULL)  {
                        Value *this = mAo(sizeof *this, GC_VALUE);
                        *this = unwrap(ty, &v);
                        pop();
                        return METHOD(member, vp, this);
                }
                n = CLASS_OBJECT;
                goto ClassLookup;
        }

        switch (v.type & ~VALUE_TAGGED) {
        case VALUE_TUPLE:
                vp = tuple_get_i(&v, member);
                if (vp == NULL) {
                        n = CLASS_TUPLE;
                        goto ClassLookup;
                }
                pop();
                return *vp;

        case VALUE_DICT:
                func = get_dict_method_i(member);
                if (func == NULL) {
                        n = CLASS_DICT;
                        goto ClassLookup;
                }
                goto BuiltinMember;

        case VALUE_SET:
                func = get_set_method_i(member);
                if (func == NULL) {
                        n = CLASS_SET;
                        goto ClassLookup;
                }
                goto BuiltinMember;

        case VALUE_ARRAY:
                func = get_array_method_i(member);
                if (func == NULL) {
                        n = CLASS_ARRAY;
                        goto ClassLookup;
                }
                goto BuiltinMember;

        case VALUE_HEAP:
                func = get_heap_method_i(member);
                if (func == NULL && (func = get_heap_view_method_i(member)) != NULL) {
                        this = mAo(sizeof *this, GC_VALUE);
                        *this = HEAP_VIEW(v.heap);
                        pop();
                        return BUILTIN_METHOD(member, func, this);
                }
                if (func == NULL) {
                        n = CLASS_HEAP;
                        goto ClassLookup;
                }
                goto BuiltinMember;

        case VALUE_STRING:
                func = get_string_method_i(member);
                if (func == NULL) {
                        n = CLASS_STRING;
                        goto ClassLookup;
                }
                goto BuiltinMember;

        case VALUE_BLOB:
                func = get_blob_method_i(member);
                if (func == NULL) {
                        n = CLASS_BLOB;
                        goto ClassLookup;
                }
                goto BuiltinMember;

        case VALUE_QUEUE:
                func = get_queue_method_i(member);
                if (func == NULL) {
                        n = CLASS_QUEUE;
                        goto ClassLookup;
                }
                goto BuiltinMember;

        case VALUE_SHARED_QUEUE:
                func = get_shared_queue_method_i(member);
                if (func == NULL) {
                        n = ClassOf(&v);
                        goto ClassLookup;
                }
                goto BuiltinMember;

BuiltinMember:
                v.type &= ~VALUE_TAGGED;
                v.tags = 0;
                if (class_lookup_getter_i(ty, ClassOf(&v), member) != NULL) {
                        v = func(ty, &v, 0, NULL);
                        pop();
                        return v;
                }
                this = mAo(sizeof *this, GC_VALUE);
                *this = v;
                pop();
                return BUILTIN_METHOD(member, func, this);

        case VALUE_GENERATOR:
                n = CLASS_GENERATOR;
                goto ClassLookup;

        case VALUE_INTEGER:
                n = CLASS_INT;
                goto ClassLookup;

        case VALUE_REAL:
                n = CLASS_FLOAT;
                goto ClassLookup;

        case VALUE_BOOLEAN:
                n = CLASS_BOOL;
                goto ClassLookup;

        case VALUE_REGEX:
                if (member == NAMES.source) {
                        Value result = vSsz(v.regex->pattern);
                        pop();
                        return result;
                }
                n = CLASS_REGEX;
                goto ClassLookup;

        case VALUE_PTR:
                n = CLASS_PTR;
                goto ClassLookup;

        case VALUE_MODULE:
                n = CLASS_MODULE;
                goto ClassLookup;

        case VALUE_METHOD:
                if (member == NAMES._class_) {
                        pop();
                        return (class_of(v.method) != -1) ? CLASS(class_of(v.method)) : NIL;
                } else if (member == NAMES._name_) {
                        pop();
                        return xSz(name_of(v.method));
                } else if (member == NAMES._fqn_) {
                        Value result = vSsz(fqn_of(v.method));
                        pop();
                        return result;
                } else if (member == NAMES._def_) {
                        Value result = FunDef(ty, v.method);
                        pop();
                        return result;
                } else if (member == NAMES._src_) {
                        Value result = PrettySource(ty, &v);
                        pop();
                        return result;
                }
                n = CLASS_FUNCTION;
                goto ClassLookup;

        case VALUE_FUNCTION:
        case VALUE_BOUND_FUNCTION:
                if (member == NAMES._class_) {
                        pop();
                        return (class_of(&v) != -1) ? CLASS(class_of(&v)) : NIL;
                } else if (member == NAMES._name_) {
                        pop();
                        return xSz(name_of(&v));
                } else if (member == NAMES._fqn_) {
                        Value result = vSsz(fqn_of(&v));
                        pop();
                        return result;
                } else if (member == NAMES._def_) {
                        Value result = FunDef(ty, &v);
                        pop();
                        return result;
                } else if (member == NAMES._src_) {
                        Value result = PrettySource(ty, &v);
                        pop();
                        return result;
                } else if (has_meta(&v)) {
                        push(*meta_of(ty, &v));
                        meta = GetMember(ty, member, false, exec);
                        if (!IsNone(meta)) {
                                pop();
                                return meta;
                        }
                }
                n = CLASS_FUNCTION;
                goto ClassLookup;

        case VALUE_JIT_FUNCTION:
        case VALUE_FOREIGN_FUNCTION:
                if (member == NAMES._class_) {
                        pop();
                        return NIL;
                } else if (member == NAMES._name_ || member == NAMES._fqn_) {
                        pop();
                        return xSz(name_of(&v));
                } else if (member == NAMES._def_) {
                        pop();
                        return NIL;
                }
                n = v.type == VALUE_JIT_FUNCTION && v.xinfo != NULL && v.xinfo->class > 0
                  ? v.xinfo->class : CLASS_FUNCTION;
                goto ClassLookup;

        case VALUE_BUILTIN_METHOD:
                if (member == NAMES._class_) {
                        pop();
                        return CLASS(ClassOf(v.this));
                } else if (member == NAMES._name_) {
                        pop();
                        return xSz(M_NAME(v.name));
                } else if (member == NAMES._fqn_) {
                        pop();
                        return STRING_FORMAT(
                                ty,
                                "%s.%s.%s",
                                class_get(ty, ClassOf(v.this))->def->mod->name,
                                class_name(ty, ClassOf(v.this)),
                                M_NAME(v.name)
                        );
                } else if (member == NAMES._src_) {
                        char const *file;
                        int line;
                        char const *src = vm_builtin_method_source(
                                ClassOf(v.this),
                                M_NAME(v.name),
                                &file,
                                &line
                        );
                        pop();
                        return (src != NULL) ? vSsz(src) : NIL;
                } else if (member == NAMES._def_) {
                        pop();
                        return NIL;
                }
                n = CLASS_FUNCTION;;
                goto ClassLookup;

        case VALUE_BUILTIN_FUNCTION:
                if (member == NAMES._class_) {
                        pop();
                        return NIL;
                } else if (member == NAMES._name_ || member == NAMES._fqn_) {
                        pop();
                        return xSz(M_NAME(v.name));
                } else if (member == NAMES._def_) {
                        pop();
                        return NIL;
                } else if (member == NAMES._src_) {
                        pop();
                        return PrettySource(ty, &v);
                }
                n = CLASS_FUNCTION;
                goto ClassLookup;

        case VALUE_OPERATOR:
                if (member == NAMES._class_) {
                        pop();
                        return NIL;
                } else if (member == NAMES._name_ || member == NAMES._fqn_) {
                        pop();
                        return xSz(intern_entry(&xD.b_ops, v.bop)->name);
                } else if (member == NAMES._def_) {
                        pop();
                        return NIL;
                }
                n = CLASS_FUNCTION;
                goto ClassLookup;

        case VALUE_CLASS:
                switch (v.class) {
                case CLASS_ARRAY:
                        if ((func = get_array_method_i(member)) != NULL) {
                                pop();
                                return PTR((void *)func);
                        }
                        break;

                case CLASS_STRING:
                        if ((func = get_string_method_i(member)) != NULL) {
                                pop();
                                return PTR((void *)func);
                        }
                        break;

                case CLASS_DICT:
                        if ((func = get_dict_method_i(member)) != NULL) {
                                pop();
                                return PTR((void *)func);
                        }
                        break;

                case CLASS_SET:
                        if ((func = get_set_method_i(member)) != NULL) {
                                pop();
                                return PTR((void *)func);
                        }
                        break;

                case CLASS_BLOB:
                        if ((func = get_blob_method_i(member)) != NULL) {
                                pop();
                                return PTR((void *)func);
                        }
                        break;
                }
                if ((vp = class_lookup_s_getter_i(ty, v.class, member)) != NULL) {
                        goto Getter;
                }
                if ((vp = class_lookup_field(ty, v.class, member)) != NULL) {
                        pop();
                        return *vp;
                }
                if ((vp = class_lookup_s_method_i(ty, v.class, member)) != NULL) {
                        goto BoundMethod;
                }
                if ((vp = class_lookup_method_i(ty, v.class, member)) != NULL) {
                        pop();
                        return *vp;
                }
                if (member == NAMES._name_) {
                        pop();
                        return xSz(class_name(ty, v.class));
                }
                if (member == NAMES._fqn_) {
                        pop();
                        Class *class = class_get(ty, v.class);
                        return STRING_FORMAT(
                                ty,
                                "%s.%s",
                                ClassModName(class),
                                class->name
                        );
                }
                if (member == NAMES._super_) {
                        Class *super = class_get(ty, v.class)->super;
                        pop();
                        return (super != NULL) ? CLASS(super->i) : NIL;
                }
                if (member == NAMES._fields_) {
                        pop();
                        return itable_dict(ty, &class_get(ty, v.class)->fields);
                }
                if (member == NAMES._methods_) {
                        pop();
                        return itable_dict(ty, &class_get(ty, v.class)->methods);
                }
                if (member == NAMES._getters_) {
                        pop();
                        return itable_dict(ty, &class_get(ty, v.class)->getters);
                }
                if (member == NAMES._setters_) {
                        pop();
                        return itable_dict(ty, &class_get(ty, v.class)->setters);
                }
                if (member == NAMES._static_fields_) {
                        pop();
                        return itable_dict(ty, &class_get(ty, v.class)->s_fields);
                }
                if (member == NAMES._static_methods_) {
                        pop();
                        return itable_dict(ty, &class_get(ty, v.class)->s_methods);
                }
                if (member == NAMES._static_getters_) {
                        pop();
                        return itable_dict(ty, &class_get(ty, v.class)->s_getters);
                }
                if (member == NAMES._id_) {
                        pop();
                        return INTEGER(v.class);
                }
                if (member == NAMES._def_) {
                        pop();
                        return ClassDef(ty, &v);
                }
                if (member == NAMES._src_) {
                        pop();
                        return PrettySource(ty, &v);
                }
                n = CLASS_CLASS;
                goto ClassLookup;

        case VALUE_OBJECT:
                vp = ObjectMember(v, member);
                if (vp != NULL) {
                        pop();
                        return *vp;
                }
                n = v.class;
ClassLookup:
                vp = class_lookup_getter_i(ty, n, member);
                if (vp != NULL) {
                        goto Getter;
                }
                vp = class_lookup_method_i(ty, n, member);
                if (vp != NULL) {
BoundMethod:
                        this = mAo(sizeof *this, GC_VALUE);
                        *this = v;
                        pop();
                        return METHOD(member, vp, this);
                }
                if (!try_missing) {
                        break;
                }
                if ((vp = class_lookup_method_i(ty, n, NAMES.missing)) != NULL) {
                        if (exec) {
                                push(xSz(M_NAME(member)));
                                exec_fn(ty, vp, &v, 1, NULL);
                                v = pop();
                                pop();
                                return v;
                        } else {
                                put(xSz(M_NAME(member)));
                                call(ty, vp, &v, 1, NULL);
                                return BREAK;
                        }
                }
                if ((vp = class_lookup_method_i(ty, n, NAMES.method_missing)) != NULL) {
                        this = mAo(sizeof (Value [3]), GC_VALUE);
                        this[0] = v;
                        this[1] = xSz(M_NAME(member));
                        pop();
                        return METHOD(NAMES.method_missing, vp, this);
                }
                if (v.type != VALUE_CLASS) {
                        break;
                }
                if ((vp = class_lookup_s_method_i(ty, v.class, NAMES.missing)) != NULL) {
                        if (exec) {
                                push(xSz(M_NAME(member)));
                                exec_fn(ty, vp, &CLASS(v.class), 1, NULL);
                                v = pop();
                                pop();
                                return v;
                        } else {
                                put(xSz(M_NAME(member)));
                                call(ty, vp, &CLASS(v.class), 1, NULL);
                                return BREAK;
                        }
                }
                if ((vp = class_lookup_s_method_i(ty, v.class, NAMES.method_missing)) != NULL) {
                        this = mAo(sizeof (Value [3]), GC_VALUE);
                        this[0] = v;
                        this[1] = xSz(M_NAME(member));
                        pop();
                        return METHOD(NAMES.method_missing, vp, this);
                }
                break;

        case VALUE_TAG:
        {
                Class *class = tags_get_class(ty, v.tag);
                if (class != NULL) {
                        vp = class_lookup_s_getter_i(ty, class->i, member);
                        if (vp != NULL) {
                                goto Getter;
                        }
                }
                vp = tags_lookup_static(ty, v.tag, member);
                if (vp == NULL) {
                        vp = tags_lookup_method_i(ty, v.tag, member);
                }
                if (vp != NULL) {
                        pop();
                        return *vp;
                }
                if (member == NAMES._fqn_) {
                        pop();
                        Class *class = tags_get_class(ty, v.tag);
                        return STRING_FORMAT(
                                ty,
                                "%s.%s",
                                ClassModName(class),
                                class->name
                        );
                }
                break;
        }
        }

        pop();

        return NONE;

Getter:
        if (exec) {
                exec_fn(ty, vp, &v, 0, NULL);
                v = pop();
                pop();
                return v;
        }

        pop();
        call(ty, vp, &v, 0, NULL);
        return BREAK;
}

static int
GetDynamicMemberId(Ty *ty, bool strict)
{
        Value v = peek();

        switch (v.type) {
        case VALUE_STRING:
        {
                InternEntry *member = intern_get_n(&xD.members, ss(v), sN(v));
                if (member->id < 0) {
                        if (!strict) {
                                pop();
                                return -1;
                        } else {
                                int z = intern_put(member, NULL)->id;
                                pop();
                                return -(z + 1);
                        }
                } else {
                        pop();
                        return member->id;
                }
        }

        default:
                zP(
                        "dynamic member expression evaluated "
                        "to non-string value: %s",
                        VSC(&v)
                );
        }
}

static bool
responds_to(Ty *ty, Value const *v, int i)
{
        BuiltinMethod *func = NULL;

        switch (v->type) {
        case VALUE_ARRAY:   func = get_array_method_i(i);   break;
        case VALUE_STRING:  func = get_string_method_i(i);  break;
        case VALUE_DICT:    func = get_dict_method_i(i);    break;
        case VALUE_BLOB:    func = get_blob_method_i(i);    break;
        default:                                            break;
        }

        return (func != NULL)
            || (
                        (ClassOf(v) != CLASS_TOP)
                     && (class_lookup_method_i(ty, ClassOf(v), i) != NULL)
               );
}

static char const *
method_hint(Ty *ty, Value const *v, int i)
{
        char const *name = M_NAME(i);
        usize n = strlen(name);
        char const *alts[3];
        int nalts = 0;

        if (n > 1 && (name[n - 1] == '?' || name[n - 1] == '!')) {
                alts[nalts++] = afmt("%.*s", (int)(n - 1), name);
        } else {
                alts[nalts++] = afmt("%s?", name);
                alts[nalts++] = afmt("%s!", name);
        }

        for (int k = 0; k < nalts; ++k) {
                int alt = M_ID(alts[k]);
                if (responds_to(ty, v, alt)) {
                        return afmt("\n\n  hint: did you mean `%s`?", KebabName(ty, M_NAME(alt)));
                }
        }

        return "";
}

bool
CallMethod(Ty *ty, int i, int n, int nkw, bool maybe, bool exec)
{
        int class;
        Value v;
        Value value;
        Value attr;
        Value *self;
        Value *vp;
        BuiltinMethod *func;
        char const *method;

        if (i == -1) {
                i = GetDynamicMemberId(ty, !maybe);
                if (i == -1) {
                        goto QuietFailure;
                }
                if (i < 0) {
                        i = -(i + 1);
                }
        }

        if (UNLIKELY(n == -1)) {
                n = vN(STACK) - vXx(SP_STACK) - nkw - 1;
        }

        value = peek();
        self = &value;

        vp = NULL;
        func = NULL;

        if (value.type & VALUE_TAGGED) {
                vp = tags_lookup_method_i(ty, tags_first(ty, value.tags), i);
                if (vp != NULL) {
                        value = unwrap(ty, &value);
                        goto DoCall;
                }
                class = CLASS_OBJECT;
                goto ClassLookup;
        }

        switch (value.type) {
        case VALUE_TAG:
                vp = class_lookup_method_immediate_i(ty, CLASS_TAG, i);
                if (vp == NULL) {
                        vp = tags_lookup_static(ty, value.tag, i);
                }
                if (vp == NULL) {
                        vp = tags_lookup_method_i(ty, value.tag, i);
                }
                if (vp == NULL) {
                        vp = class_lookup_method_immediate_i(ty, CLASS_OBJECT, i);
                }
                break;

        case VALUE_STRING:
                func = get_string_method_i(i);
                if (func == NULL) {
                        class = CLASS_STRING;
                        goto ClassLookup;
                }
                break;

        case VALUE_DICT:
                func = get_dict_method_i(i);
                if (func == NULL) {
                        class = CLASS_DICT;
                        goto ClassLookup;
                }
                break;

        case VALUE_SET:
                func = get_set_method_i(i);
                if (func == NULL) {
                        class = CLASS_SET;
                        goto ClassLookup;
                }
                break;

        case VALUE_ARRAY:
                func = get_array_method_i(i);
                if (func == NULL) {
                        class = CLASS_ARRAY;
                        goto ClassLookup;
                }
                break;

        case VALUE_HEAP:
                func = get_heap_method_i(i);
                if (func == NULL && (func = get_heap_view_method_i(i)) != NULL) {
                        value = HEAP_VIEW(value.heap);
                }
                if (func == NULL) {
                        class = CLASS_HEAP;
                        goto ClassLookup;
                }
                break;

        case VALUE_BLOB:
                func = get_blob_method_i(i);
                if (func == NULL) {
                        class = CLASS_BLOB;
                        goto ClassLookup;
                }
                break;

        case VALUE_QUEUE:
                func = get_queue_method_i(i);
                if (func == NULL) {
                        class = CLASS_QUEUE;
                        goto ClassLookup;
                }
                break;

        case VALUE_SHARED_QUEUE:
                func = get_shared_queue_method_i(i);
                if (func == NULL) {
                        class = ClassOf(&value);
                        goto ClassLookup;
                }
                break;

        case VALUE_INTEGER:
                class = CLASS_INT;
                goto ClassLookup;

        case VALUE_REAL:
                class = CLASS_FLOAT;
                goto ClassLookup;

        case VALUE_BOOLEAN:
                class = CLASS_BOOL;
                goto ClassLookup;

        case VALUE_REGEX:
                class = CLASS_REGEX;
                goto ClassLookup;

        case VALUE_PTR:
                class = CLASS_PTR;
                goto ClassLookup;

        case VALUE_MODULE:
                class = CLASS_MODULE;
                goto ClassLookup;

        case VALUE_FUNCTION:
        case VALUE_BOUND_FUNCTION:
        case VALUE_BUILTIN_FUNCTION:
        case VALUE_FOREIGN_FUNCTION:
        case VALUE_JIT_FUNCTION:
        case VALUE_METHOD:
        case VALUE_BUILTIN_METHOD:
        case VALUE_OPERATOR:
                class = CLASS_FUNCTION;
                goto ClassLookup;

        case VALUE_GENERATOR:
                class = CLASS_GENERATOR;
                goto ClassLookup;

        case VALUE_TUPLE:
                vp = tuple_get(&value, intern_entry(&xD.members, i)->name);
                if (vp == NULL) {
                        class = CLASS_TUPLE;
                        goto ClassLookup;
                } else {
                        self = NULL;
                }
                break;

        case VALUE_CLASS:
                vp = class_lookup_s_method_i(ty, value.class, i);
                if (vp == NULL) {
                        vp = class_lookup_method_immediate_i(ty, CLASS_CLASS, i);
                }
                if (vp == NULL) {
                        vp = class_lookup_method_immediate_i(ty, CLASS_OBJECT, i);
                }
                break;

        case VALUE_OBJECT:
                if (DispatchMethodFast(ty, value, i, n, nkw, exec)) {
                        return !exec;
                }
                class = value.class;
                if (0) {
ClassLookup:
                        vp = class_lookup_method_i(ty, class, i);
                }
                if (vp == NULL) {
                        push(value);
                        attr = GetMember(ty, i, false, true);
                        vp = (attr.type == VALUE_NONE) ? NULL : &attr;
                        self = NULL;
                }
                break;

        case VALUE_NIL:
                if (!maybe) {
                        zP(
                                "call to method '%s' on nil (use x.?%s() to skip the call when x is nil)",
                                M_NAME(i),
                                M_NAME(i)
                        );
                }
                (void)BuildKwargsDict(ty, &IP, nkw);
                STACK.count -= (n + 1);
                push(NIL);
                return false;

        default:
                class = CLASS_OBJECT;
                goto ClassLookup;

        }

        if (func != NULL) {
                pop();
                gP(&value);
                attr = BuildKwargsDict(ty, &IP, nkw);
                gP(&attr);
                v = (*func)(ty, &value, n, &attr);
                gX();
                gX();
                STACK.count -= n;
                push(v);
                CO_LOG("CallMethod()", TERM(92), "called builtin method '%s' on %s", M_NAME(i), VSC(&value));
                return false;
        }

        if (
                (vp == NULL)
             && ((value.type == VALUE_OBJECT) || (value.type == VALUE_MODULE))
             && (vp = class_lookup_method_i(ty, ClassOf(&value), NAMES.method_missing)) != NULL
        ) {
                method = M_NAME(i);
                v = pop();
                push(NIL);
                memmove(top() - (n + nkw - 1), top() - (n + nkw), (n + nkw) * sizeof (Value));
                top()[-(n + nkw)] = STRING_NOGC(method, strlen(method));
                push(v);
                self = &value;
                n += 1;
        } else if (
                (vp == NULL)
             && (value.type == VALUE_OBJECT)
             && ((vp = class_lookup_method_i(ty, value.class, NAMES.missing)) != NULL)
        ) {
                // TODO: Shouldn't need to recurse here
                push(xSz(M_NAME(i)));
                exec_fn(ty, vp, &value, 1, NULL);
                v = pop();
                pop();
                return DoCall(ty, &v, n, nkw, exec);
        }

DoCall:
        if (vp != NULL) {
                pop();
                if (self != NULL) {
                        v = METHOD(i, vp, self);
                } else {
                        v = *vp;
                }
                return DoCall(ty, &v, n, nkw, exec);
        } else if (maybe) {
QuietFailure:
                STACK.count -= (n + 1 + nkw);
                xpush(NIL);
                return false;
        } else {
                char const *shown = VSC(&value);
                zP("call to non-existent method '%s' on %s%s", KebabName(ty, M_NAME(i)), shown, method_hint(ty, &value, i));
        }
}

static bool
DefaultStr(Ty *ty, int class)
{
        Value const *mine = class_lookup_method_i(ty, class, NAMES._str_);
        Value const *root = class_lookup_method_i(ty, CLASS_OBJECT, NAMES._str_);

        return (mine != NULL)
            && (root != NULL)
            && (mine->type == VALUE_FUNCTION)
            && (root->type == VALUE_FUNCTION)
            && (mine->info == root->info);
}

void
vm_to_string(Ty *ty, Value *v)
{
        switch (v->type) {
        case VALUE_STRING:
                return;

        case VALUE_NIL:
                *v = STRING_EMPTY;
                return;

        case VALUE_PTR:
                *v = value_vshow_color(ty, v, 0);
                return;

        case VALUE_INTEGER:
        case VALUE_REAL:
        case VALUE_BOOLEAN:
                if (DefaultStr(ty, ClassOf(v))) {
                        *v = value_vshow(ty, v, 0);
                        return;
                }
        }

        vm_push(ty, v);
        CallMethod(ty, NAMES._str_, 0, 0, false, true);
        *v = *vm_pop(ty);
}

void
vm_concat_strings(Ty *ty, int n)
{
        usize base = vN(STACK) - n;
        usize k = 0;

        for (usize i = base; i < base + n; ++i) {
                Value v = v__(STACK, i);
                vm_to_string(ty, &v);
                *v_(STACK, i) = v;
                k += sN(v);
        }

        char *str = value_string_alloc(ty, k);

        k = 0;
        for (usize i = base; i < base + n; ++i) {
                Value const *v = v_(STACK, i);
                if (sN(*v) > 0) {
                        memcpy(str + k, ss(*v), sN(*v));
                        k += sN(*v);
                }
        }

        vN(STACK) = base;
        xvP(STACK, STRING(str, k));
}

void
DoYieldNone(Ty *ty)
{
        co_retire(ty);
}

void
DoYield(Ty *ty)
{
        Generator *gen = GetCurrentGenerator(ty);

        if (UNLIKELY(gen == NULL)) {
                abort();
                zP("attempt to yield from outside of a generator context");
        }

        co_yield_value(ty);
}


// ===/ < > <= >= == != /=======================================================
#define DEFINE_RELATIONAL_OP(name, op, _op, _op_neg)                            \
void                                                                            \
name(Ty *ty)                                                                    \
{                                                                               \
        Value v;                                                                \
        int z;                                                                  \
                                                                                \
        switch (PACK_TYPES(top()[-1].type, top()[0].type)) {                    \
        case PAIR_OF(VALUE_INTEGER):                                            \
                v = BOOLEAN(top()[-1].z op top()[0].z);                         \
                break;                                                          \
        case PAIR_OF(VALUE_REAL):                                               \
                v = BOOLEAN(top()[-1].real op top()[0].real);                   \
                break;                                                          \
        case PACK_TYPES(VALUE_INTEGER, VALUE_REAL):                             \
                v = BOOLEAN(top()[-1].z op top()[0].real);                      \
                break;                                                          \
        case PACK_TYPES(VALUE_REAL, VALUE_INTEGER):                             \
                v = BOOLEAN(top()[-1].real op top()[0].z);                      \
                break;                                                          \
        case PAIR_OF(VALUE_SET):                                                \
                z = set_order(ty, top()[-1].set, top()[0].set);                 \
                v = BOOLEAN((z != SET_UNRELATED) && (z op 0));                  \
                break;                                                          \
        default:                                                                \
                v = vm_try_2op(ty, _op, top() - 1, top());                      \
                                                                                \
                if (v.type != VALUE_NONE) {                                     \
                        break;                                                  \
                }                                                               \
                                                                                \
                v = vm_try_2op(ty, _op_neg, top() - 1, top());                  \
                                                                                \
                if (v.type != VALUE_NONE) {                                     \
                        v = BOOLEAN(!v.boolean);                                \
                        break;                                                  \
                }                                                               \
                                                                                \
                v = BOOLEAN(value_compare(ty, top() - 1, top()) op 0);          \
                                                                                \
                break;                                                          \
        }                                                                       \
                                                                                \
        pop();                                                                  \
        pop();                                                                  \
        xpush(v);                                                               \
}

inline static void
DoEq(Ty *ty)
{
        Value b = pop();
        Value a = pop();

        xpush(BOOLEAN(v_eq(&a, &b)));
}

inline static void
DoNeq(Ty *ty)
{
        Value b = pop();
        Value a = pop();

        xpush(BOOLEAN(!v_eq(&a, &b)));
}

DEFINE_RELATIONAL_OP(DoGeq, >=, OP_GEQ, OP_LT )
DEFINE_RELATIONAL_OP(DoGt,  >,  OP_GT,  OP_LEQ)
DEFINE_RELATIONAL_OP(DoLeq, <=, OP_LEQ, OP_GT )
DEFINE_RELATIONAL_OP(DoLt,  <,  OP_LT,  OP_GEQ)

#undef DEFINE_RELATIONAL_OP
// =============================================================================

void
DoCmp(Ty *ty)
{
        int i = value_compare(ty, top() - 1, top());

        pop();
        pop();

        if (i < 0)
                xpush(INTEGER(-1));
        else if (i > 0)
                xpush(INTEGER(1));
        else
                xpush(INTEGER(0));
}

inline static void
DoNot(Ty *ty)
{
        put(BOOLEAN(!value_truthy(ty, top())));
}

TY_INSTR_INLINE static void
DoQuestion(Ty *ty, bool exec)
{
        if (top()->type == VALUE_NIL) {
                *top() = BOOLEAN(false);
        } else {
                CallMethod(ty, OP_QUESTION, 0, 0, false, exec);
        }
}

TY_INSTR_INLINE static void
DoNeg(Ty *ty, bool exec)
{
        Value v = peek();

        if (v.type == VALUE_INTEGER) {
                put(INTEGER(-v.z));
        } else if (v.type == VALUE_REAL) {
                put(REAL(-v.real));
        } else {
                CallMethod(ty, OP_NEG, 0, 0, false, exec);
        }
}

void
vm_jit_neg(Ty *ty)
{
        DoNeg(ty, true);
}

void
DoCount(Ty *ty, bool exec)
{
        Value v = pop();
        ffi_type *type;

        if (v.type & VALUE_TAGGED) {
                xpush(unwrap(ty, &v));
                return;
        }

        switch (v.type) {
        case VALUE_BLOB:         xpush(INTEGER(vN(*v.blob)));                        break;
        case VALUE_ARRAY:        xpush(INTEGER(vN(*v.array)));                       break;
        case VALUE_HEAP:         xpush(INTEGER(vN(v.heap->xs)));                     break;
        case VALUE_QUEUE:        xpush(INTEGER(queue_count(v.queue)));               break;
        case VALUE_SHARED_QUEUE: xpush(INTEGER(shared_queue_count(v.shared_queue))); break;
        case VALUE_DICT:         xpush(INTEGER(v.dict->count));                      break;
        case VALUE_SET:          xpush(INTEGER(v.set->count));                       break;
        case VALUE_TUPLE:        xpush(INTEGER(v.count));                            break;
        case VALUE_STRING:       xpush(INTEGER(TyStrLen(&v)));                       break;

        case VALUE_OBJECT:
        case VALUE_CLASS:
                xpush(v);
                CallMethod(ty, NAMES._len_, 0, 0, false, exec);
                break;

        case VALUE_PTR:
                type = (v.extra != NULL) ? v.extra : &ffi_type_uint8;
                xpush(INTEGER(type->size));
                break;

        default:
                zP("unary # applied to operand of invalid type: %s", VSC(&v));
        }
}

TY_INSTR_INLINE static void
DoUnaryOp(Ty *ty, int op, bool exec)
{
        int z;
        Value v;
        Value *vp;

        switch (op) {
        case OP_COUNT:    DoCount(ty, exec);    return;
        case OP_NEG:      DoNeg(ty, exec);      return;
        case OP_NOT:      DoNot(ty);            return;
        case OP_QUESTION: DoQuestion(ty, exec); return;
        }

        if (op == OP_COMPL && peek().type == VALUE_INTEGER) {
                put(INTEGER(~peek().z));
                return;
        }

        z = ClassOf(top());
        vp = class_lookup_method_i(ty, z, op);

        if (vp == NULL) {
                zP(
                        "no matching implementation of %s%s%s for %s",
                        TERM(95;1), intern_entry(&xD.members, op)->name, TERM(0),
                        VSC(top())
                );
        }

        v = pop();

        if (exec) {
                exec_fn(ty, vp, &v, 0, NULL);
        } else {
                call(ty, vp, &v, 0, NULL);
        }
}

void
DoBinaryOp(Ty *ty, int op, bool exec)
{
        switch (op) {
        case OP_IN:
                CallMethod(ty, M_ID("contains?"), 1, 0, false, exec);
                return;

        case OP_CMP: DoCmp(ty); return;
        case OP_EQL: DoEq(ty);  return;
        case OP_NEQ: DoNeq(ty); return;
        case OP_GEQ: DoGeq(ty); return;
        case OP_LEQ: DoLeq(ty); return;
        case OP_GT:  DoGt(ty);  return;
        case OP_LT:  DoLt(ty);  return;

        case OP_ADD:    if (op_builtin_add(ty))    return; break;
        case OP_SUB:    if (op_builtin_sub(ty))    return; break;
        case OP_MUL:    if (op_builtin_mul(ty))    return; break;
        case OP_DIV:    if (op_builtin_div(ty))    return; break;
        case OP_MOD:    if (op_builtin_mod(ty))    return; break;
        case OP_DIVMOD: if (op_builtin_divmod(ty)) return; break;

        case OP_BIT_AND: if (op_builtin_and(ty)) return; break;
        case OP_BIT_OR:  if (op_builtin_or(ty))  return; break;
        case OP_BIT_XOR: if (op_builtin_xor(ty)) return; break;
        case OP_BIT_SHL: if (op_builtin_shl(ty)) return; break;
        case OP_BIT_SHR: if (op_builtin_shr(ty)) return; break;
        }

        int i = op_dispatch(ty, op, ClassOf(top() - 1), ClassOf(top()));

        if (i == -1) {
                zP(
                        "no matching implementation of %s%s%s\n"
                        FMT_MORE "%s left%s: %s"
                        FMT_MORE "%sright%s: %s\n",
                        TERM(95;1), intern_entry(&xD.b_ops, op)->name, TERM(0),
                        TERM(95), TERM(0), VSC(top() - 1),
                        TERM(95), TERM(0), VSC(top())
                );
        }

        dont_printf(
                "matching implementation of %s%s%s: %d\n"
                FMT_MORE "%s left%s (%d): %s"
                FMT_MORE "%sright%s (%d): %s\n",
                TERM(95;1), intern_entry(&xD.b_ops, op)->name, TERM(0), i,
                TERM(95), TERM(0), ClassOf(top() - 1), VSC(top() - 1),
                TERM(95), TERM(0), ClassOf(top()),     VSC(top())
        );

        if (exec) {
                exec_fn(ty, &Globals.items[i], NULL, 2, NULL);
        } else {
                call(ty, &Globals.items[i], NULL, 2, NULL);
        }
}

inline static void
DoPtrMutOp(Ty *ty, int op)
{
        Value val;
        void *v;
        ffi_type *c_type;

        v = poptarget();
        c_type = (ffi_type *)poptarget();
        push(TPTR(c_type, v));
        val = builtin_ffi_load(ty, 1, NULL);
        put(val);
        val = vm_2op(ty, op, top(), top() - 1);
        pop();
        put(TPTR(c_type, v));
        xpush(val);
        val = builtin_ffi_store(ty, 2, NULL);
        pop();
        put(val);
}

static void
DoSetterMutOp(Ty *ty, uptr p, int op, bool exec)
{
        Value self;
        Value *get;
        Value *set;
        uptr c;
        i32 m;

        switch (pT(p)) {
        case 2:
                set  = (Value *)pP(p);
                c    = (uptr)poptarget();
                self = OBJECT(vZ(TARGETS)->gc, c);
                get  = poptarget();
                break;

        case 3:
                m    = (i32)(p >> 3);
                c    = (uptr)poptarget();
                self = OBJECT(vZ(TARGETS)->gc, c);
                get  = class_lookup_method_i(ty, c, NAMES.missing);
                set  = class_lookup_setter_i(ty, c, NAMES.missing);
                goto Missing;

        case 4:
                m    = (i32)(p >> 3);
                c    = (uptr)poptarget();
                self = CLASS(c);
                get  = class_lookup_s_method_i(ty, c, NAMES.missing);
                set  = class_lookup_s_setter_i(ty, c, NAMES.missing);
                goto Missing;

        case 6:
                set  = (Value *)pP(p);
                c    = (uptr)poptarget();
                self = CLASS(c);
                get  = poptarget();
                break;

        default:
                zP("bad target pointer :(");
        }

        exec_fn(ty, get, &self, 0, NULL);
        top()[-1] = vm_2op(ty, op, top(), top() - 1);
        pop();

        if (exec) {
                exec_fn(ty, set, &self, 1, NULL);
        } else {
                call(ty, set, &self, 1, NULL);
        }

        return;

Missing:
        xpush(xSz(M_NAME(m)));
        exec_fn(ty, get, &self, 1, NULL);
        top()[-1] = vm_2op(ty, op, top(), top() - 1);
        pop();
        push(xSz(M_NAME(m)));
        swap();

        if (exec) {
                exec_fn(ty, set, &self, 2, NULL);
        } else {
                call(ty, set, &self, 2, NULL);
        }
}

void
DoMutDiv(Ty *ty, bool exec)
{
        uptr p = (uptr)poptarget();
        Value *vp, *vp2, val, x;
        unsigned char b;

        vp = (Value *)pP(p);

        switch (pT(p)) {
        case 0:
                if (
                        (vp->type == VALUE_OBJECT)
                     && ((vp2 = class_method(ty, vp->class, "/=")) != NULL)
                ) {
                        gP(vp);
                        exec_fn(ty, vp2, vp, 1, NULL);
                        gX();
                        pop();
                } else {
                        x = pop();
                        val = vm_try_2op(ty, OP_MUT_DIV, vp, &x);
                        if (val.type != VALUE_NONE) {
                                vp = &val;
                        } else {
                                *vp = vm_2op(ty, OP_DIV, vp, &x);
                        }
                }
                xpush(*vp);
                break;

        case 1:
                if (UNLIKELY(top()->type != VALUE_INTEGER)) {
                        zP("attempt to divide byte by non-integer: %s", VSC(top()));
                }
                b = ((Blob *)vZ(TARGETS)->gc)->items[((uptr)vp) >> 3] /= pop().z;
                xpush(INTEGER(b));
                break;

        case 2:
        case 3:
        case 4:
        case 6:
                DoSetterMutOp(ty, p, OP_DIV, exec);
                break;

        case 5:
                DoPtrMutOp(ty, OP_DIV);
                break;

        default:
                zP("bad target pointer :(");
        }
}

void
DoMutMod(Ty *ty, bool exec)
{
        uptr p = (uptr)poptarget();
        Value *vp, val, x;
        unsigned char b;

        vp = (Value *)(p & ~PMASK3);

        switch (p & PMASK3) {
        case 0:
                switch (PACK_TYPES(vp->type, top()->type)) {
                case PAIR_OF(VALUE_INTEGER):
                        vp->z %= top()->z;
                        pop();
                        break;
                default:
                        x = pop();
                        val = vm_try_2op(ty, OP_MUT_MOD, vp, &x);
                        if (val.type != VALUE_NONE) {
                                vp = &val;
                        } else {
                                *vp = vm_2op(ty, OP_MOD, vp, &x);
                        }
                        break;
                }
                xpush(*vp);
                break;

        case 1:
                if (UNLIKELY(top()->type != VALUE_INTEGER)) {
                        zP("attempt to divide byte by non-integer: %s", VSC(top()));
                }
                b = ((struct blob *)TARGETS.items[TARGETS.count].gc)->items[((uptr)vp) >> 3] %= pop().z;
                xpush(INTEGER(b));
                break;

        case 2:
        case 3:
        case 4:
        case 6:
                DoSetterMutOp(ty, p, OP_MOD, exec);
                break;

        case 5:
                DoPtrMutOp(ty, OP_MOD);
                break;

        default:
                zP("bad target pointer :(");
        }
}

void
DoMutMul(Ty *ty, bool exec)
{
        uptr p = (uptr)poptarget();
        Value *vp, val, x;
        unsigned char b;

        vp = (Value *)(p & ~PMASK3);

        switch (p & PMASK3) {
        case 0:
                switch (PACK_TYPES(vp->type, top()->type)) {
                case PAIR_OF(VALUE_INTEGER):
                        vp->z *= top()->z;
                        pop();
                        break;
                case PAIR_OF(VALUE_REAL):
                        vp->real *= top()->real;
                        pop();
                        break;
                case PACK_TYPES(VALUE_INTEGER, VALUE_REAL):
                        vp->type = VALUE_REAL;
                        vp->real = vp->z;
                        vp->real *= top()->real;
                        pop();
                        break;
                case PACK_TYPES(VALUE_REAL, VALUE_INTEGER):
                        vp->real *= top()->z;
                        pop();
                        break;
                default:
                        x = pop();
                        val = vm_try_2op(ty, OP_MUT_MUL, vp, &x);
                        if (val.type != VALUE_NONE) {
                                vp = &val;
                        } else {
                                *vp = vm_2op(ty, OP_MUL, vp, &x);
                        }
                        break;
                }
                xpush(*vp);
                break;

        case 1:
                if (UNLIKELY(top()->type != VALUE_INTEGER)) {
                        zP("attempt to multiply byte by non-integer");
                }
                b = ((struct blob *)TARGETS.items[TARGETS.count].gc)->items[((uptr)vp) >> 3] *= pop().z;
                xpush(INTEGER(b));
                break;

        case 2:
        case 3:
        case 4:
        case 6:
                DoSetterMutOp(ty, p, OP_MUL, exec);
                break;

        case 5:
                DoPtrMutOp(ty, OP_MUL);
                break;

        default:
                zP("bad target pointer :(");
        }
}

void
DoMutSub(Ty *ty, bool exec)
{
        uptr p = (uptr)poptarget();
        Value *vp, x, val;
        unsigned char b;

        vp = (Value *)(p & ~PMASK3);

        switch (p & PMASK3) {
        case 0:
                switch (PACK_TYPES(vp->type, top()->type)) {
                case PAIR_OF(VALUE_INTEGER):
                        vp->z -= top()->z;
                        pop();
                        break;
                case PAIR_OF(VALUE_REAL):
                        vp->real -= top()->real;
                        pop();
                        break;
                case PACK_TYPES(VALUE_INTEGER, VALUE_REAL):
                        vp->type = VALUE_REAL;
                        vp->real = vp->z;
                        vp->real -= top()->real;
                        pop();
                        break;
                case PACK_TYPES(VALUE_REAL, VALUE_INTEGER):
                        vp->real -= top()->z;
                        pop();
                        break;
                case PAIR_OF(VALUE_DICT):
                        dict_subtract(ty, vp, 1, NULL);
                        pop();
                        break;
                case PAIR_OF(VALUE_SET):
                        SetDiscard(ty, vp->set, top()->set);
                        pop();
                        break;
                case PACK_TYPES(VALUE_DICT, VALUE_SET):
                        DictDropKeys(ty, vp->dict, top()->set);
                        pop();
                        break;
                default:
                        x = pop();
                        if ((val = vm_try_2op(ty, OP_MUT_SUB, vp, &x)).type != VALUE_NONE) {
                                vp = &val;
                        } else {
                                *vp = vm_2op(ty, OP_SUB, vp, &x);
                        }
                        break;
                }
                xpush(*vp);
                break;

        case 1:
                if (UNLIKELY(top()->type != VALUE_INTEGER)) {
                        zP("attempt to subtract non-integer from byte");
                }
                b = ((struct blob *)TARGETS.items[TARGETS.count].gc)->items[((uptr)vp) >> 3] -= pop().z;
                xpush(INTEGER(b));
                break;

        case 2:
        case 3:
        case 4:
        case 6:
                DoSetterMutOp(ty, p, OP_SUB, exec);
                break;

        case 5:
                DoPtrMutOp(ty, OP_SUB);
                break;

        default:
                zP("bad target pointer :(");
        }
}

void
DoMutAdd(Ty *ty, bool exec)
{
        uptr p = (uptr)poptarget();
        Value *vp, val, x;
        unsigned char b;

        vp = (Value *)(p & ~PMASK3);

        switch (p & PMASK3) {
        case 0:
                switch (PACK_TYPES(vp->type, top()->type)) {
                case PAIR_OF(VALUE_INTEGER):
                        vp->z += top()->z;
                        pop();
                        break;
                case PAIR_OF(VALUE_REAL):
                        vp->real += top()->real;
                        pop();
                        break;
                case PACK_TYPES(VALUE_INTEGER, VALUE_REAL):
                        vp->type = VALUE_REAL;
                        vp->real = vp->z;
                        vp->real += top()->real;
                        pop();
                        break;
                case PACK_TYPES(VALUE_REAL, VALUE_INTEGER):
                        vp->real += top()->z;
                        pop();
                        break;
                case PAIR_OF(VALUE_ARRAY):
                        value_array_extend(ty, vp->array, top()->array);
                        pop();
                        break;
                case PAIR_OF(VALUE_DICT):
                        DictUpdate(ty, vp->dict, top()->dict);
                        pop();
                        break;
                default:
                        x = pop();
                        val = vm_try_2op(ty, OP_MUT_ADD, vp, &x);
                        if (val.type != VALUE_NONE) {
                                vp = &val;
                        } else {
                                *vp = vm_2op(ty, OP_ADD, vp, &x);
                        }
                        break;
                }
                xpush(*vp);
                break;

        case 1:
                if (UNLIKELY(top()->type != VALUE_INTEGER)) {
                        zP("attempt to add non-integer to byte");
                }
                b = ((struct blob *)TARGETS.items[TARGETS.count].gc)->items[((uptr)vp) >> 3] += pop().z;
                xpush(INTEGER(b));
                break;

        case 2:
        case 3:
        case 4:
        case 6:
                DoSetterMutOp(ty, p, OP_ADD, exec);
                break;

        case 5:
                DoPtrMutOp(ty, OP_ADD);
                break;

        default:
                zP("bad target pointer :(");
        }
}

void
DoMutAnd(Ty *ty, bool exec)
{
        uptr p = (uptr)poptarget();
        Value *vp, val, x;
        unsigned char b;

        vp = (Value *)(p & ~PMASK3);

        switch (p & PMASK3) {
        case 0:
                switch (PACK_TYPES(vp->type, top()->type)) {
                case PAIR_OF(VALUE_INTEGER):
                        vp->z &= top()->z;
                        top()->z = vp->z;
                        break;
                case PAIR_OF(VALUE_BOOLEAN):
                        vp->boolean &= top()->boolean;
                        top()->boolean = vp->boolean;
                        break;
                case PAIR_OF(VALUE_SET):
                        SetRetain(ty, vp->set, top()->set);
                        *top() = *vp;
                        break;
                case PAIR_OF(VALUE_DICT):
                        dict_intersect(ty, vp, 1, NULL);
                        *top() = *vp;
                        break;
                case PACK_TYPES(VALUE_DICT, VALUE_SET):
                        DictKeepKeys(ty, vp->dict, top()->set);
                        *top() = *vp;
                        break;
                default:
                        x = pop();
                        val = vm_try_2op(ty, OP_MUT_AND, vp, &x);
                        if (val.type != VALUE_NONE) {
                                vp = &val;
                        } else {
                                *vp = vm_2op(ty, OP_BIT_AND, vp, &x);
                        }
                        xpush(*vp);
                        break;
                }
                break;

        case 1:
                if (UNLIKELY(top()->type != VALUE_INTEGER)) {
                        zP("attempt to AND byte with non-integer");
                }
                b = ((Blob *)TARGETS.items[TARGETS.count].gc)->items[((uptr)vp) >> 3] &= pop().z;
                xpush(INTEGER(b));
                break;

        case 2:
        case 3:
        case 4:
        case 6:
                DoSetterMutOp(ty, p, OP_BIT_AND, exec);
                break;

        case 5:
                DoPtrMutOp(ty, OP_BIT_AND);
                break;

        default:
                zP("bad target pointer :(");
        }
}

void
DoMutOr(Ty *ty, bool exec)
{
        uptr p = (uptr)poptarget();
        Value *vp, val, x;
        unsigned char b;

        vp = (Value *)(p & ~PMASK3);

        switch (p & PMASK3) {
        case 0:
                switch (PACK_TYPES(vp->type, top()->type)) {
                case PAIR_OF(VALUE_INTEGER):
                        vp->z |= top()->z;
                        top()->z = vp->z;
                        break;
                case PAIR_OF(VALUE_BOOLEAN):
                        vp->boolean |= top()->boolean;
                        top()->boolean = vp->boolean;
                        break;
                case PAIR_OF(VALUE_SET):
                        SetAbsorb(ty, vp->set, top()->set);
                        *top() = *vp;
                        break;
                default:
                        x = pop();
                        val = vm_try_2op(ty, OP_MUT_OR, vp, &x);
                        if (val.type != VALUE_NONE) {
                                vp = &val;
                        } else {
                                *vp = vm_2op(ty, OP_BIT_OR, vp, &x);
                        }
                        xpush(*vp);
                        break;
                }
                break;

        case 1:
                if (UNLIKELY(top()->type != VALUE_INTEGER)) {
                        zP("attempt to OR byte with non-integer");
                }
                b = ((Blob *)TARGETS.items[TARGETS.count].gc)->items[((uptr)vp) >> 3] |= pop().z;
                xpush(INTEGER(b));
                break;

        case 2:
        case 3:
        case 4:
        case 6:
                DoSetterMutOp(ty, p, OP_BIT_OR, exec);
                break;

        case 5:
                DoPtrMutOp(ty, OP_BIT_OR);
                break;

        default:
                zP("bad target pointer :(");
        }
}

void
DoMutXor(Ty *ty, bool exec)
{
        uptr p = (uptr)poptarget();
        Value *vp, val, x;
        unsigned char b;

        vp = (Value *)(p & ~PMASK3);

        switch (p & PMASK3) {
        case 0:
                switch (PACK_TYPES(vp->type, top()->type)) {
                case PAIR_OF(VALUE_INTEGER):
                        vp->z ^= top()->z;
                        top()->z = vp->z;
                        break;
                case PAIR_OF(VALUE_BOOLEAN):
                        vp->boolean ^= top()->boolean;
                        top()->boolean = vp->boolean;
                        break;
                case PAIR_OF(VALUE_SET):
                        SetToggle(ty, vp->set, top()->set);
                        *top() = *vp;
                        break;
                default:
                        x = pop();
                        val = vm_try_2op(ty, OP_MUT_XOR, vp, &x);
                        if (val.type != VALUE_NONE) {
                                vp = &val;
                        } else {
                                *vp = vm_2op(ty, OP_BIT_XOR, vp, &x);
                        }
                        xpush(*vp);
                        break;
                }
                break;

        case 1:
                if (UNLIKELY(top()->type != VALUE_INTEGER)) {
                        zP("attempt to XOR byte with non-integer");
                }
                b = ((Blob *)TARGETS.items[TARGETS.count].gc)->items[((uptr)vp) >> 3] ^= pop().z;
                xpush(INTEGER(b));
                break;

        case 2:
        case 3:
        case 4:
        case 6:
                DoSetterMutOp(ty, p, OP_BIT_XOR, exec);
                break;

        case 5:
                DoPtrMutOp(ty, OP_BIT_XOR);
                break;

        default:
                zP("bad target pointer :(");
        }
}

void
DoMutShl(Ty *ty, bool exec)
{
        uptr p = (uptr)poptarget();
        Value *vp, val, x;
        unsigned char b;

        vp = (Value *)(p & ~PMASK3);

        switch (p & PMASK3) {
        case 0:
                switch (PACK_TYPES(vp->type, top()->type)) {
                case PAIR_OF(VALUE_INTEGER):
                        vp->z <<= top()->z;
                        top()->z = vp->z;
                        break;
                default:
                        x = pop();
                        val = vm_try_2op(ty, OP_MUT_SHL, vp, &x);
                        if (val.type != VALUE_NONE) {
                                vp = &val;
                        } else {
                                *vp = vm_2op(ty, OP_BIT_SHL, vp, &x);
                        }
                        xpush(*vp);
                        break;
                }
                break;

        case 1:
                if (UNLIKELY(top()->type != VALUE_INTEGER)) {
                        zP("attempt to left-shift byte by non-integer");
                }
                b = ((Blob *)TARGETS.items[TARGETS.count].gc)->items[((uptr)vp) >> 3] <<= pop().z;
                xpush(INTEGER(b));
                break;

        case 2:
        case 3:
        case 4:
        case 6:
                DoSetterMutOp(ty, p, OP_BIT_SHL, exec);
                break;

        case 5:
                DoPtrMutOp(ty, OP_BIT_SHL);
                break;

        default:
                zP("bad target pointer :(");
        }
}

void
DoMutShr(Ty *ty, bool exec)
{
        uptr p = (uptr)poptarget();
        Value *vp, val, x;
        unsigned char b;

        vp = (Value *)(p & ~PMASK3);

        switch (p & PMASK3) {
        case 0:
                switch (PACK_TYPES(vp->type, top()->type)) {
                case PAIR_OF(VALUE_INTEGER):
                        vp->z >>= top()->z;
                        top()->z = vp->z;
                        break;
                default:
                        x = pop();
                        val = vm_try_2op(ty, OP_MUT_SHR, vp, &x);
                        if (val.type != VALUE_NONE) {
                                vp = &val;
                        } else {
                                *vp = vm_2op(ty, OP_BIT_SHR, vp, &x);
                        }
                        xpush(*vp);
                        break;
                }
                break;

        case 1:
                if (UNLIKELY(top()->type != VALUE_INTEGER)) {
                        zP("attempt to right-shift byte by non-integer");
                }
                b = ((Blob *)TARGETS.items[TARGETS.count].gc)->items[((uptr)vp) >> 3] >>= pop().z;
                xpush(INTEGER(b));
                break;

        case 2:
        case 3:
        case 4:
        case 6:
                DoSetterMutOp(ty, p, OP_BIT_SHR, exec);
                break;

        case 5:
                DoPtrMutOp(ty, OP_BIT_SHR);
                break;

        default:
                zP("bad target pointer :(");
        }
}

void
DoAssign(Ty *ty)
{
        uptr m, c, p = (uptr)poptarget();
        void *v = (void *)pP(p);
        TyObject *o;

        switch (pT(p)) {
        case 0:
                *(Value *)v = peek();
                break;

        case 1:
                ((Blob *)TARGETS.items[TARGETS.count].gc)->items[((uptr)v >> 3)] = peek().z;
                break;

        case 2:
                c = (uptr)poptarget();
                o = vZ(TARGETS)->gc;
                poptarget();
                call(ty, v, &OBJECT(o, c), 1, NULL);
                break;

        case 3:
                m = (p >> 3);
                c = (uptr)poptarget();
                o = vZ(TARGETS)->gc;
                push(xSz(M_NAME(m)));
                swap();
                call(ty, class_lookup_setter_i(ty, c, NAMES.missing), &OBJECT(o, c), 2, NULL);
                break;

        case 4:
                m = (p >> 3);
                c = (uptr)poptarget();
                push(xSz(M_NAME(m)));
                swap();
                exec_fn(ty, class_lookup_s_setter_i(ty, c, NAMES.missing), &CLASS(c), 2, NULL);
                break;

        case 6:
                c = (uptr)poptarget();
                poptarget();
                call(ty, v, &CLASS(c), 1, NULL);
                break;

        default:
                zP("bad target pointer :(");
        }
}

void
DoAssignExec(Ty *ty)
{
        uptr m, c, p = (uptr)poptarget();
        void *v = (void *)pP(p);
        TyObject *o;

        switch (pT(p)) {
        case 0:
                *(Value *)v = peek();
                break;

        case 1:
                ((Blob *)TARGETS.items[TARGETS.count].gc)->items[((uptr)v >> 3)] = peek().z;
                break;

        case 2:
                c = (uptr)poptarget();
                o = vZ(TARGETS)->gc;
                poptarget();
                exec_fn(ty, v, &OBJECT(o, c), 1, NULL);
                break;

        case 3:
                m = (p >> 3);
                c = (uptr)poptarget();
                o = vZ(TARGETS)->gc;
                push(xSz(M_NAME(m)));
                swap();
                exec_fn(ty, class_lookup_setter_i(ty, c, NAMES.missing), &OBJECT(o, c), 2, NULL);
                break;

        case 4:
                m = (p >> 3);
                c = (uptr)poptarget();
                push(xSz(M_NAME(m)));
                swap();
                exec_fn(ty, class_lookup_s_setter_i(ty, c, NAMES.missing), &CLASS(c), 2, NULL);
                break;

        case 6:
                c = (uptr)poptarget();
                poptarget();
                exec_fn(ty, v, &CLASS(c), 1, NULL);
                break;

        default:
                zP("bad target pointer :(");
        }
}

void
DoTargetMember(Ty *ty, Value v, i32 z)
{
        Value *vp;
        Value *vp2;

        switch (v.type) {
        case VALUE_OBJECT:
                vp = class_lookup_setter_i(ty, v.class, z);
                if (vp != NULL) {
                        vp2 = class_lookup_getter_i(ty, v.class, z);
                        if (UNLIKELY(vp2 == NULL)) {
                                zP(
                                        "class %s%s%s needs a getter for %s%s%s!",
                                        TERM(33),
                                        class_name(ty, v.class),
                                        TERM(0),
                                        TERM(34),
                                        M_NAME(z),
                                        TERM(0)
                                );
                        }
                        pushtarget(vp2, NULL);
                        pushtarget((Value *)(uptr)v.class, v.object);
                        pushtarget((Value *)(((uptr)vp) | 2), NULL);
                        return;
                }
                vp = ObjectMember(v, z);
                if (vp != NULL) {
                        pushtarget(vp, v.object);
                        return;
                }
                vp = class_lookup_setter_i(ty, v.class, NAMES.missing);
                if (vp != NULL) {
                        vp2 = class_lookup_method_i(ty, v.class, NAMES.missing);
                        if (UNLIKELY(vp2 == NULL)) {
                                zP(
                                        "class %s%s%s needs a getter for %s%s%s!",
                                        TERM(33),
                                        class_name(ty, v.class),
                                        TERM(0),
                                        TERM(34),
                                        M_NAME(z),
                                        TERM(0)
                                );
                        }
                        pushtarget((Value *)(uptr)v.class, v.object);
                        pushtarget((Value *)(((uptr)z << 3) | 3), NULL);
                        return;
                }
                if (v.object->dynamic == NULL) {
                        v.object->dynamic = mA0(sizeof (struct itable));
                }
                pushtarget(itable_get(ty, v.object->dynamic, z), v.object);
                break;

        case VALUE_CLASS:
                vp = class_lookup_s_setter_i(ty, v.class, z);
                if (vp != NULL) {
                        vp2 = class_lookup_s_getter_i(ty, v.class, z);
                        if (UNLIKELY(vp2 == NULL)) {
                                zP(
                                        "class %s%s%s needs a static getter for %s%s%s!",
                                        TERM(33),
                                        class_name(ty, v.class),
                                        TERM(0),
                                        TERM(34),
                                        M_NAME(z),
                                        TERM(0)
                                );
                        }
                        pushtarget(vp2, NULL);
                        pushtarget((Value *)(uptr)v.class, NULL);
                        pushtarget((Value *)(((uptr)vp) | 6), NULL);
                        return;
                }
                vp = class_lookup_field(ty, v.class, z);
                if (vp != NULL) {
                        pushtarget(vp, NULL);
                        return;
                }
                vp = class_lookup_s_setter_i(ty, v.class, NAMES.missing);
                if (vp != NULL) {
                        vp2 = class_lookup_s_method_i(ty, v.class, NAMES.missing);
                        if (UNLIKELY(vp2 == NULL)) {
                                zP(
                                        "class %s%s%s needs a getter for %s%s%s!",
                                        TERM(33),
                                        class_name(ty, v.class),
                                        TERM(0),
                                        TERM(34),
                                        M_NAME(z),
                                        TERM(0)
                                );
                        }
                        pushtarget((Value *)(uptr)v.class, NULL);
                        pushtarget((Value *)(((uptr)z << 3) | 4), NULL);
                        return;
                }
                BadFieldAccess(ty, &v, z);

        case VALUE_TUPLE:
                vp = tuple_get_i(&v, z);
                if (vp == NULL) {
                        BadFieldAccess(ty, &v, z);
                }
                pushtarget(vp, v.items);
                break;

        case VALUE_FUNCTION:
        case VALUE_BOUND_FUNCTION:
                DoTargetMember(ty, *meta_of(ty, &v), z);
                break;

        default:
                zP("assignment to member of non-object: %s", VSC(&v));
        }
}

void
DoTargetSubscript(Ty *ty)
{
        Value v;
        Value p;
        Value subscript = top()[0];
        Value container = top()[-1];

        switch (container.type) {
        case VALUE_ARRAY:
                if (UNLIKELY(subscript.type != VALUE_INTEGER)) {
                        zP("non-integer array index used in subscript assignment");
                }
                if (subscript.z < 0) {
                        subscript.z += vN(*container.array);
                }
                if (UNLIKELY(subscript.z < 0 || subscript.z >= vN(*container.array))) {
                        push(TAGGED(TAG_INDEX_ERR, container, subscript));
                        RaiseException(ty);
                        return;
                }
                pushtarget(v_(*container.array, subscript.z), container.array);
                break;

        case VALUE_DICT:
                pushtarget(dict_put_key_if_not_exists(ty, container.dict, subscript), container.dict);
                break;

        case VALUE_BLOB:
                if (UNLIKELY(subscript.type != VALUE_INTEGER)) {
                        zP("non-integer index in subscript assignment to Blob: %s", VSC(&subscript));
                }
                if (subscript.z < 0) {
                        subscript.z += vN(*container.blob);
                }
                if (subscript.z < 0 || subscript.z >= vN(*container.blob)) {
                        push(TAGGED(TAG_INDEX_ERR, container, subscript));
                        RaiseException(ty);
                }
                pushtarget((Value *)((((uptr)(subscript.z)) << 3) | 1), container.blob);
                break;

        case VALUE_PTR:
                p = vm_2op(ty, OP_ADD, &container, &subscript);
                if (IP[0] == INSTR_ASSIGN) {
                        pop();
                        pop();
                        v = pop();
                        xpush(p);
                        xpush(v);
                        v = builtin_ffi_store(ty, 2, NULL);
                        pop();
                        put(v);
                        IP += 1;
                        return;
                } else {
                        pushtarget(p.extra, NULL);
                        pushtarget(p.ptr, p.gcptr);
                        pushtarget((Value *)(uptr)5, NULL);
                }
                break;

        default:
                zP(
                        "attempt to perform subscript assignment on "
                        "something other than an object or array: %s",
                        VSC(&container)
                );
        }

        pop();
        pop();
}

void
DoAssignSubscript(Ty *ty, int n, bool exec)
{
        Value v;
        Value p;
        Value *f;

        if (n == (u8)-1) {
                n = vN(STACK) - vXx(SP_STACK);
        }

        isize i_xs = vN(STACK) - (n + 1);
        isize i_x  = i_xs - 1;

        Value subscript = peek();
        Value container = v__(STACK, i_xs);
        Value value     = v__(STACK, i_x);

        switch (container.type) {
        case VALUE_ARRAY:
                if (UNLIKELY((n != 1) || (subscript.type != VALUE_INTEGER))) {
                        zP("invalid index in subscript assignment to Array: %s", VSC(&subscript));
                }
                if (subscript.z < 0) {
                        subscript.z += vN(*container.array);
                }
                if (UNLIKELY(subscript.z < 0 || subscript.z >= vN(*container.array))) {
                        push(TAGGED(TAG_INDEX_ERR, container, subscript));
                        RaiseException(ty);
                }
                *v_(*container.array, subscript.z) = value;
                break;

        case VALUE_DICT:
                dict_put_value(ty, container.dict, subscript, value);
                break;

        case VALUE_BLOB:
                if (UNLIKELY((n != 1) || (subscript.type != VALUE_INTEGER))) {
                        zP("non-integer index in subscript assignment to Blob: %s", VSC(&subscript));
                }
                if (subscript.z < 0) {
                        subscript.z += container.blob->count;
                }
                if (subscript.z < 0 || subscript.z >= vN(*container.blob)) {
                        push(TAGGED(TAG_INDEX_ERR, container, subscript));
                        RaiseException(ty);
                }
                if (UNLIKELY(value.type != VALUE_INTEGER)) {
                        zP("attempt to assign Blob element to non-integer value: %s", VSC(&value));
                }
                *v_(*container.blob, subscript.z) = value.z;
                break;

        case VALUE_PTR:
                if (UNLIKELY((n != 1) || (subscript.type != VALUE_INTEGER))) {
                        zP("non-integer offset in pointer subscript assignment: %s", VSC(&subscript));
                }
                p = vm_2op(ty, OP_ADD, &container, &subscript);
                pop();
                pop();
                put(p);
                xpush(value);
                v = builtin_ffi_store(ty, 2, NULL);
                pop();
                put(v);
                return;

        case VALUE_OBJECT:
                vvXi(STACK, i_xs);
                vvXi(STACK, i_x);
                xpush(value);
                f = class_lookup_method_i(ty, container.class, NAMES.subscript_eq);
                if (f != NULL) {
                        if (exec) {
                                exec_fn(ty, f, &container, n + 1, NULL);
                        } else {
                                call(ty, f, &container, n + 1, NULL);
                        }
                }
                return;

        case VALUE_CLASS:
                vvXi(STACK, i_xs);
                vvXi(STACK, i_x);
                xpush(value);
                f = class_lookup_s_method_i(ty, container.class, NAMES.subscript_eq);
                if (f != NULL) {
                        if (exec) {
                                exec_fn(ty, f, &container, n + 1, NULL);
                        } else {
                                call(ty, f, &container, n + 1, NULL);
                        }
                }
                return;

        default:
                zP(
                        "attempt to perform subscript assignment on "
                        "something other than an object or array: %s",
                        VSC(&container)
                );
        }

        vN(STACK) -= (n + 1);
}

inline static void
splat(Ty *ty, Dict *d, Value *v)
{
        if (v->type == VALUE_DICT) {
                DictUpdate(ty, d, v->dict);
                return;
        }

        if (v->type == VALUE_TUPLE) {
                for (int i = 0; i < v->count; ++i) {
                        if (v->ids == NULL || v->ids[i] == -1) {
                                dict_put_value(ty, d, INTEGER(i), v->items[i]);
                        } else {
                                char const *name = M_NAME(v->ids[i]);
                                dict_put_member(ty, d, name, v->items[i]);
                        }
                }
                return;
        }
        // FIXME: What else should be allowed here?
}

static void
DoRange(Ty *ty, bool inclusive)
{
        Value b = pop();
        Value a = pop();

        Value v = RawObject(inclusive ? CLASS_INC_RANGE : CLASS_RANGE);
        xpush(v);

        if (UNLIKELY(PACK_TYPES(a.type, b.type) != PAIR_OF(VALUE_INTEGER))) {
                zP(
                        "Range.init(): bad bounds: (%s, %s)",
                        VSC(&a),
                        VSC(&b)
                );
        }

        // XXX
        if (a.z > b.z) {
                SWAP(imax, a.z, b.z);
        }

        if (inclusive) {
                b.z += 1;
        }

        PutMember(v, NAMES.a, a);
        PutMember(v, NAMES.b, b);
}

static void
DoStringLiteral(Ty *ty, i32 i)
{
        InternEntry const *interned = intern_entry(&xD.strings, i);
        push(
                STRING_NOGC(
                        interned->name,
                        (uptr)interned->data
                )
        );
}

void
DoDictLiteral(Ty *ty, i32 n, Value const *dflt)
{
        GC_STOP();

        Dict *dict = dict_new(ty);
        Value val  = DICT(dict);

        if (dflt != NULL) {
                dict->dflt = *dflt;
        }

        for (usize i = vN(STACK) - n; i < vN(STACK); i += 2) {
                Value *key   = v_(STACK, i);
                Value *value = v_(STACK, i + 1);

                if (IsNone(*value)) {
                        splat(ty, dict, key);
                } else {
                        dict_put_value(ty, dict, *key, *value);
                }
        }

        GC_RESUME();

        vN(STACK) -= n;
        push(val);
}

void
DoSetCompr(Ty *ty, i32 skip, i32 n)
{
        Set *s = top()[-(n + skip)].set;

        for (usize i = vN(STACK) - n; i < vN(STACK); ++i) {
                set_add(ty, s, v__(STACK, i));
        }

        vN(STACK) -= n;
}

void
DoSetLiteral(Ty *ty, i32 n)
{
        GC_STOP();
        Value s = SET(set_new(ty));
        for (usize i = vN(STACK) - n; i < vN(STACK); ++i) {
                set_add(ty, s.set, v__(STACK, i));
        }
        GC_RESUME();

        vN(STACK) -= n;
        xpush(s);
}

static void
DoTupleLiteral(Ty *ty)
{
        i32Vector   ids    = {0};
        ValueVector values = {0};

        bool have_names = false;

        i32 n;
        i32 z;

        READVALUE(n);

        SCRATCH_SAVE();
        for (i32 i = 0; i < n; ++i) {
                Value *v = &vZ(STACK)[i - n];
                READVALUE(z);
                if (z == -2) {
                        if (UNLIKELY(v->type != VALUE_TUPLE)) {
                                zP(
                                        "attempt to spread non-tuple in tuple expression: %s",
                                        VSC(v)
                                );
                        }
                        for (int j = 0; j < v->count; ++j) {
                                if (v->ids != NULL && v->ids[j] != -1) {
                                        AddTupleEntry(ty, &ids, &values, v->ids[j], &v->items[j]);
                                        have_names = true;
                                } else {
                                        svP(ids, -1);
                                        svP(values, v->items[j]);
                                }
                        }
                } else if (v->type != VALUE_NONE) {
                        if (z == -1) {
                                svP(ids, -1);
                                svP(values, *v);
                        } else {
                                AddTupleEntry(ty, &ids, &values, z, v);
                                have_names = true;
                        }
                }
        }

        u32   k = vN(values);
        Value v = TUPLE(mAo(k * sizeof (Value), GC_TUPLE), NULL, k);

        if (k > 0) {
                __builtin_memcpy(v.items, vv(values), k * sizeof (Value));
                if (have_names) {
                        v.ids = uAo(k * sizeof (i32), GC_TUPLE);
                        __builtin_memcpy(v.ids, vv(ids), k * sizeof (i32));
                }
        }
        SCRATCH_RESTORE();

        STACK.count -= n;
        push(v);
}

void
vm_jit_tuple_literal(Ty *ty, char *ip)
{
        char *saved = IP;
        IP = ip;
        DoTupleLiteral(ty);
        IP = saved;
}

void
IncValue(Ty *ty, Value *v)
{
        i32 n;
        i32 rune;
        Value *vp;
        ffi_type const *type;

        switch (EXPECT(v->type, VALUE_INTEGER)) {
        case VALUE_INTEGER:
                v->z += 1;
                break;

        case VALUE_REAL:
                v->real += 1.0;
                break;

        case VALUE_PTR:
                type = (v->extra != NULL) ? v->extra : &ffi_type_uint8;
                v->ptr = ((char *)v->ptr) + type->size;
                break;

        case VALUE_STRING:
                if (sN(*v) > 0) {
                        n = utf8proc_iterate(ss(*v), sN(*v), &rune);
                        n = max(1, n);
                        ss(*v) += n;
                        sN(*v) -= n;
                }
                break;

        case VALUE_OBJECT:
                vp = class_method(ty, v->class, "++");
                if (vp != NULL) {
                        exec_fn(ty, vp, v, 0, NULL);
                        break;
                }
                // fall

        default:
                zP("increment applied to invalid type: %s", VSC(v));
        }
}

void
DecValue(Ty *ty, Value *v)
{
        Value *vp;
        ffi_type const *type;

        switch (EXPECT(v->type, VALUE_INTEGER)) {
        case VALUE_INTEGER:
                v->z -= 1;
                break;

        case VALUE_REAL:
                v->real -= 1.0;
                break;

        case VALUE_PTR:
                type = (v->extra != NULL) ? v->extra : &ffi_type_uint8;
                v->ptr = ((char *)v->ptr) - type->size;
                break;

        case VALUE_STRING:
                DecrementString(v);
                break;

        case VALUE_OBJECT:
                vp = class_method(ty, v->class, "--");
                if (vp != NULL) {
                        exec_fn(ty, vp, v, 0, NULL);
                        break;
                }
                // fall

        default:
                zP("decrement applied to invalid type: %s", VSC(v));
        }
}

static void
IterGetNext(Ty *ty, bool exec)
{
        Value v;
        Value *vp;

        DictItem *item;
        SetItem *sitem;

        ptrdiff_t off;

        int i;
        int n;

Top:
        v = top()[-1];
        i = top()[-2].i++;

        dont_printf("GET_NEXT: v = %s\n", VSC(&v));
        dont_printf("GET_NEXT: i = %d\n", i);
        print_stack(ty, 10);

        switch (v.type) {
        case VALUE_HEAP:
                v = HEAP_VIEW(v.heap);
        case VALUE_ARRAY:
                if (i < vN(*v.array)) {
                        push(v__(*v.array, i));
                } else {
                        push(NONE);
                }
                break;

        case VALUE_DICT:
                off = top()[-2].off;
                if (off == 0) {
                        off = (v.dict->first != NULL)
                            ? (v.dict->first - v.dict->items) + 1
                            : PTRDIFF_MAX;
                }
                if (off > v.dict->size) {
                        push(NONE);
                        break;
                }
                item = &v.dict->items[off - 1];
                if (item->next != NULL) {
                        top()[-2].off = (item->next - v.dict->items) + 1;
                } else {
                        top()[-2].off = PTRDIFF_MAX;
                }
                push(PAIR(item->k, item->v));
                break;

        case VALUE_SET:
                off = top()[-2].off;
                if (off == 0) {
                        off = (v.set->first != NULL)
                            ? (v.set->first - v.set->items) + 1
                            : PTRDIFF_MAX;
                }
                if (off > v.set->size) {
                        push(NONE);
                        break;
                }
                sitem = &v.set->items[off - 1];
                top()[-2].off = (sitem->next != NULL)
                              ? (sitem->next - v.set->items) + 1
                              : PTRDIFF_MAX;
                push(sitem->k);
                break;

        case VALUE_FUNCTION:
        case VALUE_BOUND_FUNCTION:
                push(INTEGER(i));
                if (exec) {
                        exec_fn(ty, &v, NULL, 1, NULL);
                } else {
                        call(ty, &v, NULL, 1, NULL);
                }
                break;

        case VALUE_OBJECT:
                if ((vp = class_lookup_method_i(ty, v.class, NAMES._next_)) != NULL) {
                        push(INTEGER(i));
                        if (exec) {
                                exec_fn(ty, vp, &v, 1, NULL);
                                YieldFix(ty);
                        } else {
                                call6t(ty, vp, &v, 1, NULL, next_fix);
                        }
                } else if ((vp = class_lookup_method_i(ty, v.class, NAMES._iter_)) != NULL) {
                        pop();
                        pop();
                        --top()->i;
                        if (exec) {
                                exec_fn(ty, vp, &v, 0, NULL);
                                push(SENTINEL);
                                goto Top;
                        } else {
                                /* Have to repeat this instruction */
                                call6t(ty, vp, &v, 0, NULL, iter_fix);
                        }
                        return;
                } else {
                        goto NoIter;
                }
                break;

        case VALUE_QUEUE:
                if (
                        (v.queue->cap > 0)
                     && (i < _queue_count(v.queue->head, v.queue->tail, v.queue->cap))
                ) {
                        push(v.queue->items[(v.queue->head + i) % v.queue->cap]);
                } else {
                        push(NONE);
                }
                break;

        case VALUE_BLOB:
                if (i < vN(*v.blob)) {
                        push(INTEGER(v.blob->items[i]));
                } else {
                        push(NONE);
                }
                break;

        case VALUE_TUPLE:
                if (i < v.count) {
                        push(v.items[i]);
                } else {
                        push(NONE);
                }
                break;

        case VALUE_STRING:
                vp = top() - 2;
                if ((off = vp->off) < sN(v)) {
                        vp->off += (n = u8_rune_sz(ss(v) + off));
                        push(STRING_VIEW(v, off, n));
                } else {
                        push(NONE);
                }
                break;

        case VALUE_GENERATOR:
                call_co_ex(ty, &v, 0, IP);
                YieldFix(ty);
                break;

        default:
NoIter:
                zP("for-each loop on non-iterable value: %s", VSC(&v));
        }
}

bool
vm_jit_loop_check(Ty *ty, int z)
{
        if (top()->type == VALUE_NONE) {
                pop();
                pop();
                pop();
                pop();
                return true;
        }

        if (
                (z == 1)
             && (top()[-1].type == VALUE_SENTINEL)
             && (top()->type != VALUE_SENTINEL)
        ) {
                return false;
        }

        imax k = top()[-3].z - 1;

        push(INTEGER(k));

        i32 i;
        i32 j;

        for (i = 0; top()[-i].type != VALUE_SENTINEL; ++i) {
                ;
        }

        while (i > z) {
                --i, pop();
        }

        while (i < z) {
                ++i, push(NIL);
        }

        Value v;

        for (i = 0, j = z - 1; i < j; ++i, --j) {
                v = top()[-i];
                top()[-i] = top()[-j];
                top()[-j] = v;
        }

        return false;
}

static bool
LoopCheck(Ty *ty, i32 z, char *jump)
{
        if (!vm_jit_loop_check(ty, z)) {
                return false;
        }

        DOJUMP(jump);

        return true;
}

void
vm_jit_loop_iter(Ty *ty)
{
        push(SENTINEL);
        IterGetNext(ty, true);
}

void
vm_iter_begin(Ty *ty, Value xs)
{
        push(INDEX(0, 0, 1));
        push(xs);
}

bool
vm_iter_next(Ty *ty, Value *x)
{
        push(SENTINEL);
        IterGetNext(ty, true);

        if (top()->type == VALUE_NONE) {
                STACK.count -= 4;
                return false;
        }

        Value *sentinel = top();

        while (sentinel->type != VALUE_SENTINEL) {
                sentinel -= 1;
        }

        *x = sentinel[1];
        STACK.count = sentinel - vv(STACK);

        return true;
}

inline static void
SpreadShuffle(Ty *ty, bool inject_nil)
{
        Value x = pop();
        (void)pop();
        Value xs = pop();
        Value idx = pop();

        push(x);
        if (inject_nil) {
                push(NIL);
        }
        push(idx);
        push(xs);
}

bool
vm_jit_spread_check(Ty *ty, bool inject_nil)
{
        if (vm_jit_loop_check(ty, 1)) {
                return true;
        }

        Value xs = top()[-2];
        Value const *p;
        usize n;

        switch (xs.type) {
        case VALUE_ARRAY:
                p = vv(*xs.array);
                n = vN(*xs.array);
                break;

        case VALUE_TUPLE:
                p = xs.items;
                n = xs.count;
                break;

        default:
                SpreadShuffle(ty, inject_nil);
                return false;
        }

        usize i = top()[-3].i - 1;

        vN(STACK) -= 4;

        if (inject_nil) {
                xvR(STACK, fit2(max(vC(STACK), 4), vN(STACK) + 2 * (n - i)));
                for (; i < n; ++i) {
                        xvP(STACK, p[i]);
                        xvP(STACK, NIL);
                }
        } else {
                xvPn(STACK, p + i, n - i);
        }

        return true;
}

static void
DoMatchTag(Ty *ty)
{
        char *fail;
        char *jmp;
        i32 subject_id;
        i32 entry_id;
        i32 n;

        u8 wrapped = *IP++;
        READVALUE(n);
        READJUMP(fail);

        if (wrapped) {
                if (top()->type & VALUE_TAGGED) {
                        subject_id = tags_first(ty, top()->tags);
                } else {
                        DOJUMP(fail);
                        return;
                }
        } else {
                if (top()->type == VALUE_TAG) {
                        subject_id = top()->tag;
                } else {
                        DOJUMP(fail);
                        return;
                }
        }

        for (i32 i = 0; i < n; ++i) {
                READVALUE(entry_id);
                READJUMP(jmp);
                if (entry_id == subject_id) {
                        DOJUMP(jmp);
                        return;
                }
        }

        DOJUMP(fail);
}

static void
DoMatchString(Ty *ty)
{
        i32 n;
        char *fail;
        char *table;

        READVALUE(n);
        READJUMP(fail);

        table = IP;
        IP += n * 2 * sizeof (i32);

        if (top()->type != VALUE_STRING) {
                DOJUMP(fail);
                return;
        }

        u64 h = XXH3_64bits(ss(*top()), sN(*top()));
        u32 mask = (u32)(n - 1);
        u32 bucket = (u32)(h & mask);

        for (;;) {
                char *slot = table + bucket * 2 * sizeof (i32);
                i32 id = load_i32(slot);

                if (id == -1) {
                        break;
                }

                InternEntry const *ie = intern_entry(&xD.strings, id);
                u32 len = (u32)(uptr)ie->data;

                if (sN(*top()) == len && memcmp(ss(*top()), ie->name, len) == 0) {
                        char *jmp = slot + sizeof (i32);
                        DOJUMP(jmp);
                        return;
                }

                bucket = (bucket + 1) & mask;
        }

        DOJUMP(fail);
}

void
DoCheckMatch(Ty *ty, bool exec)
{
        Value v;
        Value value;

        switch (top()->type) {
        case VALUE_CLASS:
                v = pop();
                *top() = BOOLEAN(class_is_subclass(ty, ClassOf(top()), v.class));
                break;

        case VALUE_TAG:
                v = pop();
                *top() = BOOLEAN(
                        (top()->type == VALUE_TAG && top()->tag == v.tag)
                     || (tags_first(ty, top()->tags) == v.tag)
                );
                break;

        case VALUE_BOOLEAN:
                v = pop();
                *top() = v;
                break;

        case VALUE_TYPE:
                v = pop();
                value = pop();
                xpush(BOOLEAN(t2_check(ty, as_type(&v), &value)));
                break;

        case VALUE_NIL:
                v = pop();
                *top() = BOOLEAN(top()->type == VALUE_NIL);
                break;

        default:
                CallMethod(ty, NAMES.match, 1, 0, false, exec);
        }
}

void
DoSubscript(Ty *ty, bool exec)
{
        Value subscript = top()[0];
        Value container = top()[-1];
        Value v;
        Value *vp;

        switch (container.type) {
        case VALUE_TYPE:
                break;

        case VALUE_HEAP:
                container = HEAP_VIEW(container.heap);
        case VALUE_ARRAY:
                v = ArraySubscript(ty, container, subscript, INDEX_STRICT);
                pop();
                put(v);
                break;

        case VALUE_TUPLE:
                if (LIKELY(subscript.type == VALUE_INTEGER)) {
                        if (subscript.z < 0) {
                                subscript.z += container.count;
                        }

                        if (subscript.z < 0 || subscript.z >= container.count) {
                                v = tagged(ty, TAG_INDEX_ERR, container, subscript, NONE);
                                pop();
                                put(v);
                                RaiseException(ty);
                                break;

                        }

                        pop();
                        pop();

                        xpush(container.items[subscript.z]);
                } else {
                        zP(
                                "non-integer index used in subscript expression: %s",
                                VSC(&subscript)
                        );
                }
                break;

        case VALUE_STRING:
                v = string_char(ty, &container, 1, NULL);
                if (UNLIKELY(IsNil(v))) {
                        put(TAGGED(TAG_INDEX_ERR, container, pop()));
                        RaiseException(ty);

                }
                pop();
                put(v);
                break;

        case VALUE_BLOB:
                if (UNLIKELY(subscript.type != VALUE_INTEGER)) {
                        zP("non-integer index used in subscript expression: %s", VSC(&subscript));
                }
                v = subscript;
                if (!WrapIndex(&v.z, vN(*container.blob))) {
                        put(TAGGED(TAG_INDEX_ERR, container, pop()));
                        RaiseException(ty);
                        break;
                }
                pop();
                put(INTEGER(v__(*container.blob, v.z)));
                break;

        case VALUE_DICT:
                vp = dict_get_value(ty, container.dict, &subscript);
                pop();
                put((vp == NULL) ? NIL : *vp);
                break;

        case VALUE_QUEUE:
                if (UNLIKELY(subscript.type != VALUE_INTEGER)) {
                        zP("non-integer index used in subscript expression: %s", VSC(&subscript));
                }
                vp = queue_index(container.queue, subscript.z);
                if (vp == NULL) {
                        put(TAGGED(TAG_INDEX_ERR, container, pop()));
                        RaiseException(ty);
                        break;
                }
                pop();
                put(*vp);
                break;

        case VALUE_BOOLEAN:
                pop();
                put(container);
                break;

        case VALUE_GENERATOR:
                vp = class_lookup_method_i(ty, CLASS_GENERATOR, NAMES.subscript);
                if (vp != NULL) {
                        swap();
                        pop();
                        call(ty, vp, &container, 1, NULL);
                } else {
                        goto BadContainer;
                }
                break;

        case VALUE_OBJECT:
                vp = class_lookup_method_i(ty, container.class, NAMES.subscript);
                if (vp != NULL) {
                        swap();
                        pop();
                        if (exec) {
                                exec_fn(ty, vp, &container, 1, NULL);
                        } else {
                                call(ty, vp, &container, 1, NULL);
                        }
                } else {
                        goto BadContainer;
                }
                break;

        case VALUE_CLASS:
        case VALUE_TAG:
                swap();
                CallMethod(ty, NAMES.subscript, 1, 0, false, exec);
                break;

        case VALUE_PTR:
                if (UNLIKELY(subscript.type != VALUE_INTEGER)) {
                        zP("non-integer used to subscript pointer: %s", VSC(&subscript));
                }
                v = GCPTR((container.extra == NULL) ? &ffi_type_uint8 : container.extra, container.gcptr);
                push(v);
                push(PTR(((char *)container.ptr) + ((ffi_type *)v.ptr)->size * subscript.z));
                v = builtin_ffi_load(ty, 2, NULL);
                pop();
                pop();
                pop();
                put(v);
                break;

        case VALUE_NIL:
                zP(
                        "subscript of nil: nil[%s] (use x.?[%s] to get nil when x is nil)",
                        VSC(&subscript),
                        VSC(&subscript)
                );

        default:
BadContainer:
                zP("invalid container in subscript expression: %s", VSC(&container));
        }
}

void
DoSafeSubscript(Ty *ty, bool exec)
{
        Value subscript = top()[0];
        Value container = top()[-1];
        Value v;
        Value *vp;

        switch (container.type) {
        case VALUE_NIL:
                v = NIL;
                break;

        case VALUE_HEAP:
                container = HEAP_VIEW(container.heap);
        case VALUE_ARRAY:
                v = ArraySubscript(ty, container, subscript, INDEX_SAFE);
                break;

        case VALUE_STRING:
                v = string_char(ty, &container, 1, NULL);
                break;

        case VALUE_TUPLE:
                if (UNLIKELY(subscript.type != VALUE_INTEGER)) {
                        goto Strict;
                }
                v = WrapIndex(&subscript.z, container.count)
                  ? container.items[subscript.z]
                  : NIL;
                break;

        case VALUE_BLOB:
                if (UNLIKELY(subscript.type != VALUE_INTEGER)) {
                        goto Strict;
                }
                v = WrapIndex(&subscript.z, vN(*container.blob))
                  ? INTEGER(v__(*container.blob, subscript.z))
                  : NIL;
                break;

        case VALUE_QUEUE:
                if (UNLIKELY(subscript.type != VALUE_INTEGER)) {
                        goto Strict;
                }
                vp = queue_index(container.queue, subscript.z);
                v = (vp == NULL) ? NIL : *vp;
                break;

        default:
Strict:
                DoSubscript(ty, exec);
                return;
        }

        pop();
        put(v);
}

static _Thread_local VmSnippet Snippet;

VmSnippet
vm_snippet_begin(char const *code, usize n)
{
        VmSnippet outer = Snippet;

        Snippet = (VmSnippet) {
                .lo   = code,
                .hi   = code + n,
                .made = false
        };

        return outer;
}

bool
vm_snippet_end(VmSnippet outer)
{
        bool made = Snippet.made;

        Snippet = outer;

        return made;
}

char *
DoFunction(Ty *ty, char const *ip, Value *locals, Value **env)
{
        Value v = {0};

        if (UNLIKELY(Snippet.lo != NULL) && ip >= Snippet.lo && ip < Snippet.hi) {
                Snippet.made = true;
        }

        v.type = VALUE_FUNCTION;

        u16 ncaps = load_u16(ip);
        ip += sizeof ncaps;

        char const *caps = ip;
        ip += ncaps * sizeof (u32);

        ip = ALIGNED_FOR(i64, ip);

        v.info = (i32 *)ip;

        int  hs   = v.info[FUN_INFO_HEADER_SIZE];
        int  size = v.info[FUN_INFO_CODE_SIZE];
        int  nEnv = v.info[FUN_INFO_CAPTURES];
        bool eval = from_eval(&v);

        if (eval) {
                v.info = uAo(hs + size, GC_ANY);
                memcpy(v.info, ip, hs + size);
        }

        ip += (hs + size);

        if (nEnv > 0) {
                LOG("Allocating ENV for %d caps", nEnv);
                v.env = uAo0(nEnv * sizeof (Value *), GC_ENV);
        } else {
                v.env = NULL;
        }

        for (int i = 0; i < ncaps; ++i) {
                u32 cap = load_u32(caps + i * sizeof (u32));
                Value *p;

                switch (CAP_KIND(cap)) {
                case CAP_LOCAL:
                        p = &locals[CAP_INDEX(cap)];
                        if (p->type != VALUE_REF) {
                                Value *box = uAo(sizeof (Value), GC_VALUE);
                                *box = *p;
                                *p = REF(box);
                        }
                        v.env[i] = p->ptr;
                        break;

                case CAP_CAPTURED:
                        v.env[i] = env[CAP_INDEX(cap)];
                        break;
                }
        }

        push(v);

        if (nEnv > 0 || eval) {
                CheckUsed(ty);
        }

        if (UNLIKELY(
                expr_of(&v)->fn->must_jit
             && ((uptr)jit_of(&v) == JIT_UNSEEN)
             && !NoJIT
             && !DebugJitOff
             && !eval
        )) {
                if (UNLIKELY(try_jit_now(ty, &v) == NULL)) {
                        zP("failed to JIT compile function %s", SHOW(&v));
                }
        }

        return (char *)ip;
}

char *
DoGenerator(Ty *ty, char const *ip, Value *locals, Value **env)
{
        char *end = DoFunction(ty, ip, locals, env);
        Generator *gen = NewGenerator(ty, peek());
        xvPn(gen->st->stack, LOTS_OF_NILS, gen->f.info[FUN_INFO_BOUND]);
        xvP(gen->st->frames, FRAME(1, gen->f, IP));
        put(GENERATOR(gen));
        return end;
}

static void
InstallMethods(Ty *ty, i32 c, struct itable *table, i32 n)
{
        i32 i;
        Value v;
        Value *vp;

        while (n --> 0) {
                READVALUE(i);

                v = pop();

                if ((v.env != NULL) || has_meta(&v)) {
                        gc_immortalize(ty, &v);
                }

                vp = itable_get(ty, table, i);
                if (vp->type == VALUE_REF) {
                        *vp->ref = v;
                }
                *vp = v;
        }
}

static Value
IntoMethod(Ty *ty, Value const *fun, i32 c)
{
        Value method = *fun;

        i32 c0 = method.info[FUN_INFO_CLASS];
        if (c0 == c) {
                return method;
        }

        u32 size = header_size_of(fun)
                 + code_size_of(fun);

        void *storage = from_eval(fun)
                      ? uAo(size, GC_ANY)
                      : mrealloc(NULL, size);
        method.info = memcpy(storage, fun->info, size);
        set_jit_of(&method, NULL);
        set_jit_code_of(&method, NULL);
        DebugSanitizeCode(code_of(fun), code_of(&method), code_size_of(fun));
        method.info[FUN_INFO_CLASS] = c;

        if (c0 != -1) {
                return method;
        }

        i32 np = fun->info[FUN_INFO_PARAM_COUNT];

        char *ip  = code_of(&method);
        char *end = ip + code_size_of(&method);

        int ref;
        while (ip < end) {
                switch (*ip) {
                case INSTR_LOAD_LOCAL:
                case INSTR_LOAD_REF:
                case INSTR_ASSIGN_LOCAL:
                case INSTR_TARGET_LOCAL:
                case INSTR_TARGET_REF:
                case INSTR_CAPTURE:
                        ref = load_int(ip + 1);
                        if (ref >= np) {
                                ref += 1;
                                memcpy(ip + 1, &ref, sizeof ref);
                        }
                        break;

                default:
                        break;
                }
                ip = StepInstruction(ip);
        }

        method.info[FUN_INFO_BOUND] += 1;

        return method;
}

static Value
ResolveTrace(Ty *ty, ThrowCtx const *ctx)
{
        Array *trace = vA();

        GC_STOP();

        for (int i = 0; i < vN(*ctx); ++i) {
                char const *ip = v__(*ctx, i);

                Expr const *expr = compiler_find_expr(ty, ip - 1);
                Expr const *func = compiler_find_func(ty, ip - 1);

                if (expr == NULL) {
                        continue;
                }

                Value entry = TyTraceEntryFor(ty, expr);

                if (func == NULL || vN(ctx->locals) <= i) {
                        vAp(trace, PAIR(entry, NIL));
                        continue;
                }

                ValueVector localv = v__(ctx->locals, i);
                Scope *scope = func->fn->scope;
                Dict *locals = dict_new(ty);

                for (int i = 0; i < vN(scope->owned); ++i) {
                        dict_put_member(
                                ty,
                                locals,
                                v__(scope->owned, i)->identifier,
                                v__(localv, i)
                        );
                }

                vAp(trace, PAIR(entry, DICT(locals)));
        }

        GC_RESUME();

        return ARRAY(trace);
}

bool
vm_try_exec(Ty *ty, char *code, Value *result)
{
        bool ok = true;

        if (!VM_TRY()) {
                *result = vm_catch(ty);
                ok = false;
        } else {
                vm_exec(ty, code);
                *result = pop();
                vm_finally(ty);
        }

        return ok;
}

void
vm_exec(Ty *ty, char *code)
{
        Ty   * volatile _ty = ty;
        char * volatile _ip = IP;

        IP = code;

        uptr s;
        double x;
        imax k;

        bool b;

        int i;
        int j;

        int n;
        int nkw;

        int z;
        int tag;

        Value *vp;
        Value v;
        Value value;
        Value key;

        char *str;
        char *jump;

        struct try *_try;

        if (UNLIKELY(!TY_IS_INITIALIZED)) {
                PopulateGlobals(ty);
        }

        EXEC_DEPTH += 1;
        LOG("vm_exec(): ==> %d", EXEC_DEPTH);

        CO_LOG("============== vm_exec() ==============", TERM(91;1), "%d", EXEC_DEPTH);

        if (UNLIKELY(DeoptTryBase >= 0)) {
                isize k = DeoptTryBase;
                DeoptTryBase = -1;
                for (; k < vN(TRY_STACK); ++k) {
                        _try = v__(TRY_STACK, k);
                        _try->ed = EXEC_DEPTH;
                        if (ty_setjmp(_try->jb) != 0) {
                                ty = _ty;
                                goto NextInstruction;
                        }
                }
        }

        for (;;) {
NextInstruction:
                CheckFlags(ty, IP);
                //XXLOG("stack=%zu, instruction = %s", vN(STACK), GetInstructionName(*IP));

                switch ((u8)*IP++) {
                CASE(NOP)
                        continue;
                CASE(LOAD_LOCAL)
                        READVALUE(n);
#ifndef TY_NO_LOG
                        LOG("Loading local: %s (%d)", IP, n);
                        SKIPSTR();
#endif
                        //LOGX("LOAD_LOCAL[%d] (%jd): %s", n, local(ty, n) - vv(STACK), VSC(local(ty, n)));
                        push(*local(ty, n));
                        break;

                CASE(LOAD_REF)
                        READVALUE(n);
#ifndef TY_NO_LOG
                        LOG("Loading ref: %s (%d)", IP, n);
                        SKIPSTR();
#endif
                        v = *local(ty, n);
                        while (v.type == VALUE_REF) {
                                v = *v.ref;
                        }
                        push(v);
                        break;

                CASE(LOAD_CAPTURED)
                        READVALUE(n);
#ifndef TY_NO_LOG
                        LOG("Loading capture: %s (%d) of %s", IP, n, VSC(ActiveFun(ty)));
                        SKIPSTR();
#endif
                        push(*ActiveFun(ty)->env[n]);
                        break;

                CASE(LOAD_GLOBAL)
                        READVALUE(n);
#ifndef TY_NO_LOG
                        LOG("Loading global: %s (%d)", IP, n);
                        SKIPSTR();
#endif
                        push(v__(Globals, n));
                        break;

                CASE(LOAD_THREAD_LOCAL)
                        READVALUE(n);
#ifndef TY_NO_LOG
                        LOG("Loading thread-local: %s (%d)", IP, n);
                        SKIPSTR();
#endif
                        EnsureThreadLocal(ty, n);
                        push(v__(THREAD_LOCALS, n));
                        break;

                CASE(CHECK_INIT)
                        if (top()->type == VALUE_UNINITIALIZED) {
                                // This will panic
                                VSC(top());
                        }
                        break;

                CASE(CAPTURE)
                        READVALUE(i);
                        READVALUE(j);
                        vp = mAo(sizeof (Value), GC_VALUE);
                        *vp = *local(ty, i);
                        *local(ty, i) = REF(vp);
                        ActiveFun(ty)->env[j] = vp;
                        break;

                CASE(DECORATE)
                        READVALUE(s);
                        if (top()->type == VALUE_FUNCTION) {
                                top()->xinfo = (FunUserInfo *)s;
                        }
                        break;

                CASE(BIND_CLASS)
                        READVALUE(n);
                        *top() = BindMethod(ty, top(), &CLASS(n));
                        break;

                CASE(INTO_METHOD)
                        READVALUE(i);
                        if (top()->type != VALUE_FUNCTION) {
                                zP("method decorator returned non-function: %s", VSC(top()));
                        }
                        *top() = IntoMethod(ty, top(), i);
                        break;

                CASE(EXEC_CODE)
                        READVALUE(s);
                        vm_exec(ty, (char *) s);
                        break;

                CASE(DUP)
                        push(peek());
                        break;

                CASE(DUP2_SWAP)
                        push(top()[0]);
                        push(top()[-2]);
                        break;

                CASE(JUMP)
                        READVALUE(n);
                        IP += n;
                        if (n < 0) {
                                vm_osr(ty);
                        }
                        break;

                CASE(JUMP_IF)
                        READVALUE(n);
                        v = pop();
                        if (value_truthy(ty, &v)) {
                                IP += n;
                        }
                        break;

                CASE(JUMP_IF_NOT)
                        READVALUE(n);
                        v = pop();
                        if (!value_truthy(ty, &v)) {
                                IP += n;
                        }
                        break;

                CASE(JUMP_IF_NONE)
                        READVALUE(n);
                        if (top()->type == VALUE_NONE) {
                                IP += n;
                        }
                        break;

                CASE(JUMP_IF_NIL)
                        READVALUE(n);
                        v = pop();
                        if (v.type == VALUE_NIL) {
                                IP += n;
                        }
                        break;

                CASE(JUMP_IF_INIT)
                        READVALUE(n);
                        if (GetSelf(ty).object->init) {
                                IP += n;
                        } else {
                                GetSelf(ty).object->init = true;
                        }
                        break;

                CASE(JUMP_IF_TYPE)
                        READJUMP(jump);
                        READVALUE(z);
                        if (top()->type == z) {
                                DOJUMP(jump);
                        }
                        break;

                CASE(JLE)
                        READVALUE(n);
                        DoLeq(ty);
                        if (pop().boolean) {
                                IP += n;
                        }
                        break;

                CASE(JLT)
                        READVALUE(n);
                        DoLt(ty);
                        if (pop().boolean) {
                                IP += n;
                        }
                        break;

                CASE(JGE)
                        READVALUE(n);
                        DoGeq(ty);
                        if (pop().boolean) {
                                IP += n;
                        }
                        break;

                CASE(JGT)
                        READVALUE(n);
                        DoGt(ty);
                        if (pop().boolean) {
                                IP += n;
                        }
                        break;

                CASE(JEQ)
                        READVALUE(n);
                        DoEq(ty);
                        if (pop().boolean) {
                                IP += n;
                        }
                        break;

                CASE(JNE)
                        READVALUE(n);
                        DoNeq(ty);
                        if (pop().boolean) {
                                IP += n;
                        }
                        break;

                CASE(JII)
                        READJUMP(jump);
                        READVALUE(z);
                        if (z < 0) {
                                v = pop();
                                z = -z;
                        } else {
                                v = peek();
                        }
                        if (class_is_subclass(ty, ClassOf(&v), z)) {
                                DOJUMP(jump);
                        }
                        break;

                CASE(JNI)
                        READJUMP(jump);
                        READVALUE(z);
                        if (z < 0) {
                                v = pop();
                                z = -z;
                        } else {
                                v = peek();
                        }
                        if (!class_is_subclass(ty, ClassOf(&v), z)) {
                                DOJUMP(jump);
                        }
                        break;

                CASE(JUMP_AND)
                        READVALUE(n);
                        if (value_truthy(ty, top())) {
                                pop();
                        } else {
                                IP += n;
                        }
                        break;

                CASE(JUMP_OR)
                        READVALUE(n);
                        if (value_truthy(ty, top())) {
                                IP += n;
                        } else {
                                pop();
                        }
                        break;

                CASE(JUMP_WTF)
                        READVALUE(n);
                        if (top()->type == VALUE_NIL) {
                                pop();
                        } else {
                                IP += n;
                        }
                        break;

                CASE(SKIP_CHECK)
                        READVALUE(n);
                        if (!TY_IS_INITIALIZED) {
                                IP += n;
                                *top() = BOOLEAN(true);
                        }
                        break;

                CASE(TARGET_GLOBAL)
                        READVALUE(n);
                        LOG("Global: %d", (int)n);
                        while (vN(Globals) <= n) {
                                xvP(Globals, NIL);
                        }
                        pushtarget(v_(Globals, n), NULL);
                        break;

                CASE(TARGET_THREAD_LOCAL)
                        READVALUE(n);
                        EnsureThreadLocal(ty, n);
                        pushtarget(v_(THREAD_LOCALS, n), NULL);
                        break;

                CASE(TARGET_LOCAL)
                        READVALUE(n);
                        LOG("Targeting %d (%zu frames)", n, vN(FRAMES));
                        pushtarget(local(ty, n), NULL);
                        break;

                CASE(ASSIGN_GLOBAL)
                        READVALUE(n);
                        LOG("Global: %d", (int)n);
                        while (vN(Globals) <= n) {
                                xvP(Globals, NIL);
                        }
                        *v_(Globals, n) = pop();
                        break;

                CASE(ASSIGN_LOCAL)
                        READVALUE(n);
                        LOG("Targeting %d", n);
                        *local(ty, n) = pop();
                        break;

                CASE(ASSIGN_SUBSCRIPT)
                        n = *IP++;
                        DoAssignSubscript(ty, n, false);
                        break;

                CASE(TARGET_REF)
                        READVALUE(n);
                        vp = local(ty, n);
                        if (vp->type == VALUE_REF) {
                                pushtarget((Value *)vp->ptr, NULL);
                        } else {
                                pushtarget(vp, NULL);
                        }
                        break;

                CASE(TARGET_CAPTURED)
                        READVALUE(n);
#ifndef TY_NO_LOG
                        LOG("Loading capture: %s (%d) of %s", IP, n, VSC(ActiveFun(ty)));
                        SKIPSTR();
#endif
                        pushtarget(ActiveFun(ty)->env[n], NULL);
                        break;

                CASE(TARGET_MEMBER)
                        READVALUE(z);
TargetMember:
                        if (!TargetFieldFast(ty, top(), z)) {
                                DoTargetMember(ty, peek(), z);
                        }
                        pop();
                        break;

                CASE(TARGET_SELF_MEMBER)
                        READVALUE(z);
                        v = GetSelf(ty);
                        if (!TargetFieldFast(ty, &v, z)) {
                                DoTargetMember(ty, v, z);
                        }
                        break;

                CASE(TARGET_SELF_STATIC)
                        READVALUE(z);
                        value = GetSelf(ty);
                        DoTargetMember(ty, CLASS(ClassOf(&value)), z);
                        break;

                CASE(TARGET_STATIC_MEMBER)
                        READVALUE(i);
                        READVALUE(z);
                        value = CLASS(i);
                        DoTargetMember(ty, value, z);
                        break;

                CASE(TARGET_SUBSCRIPT)
                        DoTargetSubscript(ty);
                        break;

                CASE(INC)
                        IncValue(ty, top());
                        break;

                CASE(DEC)
                        DecValue(ty, top());
                        break;

                CASE(ASSIGN)
                        DoAssign(ty);
                        break;

                CASE(TAG_PUSH)
                        READVALUE(tag);
                        top()->tags = tags_push(ty, top()->tags, tag);
                        top()->type |= VALUE_TAGGED;
                        break;

                CASE(ARRAY_REST)
                        READJUMP(jump);
                        READVALUE(i);
                        READVALUE(j);
                        if (top()->type != VALUE_ARRAY || vN(*top()->array) < i + j) {
                                DOJUMP(jump);
                        } else {
                                Array *rest = vA();
                                uvPn(*rest, vv(*top()->array) + i, vN(*top()->array) - (i + j));
                                *poptarget() = ARRAY(rest);
                        }
                        break;

                CASE(TUPLE_REST)
                        READJUMP(jump);
                        READVALUE(i);
                        vp = poptarget();
                        if (top()->type != VALUE_TUPLE) {
                                DOJUMP(jump);
                        } else {
                                i32 count = top()->count - i;
                                Value *rest = mAo(count * sizeof (Value), GC_TUPLE);
                                memcpy(rest, top()->items + i, count * sizeof (Value));
                                *vp = TUPLE(rest, NULL, count);
                        }
                        break;

                CASE(RECORD_REST)
                        READJUMP(jump);
                        if (top()->type != VALUE_TUPLE) {
                                DOJUMP(jump);
                        } else {
                                v = peek();

                                vec(i32) ids = {0};
                                vec(i32) indices = {0};

                                SCRATCH_SAVE();

                                IP = ALIGNED_FOR(i32, IP);

                                for (i32 i = 0; i < v.count; ++i) {
                                        if (v.ids == NULL || v.ids[i] == -1) {
                                                continue;
                                        }
                                        if (!search_i32((i32 const *)IP, v.ids[i])) {
                                                svP(ids, v.ids[i]);
                                                svP(indices, i);
                                        }
                                }

                                value = vT(ids.count);
                                value.ids = uAo(value.count * sizeof (i32), GC_TUPLE);

                                memcpy(value.ids, vv(ids), value.count * sizeof (i32));

                                for (i32 i = 0; i < value.count; ++i) {
                                        value.items[i] = v.items[v__(indices, i)];
                                }

                                SCRATCH_RESTORE();

                                *poptarget() = value;

                                while (*(i32 const *)IP != -1) {
                                        IP += sizeof (i32);
                                }

                                IP += sizeof (i32);
                        }
                        break;

                CASE(THROW_IF_NIL)
                        if (UNLIKELY(top()->type == VALUE_NIL)) {
                                MatchError;
                        }
                        break;

                CASE(PUSH_UNTAGGED)
                        push(peek());
                        PopTag(top());
                        break;

                CASE(UNTAG_OR_DIE)
                        READVALUE(tag);
                        if (UNLIKELY(!tags_same(ty, tags_first(ty, top()->tags), tag))) {
                                MatchError;
                        } else {
                                PopTag(top());
                        }
                        break;

                CASE(STEAL_TAG)
                        vp = poptarget();
                        if (LIKELY(top()->type & VALUE_TAGGED)) {
                                *vp = TAG(tags_first(ty, top()->tags));
                                PopTag(top());
                        } else {
                                MatchError;
                        }
                        break;

                CASE(TRY_STEAL_TAG)
                        READVALUE(n);
                        vp = poptarget();
                        if (top()->tags > 0) {
                                *vp = TAG(tags_first(ty, top()->tags));
                                PopTag(top());
                        } else {
                                IP += n;
                        }
                        break;

                CASE(BAD_MATCH)
                        MatchError;

                CASE(BAD_DISPATCH);
                        if (v_L(CALLS) == unapply) {
                                push(NONE);
                                goto RETURN;
                        } else {
                                push(TAG(TAG_DISPATCH_ERR));
                                vXx(FRAMES);
                                IP = vXx(CALLS);
                                RaiseException(ty);
                        }
                        break;

                CASE(BAD_CALL)
                        v = peek();
                        READSTR(str);
                        if (v_L(CALLS) == unapply) {
                                *top() = NONE;
                                goto RETURN;
                        }
                        zP(
                                "constraint on %s%s%s%s%s violated in call to %s%s%s%s%s: %s%s%s = %s%s%s",
                                TERM(34),
                                TERM(1),
                                IP,
                                TERM(22),
                                TERM(39),

                                TERM(34),
                                TERM(1),
                                str,
                                TERM(22),
                                TERM(39),

                                TERM(34),
                                TERM(1),
                                IP,
                                VSC(&v),
                                TERM(22),
                                TERM(39)
                        );
                        break;

                CASE(BAD_ASSIGN)
                        v = peek();
                        str = IP;
                        zP(
                                "constraint on %s%s%s%s%s violated in assignment: %s%s%s = %s%s%s",
                                TERM(34),
                                TERM(1),
                                IP,
                                TERM(22),
                                TERM(39),

                                TERM(34),
                                TERM(1),
                                IP,
                                VSC(&v),
                                TERM(22),
                                TERM(39)
                        );
                        break;

                CASE(THROW)
                        RaiseException(ty);
                        break;

                CASE(RETHROW)
                {
                        _try = GetCurrentTry(ty);
                        _try->state = TRY_THROW;
                        _try->end = NULL;
                        IP = _try->finally;
                        break;
                }

                CASE(FINALLY)
                {
                        _try = GetCurrentTry(ty);
                        _try->state = TRY_FINALLY;
                        _try->end = IP;
                        IP = _try->finally;
                        break;
                }

                CASE(END_TRY)
                {
                        _try = vXx(TRY_STACK);
                        if (_try->end == NULL) {
                                DoThrow(ty);
                        } else {
                                IP = _try->end;
                        }
                        break;
                }

                CASE(CATCH)
                        PopThrowCtx(ty);
                        v_L(TRY_STACK)->state = TRY_FINALLY;
                        break;

                CASE(POP_TRY)
                        _try = vXx(TRY_STACK);
                        if (_try->end == NULL) {
                                PopThrowCtx(ty);
                        }
                        break;

                CASE(TRY)
                {
                        _try = PushTry(ty);

                        if (ty_setjmp(_try->jb) != 0) {
                                ty = _ty;
                                break;
                        }

                        READVALUE(n);
                        _try->catch = IP + n;

                        READVALUE(n);
                        _try->finally = (n == -1) ? NULL : IP + n;

                        READVALUE(n);
                        _try->end = (n == -1) ? NULL : IP + n;
                        break;
                }

                CASE(TRACE)
                        push(ResolveTrace(ty, CurrentThrowCtx(ty)));
                        break;

                CASE(DROP)
                        DoDrop(ty);
                        break;

                CASE(DISCARD_DROP_GROUP)
                        vXx(DROP_STACK);
                        break;

                CASE(PUSH_DROP_GROUP)
                        xvP(DROP_STACK, ARRAY(vA()));
                        break;

                CASE(PUSH_DROP)
                        if (vN(DROP_STACK) == 0) {
                                zP("no active drop group for resource binding");
                        }
                        uvP(*vvL(DROP_STACK)->array, peek());
                        break;

                CASE(PUSH_DEFER_GROUP)
                        GetCurrentTry(ty)->clean = true;
                        break;

                CASE(DEFER)
                        _try = GetDeferTry(ty);
                        xvP(_try->defer, pop());
                        break;

                CASE(CLEANUP)
                        _try = *vvL(TRY_STACK);
                        while (vN(_try->defer) > 0) {
                                v = vXx(_try->defer);
                                vmC(&v, 0);
                        }
                        break;

                CASE(ENTER)
                        if ((z = ClassOf(top())) < 0) {
                                break;
                        }
                        if (vN(DROP_STACK) == 0) {
                                zP("no active drop group for enter instruction");
                        }
                        uvP(*vvL(DROP_STACK)->array, peek());
                        if ((vp = class_lookup_method_i(ty, z, NAMES._enter_)) != NULL) {
                                v = pop();
                                call(ty, vp, &v, 0, NULL);
                        }
                        break;

                CASE(ENSURE_LEN)
                        READJUMP(jump);
                        READVALUE(i);
                        if (top()->type != VALUE_ARRAY || top()->array->count > i) {
                                DOJUMP(jump);
                        }
                        break;

                CASE(ENSURE_LEN_TUPLE)
                        READJUMP(jump);
                        READVALUE(i);
                        if (top()->type != VALUE_TUPLE || top()->count > i) {
                                DOJUMP(jump);
                        }
                        break;

                CASE(MATCH_TAG)
                        DoMatchTag(ty);
                        break;

                CASE(MATCH_STRING)
                        DoMatchString(ty);
                        break;

                CASE(ENSURE_EQUALS_VAR)
                        READVALUE(n);
                        v = pop();
                        if (!v_eq(top(), &v)) {
                                IP += n;
                        }
                        break;

                CASE(TRY_ASSIGN_NON_NIL)
                        READVALUE(n);
                        vp = poptarget();
                        if (top()->type == VALUE_NIL) {
                                IP += n;
                        } else {
                                *vp = peek();
                        }
                        break;

                CASE(TRY_RANGE)
                {
                        READJUMP(jump);
                        Value hi = pop();
                        Value lo = pop();
                        if (value_compare(ty, top(), &lo) < 0 || value_compare(ty, top(), &hi) >= 0) {
                                DOJUMP(jump);
                        }
                        break;
                }

                CASE(TRY_INCRANGE)
                {
                        READJUMP(jump);
                        Value hi = pop();
                        Value lo = pop();
                        if (value_compare(ty, top(), &lo) < 0 || value_compare(ty, top(), &hi) > 0) {
                                DOJUMP(jump);
                        }
                        break;
                }

                CASE(TRY_REGEX)
                        READJUMP(jump);
                        READVALUE(s);
                        v = peek();
                        push(REGEX((Regex *)s));
                        if (
                                (v.type == VALUE_STRING)
                             && ((value = string_match(ty, &v, 1, NULL)).type != VALUE_NIL)
                        ) {
                                *top() = value;
                        } else {
                                pop();
                                DOJUMP(jump);
                        }
                        break;

                CASE(ASSIGN_REGEX_MATCHES)
                        READVALUE(n);
                        vp = poptarget();
                        v = pop();
                        if (v.type == VALUE_ARRAY) {
                                for (i = 0; i < vN(*v.array); ++i) {
                                        vp[i] = v__(*v.array, i);
                                }
                                while (i < n + 1) {
                                        vp[i++] = NIL;
                                }
                        } else {
                                *vp = v;
                        }
                        break;

                CASE(ENSURE_DICT)
                        READVALUE(n);
                        if (top()->type != VALUE_DICT) {
                                IP += n;
                        }
                        break;

                CASE(ENSURE_CONTAINS)
                        READVALUE(n);
                        v = pop();
                        if (!dict_has_value(ty, top()->dict, &v)) {
                                IP += n;
                        }
                        break;

                CASE(ENSURE_SAME_KEYS)
                        READVALUE(n);
                        v = pop();
                        if (!dict_same_keys(ty, top()->dict, v.dict)) {
                                IP += n;
                        }
                        break;

                CASE(TRY_INDEX)
                        READJUMP(jump);
                        READVALUE(i);
                        READVALUE(b);
                        if (top()->type != VALUE_ARRAY) {
                                DOJUMP(jump);
                                break;

                        }
                        if (i < 0) {
                                i += vN(*top()->array);
                        }
                        if (vN(*top()->array) <= i) {
                                if (b) {
                                        DOJUMP(jump);
                                } else {
                                        push(NIL);
                                }
                        } else {
                                push(v__(*top()->array, i));
                        }
                        break;

                CASE(INDEX_TUPLE)
                        READJUMP(jump);
                        READVALUE(i);
                        if (top()->type != VALUE_TUPLE || top()->count <= i) {
                                DOJUMP(jump);
                        } else {
                                push(top()->items[i]);
                        }
                        break;

                CASE(TRY_INDEX_TUPLE)
                        READJUMP(jump);
                        READVALUE(i);
                        if (top()->type != VALUE_TUPLE) {
                                DOJUMP(jump);
                        } else if (i < top()->count) {
                                push(top()->items[i]);
                        } else {
                                push(NIL);
                        }
                        break;

                CASE(TRY_TUPLE_MEMBER)
                        READJUMP(jump);
                        READVALUE(b);
                        READVALUE(z);
                        if (top()->type != VALUE_TUPLE) {
                                DOJUMP(jump);
                                break;

                        }
                        if (top()->ids != NULL) for (int i = 0; i < top()->count; ++i) {
                                if (top()->ids[i] == z) {
                                        push(top()->items[i]);
                                        goto NextInstruction;
                                }
                        }
                        if (!b) {
                                push(NIL);
                                goto NextInstruction;
                        }
                        DOJUMP(jump);
                        break;

                CASE(TRY_TAG_POP)
                        READJUMP(jump);
                        READVALUE(tag);
                        if (!TryUnwrap(top(), tag)) {
                                DOJUMP(jump);
                        }
                        break;

                CASE(POP)
                        pop();
                        break;

                CASE(POP2)
                        pop();
                        pop();
                        break;

                CASE(UNPOP)
                        STACK.count += 1;
                        break;

                CASE(DROP2)
                        v = v_L(STACK);
                        STACK.count -= 2;
                        v_L(STACK) = v;
                        break;

                CASE(INT8)
                        push(INTEGER((i8)*IP++));
                        break;

                CASE(INTEGER)
                        READVALUE(k);
                        push(INTEGER(k));
                        break;

                CASE(REAL)
                        READVALUE(x);
                        push(REAL(x));
                        break;

                CASE(TRUE)
                        push(BOOLEAN(true));
                        break;

                CASE(FALSE)
                        push(BOOLEAN(false));
                        break;

                CASE(STRING)
                        READVALUE(n);
                        DoStringLiteral(ty, n);
                        break;

                CASE(CLASS)
                        READVALUE(tag);
                        push(CLASS(tag));
                        break;

                CASE(TAG)
                        READVALUE(tag);
                        push(TAG(tag));
                        break;

                CASE(REGEX)
                        READVALUE(s);
                        v = REGEX((struct regex const *) s);
                        push(v);
                        break;

                CASE(ARRAY0)
                        push(ARRAY(vA()));
                        break;

                CASE(ARRAY)
                        n = vN(STACK) - vXx(SP_STACK);
                        v = ARRAY(vAn(n));
                        v.array->count = n;
                        memcpy(vv(*v.array), topN(n), n * sizeof (Value));
                        STACK.count -= n;
                        push(v);
                        break;

                CASE(TUPLE)
                        READVALUE(n);
                        READVALUE(s);
                        v = (Value) {
                                .type = VALUE_TUPLE,
                                .count = n,
                                .ids = (i32 *)s,
                                .items = mAo(n * sizeof (Value), GC_TUPLE)
                        };
                        memcpy(v.items, topN(n), n * sizeof (Value));
                        STACK.count -= n;
                        push(v);
                        break;

                CASE(XTUPLE)
                        DoTupleLiteral(ty);
                        break;

                CASE(GATHER_TUPLE)
                        n = vN(STACK) - vXx(SP_STACK);
                        vp = mAo(n * sizeof (Value), GC_TUPLE);
                        v = TUPLE(vp, NULL, n);
                        __builtin_memcpy(vp, topN(n), n * sizeof (Value));
                        STACK.count -= n;
                        push(v);
                        break;

                CASE(DICT)
                        n = vN(STACK) - vXx(SP_STACK);
                        DoDictLiteral(ty, n, NULL);
                        break;

                CASE(DEFAULT_DICT)
                        value = pop();
                        n = vN(STACK) - vXx(SP_STACK);
                        DoDictLiteral(ty, n, &value);
                        break;

                CASE(SET)
                        n = vN(STACK) - vXx(SP_STACK);
                        DoSetLiteral(ty, n);
                        break;

                CASE(NIL)
                        push(NIL);
                        break;

                CASE(TO_REGEX)
                        if (top()->type == VALUE_REGEX) {
                                put(vSsz(top()->regex->pattern));
                                break;
                        }
                        if (UNLIKELY(top()->type == VALUE_PTR)) {
                                put(value_vshow_color(ty, top(), 0));
                        } else if (top()->type != VALUE_NIL) {
                                CallMethod(ty, NAMES._str_, 0, 0, false, false);
                        }
                        put(builtin_regex_escape(ty, 1, NULL));
                        break;

                CASE(YIELD)
                        DoYield(ty);
                        ty = MyTy;
                        CheckInterrupt(ty);
                        break;

                CASE(YIELD_NONE)
                        if (vN(FRAMES) == 1) {
                                co_retire(ty);
                                CheckInterrupt(ty);
                        } else {
                                push(NIL);
                                goto RETURN;
                        }
                        break;

                CASE(YIELD_SOME)
                        put(Some(peek()));
                        DoYield(ty);
                        CheckInterrupt(ty);
                        break;

                CASE(TYPE)
                        READVALUE(s);
                        push(TYPE((T2Type)s));
                        break;

                CASE(VALUE)
                        READVALUE(s);
                        push(*(Value *)s);
                        break;

                CASE(EVAL)
                        READVALUE(s);
                        push(PTR((void *)s));
                        v = builtin_eval(ty, 2, NULL);
                        pop();
                        put(v);
                        break;

                CASE(RENDER_TEMPLATE)
                        READVALUE(s);
                        push(compiler_render_template(ty, (Expr *)s));
                        break;

                CASE(TRAP)
#ifdef _WIN32
                        __debugbreak();
#else
                        *(volatile char *)0 = 0;
#endif
                        break;

                CASE(TRAP_TY)
                        IP -= 1;
                        DebugTrap(ty, IP);
                        break;

                CASE(GET_NEXT)
                        IterGetNext(ty, false);
                        break;

                CASE(LOOP_ITER)
                        push(SENTINEL);
                        IterGetNext(ty, false);
                        break;

                CASE(ARRAY_COMPR)
                        READVALUE(i);
                        n = vN(STACK) - vXx(SP_STACK);
                        v = top()[-(n + i)];
                        vvPn(*v.array, topN(n), n);
                        STACK.count -= n;
                        break;

                CASE(DICT_COMPR)
                        READVALUE(i);
                        READVALUE(n);
                        v = top()[-(2*n + i)];
                        for (isize i = 0; i < n; ++i) {
                                value = top()[-2*i];
                                key = top()[-(2*i + 1)];
                                dict_put_value(ty, v.dict, key, value);
                        }
                        STACK.count -= 2*n;
                        break;

                CASE(SET_COMPR)
                        READVALUE(i);
                        n = vN(STACK) - vXx(SP_STACK);
                        DoSetCompr(ty, i, n);
                        break;

                CASE(LOOP_CHECK)
                        READJUMP(jump);
                        READVALUE(z);
                        LoopCheck(ty, z, jump);
                        break;

                CASE(SPREAD_CHECK)
                        READJUMP(jump);
                        READVALUE(b);
                        if (vm_jit_spread_check(ty, b)) {
                                DOJUMP(jump);
                        }
                        break;

                CASE(PUSH_INDEX)
                        READVALUE(n);
                        push(INDEX(0, 0, n));
                        break;

                CASE(READ_INDEX)
                        k = top()[-3].z - 1;
                        push(INTEGER(k));
                        break;

                CASE(SENTINEL)
                        push(SENTINEL);
                        break;

                CASE(NONE)
                        push(NONE);
                        break;

                CASE(NONE_IF_NIL)
                        YieldFix(ty);
                        break;

                CASE(NONE_IF_NOT)
                        READJUMP(jump);
                        if (!value_truthy(ty, top())) {
                                *top() = NONE;
                                DOJUMP(jump);
                        } else {
                                pop();
                        }
                        break;

                CASE(FIX_EXTRA)
                        for (n = 0; top()[-n].type != VALUE_SENTINEL; ++n) {
                                ;
                        }
                        for (i = 0, j = n - 1; i < j; ++i, --j) {
                                v = top()[-i];
                                top()[-i] = top()[-j];
                                top()[-j] = v;
                        }
                        break;

                CASE(FIX_TO)
                        READVALUE(n);
                        for (i = 0; top()[-i].type != VALUE_SENTINEL; ++i) {
                                ;
                        }
                        while (i > n) {
                                --i, pop();
                        }
                        while (i < n) {
                                ++i, push(NIL);
                        }
                        for (i = 0, j = n - 1; i < j; ++i, --j) {
                                v = top()[-i];
                                top()[-i] = top()[-j];
                                top()[-j] = v;
                        }
                        break;

                CASE(SWAP)
                        swap();
                        break;

                CASE(REVERSE)
                        READVALUE(n);
                        for (--n, i = 0; i < n; ++i, --n) {
                                v = top()[-i];
                                top()[-i] = top()[-n];
                                top()[-n] = v;
                        }
                        break;

                CASE(JUMP_IF_SENTINEL)
                        READVALUE(n);
                        if (top()->type == VALUE_SENTINEL) {
                                IP += n;
                        }
                        break;

                CASE(CLEAR_EXTRA)
                        while (top()->type != VALUE_SENTINEL) {
                                pop();
                        }
                        pop();
                        break;

                CASE(PUSH_NTH)
                        READVALUE(n);
                        push(top()[-n]);
                        break;

                CASE(PUSH_ARRAY_ELEM)
                        READVALUE(n);
                        READVALUE(b);
                        if (UNLIKELY(top()->type != VALUE_ARRAY)) {
                                MatchError;
                                zP("attempt to destructure non-array as array in assignment");
                        }
                        if (n < 0) {
                                n += top()->array->count;
                        }
                        if (n >= top()->array->count) {
                                if (b) {
                                        MatchError;
                                        zP("element index out of range in destructuring assignment");
                                } else {
                                        push(NIL);
                                }
                        } else {
                                push(top()->array->items[n]);
                        }
                        break;

                CASE(PUSH_TUPLE_ELEM)
                        READVALUE(n);
                        if (UNLIKELY(top()->type != VALUE_TUPLE)) {
                                zP(
                                        "attempt to destructure non-tuple as tuple in assignment: %s",
                                        VSC(top())
                                );
                        }
                        if (UNLIKELY(n >= top()->count)) {
                                zP(
                                        "elment index %d out of range in destructuring assignment: %s",
                                        n,
                                        VSC(top())
                                );
                        }
                        push(top()->items[n]);
                        break;

                CASE(PUSH_TUPLE_MEMBER)
                        READVALUE(b);
                        READVALUE(z);

                        v = peek();

                        if (UNLIKELY(v.type != VALUE_TUPLE || v.ids == NULL)) {
                                BadFieldAccess(ty, &v, z);
                        }

                        for (int i = 0; i < v.count; ++i) {
                                if (v.ids[i] == z) {
                                        push(v.items[i]);
                                        goto NextInstruction;
                                }
                        }

                        if (!b) {
                                push(NIL);
                                goto NextInstruction;
                        }

                        BadFieldAccess(ty, &v, z);

                CASE(CONCAT_STRINGS)
                        READVALUE(n);
                        vm_concat_strings(ty, n);
                        break;

                CASE(COMPILE_REGEX)
                        push(xSz(IP));
                        SKIPSTR();
                        v = builtin_regex(ty, 2, NULL);
                        pop();
                        put(v);
                        break;

                CASE(RANGE)
                        DoRange(ty, false);
                        break;

                CASE(INCRANGE)
                        DoRange(ty, true);
                        break;

                CASE(TRY_GET_MEMBER)
                        z = GetDynamicMemberId(ty, false);
                        if (z >= 0) {
                                goto SafeMemberAccess;
                        } else {
                                *top() = NIL;
                        }
                        break;

                CASE(GET_MEMBER)
                        z = GetDynamicMemberId(ty, true);
                        if (z < 0) {
                                z = -(z + 1);
                        }
                        goto MemberAccess;

                CASE(TARGET_DYN_MEMBER)
                        z = GetDynamicMemberId(ty, true);
                        if (z < 0) {
                                z = -(z + 1);
                        }
                        goto TargetMember;

                CASE(SELF_MEMBER_ACCESS)
                        READVALUE(z);

                        push(GetSelf(ty));

                        if (UNLIKELY(IsNone((v = LoadFieldFast(ty, z))))) {
                                v = GetMember(ty, z, true, false);
                        }

                        switch (v.type) {
                        case VALUE_BREAK:
                                continue;

                        case VALUE_NONE:
                                xpush(GetSelf(ty));
                                BadFieldAccess(ty, top(), z);
                                UNREACHABLE();

                        default:
                                xpush(v);
                                continue;
                        }
                        break;

                CASE(SELF_STATIC_ACCESS)
                        READVALUE(z);

                        v = GetSelf(ty);
                        push(CLASS(ClassOf(&v)));
                        v = GetMember(ty, z, false, false);

                        switch (v.type) {
                        case VALUE_BREAK:
                                continue;

                        default:
                                xpush(v);
                                continue;
                        }
                        break;

                CASE(STATIC_MEMBER_ACCESS)
                        READVALUE(i);
                        READVALUE(z);

                        push(CLASS(i));
                        v = GetMember(ty, z, false, false);

                        switch (v.type) {
                        case VALUE_BREAK:
                                continue;

                        default:
                                xpush(v);
                                continue;
                        }
                        break;

                CASE(TRY_MEMBER_ACCESS)
                        READVALUE(z);
SafeMemberAccess:
                        v = GetMember(ty, z, true, false);

                        switch (v.type) {
                        case VALUE_BREAK:
                                break;

                        case VALUE_NONE:
                                xpush(NIL);
                                break;

                        default:
                                xpush(v);
                                break;
                        }
                        break;

                CASE(MEMBER_ACCESS)
                        READVALUE(z);
MemberAccess:
                        if (IsNone((v = LoadFieldFast(ty, z)))) {
                                v = GetMember(ty, z, true, false);
                        }

                        switch (v.type) {
                        case VALUE_BREAK:
                                break;

                        default:
                                xpush(v);
                                break;
BadField:
                        case VALUE_NONE:
                                xpush(*vZ(STACK));
                                BadFieldAccess(ty, top(), z);
                                UNREACHABLE();
                        }
                        break;

                CASE(TRY_MEMBER)
                        READJUMP(jump);
                        READVALUE(z);

                        push(peek());
                        v = GetMember(ty, z, false, false);

                        switch (v.type) {
                        case VALUE_BREAK:
                                break;

                        case VALUE_NONE:
                                DOJUMP(jump);
                                continue;

                        default:
                                xpush(v);
                                continue;
                        }
                        break;

                CASE(SLICE)
                        CallMethod(ty, NAMES.slice, 3, 0, false, false);
                        break;

                CASE(SUBSCRIPT)
                        DoSubscript(ty, false);
                        break;

                CASE(SAFE_SUBSCRIPT)
                        DoSafeSubscript(ty, false);
                        break;

                CASE(NOT)
                        DoNot(ty);
                        break;

                CASE(QUESTION)
                        DoQuestion(ty, false);
                        break;

                CASE(NEG)
                        DoNeg(ty, false);
                        break;

                CASE(COUNT)
                        DoCount(ty, false);
                        break;

                CASE(ADD)
                        if (!op_builtin_add(ty)) {
                                n = OP_ADD;
                                goto BinaryOp;
                        }
                        break;

                CASE(SUB)
                        if (!op_builtin_sub(ty)) {
                                n = OP_SUB;
                                goto BinaryOp;
                        }
                        break;

                CASE(MUL)
                        if (!op_builtin_mul(ty)) {
                                n = OP_MUL;
                                goto BinaryOp;
                        }
                        break;

                CASE(DIV)
                        if (!op_builtin_div(ty)) {
                                n = OP_DIV;
                                goto BinaryOp;
                        }
                        break;

                CASE(MOD)
                        if (!op_builtin_mod(ty)) {
                                n = OP_MOD;
                                goto BinaryOp;
                        }
                        break;

                CASE(BIT_AND)
                        if (!op_builtin_and(ty)) {
                                n = OP_BIT_AND;
                                goto BinaryOp;
                        }
                        break;

                CASE(BIT_OR)
                        if (!op_builtin_or(ty)) {
                                n = OP_BIT_OR;
                                goto BinaryOp;
                        }
                        break;

                CASE(BIT_XOR)
                        if (!op_builtin_xor(ty)) {
                                n = OP_BIT_XOR;
                                goto BinaryOp;
                        }
                        break;

                CASE(SHR)
                        if (!op_builtin_shr(ty)) {
                                n = OP_BIT_SHR;
                                goto BinaryOp;
                        }
                        break;

                CASE(SHL)
                        if (!op_builtin_shl(ty)) {
                                n = OP_BIT_SHL;
                                goto BinaryOp;
                        }
                        break;

                CASE(EQ)
                        DoEq(ty);
                        break;

                CASE(NEQ)
                        DoNeq(ty);
                        break;

                CASE(CLASS_OF)
                        put(CLASS(ClassOf(top())));
                        break;

                CASE(CHECK_MATCH)
                        DoCheckMatch(ty, false);
                        break;

                CASE(LT)
                        DoLt(ty);
                        break;

                CASE(GT)
                        DoGt(ty);
                        break;

                CASE(LEQ)
                        DoLeq(ty);
                        break;

                CASE(GEQ)
                        DoGeq(ty);
                        break;

                CASE(CMP)
                        DoCmp(ty);
                        break;

                CASE(GET_TAG)
                        v = pop();
                        if (v.tags == 0) {
                                xpush(NIL);
                        } else {
                                xpush(TAG(tags_first(ty, v.tags)));
                        }
                        break;

                CASE(PRE_INC)
                        if (UNLIKELY(SpecialTarget(ty))) {
                                zP("pre-increment applied to invalid target");
                        }
                        IncValue(ty, peektarget());
                        push(*poptarget());
                        break;

                CASE(POST_INC)
                        if (UNLIKELY(SpecialTarget(ty))) {
                                zP("pre-increment applied to invalid target");
                        }
                        push(*peektarget());
                        IncValue(ty, poptarget());
                        break;

                CASE(PRE_DEC)
                        if (UNLIKELY(SpecialTarget(ty))) {
                                zP("pre-decrement applied to invalid target");
                        }
                        DecValue(ty, peektarget());
                        push(*poptarget());
                        break;

                CASE(POST_DEC)
                        if (UNLIKELY(SpecialTarget(ty))) {
                                zP("post-decrement applied to invalid target");
                        }
                        push(*peektarget());
                        DecValue(ty, poptarget());
                        break;

                CASE(MUT_ADD)
                        DoMutAdd(ty, false);
                        break;

                CASE(MUT_MUL)
                        DoMutMul(ty, false);
                        break;

                CASE(MUT_DIV)
                        DoMutDiv(ty, false);
                        break;

                CASE(MUT_MOD)
                        DoMutMod(ty, false);
                        break;

                CASE(MUT_SUB)
                        DoMutSub(ty, false);
                        break;

                CASE(MUT_AND)
                        DoMutAnd(ty, false);
                        break;

                CASE(MUT_OR)
                        DoMutOr(ty, false);
                        break;

                CASE(MUT_XOR)
                        DoMutXor(ty, false);
                        break;

                CASE(MUT_SHL)
                        DoMutShl(ty, false);
                        break;

                CASE(MUT_SHR)
                        DoMutShr(ty, false);
                        break;

                CASE(BINARY_OP)
                        READVALUE(n);
BinaryOp:
                        DoBinaryOp(ty, n, false);
                        break;

                CASE(UNARY_OP)
                        READVALUE(n);
                        DoUnaryOp(ty, n, false);
                        break;

                CASE(DEFINE_TAG)
                {
                        int tag, super, n, c, g, s_g;
                        READVALUE(tag);
                        READVALUE(super);
                        READVALUE(n);
                        READVALUE(c);
                        READVALUE(g);
                        READVALUE(s_g);
                        while (n --> 0) {
                                v = pop();
                                tags_add_method(ty, tag, IP, v);
                                SKIPSTR();
                        }
                        while (c --> 0) {
                                v = pop();
                                tags_add_static(ty, tag, IP, v);
                                SKIPSTR();
                        }
                        if (g != 0 || s_g != 0) {
                                Class *class = tags_get_class(ty, tag);
                                InstallMethods(ty, class->i, &class->getters, g);
                                InstallMethods(ty, class->i, &class->s_getters, s_g);
                        }
                        if (super != -1) {
                                tags_copy_methods(ty, tag, super);
                        }
                        break;
                }

                CASE(DEFINE_CLASS)
                {
                        Class *class;
                        i32 class_id;

                        i32   m,   g,   s;
                        i32 s_m, s_g, s_s;

                        READVALUE(class_id);
                        READVALUE(s_m);
                        READVALUE(s_g);
                        READVALUE(s_s);
                        READVALUE(m);
                        READVALUE(g);
                        READVALUE(s);

                        class = class_get(ty, class_id);

                        InstallMethods(ty, class_id, &class->s_methods, s_m);
                        InstallMethods(ty, class_id, &class->s_getters, s_g);
                        InstallMethods(ty, class_id, &class->s_setters, s_s);
                        InstallMethods(ty, class_id, &class->methods, m);
                        InstallMethods(ty, class_id, &class->getters, g);
                        InstallMethods(ty, class_id, &class->setters, s);

                        if (class->super != NULL) {
                                Value *hook = class_lookup_s_method_i(
                                        ty,
                                        class->super->i,
                                        NAMES._init_subclass_
                                );
                                if (hook != NULL) {
                                        Value self = CLASS(class_id);
                                        call6t(ty, hook, &self, 0, NULL, hook_fix);
                                }
                        }
                        break;
                }

                CASE(INIT_STATIC_FIELD)
                {
                        Class *class;
                        i32 class_id;
                        i32 member_id;

                        READVALUE(class_id);
                        READVALUE(member_id);

                        class = class_get(ty, class_id);

                        v = pop();

                        vp = itable_get(ty, &class->s_fields, member_id);
                        if (vp->type == VALUE_REF) {
                                *vp->ref = v;
                        }
                        *vp = v;
                        break;
                }

                CASE(FUNCTION)
                        IP = DoFunction(ty, IP, FrameLocals(ty), FrameEnv(ty));
                        break;

                CASE(GENERATOR)
                        IP = DoGenerator(ty, IP, FrameLocals(ty), FrameEnv(ty));
                        break;

                CASE(PATCH_ENV)
                        READVALUE(n);
                        *top()->env[n] = *top();
                        break;

                CASE(NAMESPACE)
                        READVALUE(s);
                        push(NAMESPACE((Expr *)s));
                        break;

                CASE(BIND_INSTANCE)
                        READVALUE(n);
                        READVALUE(z);
                        if (n < 0) {
                                vp = class_lookup_method_i(ty, -n, z);
                                *top() = BindMethod(ty, vp, top());
                        } else {
                                i = FastReadOffset(ty, &OBJECT(top()->object, n), z);
                                if (i == OFF_NOT_FOUND) {
                                        vp = SuperMember(ty, class_lookup_method_i(ty, n, z), n, z, "method");
                                        *top() = BindMethod(ty, vp, top());
                                } else {
                                        switch (i >> OFF_SHIFT) {
                                        case OFF_METHOD:
                                                vp = v_(class_get(ty, n)->methods.values, i & OFF_MASK);
                                                break;

                                        case OFF_METHOD_X:
                                                vp = DecoratedSlot(top(), n, i & OFF_MASK);
                                                if (vp == NULL) {
                                                        vp = class_lookup_method_i(ty, n, z);
                                                }
                                                break;

                                        default:
                                                UNREACHABLE("BIND_INSTANCE: invalid offset type");
                                        }
                                        *top() = BindMethod(ty, vp, top());
                                }
                        }
                        break;

                CASE(BIND_GETTER)
                        READVALUE(n);
                        READVALUE(z);
                        if (n < 0) {
                                vp = class_lookup_getter_i(ty, -n, z);
                                *top() = BindMethod(ty, vp, top());
                        } else {
                                i = FastReadOffset(ty, &OBJECT(top()->object, n), z);
                                if (i == OFF_NOT_FOUND) {
                                        vp = SuperMember(ty, class_lookup_getter_i(ty, n, z), n, z, "getter");
                                        *top() = BindMethod(ty, vp, top());
                                } else {
                                        switch (i >> OFF_SHIFT) {
                                        case OFF_GETTER:
                                                vp = v_(class_get(ty, n)->getters.values, i & OFF_MASK);
                                                break;

                                        case OFF_GETTER_X:
                                                vp = DecoratedSlot(top(), n, i & OFF_MASK);
                                                if (vp == NULL) {
                                                        vp = class_lookup_getter_i(ty, n, z);
                                                }
                                                break;

                                        default:
                                                UNREACHABLE("BIND_GETTER: invalid offset type");
                                        }
                                        *top() = BindMethod(ty, vp, top());
                                }
                        }
                        break;

                CASE(BIND_SETTER)
                        READVALUE(n);
                        READVALUE(z);
                        if (n < 0) {
                                vp = class_lookup_setter_i(ty, -n, z);
                                *top() = BindMethod(ty, vp, top());
                        } else {
                                i = FastWriteOffset(ty, &OBJECT(top()->object, n), z);
                                if (i == OFF_NOT_FOUND) {
                                        vp = SuperMember(ty, class_lookup_setter_i(ty, n, z), n, z, "setter");
                                        *top() = BindMethod(ty, vp, top());
                                } else {
                                        switch (i >> OFF_SHIFT) {
                                        case OFF_SETTER:
                                                vp = v_(class_get(ty, n)->setters.values, i & OFF_MASK);
                                                break;

                                        case OFF_SETTER_X:
                                                vp = DecoratedSlot(top(), n, i & OFF_MASK);
                                                if (vp == NULL) {
                                                        vp = class_lookup_setter_i(ty, n, z);
                                                }
                                                break;

                                        default:
                                                UNREACHABLE("BIND_SETTER: invalid offset type");
                                        }
                                        *top() = BindMethod(ty, vp, top());
                                }
                        }
                        break;

                CASE(BIND_STATIC)
                        READVALUE(n);
                        READVALUE(z);
                        vp = SuperMember(ty, class_lookup_s_method_i(ty, n, z), n, z, "static method");
                        push(*vp);
                        break;

                CASE(OPERATOR)
                        READVALUE(i);
                        READVALUE(j);
                        push(OPERATOR(i, j));
                        break;

                CASE(TRY_UNAPPLY)
                        READJUMP(jump);
                        v = pop();
                        switch (v.type) {
                        case VALUE_CLASS:
                                vp = class_lookup_s_method_i(ty, v.class, NAMES.unapply);
                                if (vp != NULL) {
                                        DOJUMP(jump);
                                        push(peek());
                                        if (call(ty, vp, &CLASS(n), 1, NULL)) {
                                                xvP(CALLS, unapply);
                                        }
                                }
                                break;

                        default:
                                DOJUMP(jump);
                                push(peek());
                                if (DoCall(ty, &v, 1, 0, false)) {
                                        xvP(CALLS, unapply);
                                }
                                break;

                        }
                        break;

                CASE(UNAPPLY)
                        v = pop();
                        push(peek());
                        call6t(ty, &v, NULL, 1, NULL, unapply);
                        break;

                CASE(TAIL_CALL)
                        n = ActiveFun(ty)->info[FUN_INFO_PARAM_COUNT];

                        memcpy(
                                local(ty, 0),
                                topN(n),
                                n * sizeof (Value)
                        );

                        i = n + (ActiveFun(ty)->info[FUN_INFO_CLASS] != -1);
                        n = ActiveFun(ty)->info[FUN_INFO_BOUND];

                        for (; i < n; ++i) {
                                *local(ty, i) = NIL;
                        }

                        STACK.count = vvL(FRAMES)->fp + n;
                        count_call(ActiveFun(ty));
                        IP = code_of(ActiveFun(ty));
                        break;

                CASE(CALL)
                        v = pop();
                        READVALUE(n);
                        READVALUE(nkw);
                        DoCall(ty, &v, n, nkw, false);
                        break;

                CASE(CALL_GLOBAL)
                        READVALUE(i);
                        READVALUE(n);
                        READVALUE(nkw);
                        DoCall(ty, v_(Globals, i), n, nkw, false);
                        break;

                CASE(TRY_YIELD_FROM)
                        READJUMP(jump);
                        if (UNLIKELY(
                                (top()->type != VALUE_GENERATOR)
                             || ((top()->gen->co != NULL) | (u8)(top()->gen->st == NULL))
                        )) {
                                break;
                        }
                        v = pop();
                        xvP(FRAMES, v_0(v.gen->st->frames));
                        vvL(FRAMES)->fp = vN(STACK);
                        xvPn(STACK, v_(v.gen->st->stack, 1), vN(v.gen->st->stack) - 1);
                        if (v.gen->ip != code_of(&v.gen->f)) {
                                push(NIL);
                        }
                        xvP(ty->co_states, v.gen->st);
                        v.gen->st = NULL;
                        DOJUMP(jump);
                        xvP(CALLS, IP);
                        IP = v.gen->ip;
                        break;

                CASE(TRY_CALL_METHOD)
                        READVALUE(n);
                        READVALUE(i);
                        READVALUE(nkw);
                        CallMethod(ty, i, n, nkw, true, false);
                        break;

                CASE(CALL_METHOD)
                        READVALUE(n);
                        READVALUE(z);
                        READVALUE(nkw);
                        CallMethod(ty, z, n, nkw, false, false);
                        break;

                CASE(CALL_SELF_METHOD)
                        READVALUE(n);
                        READVALUE(z);
                        READVALUE(nkw);
                        push(GetSelf(ty));
                        CallMethod(ty, z, n, nkw, false, false);
                        break;

                CASE(CALL_SELF_STATIC)
                        READVALUE(n);
                        READVALUE(z);
                        READVALUE(nkw);
                        v = GetSelf(ty);
                        push(CLASS(ClassOf(&v)));
                        CallMethod(ty, z, n, nkw, false, false);
                        break;

                CASE(CALL_STATIC_METHOD)
                        READVALUE(i);
                        READVALUE(n);
                        READVALUE(z);
                        READVALUE(nkw);
                        push(CLASS(i));
                        CallMethod(ty, z, n, nkw, false, false);
                        break;

                CASE(SAVE_STACK_POS)
                        xvP(SP_STACK, vN(STACK));
                        break;

                CASE(POP_STACK_POS)
                        vN(STACK) = vXx(SP_STACK);
                        break;

                CASE(POP_STACK_POS_POP)
                        vN(STACK) = vXx(SP_STACK) - 1;
                        break;

                CASE(POP_STACK_POS_POP2)
                        vN(STACK) = vXx(SP_STACK) - 2;
                        break;

                CASE(RESTORE_STACK_POS)
                        vN(STACK) = v_L(SP_STACK);
                        break;

                CASE(DROP_STACK_POS)
                        vXx(SP_STACK);
                        break;

                CASE(DEBUG)
                        fprintf(stderr, "%s\n", IP);
                        SKIPSTR();
                        break;

                CASE(RETURN_IF_NOT_NONE)
                        if (top()->type != VALUE_NONE) {
                                goto RETURN;
                        }
                        break;

RETURN:
                CASE(RETURN)
                        CO_LOG("RETURN", TERM(91), "<-- %sreturn%s from %s: %s", TERM(93), TERM(0), VSC(ActiveFun(ty)), VSC(top()));
#ifdef TY_HAVE_USDT
                        if (TY_PROBING(function__return)) {
                                ProbeFunction(ty, &vvL(FRAMES)->f, false);
                        }
#endif
                        n = vXx(FRAMES).fp;
                        STACK.items[n] = peek();
                        STACK.count = n + 1;
                        CO_LOG("RETURN", TERM(92), "<-- %sreturn%s: %s", TERM(93), TERM(0), VSC(top()));
                CASE(RETURN_PRESERVE_CTX)
                        IP = vXx(CALLS);
                        break;

                CASE(HALT)
                        EXEC_DEPTH -= 1;
                        IP = _ip;
                        CO_LOG("===== HALT ===========", TERM(91;1), "vm_exec(): <== %d (HALT: IP=%p)", EXEC_DEPTH, (void *)IP);
                        return;

                default:
                        UNREACHABLE();

                }
        }
}

static void
RunExitHooks(void)
{
        Ty *ty = MyTy;
        int id = NAMES.exit_hooks;

#if defined(TY_HAVE_SAMPLER)
        if (ProfMode) {
                prof_report(ty);
        } else {
                prof_attach_exit(ty);
        }
#endif

        if (
                (id == -1)
             || (Globals.items[id].type != VALUE_ARRAY)
        ) {
                return;
        }

        StringVector msgs = {0};
        Array      *hooks = v_(Globals, id)->array;
        char       *first = !DyingOfError ? NULL : S2(TyError(ty));

        bool bReprintFirst = false;

        for (usize i = 0; i < vN(*hooks); ++i) {
                if (TY_CATCH_ERROR()) {
                        char *trace = FormatTrace(ty, NULL, NULL);
                        Value error = TY_CATCH();
                        xvP(
                                msgs,
                                xfmt(
                                        "%s\n%sERROR:%s %s",
                                        trace,
                                        TERM(91;1),
                                        TERM(0),
                                        VSC(&error)
                                )
                        );
                        xmF(trace);
                } else {
                        Value v = vmC(v_(*hooks, i), 0);
                        bReprintFirst = bReprintFirst || value_truthy(ty, &v);
                        TY_CATCH_END();
                }
        }

        if (first != NULL && bReprintFirst) {
                fprintf(stderr, "%s\n", first);
        }

        for (usize i = 0; i < vN(msgs); ++i) {
                fprintf(stderr, "%s\n", v__(msgs, i));
        }
}

static char *
xtruncln(Ty *ty, byte_vector *line, int cols)
{
        isize n = term_fit_cols(vv(*line), vN(*line), cols - 1);

        if (n < vN(*line)) {
                vN(*line) = n;
                sxdf(line, "%s%s%s", TERM(1;90), "…", TERM(0));
        }

        svP(*line, '\0');

        return vv(*line);;
}

char *
FormatTrace(Ty *ty, ThrowCtx const *ctx, byte_vector *out)
{
        byte_vector message = {0};

        if (out == NULL) {
                out = &message;
        }

        int _rows;
        int cols;

        if (!get_terminal_size(-1, &_rows, &cols)) {
                cols = 80;
        }

        if (ctx == NULL) {
                ctx = CurrentThrowCtx(ty);
        }

        StringVector locals = {0};

        WITH_SCRATCH for (int i = 0; i < vN(*ctx); ++i) {
                char *ip = (char *)v__(*ctx, i);
                if (ip == NULL) {
                        break;
                }

                Expr const *expr = compiler_find_expr(ty, ip - 1);
                if (expr == NULL) {
                        continue;
                }

                if (!InteractiveSession) {
                        WriteExpressionSourceHeading(ty, out, cols, expr);

                        Expr const *func;
                        if (
                                DetailedExceptions
                             && ((func = compiler_find_func(ty, ip - 1)) != NULL)
                             && (func->fn->scope != NULL)
                             && (vN(func->fn->scope->owned) > 0)
                        ) {
                                ValueVector localv = v__(ctx->locals, i);
                                Scope *scope = func->fn->scope;

                                int max_width = 0;
                                for (int i = 0; i < vN(scope->owned); ++i) {
                                        int width = term_width(v__(scope->owned, i)->identifier, -1);
                                        if (width > max_width) {
                                                max_width = width;
                                        }
                                }

                                int vcols = cols/2 - (max_width + 5);

                                for (int i = 0; i < vN(scope->owned) && i < vN(localv); ++i) {
                                        Value  val = v__(localv, i);
                                        char *show = NULL;
                                        bool  good = true;
                                        byte_vector line = {0};
                                        for (int fuel = 3; (show == NULL) && (fuel > 0); --fuel) {
                                                if (!VM_TRY()) {
                                                        val = vm_catch(ty);
                                                        good = false;
                                                } else {
                                                        show = SHOW(&val, BASIC);
                                                        vm_finally(ty);
                                                }
                                        }
                                        if (good) {
                                                sxdf(
                                                        &line,
                                                        "%s%*s%s = ",
                                                        TERM(1;93),
                                                        max_width,
                                                        v__(scope->owned, i)->identifier,
                                                        TERM(22;39)
                                                );
                                                for (char const *c = show; *c != '\0'; ++c) {
                                                        if (*c == '\n') {
                                                                svP(locals, xtruncln(ty, &line, vcols));
                                                                v00(line);
                                                                sxdf(&line, "%*s", max_width + 3, "");
                                                        } else {
                                                                svP(line, *c);
                                                        }
                                                }
                                                svP(line, '\0');
                                        } else {
                                                sxdf(
                                                        &line,
                                                        "%s%*s%s = [failed to read: %s]",
                                                        TERM(1;91),
                                                        max_width,
                                                        v__(scope->owned, i)->identifier,
                                                        TERM(22;39),
                                                        (show != NULL) ? show : "too many errors"
                                                );
                                        }
                                        if (show != NULL) {
                                                xmF(show);
                                        }
                                        svP(locals, xtruncln(ty, &line, vcols));
                                }
                        }

                        if (vN(locals) > 0) {
                                WriteExpressionSourceContext(ty, out, cols / 2, expr, &locals);
                                v0(locals);
                        } else {
                                WriteExpressionSourceContext(ty, out, cols, expr, NULL);
                        }
                } else if (expr->origin != NULL) {
                        WriteExpressionTrace(ty, out, expr->origin, -1, i == 0);
                        WriteExpressionOrigin(ty, out, expr);
                } else {
                        WriteExpressionTrace(ty, out, expr, -1, i == 0);
                }
        }

        if (vN(*out) == 0) {
                xvP(*out, '\0');
                vXx(*out);
        }

        return vv(*out);
}

static void
xDcringe(Ty *ty)
{
        dump(&ErrorBuffer, "Stack trace:\n");

        for (int i = 0; IP != NULL; ++i) {
                if (vN(FRAMES) > 0 && is_hidden_fun(ActiveFun(ty))) {
                        goto Next;
                }

                Frame const *frame = vN(FRAMES) > 0 ? vvL(FRAMES) : NULL;
                char const *ip = jit_frame_ip(frame, IP);
                Expr const *expr = compiler_find_expr(ty, ip - 1);

                WriteExpressionTrace(ty, &ErrorBuffer, expr, 0, i == 0);
                if (expr != NULL && expr->origin != NULL) {
                        WriteExpressionOrigin(ty, &ErrorBuffer, expr->origin);
                }

                while (vN(FRAMES) == 0 && co_abort(ty)) {
                        ;
                }

                if (vN(FRAMES) == 0) {
                        break;
                }

Next:
                IP = (char *)vXx(FRAMES).ip;
        }

        if (CompilationDepth(ty) > 1) {
                dump(
                        &ErrorBuffer,
                        "\n%s%sCompilation context:%s\n",
                        TERM(1),
                        TERM(34),
                        TERM(0)
                );
                CompilationTrace(ty, &ErrorBuffer);
        }
}

void
CaptureContextEx(Ty *ty, ThrowCtx *ctx)
{
        co_state st = *ty->st;
        char const *ip = IP;
        char const *up;

        while (ip != NULL) {
                Frame const *frame = vN(st.frames) > 0 ? vvL(st.frames) : NULL;
                ip = jit_frame_ip(frame, ip);

                if (
                        (vN(st.frames) > 0)
                     && is_hidden_fun(FrameFun(ty, vvL(st.frames)))
                ) {
                        goto Next;
                }

                i32 fp;
                i32 nvar;
                if (frame != NULL) {
                        fp = frame->fp;
                        nvar = FrameFun(ty, frame)->info[FUN_INFO_BOUND];
                } else {
                        fp = 0;
                        nvar = 0;
                }

                ValueVector locals = {0};
                xvPn(locals, vv(st.stack) + fp, nvar);

                for (int i = 0; i < vN(locals); ++i) {
                        Value *v = v_(locals, i);
                        while (v->type == VALUE_REF) {
                                *v = *v->ref;
                        }
                }

                xvP(*ctx, (void *)ip);
                xvP(ctx->locals, locals);

                if (
                        (vN(st.frames) == 1)
                     && ((up = co_up(ty, &st)) != NULL)
                ) {
                        ip = up;
                        continue;
                }
Next:
                if (vN(st.frames) == 0) {
                        break;
                }

                ip = vXx(st.frames).ip;
        }

        int i = 0;
        int j = (isize)vN(*ctx) - 1;

        while (i < j) {
                SWAP(void *, v__(*ctx, i), v__(*ctx, j));
                SWAP(ValueVector, v__(ctx->locals, i), v__(ctx->locals, j));
                i += 1;
                j -= 1;
        }
}

void
CaptureContext(Ty *ty, ThrowCtx *ctx)
{
        co_state st = *ty->st;
        char const *ip = IP;
        char const *up;

        while (ip != NULL) {
                Frame const *frame = vN(st.frames) > 0 ? vvL(st.frames) : NULL;
                ip = jit_frame_ip(frame, ip);

                if (
                        (vN(st.frames) > 0)
                     && is_hidden_fun(FrameFun(ty, vvL(st.frames)))
                ) {
                        goto Next;
                }

                xvP(*ctx, (void *)ip);

                if (
                        (vN(st.frames) == 1)
                     && ((up = co_up(ty, &st)) != NULL)
                ) {
                        ip = up;
                        continue;
                }

                if (vN(st.frames) == 0) {
                        break;
                }
Next:
                ip = vXx(st.frames).ip;
        }

        int i = 0;
        int j = (isize)vN(*ctx) - 1;

        while (i < j) {
                SWAP(void *, v__(*ctx, i), v__(*ctx, j));
                i += 1;
                j -= 1;
        }
}

inline static void
FormatPanicEntryFor(Ty *ty, byte_vector *buf, char const *ip)
{
        Expr const *expr = compiler_find_expr(ty, ip - 1);

        WriteExpressionTrace(ty, buf, expr, 0, false);
        if (expr != NULL && expr->origin != NULL) {
                WriteExpressionOrigin(ty, buf, expr->origin);
        }
}

static noreturn void
vm_vpanic_ex(Ty *ty, char const *fmt, va_list _ap)
{
        byte_vector msg = {0};
        va_list ap;

        va_copy(ap, _ap);
        sxdf(&msg, "%s%sRuntimeError%s%s: ", TERM(1), TERM(31), TERM(22), TERM(39));
        vsxdf(&msg, fmt, ap);
        sxdf(&msg, "%c", '\n');
        va_end(ap);

        ThrowCtx *ctx = CurrentThrowCtx(ty);

        FormatTrace(ty, ctx, &msg);

        if (CompilationDepth(ty) > 1) {
                dump(
                        &msg,
                        "\n%s%sCompilation context:%s\n",
                        TERM(1),
                        TERM(34),
                        TERM(0)
                );
                CompilationTrace(ty, &msg);
        }

        PopThrowCtx(ty);

        GC_STOP();
        Value what = vSs(vv(msg), vN(msg));
        Value error = RawObject(CLASS_RUNTIME_ERROR);
        PutMember(error, NAMES._what,  what);
        PutMember(error, NAMES._ctx,   NIL);
        PutMember(error, NAMES._cause, NIL);
        GC_RESUME();

        vm_throw(ty, &error);
}

noreturn void
vm_panic_ex(Ty *ty, char const *fmt, ...)
{
        va_list ap;

        va_start(ap, fmt);
        vm_vpanic_ex(ty, fmt, ap);
        va_end(ap);

        UNREACHABLE();
}

noreturn void
vm_panic(Ty *ty, char const *fmt, ...)
{
        va_list ap;

        (void)PushThrowCtx(ty);

        va_start(ap, fmt);
        vm_vpanic_ex(ty, fmt, ap);
        va_end(ap);

        UNREACHABLE();
}

noreturn void
vm_verror(Ty *ty, int kind, char const *fmt, va_list ap)
{
        GC_STOP();

        Value msg = STRING_VFORMAT(ty, fmt, ap);
        Value error = RawObject(kind);
        PutMember(error, NAMES._what,  msg);
        PutMember(error, NAMES._ctx,   NIL);
        PutMember(error, NAMES._cause, NIL);

        GC_RESUME();

        vm_throw(ty, &error);
}

noreturn void
vm_error(Ty *ty, char const *fmt, ...)
{
        va_list ap;
        va_start(ap, fmt);
        vm_verror(ty, CLASS_RUNTIME_ERROR, fmt, ap);
        UNREACHABLE();
}

noreturn void
vm_xerror(Ty *ty, int kind, char const *fmt, ...)
{
        va_list ap;
        va_start(ap, fmt);
        vm_verror(ty, kind, fmt, ap);
        UNREACHABLE();
}

bool
vm_execute_file(Ty *ty, char const *path)
{
        char *source = slurp(path, NULL);
        if (source == NULL) {
                GC_STOP();
                Value msg = TyErrorMessage(
                        ty,
                        afmt(
                                "%s%s%s: failed to read source file: %s%s%s",
                                TERM(91;1), "Error", TERM(0),
                                TERM(95), path, TERM(0)
                        )
                );
                TySetError(ty, msg, NIL);
                GC_RESUME();
                return false;
        }

        bool success = vm_execute(ty, source, path);

        xmF(source - 1);

        return success;
}


#ifdef TY_CATCH_SIGSEGV
static void
cringe(int _)
{
        static u32 n;

        if (++n > 1) {
                return;
        }

        Ty *ty = MyTy;

#ifdef UNW_LOCAL_ONLY
        print_stack_trace();
#endif

        for (i32 i = 0; i < vN(ty->group->TyList); ++i) {
                Ty *_ty = v__(ty->group->TyList, i);
                if (_ty != ty) {
                        xDcringe(_ty);
                        fprintf(
                                stderr,
                                "============== Thread %d =====================\n"
                                "%s\n"
                                "==============================================\n",
                                i,
                                vv(_ty->err)
                        );
                }
        }
        zP("xdDDDDDD[%"PRIu64"]", MyId);
}
#endif

#if !defined(TY_RELEASE)
static void
FlipGC_EVERY_ALLOC(int _)
{
        GC_EVERY_ALLOC = !GC_EVERY_ALLOC;
}
#endif

static bool
TestSelected(TyTest const *test)
{
        return test->pub
            && (test->def->mod != NULL)
            && (test->def->mod->flags & MOD_TESTS);
}

static bool
TestCallable(Value const *v)
{
        switch (v->type) {
        case VALUE_FUNCTION:
        case VALUE_BOUND_FUNCTION:
        case VALUE_METHOD:
        case VALUE_BUILTIN_FUNCTION:
        case VALUE_BUILTIN_METHOD:
        case VALUE_FOREIGN_FUNCTION:
        case VALUE_JIT_FUNCTION:
        case VALUE_OPERATOR:
                return true;

        default:
                return false;
        }
}

int
RunTestsNative(Ty *ty)
{
        usize n = vN(xD.tests);
        int maxw = 0;
        int pass = 0;
        int fail = 0;

        for (usize i = 0; i < n; ++i) {
                TyTest const *test = v_(xD.tests, i);
                if (TestSelected(test)) {
                        maxw = max(maxw, term_width(test->name, -1));
                }
        }

        for (usize i = 0; i < n; ++i) {
                TyTest test = v__(xD.tests, i);

                if (!TestSelected(&test)) {
                        continue;
                }

                char const *name = test.name;
                Symbol *var = test.var;

                if (CompileOnly) {
                        printf("%s\n", name);
                        continue;
                }

                Value fun = (var->i >= 0 && var->i < vN(Globals))
                          ? v__(Globals, var->i)
                          : NIL;

                if (fun.type == VALUE_UNINITIALIZED) {
                        fun = NIL;
                }

                if (!TestCallable(&fun)) {
                        fprintf(
                                stderr,
                                "%sFAIL%s %s%*s%s (not callable: %s)\n",
                                TERM(91;1),
                                TERM(0),
                                TERM(93),
                                -maxw,
                                name,
                                TERM(0),
                                VSC(&fun)
                        );
                        fail += 1;
                        continue;
                }

                if (TY_CATCH_ERROR()) {
                        char *trace = FormatTrace(ty, NULL, NULL);
                        Value   exc = TY_CATCH();
                        fprintf(
                                stderr,
                                "%sFAIL%s %s%*s%s\n%s\n%s\n",
                                TERM(91;1),
                                TERM(0),
                                TERM(93),
                                -maxw,
                                name,
                                TERM(0),
                                trace,
                                VSC(&exc)
                        );
                        fail += 1;
                } else {
                        u64 t0 = TyMonotonicTime();
                        vm_call(ty, &fun, 0);
                        u64 t1 = TyMonotonicTime();
                        fprintf(
                                stderr,
                                "%sPASS%s %s%*s%s %s(%.2fms)%s\n",
                                TERM(92),
                                TERM(0),
                                TERM(93),
                                -maxw,
                                name,
                                TERM(0),
                                TERM(90),
                                (t1 - t0) / 1.0e6,
                                TERM(0)
                        );
                        pass += 1;
                        TY_CATCH_END();
                }
        }

        if (!CompileOnly) {
                fprintf(stderr, "%d passed, %d failed\n", pass, fail);
        }

        return (fail == 0) ? 0 : 1;
}

int
RunTestHarness(Ty *ty, char **args, int n)
{
        Symbol *sym = compiler_lookup(ty, "ty/test", "main");
        int volatile rc = 70;

        if (
                (getenv("TY_TEST_NATIVE") != NULL)
             || compiler_test_runner_failed()
             || (sym == NULL)
             || (sym->i < 0)
             || (sym->i >= vN(Globals))
             || !TestCallable(v_(Globals, sym->i))
        ) {
                return RunTestsNative(ty);
        }

        if (TY_CATCH_ERROR()) {
                Value exc = TY_CATCH();
                fprintf(stderr, "ty --test: internal runner error: %s\n", VSC(&exc));
        } else {
                Value main = v__(Globals, sym->i);
                GC_STOP();
                Value argv = ARRAY(vA());
                for (int i = 0; i < n; ++i) {
                        vAp(argv.array, vSsz(args[i]));
                }
                push(argv);
                GC_RESUME();
                Value r = vm_call(ty, &main, 1);
                if (r.type == VALUE_INTEGER) {
                        rc = (int)r.z;
                } else {
                        fprintf(stderr, "ty --test: runner returned %s, not an Int\n", VSC(&r));
                }
                TY_CATCH_END();
        }

        return rc;
}

void
vm_reload_dirs(Ty *ty)
{
        dirs_reload();

        if (!DirsBound) {
                return;
        }

        for (int i = 0; i < DIR_COUNT; ++i) {
                *v_(Globals, DirSlots[i]) = vSsz(dirs_get(i));
        }
}

bool
vm_init(Ty *ty, int ac, char **av)
{
#if defined(TY_CATCH_SIGSEGV)
        signal(SIGSEGV, cringe);
#endif

#if !defined(TY_RELEASE)
        signal(SIGUSR2, FlipGC_EVERY_ALLOC);
#endif

        ReserveGlobals();
        InitThreadGroup(&MainGroup, 1, NULL);
        TySpinLockInit(&GroupIdLock);
        InitializeTY(&xD, ty);
        TyDiagInit();

        TY_BEGIN_LOADING();

        MyTy = ty;
        MyId = 0;

        build_string_method_table();
        build_array_method_table();
        build_heap_method_table();
        build_blob_method_table();
        build_queue_method_table();
        build_shared_queue_method_table();
        build_dict_method_table();
        build_set_method_table();

        NAMES.a                = M_ID("a");
        NAMES.b                = M_ID("b");
        NAMES.call             = M_ID("__call__");
        NAMES._class_          = M_ID("__class__");
        NAMES.count            = M_ID("__count__");
        NAMES._def_            = M_ID("__def__");
        NAMES._drop_           = M_ID("__drop__");
        NAMES._enter_          = M_ID("__enter__");
        NAMES.fmt              = M_ID("__fmt__");
        NAMES._free_           = M_ID("__free__");
        NAMES._fqn_            = M_ID("__fqn__");
        NAMES.groups           = M_ID("groups");
        NAMES._hash_           = M_ID("__hash__");
        NAMES._id_             = M_ID("__id__");
        NAMES.init             = M_ID("init");
        NAMES._init_subclass_  = M_ID("__init_subclass__");
        NAMES._iter_           = M_ID("__iter__");
        NAMES.json             = M_ID("__json__");
        NAMES._len_            = M_ID("#");
        NAMES.len              = M_ID("len");
        NAMES.match            = M_ID("__match__");
        NAMES._meta_           = M_ID("__meta__");
        NAMES.missing          = M_ID("__missing__");
        NAMES.method_missing   = M_ID("__method_missing__");
        NAMES._name_           = M_ID("__name__");
        NAMES._next_           = M_ID("__next__");
        NAMES._path_           = M_ID("__path__");
        NAMES.ptr              = M_ID("__ptr__");
        NAMES._repr_           = M_ID("__repr__");
        NAMES.slice            = M_ID("[;;]");
        NAMES.source           = M_ID("source");
        NAMES._src_            = M_ID("__src__");
        NAMES.str              = M_ID("str");
        NAMES._str_            = M_ID("__str__");
        NAMES.subscript        = M_ID("[]");
        NAMES.subscript_eq     = M_ID("[]=");
        NAMES.unapply          = M_ID("unapply");

        NAMES._what            = M_ID(sfmt("_what$%d",  CLASS_RUNTIME_ERROR));
        NAMES._ctx             = M_ID(sfmt("_ctx$%d",   CLASS_RUNTIME_ERROR));
        NAMES._cause           = M_ID(sfmt("_cause$%d", CLASS_RUNTIME_ERROR));
        NAMES._msg             = M_ID(sfmt("_msg$%d",     CLASS_COMPILE_ERROR));
        NAMES._locs            = M_ID(sfmt("_locs$%d",    CLASS_COMPILE_ERROR));
        NAMES._detail          = M_ID(sfmt("_detail$%d",  CLASS_COMPILE_ERROR));
        NAMES._related         = M_ID(sfmt("_related$%d", CLASS_COMPILE_ERROR));
        NAMES._code            = M_ID(sfmt("_code$%d",    CLASS_COMPILE_ERROR));
        NAMES._notes           = M_ID(sfmt("_notes$%d",   CLASS_COMPILE_ERROR));

        NAMES._fields_         = M_ID("__fields__");
        NAMES._methods_        = M_ID("__methods__");
        NAMES._getters_        = M_ID("__getters__");
        NAMES._setters_        = M_ID("__setters__");
        NAMES._static_fields_  = M_ID("__static_fields__");
        NAMES._static_methods_ = M_ID("__static_methods__");
        NAMES._static_getters_ = M_ID("__static_getters__");
        NAMES._super_          = M_ID("__super__");

        TyFunctionsInit(ty);

        GC_STOP();

        NewArenaNoGC(ty, 1ULL << 25);

        compiler_init(ty);
        add_builtins(ty, ac, av);

        AddThread(ty, TyThreadSelf());

        DebugInit(ty);

        if (TY_CATCH_ERROR()) {
                TY_CATCH_FAIL();
                GC_RESUME();
                return false;
        }

        char *prelude = compiler_load_prelude(ty);
        if (prelude == NULL) {
                TY_CATCH_END();
                GC_RESUME();
                return false;
        }

        atexit(RunExitHooks);

        vm_exec(ty, prelude);

        compiler_load_builtin_modules(ty);

        sqlite_load(ty);

        GC_RESUME();
        TY_CATCH_END();

#if defined(TY_HAVE_SAMPLER)
        if (ProfMode) {
                prof_start(ty);
        } else if (!LangServer) {
                prof_attach_init(ty);
        }
#endif

        TY_FINISH_LOADING();
        PopulateGlobals(ty);
        TY_IS_INITIALIZED = true;

        return true;
}

bool
vm_reset(Ty *ty)
{
        v0(Globals);
        v0(FRAMES);
        v0(STACK);
        v0(CALLS);

        for (int i = 0; i < vN(ty->_2op_cache); ++i) {
                xvF(v__(ty->_2op_cache, i));
        }
        v0(ty->_2op_cache);

        GC_STOP();
        TY_IS_INITIALIZED = false;
        TY_BEGIN_LOADING();
        CompilerReset(ty);
        add_builtins(ty, 0, NULL);

        if (TY_CATCH_ERROR()) {
                TY_CATCH_FAIL();
                GC_RESUME();
                return false;
        }

        char *code = compiler_load_prelude(ty);
        vm_exec(ty, code);

        compiler_load_builtin_modules(ty);
        sqlite_load(ty);
        TY_FINISH_LOADING();
        PopulateGlobals(ty);
        TY_IS_INITIALIZED = true;
        GC_RESUME();

        return true;
}

bool
vm_load_program(Ty *ty, char const *source, char const *file)
{
        TY_BEGIN_LOADING();

        Module * volatile mod = NULL;

        if (TY_CATCH_ERROR()) {
                TY_CATCH_FAIL();
                TY_FINISH_LOADING();
                return false;
        }

        GC_STOP();

        mod = compiler_compile_source(ty, source, file);
        if (mod == NULL) {
                TY_CATCH_END();
                GC_RESUME();
                TY_FINISH_LOADING();
                return false;
        }

        if (DisassemblyOut != NULL) {
                byte_vector out = {0};
                DumpProgram(ty, &out, mod->path, NULL, NULL, true);
                fwrite(vv(out), 1, vN(out), DisassemblyOut);
                xvF(out);
        }

        TY_CATCH_END();
        GC_RESUME();
        TY_FINISH_LOADING();

        DoGC(ty);
        ty_collect(true);

        ty->code = mod->code;

        return true;
}

bool
vm_execute(Ty *ty, char const *source, char const *file)
{
        if (source != NULL && !vm_load_program(ty, source, file)) {
                return false;
        }

        if (CompileOnly) {
                return true;
        }

        if (TY_CATCH_ERROR()) {
                GetCurrentTry(ty)->state = TRY_TRY;
                GC_STOP();
                Value detail;
                Value exc = TyCatchDetail(ty, &detail);
                TySetError(ty, exc, detail);
                GC_RESUME();
                return false;
        }

        vm_exec(ty, ty->code);

        if (PrintResult && vC(STACK) > 0) {
                vN(STACK) += 1;
                printf("%s\n", VSC(top()));
        }

#if defined(TY_GC_STATS)
        printf("--------------------------------------\n");
        printf("GC stats (ran %llu times):\n", GCRunCount);
        printf("--------------------------------------\n");
        printf("  Allocated: %.2f MB\n", TotalBytesAllocated / 1.0e6);
        printf("  Peak RSS:  %.2f MB\n", GCMaxHeap / 1.0e6);
        printf("  Total time: %.4fs\n", GCTimeTotal / 1.0e9);
        printf("       Wait time:  %.4fs\n", GCTimeWait / 1.0e9);
        printf("       Mark time:  %.4fs\n", GCTimeMark / 1.0e9);
        printf("       Sweep time: %.4fs\n", GCTimeSweep / 1.0e9);
        printf("--------------------------------------\n");
#endif

        TY_CATCH_END();

        return true;
}

void
vm_push(Ty *ty, Value const *v)
{
        push(*v);
}

Value *
vm_pop(Ty *ty)
{
        return vvX(STACK);
}

Value *
vm_get(Ty *ty, int i)
{
        return v_(STACK, vN(STACK) - (i + 1));
}

noreturn void
vm_throw(Ty *ty, Value const *v)
{
        ThrowCtx *ctx = PushThrowCtx(ty);
        ctx->exc = *v;
        if (UNLIKELY(VmPoll.debug | DebugJitOff)) {
                DebugOnThrow(ty);
        }
        DoThrow(ty);
        vm_exec(ty, IP);
        UNREACHABLE();
}

FrameStack *
vm_get_frames(Ty *ty)
{
        return &FRAMES;
}

Value
vm_call_method(Ty *ty, Value const *self, Value const *f, int argc)
{
        CheckPendingSignals(ty);
        exec_fn(ty, f, self, argc, NULL);
        return pop();
}

Value
vm_call_ex(Ty *ty, Value const *f, int argc, Value *kwargs, bool collect)
{
        Value v, *init, *vp;
        usize n = vN(STACK) - argc;

        CheckPendingSignals(ty);

        switch (f->type) {
        case VALUE_FUNCTION:
        case VALUE_BOUND_FUNCTION:
                exec_fn(ty, f, NULL, argc, kwargs);
                goto Collect;

        case VALUE_METHOD:
                exec_fn(ty, f->method, f->this, argc, kwargs);
                goto Collect;

        case VALUE_BUILTIN_FUNCTION:
                v = f->builtin_function(ty, argc, kwargs);
                STACK.count = n;
                return v;

        case VALUE_JIT_FUNCTION:
                v = jfun_call(ty, f, argc, kwargs);
                STACK.count = n;
                return v;

        case VALUE_FOREIGN_FUNCTION:
                v = cffi_fast_call(ty, f, argc, kwargs);
                STACK.count = n;
                return v;

        case VALUE_BUILTIN_METHOD:
                v = f->builtin_method(ty, f->this, argc, NULL);
                STACK.count = n;
                return v;

        case VALUE_TAG:
                DoTag(ty, f->tag, argc, kwargs);
                return pop();

        case VALUE_CLASS:
                if (f->class <= CLASS_PRIMITIVE) {
                        v = ConstructPrimitive(ty, f->class, argc, kwargs);
                } else {
                        init = class_ctor(ty, f->class);
                        v = RawObject(f->class);
                        if (LIKELY(!IsZero(*init)) && !InertInit(init, argc, NULL)) {
                                exec_fn(ty, init, &v, argc, NULL);
                                pop();
                        }
                }
                return v;

        case VALUE_DICT:
                vp = (argc >= 1) ? dict_get_value(ty, f->dict, top() - (argc - 1)) : NULL;
                STACK.count -= argc;
                return (vp == NULL) ? None : Some(*vp);

        case VALUE_SET:
                v = (argc >= 1) ? top()[-(argc - 1)] : NONE;
                v = BOOLEAN((argc >= 1) && set_has(ty, f->set, &v));
                STACK.count -= argc;
                return v;

        case VALUE_ARRAY:
                v = (argc >= 1) ? ArraySubscript(ty, *f, top()[-(argc - 1)], INDEX_OPTIONAL) : None;
                STACK.count -= argc;
                return v;

        case VALUE_OBJECT:
                vp = class_lookup_method_i(ty, f->class, NAMES.call);
                if (vp == NULL) {
                        goto NotCallable;
                }
                exec_fn(ty, vp, f, argc, kwargs);
                goto Collect;


        default:
        NotCallable:
                zP("non-callable value passed to vm_call_ex(): %s", VSC(f));
        }

Collect:

        if (!collect) {
                STACK.count = n + 1;
                return pop();
        }

        Value xs = ARRAY(vA());
        NOGC(xs.array);
        for (usize i = n; i < STACK.count; ++i) {
                vAp(xs.array, STACK.items[i]);
        }
        OKGC(xs.array);

        STACK.count = n;

        return xs;
}

Value
vm_call(Ty *ty, Value const *f, int argc)
{
        Value a, b, v;
        Value *vp;

        usize n = vN(STACK) - argc;

        CheckPendingSignals(ty);

        switch (f->type) {
        case VALUE_FUNCTION:
        case VALUE_BOUND_FUNCTION:
                exec_fn(ty, f, NULL, argc, NULL);
                return pop();

        case VALUE_METHOD:
                exec_fn(ty, f->method, f->this, argc, NULL);
                return pop();

        case VALUE_BUILTIN_FUNCTION:
                v = f->builtin_function(ty, argc, NULL);
                STACK.count = n;
                return v;

        case VALUE_JIT_FUNCTION:
                v = jfun_call(ty, f, argc, NULL);
                STACK.count = n;
                return v;

        case VALUE_FOREIGN_FUNCTION:
                v = cffi_fast_call(ty, f, argc, NULL);
                STACK.count = n;
                return v;

        case VALUE_BUILTIN_METHOD:
                v = f->builtin_method(ty, f->this, argc, NULL);
                STACK.count = n;
                return v;

        case VALUE_OPERATOR:
                switch (argc) {
                case 1:
                        DoUnaryOp(ty, f->uop, true);
                        return pop();

                case 2:
                        b = pop();
                        a = pop();
                        return vm_2op(ty, f->bop, &a, &b);

                default:
                        vm_throw(ty, &TAG(TAG_DISPATCH_ERR));
                }

        case VALUE_TAG:
                DoTag(ty, f->tag, argc, NULL);
                return pop();

        case VALUE_CLASS:
                if (f->class <= CLASS_PRIMITIVE) {
                        v = ConstructPrimitive(ty, f->class, argc, NULL);
                } else {
                        vp = class_ctor(ty, f->class);
                        v = RawObject(f->class);
                        if (LIKELY(!IsZero(*vp)) && !InertInit(vp, argc, NULL)) {
                                exec_fn(ty, vp, &v, argc, NULL);
                                pop();
                        }
                }
                return v;

        case VALUE_DICT:
                vp = (argc >= 1) ? dict_get_value(ty, f->dict, top() - (argc - 1)) : NULL;
                STACK.count -= argc;
                return (vp == NULL) ? None : Some(*vp);

        case VALUE_SET:
                v = (argc >= 1) ? top()[-(argc - 1)] : NONE;
                v = BOOLEAN((argc >= 1) && set_has(ty, f->set, &v));
                STACK.count -= argc;
                return v;

        case VALUE_ARRAY:
                v = (argc >= 1) ? ArraySubscript(ty, *f, top()[-(argc - 1)], INDEX_OPTIONAL) : None;
                STACK.count -= argc;
                return v;

        case VALUE_OBJECT:
                vp = class_lookup_method_i(ty, f->class, NAMES.call);
                if (vp == NULL) {
                        goto NotCallable;
                }
                exec_fn(ty, vp, f, argc, NULL);
                return pop();

        default:
        NotCallable:
                zP("non-callable value passed to vm_call(): %s", VSC(f));
        }
}

Value
vm_call1(Ty *ty, Value const *f, Value const *x)
{
        Value v;
        usize n = vN(STACK);

        push(*x);

        switch (f->type) {
        case VALUE_FUNCTION:
        case VALUE_BOUND_FUNCTION:
                exec_fn(ty, f, NULL, 1, NULL);
                return pop();

        case VALUE_METHOD:
                exec_fn(ty, f->method, f->this, 1, NULL);
                return pop();

        case VALUE_BUILTIN_FUNCTION:
                v = f->builtin_function(ty, 1, NULL);
                STACK.count = n;
                return v;

        case VALUE_JIT_FUNCTION:
                v = jfun_call(ty, f, 1, NULL);
                STACK.count = n;
                return v;

        case VALUE_FOREIGN_FUNCTION:
                v = cffi_fast_call(ty, f, 1, NULL);
                STACK.count = n;
                return v;

        case VALUE_BUILTIN_METHOD:
                v = f->builtin_method(ty, f->this, 1, NULL);
                STACK.count = n;
                return v;

        case VALUE_OPERATOR:
                DoUnaryOp(ty, f->uop, true);
                return pop();

        case VALUE_REGEX:
                if (UNLIKELY(x->type != VALUE_STRING)) {
                        zP("Regex.__call__(): expected String but got: %s", VSC(x));
                }
                v = *x;
                push(*f);
                v = string_match(ty, &v, 1, NULL);
                STACK.count = n;
                return v;

        default:
                return vm_call(ty, f, 1);
        }
}

Value
vm_eval_function(Ty *ty, Value const *f, ...)
{
        int argc;
        va_list ap;
        Value r;
        Value const *v;
        Value a, b;

        CheckPendingSignals(ty);

        va_start(ap, f);
        argc = 0;

        while ((v = va_arg(ap, Value const *)) != NULL) {
                push(*v);
                argc += 1;
        }

        va_end(ap);

        usize n = vN(STACK) - argc;

        switch (f->type) {
        case VALUE_FUNCTION:
        case VALUE_BOUND_FUNCTION:
                exec_fn(ty, f, NULL, argc, NULL);
                return pop();

        case VALUE_METHOD:
                exec_fn(ty, f->method, f->this, argc, NULL);
                return pop();

        case VALUE_BUILTIN_FUNCTION:
                r = f->builtin_function(ty, argc, NULL);
                STACK.count = n;
                return r;

        case VALUE_JIT_FUNCTION:
                r = jfun_call(ty, f, argc, NULL);
                STACK.count = n;
                return r;

        case VALUE_FOREIGN_FUNCTION:
                r = cffi_fast_call(ty, f, argc, NULL);
                STACK.count = n;
                return r;

        case VALUE_BUILTIN_METHOD:
                r = f->builtin_method(ty, f->this, argc, NULL);
                STACK.count = n;
                return r;

        case VALUE_OBJECT:
                v = class_lookup_method_i(ty, f->class, NAMES.call);
                if (v == NULL) {
                        goto NotCallable;
                }
                exec_fn(ty, v, f, argc, NULL);
                break;

        case VALUE_OPERATOR:
                switch (argc) {
                case 1:
                        DoUnaryOp(ty, f->uop, true);
                        return pop();

                case 2:
                        b = pop();
                        a = pop();
                        return vm_2op(ty, f->bop, &a, &b);

                default:
                        vmE(&TAG(TAG_DISPATCH_ERR));
                }

        case VALUE_TAG:
                DoTag(ty, f->tag, argc, NULL);
                return pop();

        case VALUE_CLASS:
                return vm_call(ty, f, argc);

        default:
        NotCallable:
                zP("non-callable value passed to vm_eval_function(): %s", VSC(f));
        }

        UNREACHABLE();
}

Value
vm_2op(Ty *ty, int op, Value const *a, Value const *b)
{
        push(*a);
        push(*b);

        DoBinaryOp(ty, op, true);

        return pop();
}

Value
vm_try_2op(Ty *ty, int op, Value const *a, Value const *b)
{
        int i = op_dispatch(ty, op, ClassOf(a), ClassOf(b));

        if (i == -1) {
                dont_printf(
                        "no matching implementation of %s%s%s for %s\n",
                        TERM(95;1), intern_entry(&xD.members, op)->name, TERM(0),
                        VSC(top())
                );
                return NONE;
        }

        dont_printf(
                "matching implementation of %s%s%s: %d\n"
                FMT_MORE "%s left%s (%d): %s"
                FMT_MORE "%sright%s (%d): %s\n",
                TERM(95;1), intern_entry(&xD.b_ops, op)->name, TERM(0), i,
                TERM(95), TERM(0), ClassOf(a), VSC(a),
                TERM(95), TERM(0), ClassOf(b), VSC(b)
        );

        push(*a);
        push(*b);

        exec_fn(ty, &Globals.items[i], NULL, 2, NULL);

        return pop();
}


void
MarkStorage(Ty *ty)
{
        GCLOG("Marking root set (%zu items)", vN(RootSet));
        RESET_TOTAL_REACHED();
        for (int i = 0; i < vN(RootSet); ++i) {
                value_mark(ty, v_(RootSet, i));
        }
        LOG_REACHED(" => root_set reached %llu", TotalReached);

        GCLOG("Marking thread-local storage");
        RESET_TOTAL_REACHED();
        for (int i = 0; i < vN(THREAD_LOCALS); ++i) {
                value_mark(ty, v_(THREAD_LOCALS, i));
        }
        LOG_REACHED(" => TLS reached %llu", TotalReached);

        GCLOG("Marking stack");
        RESET_TOTAL_REACHED();
        for (int i = 0; i < vN(STACK); ++i) {
                value_mark(ty, v_(STACK, i));
        }
        LOG_REACHED(" => stack reached %llu", TotalReached);

        GCLOG("Marking try stack");
        RESET_TOTAL_REACHED();
        for (int i = 0; i < vN(TRY_STACK); ++i) {
                struct try *t = v__(TRY_STACK, i);
                for (int i = 0; i < vN(t->defer); ++i) {
                        value_mark(ty, v_(t->defer, i));
                }
        }
        LOG_REACHED(" => try_stack reached %llu", TotalReached);

        GCLOG("Marking throw stack");
        RESET_TOTAL_REACHED();
        for (int i = 0; i < vN(THROW_STACK); ++i) {
                ThrowCtx *ctx = v__(THROW_STACK, i);
                for (int i = 0; i < vN(ctx->locals); ++i) {
                        ValueVector const *locals = v_(ctx->locals, i);
                        for (int i = 0; i < vN(*locals); ++i) {
                                value_mark(ty, v_(*locals, i));
                        }
                }
                value_mark(ty, &ctx->exc);
        }
        value_mark(ty, &ty->exc);
        TyDiagMark(ty);
        LOG_REACHED(" => throw_stack reached %llu", TotalReached);

        GCLOG("Marking drop stack");
        RESET_TOTAL_REACHED();
        for (int i = 0; i < vN(DROP_STACK); ++i) {
                value_mark(ty, v_(DROP_STACK, i));
        }
        value_mark(ty, &ty->st->ctx);
        LOG_REACHED(" => drop_stack reached %llu", TotalReached);

        GCLOG("Marking %zu targets", vN(TARGETS));
        RESET_TOTAL_REACHED();
        for (int i = 0; i < vN(TARGETS); ++i) {
                Target *target = v_(TARGETS, i);
                if (target->gc != NULL) {
                        MARK(target->gc);
                }
        }
        LOG_REACHED(" => targets reached %llu", TotalReached);

        RESET_TOTAL_REACHED();
        GCLOG("Marking frame functions");
        for (int i = 0; i < vN(FRAMES); ++i) {
                value_mark(ty, FrameFun(ty, v_(FRAMES, i)));
        }
        LOG_REACHED(" => frame fns reached %llu", TotalReached);
}

char const *
GetInstructionName(u8 i)
{
        return (i < countof(InstructionNames))
             ? InstructionNames[i]
             : "INVALID_INSTRUCTION";
}

char *
StepInstruction(char const *ip)
{
#undef  CASE
#define CASE(name) case INSTR_##name:
#undef  SKIPSTR
#undef  READVALUE
#define SKIPSTR() (ip += strlen(ip) + 1)
#define SKIPVALUE(x) (ip += sizeof x)
#define READVALUE(x) (__builtin_memcpy(&x, ip, sizeof x), SKIPVALUE(x))

        uptr s;
        imax k;
        bool b = false;
        double x;
        int n, nkw, i, j, tag;

        u8 op = (u8)*ip++;

        if (UNLIKELY(op == INSTR_TRAP_TY)) {
                op = DebugOriginalOp(ip - 1);
        }

        switch (op) {
        CASE(NOP)
                break;
        CASE(LOAD_LOCAL)
        CASE(LOAD_REF)
        CASE(LOAD_CAPTURED)
        CASE(LOAD_GLOBAL)
        CASE(LOAD_THREAD_LOCAL)
                SKIPVALUE(n);
#ifndef TY_NO_LOG
                SKIPSTR();
#endif
                break;
        CASE(CHECK_INIT)
                break;
        CASE(CAPTURE)
                SKIPVALUE(i);
                SKIPVALUE(j);
                break;
        CASE(DECORATE)
                SKIPVALUE(s);
                break;
        CASE(EXEC_CODE)
                SKIPVALUE(s);
                break;
        CASE(DUP)
        CASE(DUP2_SWAP)
                break;
        CASE(JUMP)
        CASE(TRY_UNAPPLY)
        CASE(TRY_YIELD_FROM)
                SKIPVALUE(n);
                break;
        CASE(JUMP_IF)
        CASE(JUMP_IF_NOT)
        CASE(JUMP_IF_NONE)
        CASE(JUMP_IF_NIL)
        CASE(JUMP_IF_INIT)
                SKIPVALUE(n);
                break;
        CASE(JUMP_IF_TYPE)
        CASE(JII)
        CASE(JNI)
                SKIPVALUE(n);
                SKIPVALUE(i);
                break;
        CASE(JLT)
        CASE(JLE)
        CASE(JGT)
        CASE(JGE)
        CASE(JEQ)
        CASE(JNE)
        CASE(JUMP_AND)
        CASE(JUMP_OR)
        CASE(JUMP_WTF)
        CASE(NONE_IF_NOT)
        CASE(SKIP_CHECK)
                SKIPVALUE(n);
                break;
        CASE(TARGET_GLOBAL)
        CASE(TARGET_THREAD_LOCAL)
        CASE(ASSIGN_GLOBAL)
                SKIPVALUE(n);
                break;
        CASE(TARGET_LOCAL)
        CASE(ASSIGN_LOCAL)
                SKIPVALUE(n);
                break;
        CASE(ASSIGN_SUBSCRIPT)
                READVALUE(b);
                break;
        CASE(TARGET_REF)
                SKIPVALUE(n);
                break;
        CASE(TARGET_CAPTURED)
                SKIPVALUE(n);
#ifndef TY_NO_LOG
                // TODO
                SKIPSTR();
#endif
                break;
        CASE(TARGET_STATIC_MEMBER)
                SKIPVALUE(n);
        CASE(TARGET_MEMBER)
        CASE(TARGET_SELF_MEMBER)
        CASE(TARGET_SELF_STATIC)
                SKIPVALUE(n);
                break;
        CASE(TARGET_SUBSCRIPT)
                break;
        CASE(ASSIGN)
                break;
        CASE(TAG_PUSH)
                SKIPVALUE(tag);
                break;
        CASE(ARRAY_REST)
                SKIPVALUE(n);
                SKIPVALUE(i);
                SKIPVALUE(j);
                break;
        CASE(TUPLE_REST)
                SKIPVALUE(n);
                SKIPVALUE(i);
                break;
        CASE(RECORD_REST)
                SKIPVALUE(n);
                ip = ALIGNED_FOR(int, ip);
                while (*(int const *)ip != -1) ip += sizeof (int);
                ip += sizeof (int);
                break;
        CASE(THROW_IF_NIL)
                break;
        CASE(UNTAG_OR_DIE)
                SKIPVALUE(tag);
                break;
        CASE(PUSH_UNTAGGED)
        CASE(STEAL_TAG)
                break;
        CASE(TRY_STEAL_TAG)
                SKIPVALUE(n);
                break;
        CASE(BAD_MATCH)
                break;
        CASE(BAD_DISPATCH);
                break;
        CASE(BAD_CALL)
                SKIPSTR();
                SKIPSTR();
                break;
        CASE(BAD_ASSIGN)
                SKIPSTR();
                break;
        CASE(THROW)
        CASE(RETHROW)
                break;
        CASE(FINALLY)
                break;
        CASE(END_TRY)
                break;
        CASE(POP_TRY)
                break;
        CASE(CATCH)
                break;
        CASE(TRY)
                SKIPVALUE(n);
                SKIPVALUE(n);
                SKIPVALUE(n);
                break;
        CASE(DROP)
        CASE(ENTER)
                break;
        CASE(PUSH_DROP_GROUP)
                break;
        CASE(PUSH_DROP)
                break;
        CASE(PUSH_DEFER_GROUP)
                break;
        CASE(DEFER)
                break;
        CASE(CLEANUP)
                break;
        CASE(ENSURE_LEN)
                SKIPVALUE(n);
                SKIPVALUE(n);
                break;
        CASE(ENSURE_LEN_TUPLE)
                SKIPVALUE(n);
                SKIPVALUE(n);
                break;
        CASE(MATCH_TAG)
        {
                i32 n;

                ip += 1;                    /* mode byte */
                READVALUE(n);               /* n_entries */
                ip += sizeof (i32);         /* default_offset */
                ip += n * 2 * sizeof (i32); /* tag+offset pairs */
                break;
        }
        CASE(MATCH_STRING)
        {
                i32 sz;

                READVALUE(sz);               /* table size */
                ip += sizeof (i32);          /* default_offset */
                ip += sz * 2 * sizeof (i32); /* hash table slots */
                break;
        }
        CASE(ENSURE_EQUALS_VAR)
                SKIPVALUE(n);
                break;
        CASE(TRY_ASSIGN_NON_NIL)
                SKIPVALUE(n);
                break;
        CASE(TRY_REGEX)
                SKIPVALUE(n);
                SKIPVALUE(s);
                break;
        CASE(ASSIGN_REGEX_MATCHES)
                SKIPVALUE(n);
                break;
        CASE(TRY_RANGE)
        CASE(TRY_INCRANGE)
                SKIPVALUE(n);
                break;
        CASE(ENSURE_DICT)
                SKIPVALUE(n);
                break;
        CASE(ENSURE_CONTAINS)
                SKIPVALUE(n);
                break;
        CASE(ENSURE_SAME_KEYS)
                SKIPVALUE(n);
                break;
        CASE(TRY_INDEX)
                SKIPVALUE(n);
                SKIPVALUE(i);
                SKIPVALUE(b);
                break;
        CASE(INDEX_TUPLE)
        CASE(TRY_INDEX_TUPLE)
                SKIPVALUE(n);
                SKIPVALUE(i);
                break;
        CASE(TRY_TUPLE_MEMBER)
                SKIPVALUE(n);
                SKIPVALUE(b);
                SKIPVALUE(n);
                break;
        CASE(TRY_MEMBER)
                SKIPVALUE(n);
                SKIPVALUE(n);
                break;
        CASE(TRY_TAG_POP)
                SKIPVALUE(n);
                SKIPVALUE(tag);
                break;
        CASE(POP)
        CASE(POP2)
                break;
        CASE(UNPOP)
                break;
        CASE(INT8)
                ip += 1;
                break;
        CASE(INTEGER)
                SKIPVALUE(k);
                break;
        CASE(REAL)
                SKIPVALUE(x);
                break;
        CASE(TRUE)
        CASE(FALSE)
                break;
        CASE(STRING)
                SKIPVALUE(n);
                break;
        CASE(CLASS)
                SKIPVALUE(tag);
                break;
        CASE(TAG)
                SKIPVALUE(tag);
                break;
        CASE(REGEX)
                SKIPVALUE(s);
                break;
        CASE(ARRAY)
        CASE(ARRAY0)
                break;
        CASE(TUPLE)
                SKIPVALUE(n);
                SKIPVALUE(s);
                break;
        CASE(XTUPLE)
                READVALUE(n);
                while (n --> 0) {
                        SKIPVALUE(i);
                }
                break;
        CASE(GATHER_TUPLE)
                break;
        CASE(DICT)
        CASE(DEFAULT_DICT)
        CASE(SET)
                break;
        CASE(SELF)
                break;
        CASE(NIL)
                break;
        CASE(TO_REGEX)
                break;
        CASE(YIELD)
        CASE(YIELD_SOME)
        CASE(YIELD_NONE)
                break;
        CASE(TYPE)
                SKIPVALUE(s);
                break;
        CASE(VALUE)
                SKIPVALUE(s);
                break;
        CASE(EVAL)
                SKIPVALUE(s);
                break;
        CASE(RENDER_TEMPLATE)
        CASE(NAMESPACE)
                SKIPVALUE(s);
                break;
        CASE(UNAPPLY)
                break;
        CASE(TRAP)
        CASE(TRAP_TY)
                break;
        CASE(GET_NEXT)
                break;
        CASE(LOOP_ITER)
                break;
        CASE(LOOP_CHECK)
                SKIPVALUE(n);
                SKIPVALUE(n);
                break;
        CASE(SPREAD_CHECK)
                SKIPVALUE(n);
                SKIPVALUE(b);
                break;
        CASE(ARRAY_COMPR)
        CASE(SET_COMPR)
                SKIPVALUE(n);
                break;
        CASE(DICT_COMPR)
                SKIPVALUE(n);
                SKIPVALUE(n);
                break;
        CASE(PUSH_INDEX)
                SKIPVALUE(n);
                break;
        CASE(READ_INDEX)
                break;
        CASE(SENTINEL)
                break;
        CASE(NONE)
                break;
        CASE(NONE_IF_NIL)
                break;
        CASE(FIX_EXTRA)
                break;
        CASE(FIX_TO)
                SKIPVALUE(n);
                break;
        CASE(SWAP)
                break;
        CASE(REVERSE)
                SKIPVALUE(n);
                break;
        CASE(JUMP_IF_SENTINEL)
                SKIPVALUE(n);
                break;
        CASE(CLEAR_EXTRA)
                break;
        CASE(PUSH_NTH)
                SKIPVALUE(n);
                break;
        CASE(PUSH_ARRAY_ELEM)
                SKIPVALUE(n);
                SKIPVALUE(b);
                break;
        CASE(PUSH_TUPLE_ELEM)
                SKIPVALUE(n);
                break;
        CASE(PUSH_TUPLE_MEMBER)
                SKIPVALUE(b);
                SKIPVALUE(n);
                break;
        CASE(CONCAT_STRINGS)
                SKIPVALUE(n);
                break;
        CASE(COMPILE_REGEX)
                SKIPSTR();
                break;
        CASE(RANGE)
        CASE(INCRANGE)
                break;
        CASE(STATIC_MEMBER_ACCESS)
                SKIPVALUE(n);
        CASE(TRY_MEMBER_ACCESS)
        CASE(MEMBER_ACCESS)
        CASE(SELF_MEMBER_ACCESS)
        CASE(SELF_STATIC_ACCESS)
                SKIPVALUE(n);
                break;
        CASE(TRY_GET_MEMBER)
        CASE(GET_MEMBER)
        CASE(TARGET_DYN_MEMBER)
                break;
        CASE(BIND_CLASS)
        CASE(INTO_METHOD)
                SKIPVALUE(n);
                break;
        CASE(SLICE)
        CASE(SUBSCRIPT)
        CASE(SAFE_SUBSCRIPT)
        CASE(NOT)
        CASE(QUESTION)
        CASE(NEG)
        CASE(COUNT)
        CASE(ADD)
        CASE(SUB)
        CASE(MUL)
        CASE(DIV)
        CASE(MOD)
        CASE(EQ)
        CASE(NEQ)
        CASE(CHECK_MATCH)
        CASE(CLASS_OF)
        CASE(LT)
        CASE(GT)
        CASE(LEQ)
        CASE(GEQ)
        CASE(CMP)
        CASE(GET_TAG)
        CASE(INC)
        CASE(DEC)
        CASE(PRE_INC)
        CASE(POST_INC)
        CASE(PRE_DEC)
        CASE(POST_DEC)
        CASE(MUT_ADD)
        CASE(MUT_MUL)
        CASE(MUT_DIV)
        CASE(MUT_MOD)
        CASE(MUT_SUB)
                 break;
        CASE(UNARY_OP)
        CASE(BINARY_OP)
                SKIPVALUE(n);
                break;
        CASE(DEFINE_TAG)
        {
                int tag, super, t, n, g, s_g;
                READVALUE(tag);
                READVALUE(super);
                READVALUE(n);
                READVALUE(t);
                READVALUE(g);
                READVALUE(s_g);
                while (n --> 0) {
                        SKIPSTR();
                }
                while (t --> 0) {
                        SKIPSTR();
                }
                for (int i = 0; i < g + s_g; ++i) {
                        i32 member;
                        SKIPVALUE(member);
                }
                break;
        }
        CASE(DEFINE_CLASS)
        {
                i32 class;
                i32   m,   g,   s;
                i32 s_m, s_g, s_s;

                SKIPVALUE(class);

                READVALUE(s_m);
                READVALUE(s_g);
                READVALUE(s_s);
                READVALUE(m);
                READVALUE(g);
                READVALUE(s);

                while (s_m --> 0) { SKIPVALUE(i); }
                while (s_g --> 0) { SKIPVALUE(i); }
                while (s_s --> 0) { SKIPVALUE(i); }
                while (  m --> 0) { SKIPVALUE(i); }
                while (  g --> 0) { SKIPVALUE(i); }
                while (  s --> 0) { SKIPVALUE(i); }
                break;
        }
        CASE(INIT_STATIC_FIELD)
                SKIPVALUE(i);
                SKIPVALUE(i);
                break;
        CASE(FUNCTION)
        CASE(GENERATOR)
        {
                u16 ncaps;
                READVALUE(ncaps);

                ip += ncaps * sizeof (u32);
                ip = ALIGNED_FOR(i64, ip);

                i32 *info = (i32 *) ip;

                ip += info[0] + info[1];

                break;
        }
        CASE(BIND_INSTANCE)
        CASE(BIND_GETTER)
        CASE(BIND_SETTER)
        CASE(BIND_STATIC)
                SKIPVALUE(i);
                SKIPVALUE(j);
                break;
        CASE(PATCH_ENV)
                SKIPVALUE(n);
                break;
        CASE(OPERATOR)
                SKIPVALUE(i);
                SKIPVALUE(j);
                break;
        CASE(TAIL_CALL)
                break;
        CASE(CALL_GLOBAL)
                SKIPVALUE(n);
        CASE(CALL)
                SKIPVALUE(n);
                READVALUE(nkw);
                for (int i = 0; i < nkw; ++i) {
                        SKIPSTR();
                }
                break;
        CASE(CALL_STATIC_METHOD)
                SKIPVALUE(n);
        CASE(TRY_CALL_METHOD)
        CASE(CALL_METHOD)
        CASE(CALL_SELF_METHOD)
        CASE(CALL_SELF_STATIC)
                SKIPVALUE(n);
                SKIPVALUE(n);
                READVALUE(nkw);
                for (int i = 0; i < nkw; ++i) {
                        SKIPSTR();
                }
                break;
        CASE(SAVE_STACK_POS)
                break;
        CASE(POP_STACK_POS)
        CASE(POP_STACK_POS_POP)
                break;
        CASE(RETURN_IF_NOT_NONE)
        CASE(RETURN)
        CASE(RETURN_PRESERVE_CTX)
        CASE(HALT)
                break;
        CASE(DEBUG)
                SKIPSTR();
                break;
        }

        return (char *)ip;
}

Ty *
vm_new_debug_ty(void)
{
        Ty *ty = mrealloc(NULL, sizeof *ty);

        InitializeTy(ty, &MainGroup);

        MyTy = ty;
        MyId = ty->id = NextThreadId();

        AddThread(ty, TyThreadSelf());

        return ty;
}

void
vm_free_debug_ty(Ty *ty)
{
        CleanupThread(ty);
}

Value *
vm_global(Ty *ty, int i)
{
        return v_(Globals, i);
}

Value *
vm_local(Ty *ty, int i)
{
        return local(ty, i);
}

Value
vm_make_range(Ty *ty, Value const *a, Value const *b, bool inclusive)
{
        xvP(STACK, *a);
        xvP(STACK, *b);
        DoRange(ty, inclusive);
        Value result = *vvL(STACK);
        vN(STACK) -= 1;
        return result;
}

bool
TyReloadModule(Ty *ty, char const *module)
{
        UnlockTy();
        TySpinLockLock(&ty->group->GCLock);
        TakeLockRaw(ty);

        TySpinLockLock(&ty->group->Lock);

        ty->group->WantGC = true;
        JitInterruptFlag  = 1;

        usize nThreads = vN(ty->group->ThreadList);
        if (nThreads > ty->group->GCThreadCapacity) {
                ty->group->GCBlockedThreads = mrealloc(
                        ty->group->GCBlockedThreads,
                        nThreads * sizeof *ty->group->GCBlockedThreads
                );
                ty->group->GCThreadCapacity = nThreads;
        }
        int *blockedThreads = ty->group->GCBlockedThreads;

        int nBlocked = 0;
        int nRunning = 0;

        for (int i = 0; i < vN(ty->group->ThreadList); ++i) {
                if (ty->lock == v__(ty->group->ThreadLocks, i)) {
                        continue;
                }
                TySpinLockLock(v__(ty->group->ThreadLocks, i));
                if (TryFlipTo(v__(ty->group->ThreadStates, i), true)) {
                        nRunning += 1;
                        TySpinLockUnlock(v__(ty->group->ThreadLocks, i));
                } else {
                        blockedThreads[nBlocked++] = i;
                }
        }

        StartGC(ty);

        while (ty->group->GCReadyCount < nRunning) {
                ;
        }
        // ======================================================================================
        GC_STOP();
        TY_BEGIN_LOADING();


        bool ok = false;

        if (TY_CATCH_ERROR()) {
                TY_CATCH();
        } else {
                Module *mod = CompilerGetModule(ty, module);
                if (mod != NULL && CompilerReloadModule(ty, mod, NULL)) {
                        vm_exec(ty, mod->code);
                        ok = true;
                }
                TY_CATCH_END();
        }

        TY_FINISH_LOADING();
        GC_RESUME();
        // ======================================================================================
        NextGCPhase(ty, GC_PHASE_SWEEP, nRunning);
        ty->group->WantGC = false;
        NextGCPhase(ty, GC_PHASE_DONE, nRunning);
        EndGC(ty);
        UnlockThreads(ty, blockedThreads, nBlocked);
        TySpinLockUnlock(&ty->group->Lock);
        TySpinLockUnlock(&ty->group->GCLock);

        return ok;
}

noreturn void
ZeroDividePanic(Ty *ty)
{
        vmE(&TAG(TAG_ZERO_DIV_ERR));
}

struct try *
vm_push_try(Ty *ty)
{
        struct try *t = PushTry(ty);
        t->catch  = IP;
        t->end    = IP;
        t->native = true;
        return t;
}

Value
vm_catch(Ty *ty)
{
        Value exc = pop();

        while (pop().type != VALUE_SENTINEL) {
                continue;
        }

        vXx(TRY_STACK);
        vXx(THROW_STACK);

        return exc;
}

Value
TyCatchDetail(Ty *ty, Value *detail)
{
        ThrowCtx *ctx = CurrentThrowCtx(ty);
        Value exc = ctx->exc;

        if (detail != NULL) {
                byte_vector trace = {0};
                *detail = NIL;
                FormatTrace(ty, ctx, &trace);
                if (vN(trace) > 0) {
                        GC_STOP();
                        *detail = vSs(vv(trace), vN(trace));
                        GC_RESUME();
                }
                xvF(trace);
        }

        return vm_catch(ty);
}

noreturn void
vm_rethrow(Ty *ty)
{
        Value exc = pop();

        while (pop().type != VALUE_SENTINEL) {
                continue;
        }

        push(exc);

        vXx(TRY_STACK);
        DoThrow(ty);
        vm_exec(ty, IP);

        UNREACHABLE();
}

void
vm_finally(Ty *ty)
{
        vXx(TRY_STACK);
}

void *
vm_jit_push_try(Ty *ty, char *catch_addr, char *finally_addr, char *end_addr)
{
        struct try *t = PushTry(ty);
        t->catch   = catch_addr;
        t->finally = finally_addr;
        t->end     = end_addr;
        return t->jb;
}

noreturn void
vm_jit_end_try_rethrow(Ty *ty)
{
        DoThrow(ty);
        UNREACHABLE();
}

bool
vm_jit_array_rest(Ty *ty, Value *tos, Value *target, i32 start, i32 suffix)
{
        if (tos->type != VALUE_ARRAY || vN(*tos->array) < start + suffix) {
                return false;
        }

        Array *rest = vA();
        uvPn(*rest, vv(*tos->array) + start, vN(*tos->array) - (start + suffix));
        *target = ARRAY(rest);

        return true;
}

bool
vm_jit_tuple_rest(Ty *ty, Value *tos, Value *target, i32 start)
{
        if (tos->type != VALUE_TUPLE) {
                return false;
        }

        i32 count = tos->count - start;
        Value *rest = mAo(count * sizeof (Value), GC_TUPLE);
        memcpy(rest, tos->items + start, count * sizeof (Value));
        *target = TUPLE(rest, NULL, count);

        return true;
}

bool
vm_jit_record_rest(Ty *ty, Value *tos, Value *target, i32 const *excluded_ids)
{
        if (tos->type != VALUE_TUPLE) {
                return false;
        }

        Value v = *tos;

        vec(i32) ids = {0};
        vec(i32) indices = {0};

        SCRATCH_SAVE();

        for (i32 i = 0; i < v.count; ++i) {
                if (v.ids == NULL || v.ids[i] == -1) {
                        continue;
                }
                if (!search_i32(excluded_ids, v.ids[i])) {
                        svP(ids, v.ids[i]);
                        svP(indices, i);
                }
        }

        Value value = vT(ids.count);
        value.ids = uAo(value.count * sizeof (i32), GC_TUPLE);

        memcpy(value.ids, vv(ids), value.count * sizeof (i32));

        for (i32 i = 0; i < value.count; ++i) {
                value.items[i] = v.items[v__(indices, i)];
        }

        SCRATCH_RESTORE();

        *target = value;

        return true;
}

Value
vm_jit_member_access(Ty *ty, int z)
{
        Value receiver = peek();

        if (receiver.type == VALUE_OBJECT) {
                u16 offset = FastReadOffset(ty, &receiver, z);
                if (offset != OFF_NOT_FOUND) {
                        int kind = offset >> OFF_SHIFT;
                        int index = offset & OFF_MASK;
                        Value *callee;
                        Value *self;

                        switch (kind) {
                        case OFF_FIELD:
                                pop();
                                return receiver.object->slots[index];

                        case OFF_GETTER:
                                callee = v_(
                                        class_get(ty, receiver.class)->getters.values,
                                        index
                                );
                                exec_fn(ty, callee, &receiver, 0, NULL);
                                receiver = pop();
                                pop();
                                return receiver;

                        case OFF_GETTER_X:
                                callee = &receiver.object->slots[index];
                                exec_fn(ty, callee, &receiver, 0, NULL);
                                receiver = pop();
                                pop();
                                return receiver;

                        case OFF_METHOD:
                                callee = v_(
                                        class_get(ty, receiver.class)->methods.values,
                                        index
                                );
                                self = uAo(sizeof *self, GC_VALUE);
                                *self = receiver;
                                pop();
                                return METHOD(z, callee, self);
                        }
                }
        }

        Value value = GetMember(ty, z, true, true);
        if (UNLIKELY(value.type == VALUE_NONE)) {
                xpush(*vZ(STACK));
                BadFieldAccess(ty, top(), z);
                UNREACHABLE();
        }
        return value;
}

void
vm_jit_get_member(Ty *ty)
{
        i32 z = GetDynamicMemberId(ty, true);
        if (z < 0) {
                z = -(z + 1);
        }

        xpush(vm_jit_member_access(ty, z));
}

void
vm_jit_target_member(Ty *ty, Value *v, i32 z)
{
        if (!TargetFieldFast(ty, v, z)) {
                DoTargetMember(ty, *v, z);
        }
}

void
vm_jit_dyn_member_assign(Ty *ty)
{
        i32 z = GetDynamicMemberId(ty, true);
        if (z < 0) {
                z = -(z + 1);
        }

        if (!TargetFieldFast(ty, top(), z)) {
                DoTargetMember(ty, peek(), z);
        }

        pop();
        DoAssignExec(ty);
}

void
vm_jit_try_member_access(Ty *ty, int z)
{
        Value v = GetMember(ty, z, true, true);
        push(!IsNone(v) ? v : NIL);
}

bool
vm_jit_try_match_member(Ty *ty, int z)
{
        push(peek());
        Value value = GetMember(ty, z, false, true);
        if (IsNone(value)) {
                return false;
        }
        push(value);
        return true;
}

bool
vm_jit_unapply(Ty *ty, bool maybe)
{
        Value f = pop();
        Value self = NIL;
        if (maybe && f.type == VALUE_CLASS) {
                Value *method = class_lookup_s_method_i(ty, f.class, NAMES.unapply);
                if (method == NULL) {
                        return false;
                }
                self = f;
                f = *method;
        }
        if (f.type == VALUE_METHOD) {
                self = *f.this;
                f = *f.method;
        }
        char *saved = IP;
        IP = &halt;
        push(peek());
        if (f.type == VALUE_FUNCTION || f.type == VALUE_BOUND_FUNCTION) {
                call6t(ty, &f, self.type == VALUE_NIL ? NULL : &self, 1, NULL, unapply);
                if (!is_starred(&f) && call_jit(ty, &f)) {
                        vXx(CALLS);
                } else {
                        vm_exec(ty, IP);
                }
        } else if (DoCall(ty, &f, 1, 0, false)) {
                xvP(CALLS, unapply);
                vm_exec(ty, IP);
        }
        IP = saved;
        return true;
}

bool
vm_jit_yield_from(Ty *ty)
{
        Value value = peek();
        if (value.type != VALUE_GENERATOR
            || value.gen->co != NULL || value.gen->st == NULL) {
                return false;
        }
        char *saved = IP;
        char *body = value.gen->ip;
        pop();
        xvP(FRAMES, v_0(value.gen->st->frames));
        vvL(FRAMES)->fp = vN(STACK);
        xvPn(STACK, v_(value.gen->st->stack, 1), vN(value.gen->st->stack) - 1);
        if (body != code_of(&value.gen->f)) {
                push(NIL);
        }
        xvP(ty->co_states, value.gen->st);
        value.gen->st = NULL;
        xvP(CALLS, &halt);
        IP = body;
        Value f = vvL(FRAMES)->f;
        if (body == &JIT) {
                go_jit(ty);
        } else if (body != code_of(&f) || !call_jit(ty, &f)) {
                vm_exec(ty, body);
        }
        IP = saved;
        return true;
}

void
vm_jit_declaration(Ty *ty, char *ip)
{
        char *saved = IP;
        int op = (u8)*ip;
        IP = ip + 1;
        if (op == INSTR_DEFINE_TAG) {
                i32 tag;
                i32 super;
                i32 n;
                i32 c;
                i32 g;
                i32 s_g;
                memcpy(&tag, IP, sizeof tag);
                IP += sizeof tag;
                memcpy(&super, IP, sizeof super);
                IP += sizeof super;
                memcpy(&n, IP, sizeof n);
                IP += sizeof n;
                memcpy(&c, IP, sizeof c);
                IP += sizeof c;
                memcpy(&g, IP, sizeof g);
                IP += sizeof g;
                memcpy(&s_g, IP, sizeof s_g);
                IP += sizeof s_g;
                while (n-- > 0) {
                        Value value = pop();
                        tags_add_method(ty, tag, IP, value);
                        IP += strlen(IP) + 1;
                }
                while (c-- > 0) {
                        Value value = pop();
                        tags_add_static(ty, tag, IP, value);
                        IP += strlen(IP) + 1;
                }
                if (g != 0 || s_g != 0) {
                        Class *class = tags_get_class(ty, tag);
                        InstallMethods(ty, class->i, &class->getters, g);
                        InstallMethods(ty, class->i, &class->s_getters, s_g);
                }
                if (super != -1) {
                        tags_copy_methods(ty, tag, super);
                }
        } else if (op == INSTR_DEFINE_CLASS) {
                i32 id;
                i32 s_m;
                i32 s_g;
                i32 s_s;
                i32 m;
                i32 g;
                i32 s;
                memcpy(&id, IP, sizeof id);
                IP += sizeof id;
                memcpy(&s_m, IP, sizeof s_m);
                IP += sizeof s_m;
                memcpy(&s_g, IP, sizeof s_g);
                IP += sizeof s_g;
                memcpy(&s_s, IP, sizeof s_s);
                IP += sizeof s_s;
                memcpy(&m, IP, sizeof m);
                IP += sizeof m;
                memcpy(&g, IP, sizeof g);
                IP += sizeof g;
                memcpy(&s, IP, sizeof s);
                IP += sizeof s;
                Class *class = class_get(ty, id);
                        InstallMethods(ty, id, &class->s_methods, s_m);
                InstallMethods(ty, id, &class->s_getters, s_g);
                InstallMethods(ty, id, &class->s_setters, s_s);
                InstallMethods(ty, id, &class->methods, m);
                InstallMethods(ty, id, &class->getters, g);
                InstallMethods(ty, id, &class->setters, s);
                if (class->super != NULL) {
                        Value *hook = class_lookup_s_method_i(ty, class->super->i, NAMES._init_subclass_);
                        if (hook != NULL) {
                                Value self = CLASS(id);
                                exec_fn(ty, hook, &self, 0, NULL);
                                pop();
                        }
                }
        } else {
                i32 id;
                i32 member;
                memcpy(&id, IP, sizeof id);
                IP += sizeof id;
                memcpy(&member, IP, sizeof member);
                IP += sizeof member;
                Value value = pop();
                Value *slot = itable_get(ty, &class_get(ty, id)->s_fields, member);
                if (slot->type == VALUE_REF) {
                        *slot->ref = value;
                }
                *slot = value;
        }
        IP = saved;
}

void
vm_jit_failure(Ty *ty, int op, char *ip)
{
        if (op != INSTR_BAD_ASSIGN && v_L(CALLS) == unapply) {
                if (op == INSTR_BAD_DISPATCH) {
                        push(NONE);
                } else {
                        put(NONE);
                }
                return;
        }
        if (op == INSTR_BAD_DISPATCH) {
                push(TAG(TAG_DISPATCH_ERR));
                vXx(FRAMES);
                IP = vXx(CALLS);
                RaiseException(ty);
                UNREACHABLE("dispatch failure returned");
        }
        char *name = ip + 1;
        char *label = name;
        if (op == INSTR_BAD_CALL) {
                label += strlen(name) + 1;
                zP(
                        "constraint on %s%s%s%s%s violated in call to %s%s%s%s%s: %s%s%s = %s%s%s",
                        TERM(34), TERM(1), label, TERM(22), TERM(39),
                        TERM(34), TERM(1), name, TERM(22), TERM(39),
                        TERM(34), TERM(1), label, VSC(top()), TERM(22), TERM(39)
                );
        }
        zP(
                "constraint on %s%s%s%s%s violated in assignment: %s%s%s = %s%s%s",
                TERM(34), TERM(1), label, TERM(22), TERM(39),
                TERM(34), TERM(1), label, VSC(top()), TERM(22), TERM(39)
        );
}

bool
vm_jit_check_init(Ty *ty)
{
        Value self = GetSelf(ty);
        bool initialized = self.object->init;
        self.object->init = true;
        return initialized;
}

bool
vm_jit_extra_branch(Ty *ty, int op)
{
        switch (op) {
        case INSTR_JUMP_WTF:
                if (top()->type == VALUE_NIL) {
                        pop();
                        return false;
                }
                return true;
        case INSTR_NONE_IF_NOT:
                if (value_truthy(ty, top())) {
                        pop();
                        return false;
                }
                put(NONE);
                return true;
        default:
                if (!TY_IS_INITIALIZED) {
                        put(BOOLEAN(true));
                        return true;
                }
                return false;
        }
}

void
vm_jit_misc(Ty *ty, int op, int n, void *data)
{
        Value value;
        switch (op) {
        case INSTR_UNARY_OP:
                DoUnaryOp(ty, n, true);
                break;
        case INSTR_BINARY_OP:
                DoBinaryOp(ty, n, true);
                break;
        case INSTR_QUESTION:
                DoQuestion(ty, true);
                break;
        case INSTR_SLICE:
                CallMethod(ty, NAMES.slice, 3, 0, false, true);
                break;
        case INSTR_TO_REGEX:
                if (top()->type == VALUE_REGEX) {
                        put(vSsz(top()->regex->pattern));
                        break;
                }
                if (top()->type == VALUE_PTR) {
                        put(value_vshow_color(ty, top(), 0));
                } else if (top()->type != VALUE_NIL) {
                        CallMethod(ty, NAMES._str_, 0, 0, false, true);
                }
                put(builtin_regex_escape(ty, 1, NULL));
                break;
        case INSTR_COMPILE_REGEX:
                push(xSz(data));
                value = builtin_regex(ty, 2, NULL);
                pop();
                put(value);
                break;
        case INSTR_EVAL:
                push(PTR(data));
                value = builtin_eval(ty, 2, NULL);
                pop();
                put(value);
                break;
        case INSTR_EXEC_CODE:
                vm_exec(ty, data);
                break;
        case INSTR_RENDER_TEMPLATE:
                push(compiler_render_template(ty, data));
                break;
        case INSTR_NAMESPACE:
                push(NAMESPACE(data));
                break;
        case INSTR_TRACE:
                push(ResolveTrace(ty, CurrentThrowCtx(ty)));
                break;
        case INSTR_GET_TAG:
                value = pop();
                push(value.tags == 0 ? NIL : TAG(tags_first(ty, value.tags)));
                break;
        case INSTR_OPERATOR: {
                i32 b;
                memcpy(&b, data, sizeof b);
                push(OPERATOR(n, b));
                break;
        }
        case INSTR_GET_NEXT:
                IterGetNext(ty, true);
                break;
        case INSTR_READ_INDEX:
                push(INTEGER(top()[-3].z - 1));
                break;
        case INSTR_NONE_IF_NIL:
                YieldFix(ty);
                break;
        case INSTR_FIX_EXTRA:
        case INSTR_FIX_TO: {
                i32 count = 0;
                while (top()[-count].type != VALUE_SENTINEL) {
                        ++count;
                }
                if (op == INSTR_FIX_TO) {
                        while (count > n) {
                                --count;
                                pop();
                        }
                        while (count < n) {
                                ++count;
                                push(NIL);
                        }
                }
                for (i32 i = 0, j = count - 1; i < j; ++i, --j) {
                        value = top()[-i];
                        top()[-i] = top()[-j];
                        top()[-j] = value;
                }
                break;
        }
        case INSTR_REVERSE:
                for (i32 i = 0, j = n - 1; i < j; ++i, --j) {
                        value = top()[-i];
                        top()[-i] = top()[-j];
                        top()[-j] = value;
                }
                break;
        case INSTR_DEBUG:
                fprintf(stderr, "%s\n", (char const *)data);
                break;
        case INSTR_TRAP:
                *(volatile char *)0 = 0;
                break;
        default:
                UNREACHABLE("invalid JIT miscellaneous operation");
        }
}

Value *
vm_jit_state_slot(Ty *ty, int n, bool tls)
{
        if (tls) {
                EnsureThreadLocal(ty, n);
                return v_(THREAD_LOCALS, n);
        }
        while (vN(Globals) <= n) {
                xvP(Globals, NIL);
        }
        return v_(Globals, n);
}

void
vm_jit_scope(Ty *ty, int op)
{
        switch (op) {
        case INSTR_DROP:
                DoDrop(ty);
                break;
        case INSTR_DISCARD_DROP_GROUP:
                vXx(DROP_STACK);
                break;
        case INSTR_PUSH_DROP_GROUP:
                xvP(DROP_STACK, ARRAY(vA()));
                break;
        case INSTR_PUSH_DROP:
                if (vN(DROP_STACK) == 0) {
                        zP("no active drop group for resource binding");
                }
                uvP(*vvL(DROP_STACK)->array, peek());
                break;
        case INSTR_PUSH_DEFER_GROUP:
                GetCurrentTry(ty)->clean = true;
                break;
        case INSTR_DEFER:
                xvP(GetDeferTry(ty)->defer, pop());
                break;
        case INSTR_CLEANUP: {
                struct try *t = GetCurrentTry(ty);
                while (vN(t->defer) > 0) {
                        Value f = vXx(t->defer);
                        vm_call(ty, &f, 0);
                }
                break;
        }
        case INSTR_ENTER: {
                int class = ClassOf(top());
                if (class < 0) {
                        break;
                }
                if (vN(DROP_STACK) == 0) {
                        zP("no active drop group for enter instruction");
                }
                uvP(*vvL(DROP_STACK)->array, peek());
                Value *f = class_lookup_method_i(ty, class, NAMES._enter_);
                if (f != NULL) {
                        Value self = pop();
                        exec_fn(ty, f, &self, 0, NULL);
                }
                break;
        }
        default:
                UNREACHABLE("invalid JIT scope operation");
        }
}

void
vm_jit_mutation(Ty *ty, int op)
{
        if (SpecialTarget(ty)) {
                char const *name = op == INSTR_POST_DEC ? "post-decrement" : "pre-increment";
                if (op == INSTR_PRE_DEC) {
                        name = "pre-decrement";
                }
                zP("%s applied to invalid target", name);
        }
        bool post = op == INSTR_POST_INC || op == INSTR_POST_DEC;
        bool dec = op == INSTR_PRE_DEC || op == INSTR_POST_DEC;
        if (post) {
                push(*peektarget());
        }
        if (dec) {
                DecValue(ty, peektarget());
        } else {
                IncValue(ty, peektarget());
        }
        Value value = *poptarget();
        if (!post) {
                push(value);
        }
}

void
vm_jit_target(Ty *ty, int op, int n, int z)
{
        switch (op) {
        case INSTR_TARGET_GLOBAL:
        case INSTR_TARGET_THREAD_LOCAL:
                vm_jit_push_target(ty, vm_jit_state_slot(ty, n, op == INSTR_TARGET_THREAD_LOCAL));
                break;
        case INSTR_TARGET_SELF_STATIC: {
                Value self = GetSelf(ty);
                DoTargetMember(ty, CLASS(ClassOf(&self)), n);
                break;
        }
        case INSTR_TARGET_STATIC_MEMBER:
                DoTargetMember(ty, CLASS(n), z);
                break;
        case INSTR_TARGET_DYN_MEMBER:
                z = GetDynamicMemberId(ty, true);
                if (z < 0) {
                        z = -(z + 1);
                }
                DoTargetMember(ty, peek(), z);
                pop();
                break;
        default:
                UNREACHABLE("invalid JIT target operation");
        }
}

void
vm_jit_binding(Ty *ty, int op, int n, int z, void *info)
{
        isize index = vN(STACK) - 1;
        Value value = NIL;
        if (
                op != INSTR_BIND_STATIC
             && op != INSTR_SELF_STATIC_ACCESS
             && op != INSTR_STATIC_MEMBER_ACCESS
        ) {
                value = peek();
        }
        Value *f;
        int class = n < 0 ? -n : n;
        switch (op) {
        case INSTR_DECORATE:
                if (value.type == VALUE_FUNCTION) {
                        top()->xinfo = info;
                }
                return;
        case INSTR_INTO_METHOD:
                if (value.type != VALUE_FUNCTION) {
                        zP("method decorator returned non-function: %s", VSC(&value));
                }
                value = IntoMethod(ty, &value, n);
                break;
        case INSTR_BIND_CLASS:
                value = BindMethod(ty, &value, &CLASS(n));
                break;
        case INSTR_BIND_STATIC:
                f = SuperMember(ty, class_lookup_s_method_i(ty, n, z), n, z, "static method");
                push(*f);
                return;
        case INSTR_SELF_STATIC_ACCESS:
                value = GetSelf(ty);
                z = n;
                n = ClassOf(&value);
        case INSTR_STATIC_MEMBER_ACCESS:
                push(CLASS(n));
                value = GetMember(ty, z, false, true);
                push(value);
                return;
        default: {
                u16 offset = OFF_NOT_FOUND;
                if (n >= 0) {
                        Value receiver = OBJECT(value.object, n);
                        offset = op == INSTR_BIND_SETTER
                               ? FastWriteOffset(ty, &receiver, z)
                               : FastReadOffset(ty, &receiver, z);
                }
                if (offset == OFF_NOT_FOUND) {
                        switch (op) {
                        case INSTR_BIND_INSTANCE: f = SuperMember(ty, class_lookup_method_i(ty, class, z), class, z, "method"); break;
                        case INSTR_BIND_GETTER:   f = SuperMember(ty, class_lookup_getter_i(ty, class, z), class, z, "getter"); break;
                        default:                 f = SuperMember(ty, class_lookup_setter_i(ty, class, z), class, z, "setter"); break;
                        }
                } else {
                        int kind = offset >> OFF_SHIFT;
                        int slot = offset & OFF_MASK;
                        switch (kind) {
                        case OFF_METHOD: f = v_(class_get(ty, n)->methods.values, slot); break;
                        case OFF_GETTER: f = v_(class_get(ty, n)->getters.values, slot); break;
                        case OFF_SETTER: f = v_(class_get(ty, n)->setters.values, slot); break;
                        case OFF_METHOD_X:
                        case OFF_GETTER_X:
                        case OFF_SETTER_X:
                                f = DecoratedSlot(&value, n, slot);
                                if (f == NULL) {
                                        switch (kind) {
                                        case OFF_METHOD_X: f = class_lookup_method_i(ty, n, z); break;
                                        case OFF_GETTER_X: f = class_lookup_getter_i(ty, n, z); break;
                                        default:          f = class_lookup_setter_i(ty, n, z); break;
                                        }
                                }
                                break;
                        default:
                                UNREACHABLE("invalid JIT binding offset");
                        }
                }
                value = BindMethod(ty, f, &value);
                break;
        }
        }
        *v_(STACK, index) = value;
}

void
vm_jit_try_get_member(Ty *ty)
{
        i32 z = GetDynamicMemberId(ty, false);

        if (z < 0) {
                *top() = NIL;
        } else {
                vm_jit_try_member_access(ty, z);
        }
}

void
TyPostFork(Ty *ty)
{
        TySpinLockInit(&ty->group->GCLock);
        TySpinLockInit(&ty->group->Lock);
        TySpinLockInit(&ty->group->DLock);
        TySpinLockInit(ty->lock);
        TySpinLockLock(ty->lock);
}

void
TyRunForkHooks(Ty *ty)
{
        int id = NAMES.fork_hooks;

        if (
                (id == -1)
             || (Globals.items[id].type != VALUE_ARRAY)
        ) {
                return;
        }

        Array *hooks = v_(Globals, id)->array;

        for (usize i = 0; i < vN(*hooks); ++i) {
                if (TY_CATCH_ERROR()) {
                        TY_CATCH();
                } else {
                        vmC(v_(*hooks, i), 0);
                        TY_CATCH_END();
                }
        }
}

void
TySyncThreadState(Ty *ty)
{
        MyTy = ty;
        MyId = ty->id;
}

Value
TyActiveGenerator(Ty *ty)
{
        Generator *gen = GetCurrentGenerator(ty);
        return (gen != NULL) ? GENERATOR(gen) : NIL;
}

Ty *
GetMyTy(void)
{
        if (UNLIKELY(MyTy == NULL)) {
                Ty *ty = mrealloc(NULL, sizeof *ty);
                ThreadGroup *group = NewThreadGroup(&MainGroup);
                if (group == NULL) {
                        panic("too many isolated thread groups (at most %d)", GC_OWNER_MAX - 1);
                }
                InitializeTy(ty, group);
                AddThread(ty, TyThreadSelf());
                ty->flags |= TY_F_FOREIGN;
                ty->id = NextThreadId();
                MyTy = ty;
                MyId = ty->id;
        }

        return MyTy;
}

/* vim: set sts=8 sw=8 expandtab: */
