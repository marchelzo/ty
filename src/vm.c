#ifdef _WIN32
#include <winsock2.h>
#include <ws2tcpip.h>
#endif

#include "ty.h"

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


#include <curl/curl.h>
#include <pcre2.h>

#include <fcntl.h>
#include <signal.h>
#include <unistd.h>

#include "polyfill_unistd.h"
#include "polyfill_stdatomic.h"
#include "barrier.h"
#include "tthread.h"

#ifdef __linux__
#include <sys/epoll.h>
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
#include <sys/socket.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <sys/un.h>
#include <sys/wait.h>
#include <termios.h>
#endif

#include "alloc.h"
#include "array.h"
#include "blob.h"
#include "cffi.h"
#include "class.h"
#include "compiler.h"
#include "curl.h"
#include "dict.h"
#include "functions.h"
#include "gc.h"
#include "html.h"
#include "intern.h"
#include "istat.h"
#include "log.h"
#include "object.h"
#include "operators.h"
#include "sqlite.h"
#include "str.h"
#include "tags.h"
#include "test.h"
#include "types.h"
#include "utf8.h"
#include "xd.h"
#include "value.h"
#include "vm.h"

#define TY_LOG_VERBOSE 1

#define SKIPSTR()    (IP += strlen(IP) + 1)
#define READSTR(s)   do { (s) = IP; SKIPSTR(); } while (0)
#define READVALUE(s) (__builtin_memcpy(&s, IP, sizeof s), (IP += sizeof s))
#define READJUMP(c)  (((c) = IP), (IP += sizeof (int)))
#define DOJUMP(c)    (IP = (c) + load_int((c)) + sizeof (int))

#if defined(TY_LOG_VERBOSE) && !defined(TY_NO_LOG)
  static _Thread_local Expr *expr;
  #define CASE(i)                                        \
        case INSTR_ ## i:                                \
        expr = compiler_find_expr(ty, IP - 1);           \
        LOG(                                             \
                "%07ju:%s:%d:%d: " #i,                   \
                (uptr)(IP - 1) & 0xFFFFFFFF,        \
                expr ? GetExpressionModule(expr) : "",   \
                (expr ? expr->start.line : 0) + 1,       \
                (expr ? expr->start.col : 0) + 1         \
        );
#else
  #define XXCASE(i) case INSTR_ ## i: expr = compiler_find_expr(ty, IP); fprintf(stderr, "%s:%d:%d: " #i "\n", GetExpressionModule(expr), (expr ? expr->start.line : 0) + 1, (expr ? expr->start.col : 0) + 1);
  #define CASE(i) case INSTR_ ## i:
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
static char next_fix[]  = { INSTR_NONE_IF_NIL, INSTR_RETURN_PRESERVE_CTX };
static char iter_fix[]  = { INSTR_SENTINEL, INSTR_GET_NEXT, INSTR_RETURN_PRESERVE_CTX };
static char hook_fix[]  = { INSTR_POP, INSTR_RETURN_PRESERVE_CTX };
static char unapply[]   = { INSTR_RETURN_PRESERVE_CTX };

InternedNames NAMES;

static ValueVector Globals;
/* ========================================================================== */

#define FRAME(n, fn, from) ((Frame){ .fp = (n), .f = (fn), .ip = (from) })

#define TY_INSTR_INLINE

#define IP            (ty->ip)
#define CO_THREADS    (ty->cothreads)
#define JB            (ty->jb)
#define RC            (ty->rc)
#define STACK         (ty->stack)
#define THREAD_LOCALS (ty->tls)
#define THROW_STACK   (ty->throw_stack)

#define CALLS         (ty->st.calls)
#define DROP_STACK    (ty->st.to_drop)
#define EXEC_DEPTH    (ty->st.exec_depth)
#define FRAMES        (ty->st.frames)
#define SP_STACK      (ty->st.sps)
#define TARGETS       (ty->st.targets)
#define TRY_STACK     (ty->st.try_stack)
#define VISITING      (ty->visiting)

#define top()   ((top)(ty))
#define topN(i) ((topN)(ty, i))
#define pop()   ((pop)(ty))
#define peek()  ((peek)(ty))
#define push(x) ((push)(ty, (x)))
#define swap()  ((swap)(ty))

#define poptarget()      ((poptarget)(ty))
#define peektarget()     ((peektarget)(ty))
#define pushtarget(t, g) ((pushtarget)(ty, (t), (g)))

#define GC_IS_WAITING \
        atomic_load_explicit(&MyGroup->WantGC, memory_order_relaxed)

#define TAKE_PENDING_SIGNALS() \
        __sync_bool_compare_and_swap(&AnySignalPending, 1, 0)


#ifdef TY_PROFILER
bool UseWallTime = false;
FILE *ProfileOut = NULL;

static char throw = INSTR_THROW;

inline static u64 TyThreadWallTime()
{
#ifdef _WIN32
        LARGE_INTEGER counter;
        LARGE_INTEGER frequency;
        QueryPerformanceCounter(&counter);
        QueryPerformanceFrequency(&frequency);
        return (u64)(counter.QuadPart * 1000000000ULL / frequency.QuadPart);
#else
        struct timespec t;
        clock_gettime(CLOCK_MONOTONIC, &t);
        return 1000000000ULL * t.tv_sec + t.tv_nsec;
#endif
}

inline static u64
TyThreadTime(void)
{
        return UseWallTime ? TyThreadWallTime() : TyThreadCPUTime();
}

typedef struct profile_entry {
        int64_t count;
        void *ctx;
} ProfileEntry;

char const *GC_ENTRY = "(Garbage Collection)";

static int
CompareProfileEntriesByWeight(void const *a_, void const *b_)
{
        ProfileEntry const *a = a_;
        ProfileEntry const *b = b_;

        if (a->count > b->count)
                return -1;

        if (a->count < b->count)
                return 1;

        return 0;
}

static int
CompareProfileEntriesByLocation(void const *a_, void const *b_)
{
        ProfileEntry const *a = a_;
        ProfileEntry const *b = b_;

        char const *aIp = a->ctx;
        char const *bIp = b->ctx;

        //printf("Instruction(%lu) = %s\n", (uptr)aIp, InstructionNames[(uint8_t)((char *)a->ctx)[0]]);
        Expr const *aExpr = compiler_find_expr(&vvv, a->ctx);

        //printf("Instruction(%lu) = %s\n", (uptr)bIp, InstructionNames[(uint8_t)((char *)b->ctx)[0]]);
        Expr const *bExpr = compiler_find_expr(&vvv, b->ctx);

        if (aExpr == bExpr) return 0;
        if (aExpr == NULL) return -1;
        if (bExpr == NULL) return  1;

        uptr aPtr = (uptr)aExpr;
        uptr bPtr = (uptr)bExpr;

        if (aPtr < bPtr) return -1;
        if (aPtr > bPtr) return  1;

        return 0;
}

static void
ProfileReport(Ty *ty);

static _Thread_local char *LastIP;
static _Thread_local u64 LastThreadTime;
static _Thread_local u64 LastThreadGCTime;
static TySpinLock ProfileMutex;
static Dict *Samples;
static Dict *FuncSamples;
istat prof;

static bool WantReport = false;
static int64_t LastReportRequest;

#endif

bool PrintResult = false;
FILE *DisassemblyOut = NULL;

u64 HITS = 0;
u64 MISSES = 0;

typedef struct {
        atomic_bool *created;
        Value *ctx;
        Value *name;
        Thread *t;
        ThreadGroup *group;
        Ty *ty;
} NewThreadCtx;

static ThreadGroup MainGroup;

static _Thread_local Ty *co_ty;

static _Thread_local Ty *MyTy;
_Thread_local TySpinLock *MyLock;
static _Thread_local TyThreadState *MyState;
static _Thread_local bool HaveLock = true;
static _Thread_local u64 MyId;
static _Thread_local bool GCInProgress;

// ==========/ Signal Handling /========================================
ValueVector                  SignalGCRoots;
static Value                 SignalHandlers[NSIG];
static volatile u8           SignalStates[NSIG];
static volatile sig_atomic_t AnySignalPending;
static pthread_rwlock_t      SignalLock = PTHREAD_RWLOCK_INITIALIZER;

void
vm_do_signal(int sig, siginfo_t *info, void *ctx)
{
        SignalStates[sig] = 1;
        AnySignalPending  = 1;
}
// =====================================================================

void
MarkStorage(Ty *ty);

static TyThreadReturnValue
vm_run_thread(void *p);

inline static void
DoUnaryOp(Ty *ty, int op, bool exec);

static void
InitializeTY(Ty *ty)
{
#define X(op, id) intern(&xD.b_ops, id)
        TY_BINARY_OPERATORS;
#undef X

#define X(op, id) intern(&xD.members, id)
        TY_UNARY_OPERATORS;
#undef X

        intern(&xD.strings, "");

        srandom(TyThreadCPUTime() & 0xFFFFFFFF);

        xD.ty = ty;
}

Ty *
get_my_ty(void)
{
        return MyTy;
}

static void
InitializeTy(Ty *ty)
{
        memset(ty, 0, sizeof *ty);

        ty->ty = &xD;

        ExpandScratch(ty);
        ty->memory_limit = GC_INITIAL_LIMIT;

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
}

inline static void
UnlockThreads(Ty *ty, int *threads, int n)
{
        for (int i = 0; i < n; ++i) {
                TySpinLockUnlock(MyGroup->ThreadLocks.items[threads[i]]);
        }
}

inline static void
SetState(Ty *ty, bool blocking)
{
        *MyState = blocking;
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
InitThreadGroup(Ty *ty, ThreadGroup *g)
{
        v00(g->ThreadList);
        v00(g->TyList);
        v00(g->ThreadStates);
        v00(g->ThreadLocks);
        v00(g->DeadAllocs);
        TySpinLockInit(&g->Lock);
        TySpinLockInit(&g->GCLock);
        TySpinLockInit(&g->DLock);
        g->WantGC = false;
        g->DeadUsed = 0;

        return g;
}

inline static ThreadGroup *
NewThreadGroup(Ty *ty)
{
        return InitThreadGroup(ty, mA(sizeof (ThreadGroup)));
}

static void
WaitGC(Ty *ty)
{
        if (GCInProgress) {
                return;
        }

        GCLOG("Waiting for GC on thread %llu", TID);

        lGv(false);

#ifdef TY_PROFILER
        u64 start = TyThreadTime();
#endif

        while (!*MyState) {
                if (!MyGroup->WantGC && TryFlipTo(MyState, true)) {
                        lTk();
                        GCLOG("Finished waiting: %llu", TID);
#ifdef TY_PROFILER
                        LastThreadGCTime = TyThreadTime() - start;
#endif
                        return;
                }
        }

        lTk();

        GCLOG("Waiting to mark: %llu", TID);
        TyBarrierWait(&MyGroup->GCBarrierStart);
        GCLOG("Marking: %llu", TID);
        MarkStorage(ty);

        GCLOG("Waiting to sweep: %llu", TID);
        TyBarrierWait(&MyGroup->GCBarrierMark);
        GCLOG("Sweeping: %llu", TID);
        GCSweepTy(ty);

        GCLOG("Waiting to continue execution: %llu", TID);
        TyBarrierWait(&MyGroup->GCBarrierSweep);
        TyBarrierWait(&MyGroup->GCBarrierDone);
        GCLOG("Continuing execution: %llu", TID);

#ifdef TY_PROFILER
        LastThreadGCTime = TyThreadTime() - start;
#endif

        dont_printf("Thread %-3llu: %lluus\n", TID, (TyThreadTime() - start) / 1000);
}

void
DoGC(Ty *ty)
{
        GCLOG("Trying to do GC. Used = %zu, DeadUsed = %zu", MemoryUsed, MyGroup->DeadUsed);

        if (!TySpinLockTryLock(&MyGroup->GCLock)) {
                GCLOG("Couldn't take GC lock: calling WaitGC() on thread %llu", TID);
                WaitGC(ty);
                return;
        }

#ifdef TY_PROFILER
        u64 start = TyThreadTime();
#endif

        GCInProgress = true;

        GCLOG("Doing GC: MyGroup = %p, (%zu threads)", MyGroup, MyGroup->ThreadList.count);

        TySpinLockLock(&MyGroup->Lock);

        GCLOG("Took threads lock on thread %llu to do GC", TID);
        GCLOG(
                "[%.4f] [%s:%d] DoGC(): TDB_IS_%s",
                TyThreadCPUTime() / 1.0e9,
                I_AM_TDB ? "TDB" : "Ty",
                (int)(TDB && TyThreadEqual(TyThreadSelf(), TDB->thread.thread->t)),
                TDB_STATE_NAME
        );
        GCLOG("Storing true in WantGC on thread %llu", TID);

        MyGroup->WantGC = true;

        static int *blockedThreads;
        static int *runningThreads;
        static usize capacity;

        if (MyGroup->ThreadList.count > capacity) {
                blockedThreads = mrealloc(blockedThreads, vN(MyGroup->ThreadList) * sizeof *blockedThreads);
                runningThreads = mrealloc(runningThreads, vN(MyGroup->ThreadList) * sizeof *runningThreads);
                capacity = vN(MyGroup->ThreadList);
        }

        int nBlocked = 0;
        int nRunning = 0;

        for (int i = 0; i < vN(MyGroup->ThreadList); ++i) {
                if (MyLock == v__(MyGroup->ThreadLocks, i)) {
                        continue;
                }
                GCLOG("Trying to take lock for thread %llu: %p", (long long unsigned)MyGroup->ThreadList.items[i], (void *)MyGroup->ThreadLocks.items[i]);
                TySpinLockLock(v__(MyGroup->ThreadLocks, i));
                if (TryFlipTo(v__(MyGroup->ThreadStates, i), true)) {
                        GCLOG("Thread %llu is running", MyGroup->TyList.items[i]->id);
                        runningThreads[nRunning++] = i;
                } else {
                        GCLOG("Thread %llu is blocked", MyGroup->TyList.items[i]->id);
                        blockedThreads[nBlocked++] = i;
                }
        }

        GCLOG("nBlocked = %d, nRunning = %d on thread %llu", nBlocked, nRunning, TID);

        TyBarrierInit(&MyGroup->GCBarrierStart, nRunning + 1);
        TyBarrierInit(&MyGroup->GCBarrierMark,  nRunning + 1);
        TyBarrierInit(&MyGroup->GCBarrierSweep, nRunning + 1);
        TyBarrierInit(&MyGroup->GCBarrierDone,  nRunning + 1);

        UnlockThreads(ty, runningThreads, nRunning);

        TyBarrierWait(&MyGroup->GCBarrierStart);

        for (int i = 0; i < nBlocked; ++i) {
                GCLOG("Marking thread %d storage from thread %llu", blockedThreads[i], TID);
                MarkStorage(v__(MyGroup->TyList, blockedThreads[i]));
        }

        GCLOG("Marking own storage on thread %llu", TID);
        MarkStorage(ty);

        if (MyGroup == &MainGroup) {
                GCLOG("Marking %zu global roots on thread %llu", vN(Globals), TID);
                RESET_TOTAL_REACHED();
                for (int i = 0; i < vN(Globals); ++i) {
                        value_mark(ty, v_(Globals, i));
                }
                LOG_REACHED(" => globals reached %llu", TotalReached);

                RESET_TOTAL_REACHED();
                GCRootSet *immortal = GCImmortalSet(ty);
                for (int i = 0; i < vN(*immortal); ++i) {
                        value_mark(ty, v_(*immortal, i));
                }
                LOG_REACHED(" => immortal reached %llu", TotalReached);

                for (int i = 0; i < vN(SignalGCRoots); ++i) {
                        value_mark(ty, v_(SignalGCRoots, i));
                }
        }

        TyBarrierWait(&MyGroup->GCBarrierMark);

        GCLOG("Storing false in WantGC on thread %llu", TID);
        MyGroup->WantGC = false;

        for (int i = 0; i < nBlocked; ++i) {
                Ty *other = v__(MyGroup->TyList, blockedThreads[i]);
                GCLOG("Sweeping thread %llu storage from thread %llu", other->id, TID);
                GCSweepTy(other);
        }
        GCLOG("Sweeping own storage on thread %llu", TID);
        GCSweepTy(ty);
        GCLOG("Sweeping objects from dead threads on thread %llu", TID);
        TySpinLockLock(&MyGroup->DLock);
        GCSweep(ty, &MyGroup->DeadAllocs, &MyGroup->DeadUsed);
        TySpinLockUnlock(&MyGroup->DLock);

        TyBarrierWait(&MyGroup->GCBarrierSweep);

        UnlockThreads(ty, blockedThreads, nBlocked);

        GCLOG("Unlocking ThreadsLock and GCLock. Used = %lld, DeadUsed = %lld", MemoryUsed, MyGroup->DeadUsed);

        TySpinLockUnlock(&MyGroup->Lock);
        TySpinLockUnlock(&MyGroup->GCLock);

        GCLOG("Unlocked ThreadsLock and GCLock on thread %llu", TID);

        TyBarrierWait(&MyGroup->GCBarrierDone);

        GCInProgress = false;

#ifdef TY_PROFILER
        LastThreadGCTime = TyThreadTime() - start;
#endif

        dont_printf("Thread %-3llu: %.6fs\n", TID, (t1 - t0) / 1.0e9);
}

//====/ Builtin Values /======================================================================
#define BUILTIN(f)    { .type = VALUE_BUILTIN_FUNCTION, .builtin_function = (f), .tags = 0 }
#define FLOAT(x)      { .type = VALUE_REAL,             .real             = (x), .tags = 0 }
#define INT(k)        { .type = VALUE_INTEGER,          .z                = (k), .tags = 0 }
#define BOOL_(b)      { .type = VALUE_BOOLEAN,          .boolean          = (b), .tags = 0 }
#define POINTER(p)    { .type = VALUE_PTR,              .ptr              = (p), .tags = 0 }
#include "builtins.h"
#undef INT
#undef FLOAT
#undef BUILTIN
#undef BOOL_
#undef POINTER
//============================================================================================

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

static void
add_builtins(Ty *ty, int ac, char **av)
{
        GC_STOP();

        for (int i = CLASS_OBJECT; i < CLASS_BUILTIN_END; ++i) {
                xvP(Globals, CLASS(i));
        }

        for (int i = 0; i < countof(builtins); ++i) {
                Symbol *sym = compiler_introduce_symbol(
                        ty,
                        builtins[i].module,
                        builtins[i].name
                );
                Value *v = &builtins[i].value;
                if (v->type == VALUE_BUILTIN_FUNCTION) {
                        v->name = M_ID(builtins[i].name);
                        v->module = builtins[i].module;
                        sym->flags |= SYM_FUNCTION;
                }
                xvP(Globals, builtins[i].value);
                switch (ClassOf(v)) {
                case CLASS_INT:
                        sym->type = type_integer(ty, v->z);
                        sym->flags |= SYM_CONST;
                        break;

                case CLASS_STRING:
                case CLASS_BOOL:
                case CLASS_FLOAT:
                        sym->type = class_get(ty, ClassOf(v))->object_type;
                        sym->flags |= SYM_CONST;
                        break;
                }
        }

        Array *args = vA();

        for (int i = 0; i < ac; ++i) {
                vAp(args, STRING_NOGC(av[i], strlen(av[i])));
        }

        compiler_introduce_symbol(ty, NULL, "argv");
        xvP(Globals, ARRAY(args));

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

//===========================================================================
#define BUILTIN_VAR(m, t)                    \
        compiler_introduce_symbol(ty, m, t); \
        *xvP(Globals, NIL)

#define BUILTIN_NAMED_VAR(m, t, c)           \
        compiler_introduce_symbol(ty, m, t); \
        NAMES.c = vN(Globals);               \
        *xvP(Globals, NIL)
//---------------------------------------------------------------------------
        BUILTIN_NAMED_VAR(NULL,  "__env",          env       ) = DICT(env);
        BUILTIN_NAMED_VAR(NULL,  "__EXIT_HOOKS__", exit_hooks) = ARRAY(vA());
        BUILTIN_NAMED_VAR("tdb", "hook",           tdb_hook  ) = NIL;
        BUILTIN_NAMED_VAR(NULL,  "_readln",        _readln   ) = NIL;
        BUILTIN_NAMED_VAR(NULL,  "pretty",         pretty    ) = NIL;
        BUILTIN_NAMED_VAR(NULL,  "pp",             pp        ) = NIL;
        BUILTIN_NAMED_VAR("ty",  "q",              q         ) = BOOLEAN(!CheckTypes);

        BUILTIN_VAR("ty",  "executable") = this_executable(ty);
#if defined(_WIN32)
        BUILTIN_VAR("os",  "PAGE_SIZE" ) = INTEGER(4096);
#else
        BUILTIN_VAR("os",  "PAGE_SIZE" ) = INTEGER(sysconf(_SC_PAGESIZE));
#endif
#if defined(__linux__)
        BUILTIN_VAR("os",  "SIGRTMIN"  ) = INTEGER(SIGRTMIN);
        BUILTIN_VAR("os",  "SIGRTMAX"  ) = INTEGER(SIGRTMAX);
#endif
//---------------------------------------------------------------------------
#undef BUILTIN_VAR
//===========================================================================



//===========================================================================
/* Add FFI types here because they aren't constant expressions on Windows. */
//---------------------------------------------------------------------------
#define BUILTIN_FFI_TYPE(name, ffi_type_ptr)        \
        compiler_introduce_symbol(ty, "ffi", name); \
        xvP(Globals, PTR(ffi_type_ptr))
//---------------------------------------------------------------------------
        BUILTIN_FFI_TYPE("char",    &ffi_type_schar   );
        BUILTIN_FFI_TYPE("short",   &ffi_type_sshort  );
        BUILTIN_FFI_TYPE("int",     &ffi_type_sint    );
        BUILTIN_FFI_TYPE("long",    &ffi_type_slong   );
        BUILTIN_FFI_TYPE("uchar",   &ffi_type_uchar   );
        BUILTIN_FFI_TYPE("ushort",  &ffi_type_ushort  );
        BUILTIN_FFI_TYPE("uint",    &ffi_type_uint    );
        BUILTIN_FFI_TYPE("ulong",   &ffi_type_ulong   );
        BUILTIN_FFI_TYPE("u8",      &ffi_type_uint8   );
        BUILTIN_FFI_TYPE("u16",     &ffi_type_uint16  );
        BUILTIN_FFI_TYPE("u32",     &ffi_type_uint32  );
        BUILTIN_FFI_TYPE("u64",     &ffi_type_uint64  );
        BUILTIN_FFI_TYPE("i8",      &ffi_type_sint8   );
        BUILTIN_FFI_TYPE("i16",     &ffi_type_sint16  );
        BUILTIN_FFI_TYPE("i32",     &ffi_type_sint32  );
        BUILTIN_FFI_TYPE("i64",     &ffi_type_sint64  );
        BUILTIN_FFI_TYPE("float",   &ffi_type_float   );
        BUILTIN_FFI_TYPE("double",  &ffi_type_double  );
        BUILTIN_FFI_TYPE("ptr",     &ffi_type_pointer );
        BUILTIN_FFI_TYPE("void",    &ffi_type_void    );
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


//====/ Types Enum /=========================================================
#define X(name)                                             \
        compiler_introduce_tag(ty, "ty/types", #name, -1);  \
        xvP(Globals, TAG(Ty ## name ## T));                 \

        TY_TYPE_TAGS
#undef X
//===========================================================================


        GC_RESUME();
}

void
vm_load_c_module(Ty *ty, char const *name, void *p)
{
        struct {
                char const *name;
                Value value;
        } *mod = p;

        for (isize i = 0; mod[i].name != NULL; ++i) {
                compiler_introduce_symbol(ty, name, mod[i].name);
                xvP(Globals, mod[i].value);
        }
}

inline static Value *
(topN)(Ty *ty, int n)
{
        return &STACK.items[STACK.count - n];
}

inline static Value *
(top)(Ty *ty)
{
        return topN(1);
}

inline static void
xprint_stack(Ty *ty, int n)
{
        printf("STACK: (%zu)\n", vN(STACK));
        for (int i = 0; i < zminu(n, vN(STACK)); ++i) {
                if (vN(FRAMES) == 0) {
                        printf("      %s\n", VSC(top() - i));
                        continue;
                }

                int i_abs = vN(STACK) - (i + 1);
                int off = i_abs - vvL(FRAMES)->fp;

                Expr const *func = compiler_find_func(ty, IP);
                char const *name = (func != NULL && vN(func->scope->owned) > off)
                                 ? v_(func->scope->owned, off)[0]->identifier
                                 : NULL;

                if (off == 0) {
                        printf(
                                "%s%8.8s%s --> %s%8.8s%s = %s\n",
                                TERM(95;1),
                                (func == NULL ? "???" : func->name),
                                TERM(0;92),
                                TERM(33),
                                name,
                                TERM(0),
                                VSC(top() - i)
                        );
                } else if (name != NULL) {
                        printf(
                                "   %s%18.18s%s = %s\n",
                                TERM(33),
                                name,
                                TERM(0),
                                VSC(top() - i)
                        );
                } else {
                        printf(
                                "%24s%s\n",
                                "",
                                VSC(top() - i)
                        );
                }
        }
}

#define print_stack(...)

inline static Value
(pop)(Ty *ty)
{
        return *vvX(STACK);
}

inline static Value
(peek)(Ty *ty)
{
        return *topN(1);
}

inline static void
(push)(Ty *ty, Value v)
{
        xvP(STACK, v);
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
(poptarget)(Ty *ty)
{
        return vvX(TARGETS)->t;
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
        u32  np = param_count_of(fun);

        Value v = v__(STACK, vvL(FRAMES)->fp + np);

        while (v.type == VALUE_REF) {
                v = *v.ref;
        }

        return v;
}

inline static Value
BindMethod(Ty *ty, Value *f, Value *v, int id)
{
        Value *this = mAo(sizeof *this, GC_VALUE);
        *this = *v;
        return METHOD(id, f, this);
}

static bool
co_yield_value(Ty *ty);

noreturn static void
do_co(void)
{
        Ty *ty = co_ty;
        vm_exec(ty, IP);
        UNREACHABLE();
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

inline static bool
GeneratorIsSuspended(Generator *gen)
{
        return (gen->ip != NULL);
}

inline static Generator *
GetCurrentGenerator(Ty *ty)
{
        if (vN(FRAMES) == 0 || vN(STACK) == 0) {
                return NULL;
        }

        usize n = FRAMES.items[0].fp;

        if (n == 0 || STACK.items[n - 1].type != VALUE_GENERATOR) {
                return NULL;
        }

        return STACK.items[n - 1].gen;
}

inline static Generator *
GetGeneratorForFrame(Ty *ty, int i)
{
        int n = FRAMES.items[i].fp;

        if (n == 0 || STACK.items[n - 1].type != VALUE_GENERATOR) {
                return NULL;
        }

        return STACK.items[n - 1].gen;
}

inline static cothread_t
GetFreeCoThread(Ty *ty)
{
        void *base;
        if (vN(CO_THREADS) == 0) {
                GCLOG("GetFreeCoThread(): new");
                base = xmA(CO_STACK_SIZE);
        } else {
                GCLOG("GetFreeCoThread(): recycled");
                base = *vvX(CO_THREADS);
        }
        return co_derive(base, CO_STACK_SIZE, do_co);
}

static char const *
co_up(Ty *ty, co_state *st)
{
        if (vN(st->frames) == 0 || vN(STACK) == 0) {
                return NULL;
        }

        usize n = vv(st->frames)->fp;

        if (n == 0 || v_(STACK, n - 1)->type != VALUE_GENERATOR) {
                return NULL;
        }

        Generator *gen = v_(STACK, n - 1)->gen;

        *st = gen->st;

        return gen->ip;
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

        SWAP(co_state, gen->st, ty->st);
        SWAP(GCRootSet, gen->gc_roots, RootSet);

        vvX(FRAMES);
        IP = *vvX(CALLS);
        return true;
}

static bool
co_yield_value(Ty *ty)
{
        if (FRAMES.count == 0 || STACK.count == 0)
                return false;

        int n = FRAMES.items[0].fp;

        if (n == 0 || STACK.items[n - 1].type != VALUE_GENERATOR) {
                return false;
        }

        Generator *gen = STACK.items[n - 1].gen;
        gen->ip = IP;
        gen->frame.count = 0;

        SWAP(co_state, gen->st, ty->st);
        SWAP(GCRootSet, gen->gc_roots, RootSet);

        xvPn(gen->frame, STACK.items + n, STACK.count - n - 1);

        STACK.items[n - 1] = peek();
        STACK.count = n;

        vvX(FRAMES);

        IP = *vvX(CALLS);

        if (gen->st.exec_depth > 1) {
                GCLOG("co_yield() [%p]: switch to [%p] with %s (RECURSED)", co_active(), gen->co, VSC(top()));
                cothread_t co = gen->co;
                gen->co = co_active();
                co_switch(co);
        } else {
                GCLOG("co_yield() [%p]: switch to [%p] with %s", co_active(), gen->co, VSC(top()));
                cothread_t co = gen->co;
                gen->co = NULL;
                gen->st.exec_depth = 0;
                xvP(CO_THREADS, co_active());
                co_switch(co);
        }

        GCLOG("co_yield() [%p]: resume", co_active());

        return true;
}

#if !defined(TY_RELEASE)
__attribute__((optnone, noinline))
#endif
inline static void
xcall(Ty *ty, Value const *f, Value const *pSelf, int argc, Value const *pKwargs, char *whence)
{
        int   np      = f->info[FUN_INFO_PARAM_COUNT];
        int   bound   = f->info[FUN_INFO_BOUND];

        int   irest   = rest_idx_of(f);
        int   ikwargs = kwargs_idx_of(f);
        Value kwargs  = (pKwargs != NULL) ? *pKwargs : NIL;

        Value self;
        int   class   = f->info[FUN_INFO_CLASS];

        int   fp      = vN(STACK) - argc;

        if (class != -1) {
                self = (pSelf != NULL) ? *pSelf
                     : is_decorated(f) ? GetSelf(ty)
                     : NIL;
        } else {
                self = NONE;
        }

        LOG(
                "Calling %s with %d args, bound = %d, self = %s, env size = %d",
                VSC(f), argc, bound, VSC(&self), f->info[2]
        );

        int n = argc;

        /*
         * Default missing arguments to NIL and make space for all of this function's local variables.
         */
        while (n < bound) {
                push(NIL);
                n += 1;
        }

        if (irest != ikwargs) {
                gP(&self);
                gP(&kwargs);
                if (irest != -1) {
                        int nExtra = max(argc - irest, 0);
                        Array *extra = vAn(nExtra);

                        memcpy(v_(*extra, 0), vv(STACK) + fp + irest, nExtra * sizeof (Value));
                        extra->count = nExtra;

                        *v_(STACK, fp + irest) = ARRAY(extra);

                        for (int i = irest + 1; i < argc; ++i) {
                                *v_(STACK, fp + i) = NIL;
                        }
                }
                if (ikwargs != -1) {
                        // FIXME: don't allocate a dict when there are no kwargs
                        *v_(STACK, fp + ikwargs) = !IsNil(kwargs) ? kwargs : DICT(dict_new(ty));
                }
                gX();
                gX();
        }

        // Throw away extra args
        if (n > bound) {
                STACK.count -= (n - bound);
        }

        if (class != -1) {
                *v_(STACK, fp + np) = self;
        }

        xvP(FRAMES, FRAME(fp, *f, IP));
        xvP(CALLS, whence);

        // Fill in kwargs (overwriting positional args)
        if (!IsNil(kwargs)) {
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
}

static bool
call(Ty *ty, Value const *f, Value const *pSelf, int argc, Value const *pKwargs)
{
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
        IP = code_of(f);

        return true;
}

static void
call6(Ty *ty, Value const *f, Value const *pSelf, int argc, Value const *pKwargs, char *whence)
{
        xcall(ty, f, pSelf, argc, pKwargs, whence);
        IP = code_of(f);
}

static void
call6t(Ty *ty, Value const *f, Value const *pSelf, int argc, Value const *pKwargs, char *whence)
{
        xvP(CALLS, IP);
        xcall(ty, f, pSelf, argc, pKwargs, whence);
        IP = code_of(f);
}

static void
exec_fn(Ty *ty, Value const *f, Value const *pSelf, int argc, Value const *pKwargs)
{
        xcall(ty, f, pSelf, argc, pKwargs, &halt);
        vm_exec(ty, code_of(f));
}

TY_INSTR_INLINE static void
call_co_ex(Ty *ty, Value *v, int n, char *whence)
{
        if (UNLIKELY(!GeneratorIsSuspended(v->gen))) {
                zP("attempt to invoke an already-active coroutine");
        }

        Generator *gen = v->gen;

        if (gen->ip != code_of(&gen->f)) {
                if (n == 0) {
                        xvP(gen->frame, NIL);
                } else {
                        xvPn(gen->frame, vZ(STACK) - n, n);
                        STACK.count -= n;
                }
        }

        push(*v);
        call6(ty, &gen->f, NULL, 0, NULL, whence);
        STACK.count = vvL(FRAMES)->fp;

        if (vN(gen->st.frames) == 0) {
                xvP(gen->st.frames, *vvL(FRAMES));
        } else {
                gen->st.frames.items[0] = *vvL(FRAMES);
        }

        int diff = (isize)vN(STACK) - gen->fp;
        for (int i = 1; i < vN(gen->st.frames); ++i) {
                gen->st.frames.items[i].fp += diff;
        }

        gen->fp = vN(STACK);

        SWAP(co_state, gen->st, ty->st);
        SWAP(GCRootSet, gen->gc_roots, RootSet);

        for (int i = 0; i < gen->frame.count; ++i) {
                push(gen->frame.items[i]);
        }

        IP = gen->ip;
        gen->ip = NULL;

        if (gen->co != NULL) {
                cothread_t co = gen->co;
                gen->co = co_active();
                GCLOG("co_call() [%p]: switch to %s on [%p]", co_active(), name_of(&gen->f), (void *)co);
                xco_switch(co);
        } else {
                cothread_t co = GetFreeCoThread(ty);
                gen->co = co_active();
                GCLOG("co_call() [%p]: switch to %s on [%p] (NEW)", co_active(), name_of(&gen->f), (void *)co);
                co_ty = ty;
                xco_switch(co);

        }

        GCLOG("co_call() [%p]: back from %s with %s", co_active(), name_of(&v->gen->f), VSC(top()));
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

        for (int i = 0; i < vN(ctx->locals); ++i) {
                vN(v__(ctx->locals, i)) = 0;
        }

        vN(ctx->locals) = 0;
        //=========================================

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
        return *vvL(THROW_STACK);
}

static ThrowCtx *
PopThrowCtx(Ty *ty)
{
        return *vvX(THROW_STACK);
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

void
TakeLock(Ty *ty)
{
        GCLOG("Taking MyLock%s", "");
        TySpinLockLock(MyLock);
        GCLOG("Took MyLock");
        HaveLock = true;
}

bool
MaybeTakeLock(Ty *ty)
{
        return HaveLock ? false : (TakeLock(ty), true);
}

void
ReleaseLock(Ty *ty, bool blocked)
{
        SetState(ty, blocked);
        GCLOG("Releasing MyLock: %d", (int)blocked);
        TySpinLockUnlock(MyLock);
        HaveLock = false;
}

bool
HoldingLock(Ty *ty)
{
        return HaveLock;
}

void
NewThread(Ty *ty, Thread *t, Value *call, Value *name, bool isolated)
{
        lGv(true);

        atomic_bool created = false;

        NewThreadCtx *ctx = mrealloc(NULL, sizeof *ctx);
        *ctx = (NewThreadCtx) {
                .ty = ty,
                .ctx = call,
                .name = name,
                .created = &created,
                .t = t,
                .group = isolated ? NewThreadGroup(ty) : MyGroup
        };

        TyMutexInit(&t->mutex);
        TyCondVarInit(&t->cond);
        t->alive = true;

        int r = TyThreadCreate(&t->t, vm_run_thread, ctx);
        if (r != 0) {
                zP("TyThreadCreate(): %s", strerror(r));
        }

        while (!created) {
                continue;
        }

        lTk();
}

static void
AddThread(Ty *ty, TyThread self)
{
        MyLock = mrealloc(NULL, sizeof *MyLock);
        TySpinLockInit(MyLock);
        TySpinLockLock(MyLock);

        MyState = mrealloc(NULL, sizeof *MyState);
        *MyState = false;

        GC_STOP();
        GCLOG("AddThread(): %llu: taking lock", TID);
        TySpinLockLock(&MyGroup->Lock);
        GCLOG("AddThread(): %llu: took lock", TID);
        vvP(MyGroup->TyList, ty);
        vvP(MyGroup->ThreadList, self);
        vvP(MyGroup->ThreadLocks, MyLock);
        vvP(MyGroup->ThreadStates, MyState);
        TySpinLockUnlock(&MyGroup->Lock);
        GCLOG("AddThread(): %llu: finished", TID);
        GC_RESUME();
}

static void
CleanupThread(void *ctx)
{
        Ty *ty = ctx;

        GCLOG("Cleaning up thread: %zu bytes in use. DeadUsed = %zu", MemoryUsed, MyGroup->DeadUsed);

        TySpinLockLock(&MyGroup->DLock);
        if (MyGroup->DeadUsed + MemoryUsed > MemoryLimit) {
                TySpinLockUnlock(&MyGroup->DLock);
                DoGC(ty);
                TySpinLockLock(&MyGroup->DLock);
        }
        xvPv(MyGroup->DeadAllocs, ty->allocs);
        MyGroup->DeadUsed += MemoryUsed;
        v0(ty->allocs);
        TySpinLockUnlock(&MyGroup->DLock);

        lGv(true);

        TySpinLockLock(&MyGroup->Lock);

        GCLOG("Got threads lock on thread: %llu -- ready to clean up. Group size = %zu", TID, vN(MyGroup->ThreadList));

        for (int i = 0; i < vN(MyGroup->ThreadList); ++i) {
                if (MyLock == v__(MyGroup->ThreadLocks, i)) {
                        *v_(MyGroup->ThreadList,   i) = *vvX(MyGroup->ThreadList);
                        *v_(MyGroup->TyList,       i) = *vvX(MyGroup->TyList);
                        *v_(MyGroup->ThreadLocks,  i) = *vvX(MyGroup->ThreadLocks);
                        *v_(MyGroup->ThreadStates, i) = *vvX(MyGroup->ThreadStates);
                        break;
                }
        }

        usize group_remaining = vN(MyGroup->ThreadList);

        TySpinLockUnlock(&MyGroup->Lock);

        for (int i = 0; i < vC(TRY_STACK); ++i) {
                struct try *t = *v_(TRY_STACK, i);
                xvF(t->defer);
                free(t);
        }

        for (int i = 0; i < vC(THROW_STACK); ++i) {
                ThrowCtx *ctx = v__(THROW_STACK, i);
                xvF(*ctx);
                xvF(ctx->locals);
                free(ctx);
        }

        for (int i = 0; i < vN(ty->_2op_cache); ++i) {
                xvF(v__(ty->_2op_cache, i));
        }

        for (int i = 0; i < vN(CO_THREADS); ++i) {
                free(v__(CO_THREADS, i));
        }

        for (int i = 0; i < TY_TMP_BUF_COUNT; ++i) {
                free(ty->tmp[i].p);
        }

        for (int i = 0; i < vN(ty->scratch.arenas); ++i) {
                free(v_(ty->scratch.arenas, i)->base);
        }

        TySpinLockDestroy(MyLock);
        free(MyLock);
        free((void *)MyState);
        xvF(STACK);
        xvF(THREAD_LOCALS);
        xvF(RootSet);
        xvF(CALLS);
        xvF(FRAMES);
        xvF(SP_STACK);
        xvF(TARGETS);
        xvF(TRY_STACK);
        xvF(THROW_STACK);
        xvF(DROP_STACK);
        xvF(CO_THREADS);
        xvF(ty->allocs);
        xvF(ty->_2op_cache);
        xvF(ty->err);
        xvF(ty->marking);
        xvF(ty->visiting);
        xvF(ty->scratch.arenas);
        FreeArena(&ty->arena);
        pcre2_match_data_free(ty->pcre2.match);
        pcre2_match_context_free(ty->pcre2.ctx);
        pcre2_jit_stack_free(ty->pcre2.stack);

        TyValueCleanup();
        TyFunctionsCleanup();

        if (group_remaining == 0) {
                GCLOG("Cleaning up group %p", (void*)MyGroup);
                TySpinLockDestroy(&MyGroup->Lock);
                TySpinLockDestroy(&MyGroup->GCLock);
                TySpinLockDestroy(&MyGroup->DLock);
                vvF(MyGroup->TyList);
                vvF(MyGroup->ThreadList);
                vvF(MyGroup->ThreadLocks);
                vvF(MyGroup->ThreadStates);
                xvF(MyGroup->DeadAllocs);
                mF(MyGroup);
        }

        GCLOG("Finished cleaning up on thread: %llu -- releasing threads lock", TID);
}

static TyThreadReturnValue
vm_run_thread(void *p)
{
        NewThreadCtx *ctx = p;
        Value *call = ctx->ctx;
        Value *name = ctx->name;
        Thread *t = ctx->t;

        Ty *ty = mrealloc(NULL, sizeof *ty);
        InitializeTy(ty);

        MyTy = ty;
        MyId = ty->id = t->i;

        int argc = 0;

        GCLOG("New thread: %llu", TID);

        while (call[argc + 1].type != VALUE_NONE) {
                push(call[++argc]);
        }

        MyGroup = ctx->group;

        AddThread(ty, t->t);

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
                TyClearError(ty);
                fprintf(stderr, "Thread %lld dying with error: %s\n", TID, TyError(ty));
                t->v = TY_CATCH();
        } else {
                t->v = vmC(call, argc);
                TY_CATCH_END();
        }

#ifndef _WIN32
        pthread_cleanup_pop(1);
#else
        CleanupThread(ty);
#endif

        free(ctx);
        mF(call);

        TyMutexLock(&t->mutex);
        t->alive = false;
        TyMutexUnlock(&t->mutex);
        TyCondVarSignal(&t->cond);

        OKGC(t);

        return TY_THREAD_OK;
}

inline static void
tdb_set_trap(DebugBreakpoint *breakpoint, char *ip)
{
        breakpoint->ip = ip;
        breakpoint->op = *ip;
        *ip = (char)INSTR_TRAP_TY;
}

static TyThreadReturnValue
vm_run_tdb(void *ctx)
{
        Ty *ty = mrealloc(NULL, sizeof *ty);
        InitializeTy(ty);

        TDB = ctx;
        Thread *t = TDB->thread.thread;

        MyTy = TDB->ty = ty;
        MyId = t->i;

        MyGroup = TDB->host->my_group;

        AddThread(ty, t->t);

        if (TY_CATCH_ERROR()) {
                TY_CATCH();
                fprintf(stderr, "TDB thread unrecoverable error: %s\n", TyError(ty));
                goto TDB_HAS_BEEN_STOPPED;
        }

#ifndef _WIN32
        pthread_cleanup_push(CleanupThread, ty);
#endif

        *((atomic_bool *)t->v.ptr) = true;

        for (;;) {
                u8 next = TDB_STATE_STOPPED;

                if (TY_CATCH_ERROR()) {
                        TY_CATCH();
                        fprintf(stderr, "TDB thread error: %s\n", TyError(ty));
                        goto KeepRunning;
                }

                lGv(true);

                TyMutexLock(&TDB_MUTEX);
                while (TDB_IS(STOPPED)) {
                        TyCondVarWait(&TDB_CONDVAR, &TDB_MUTEX);
                }

                lTk();

                DebugBreakpoint *breakpoint = tdb_get_break(ty, TDB->host->ip);

                if (breakpoint   != NULL) *breakpoint->ip = breakpoint->op;
                if (TDB->next.ip != NULL) *TDB->next.ip   = TDB->next.op;
                if (TDB->alt.ip  != NULL) *TDB->alt.ip    = TDB->alt.op;

                Value *hook;
                if (
                        (vN(Globals) > NAMES.tdb_hook)
                     && (hook = v_(Globals, NAMES.tdb_hook))->type != VALUE_NIL
                ) {
                        TDB_IS_NOW(ACTIVE);
                        Value state = vm_call(ty, hook, 0);
                        if (
                                (state.type == VALUE_INTEGER)
                             && (state.z >= 0)
                             && (state.z < TDB_MAX_STATE)
                        ) {
                                next = state.z;
                        }
                }

                TY_CATCH_END();

KeepRunning:
                TDB_SET_STATE(next);

                TyMutexUnlock(&TDB_MUTEX);
                TyCondVarSignal(&TDB_CONDVAR);
        }

TDB_HAS_BEEN_STOPPED:

        TDB_IS_NOW(DEAD);
        TyMutexUnlock(&TDB_MUTEX);
        TyCondVarSignal(&TDB_CONDVAR);

#ifndef _WIN32
        pthread_cleanup_pop(1);
#else
        CleanupThread(ty);
#endif
        TyMutexLock(&t->mutex);
        t->alive = false;
        TyMutexUnlock(&t->mutex);
        TyCondVarSignal(&t->cond);

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

static void
HandlePendingSignals(Ty *ty)
{
        GC_STOP();

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
                }
        }

        GC_RESUME();
}

inline static void
CheckPendingSignals(Ty *ty)
{
        if (UNLIKELY(TAKE_PENDING_SIGNALS())) {
                HandlePendingSignals(ty);
        }
}

#ifndef TY_RELEASE
__attribute__((noinline))
#else
TY_INSTR_INLINE
#endif
static void
DoDrop(Ty *ty)
{
        Value group = *vvL(DROP_STACK);

        for (int i = 0; i < vN(*group.array); ++i) {
                Value v = v__(*group.array, i);
                if (v.type != VALUE_OBJECT) {
                        continue;
                }
                Value *f = class_lookup_method_i(ty, v.class, NAMES._drop_);
                if (f == NULL) {
                        continue;
                }
                vm_call_method(ty, &v, f, 0);
        }

        vvX(DROP_STACK);
}

inline static struct try *
GetCurrentTry(Ty *ty)
{
        return *vvL(TRY_STACK);
}

inline static noreturn void
BadFieldAccess(Ty *ty, Value const *val, i32 z)
{
        if (val->type == VALUE_TUPLE) {
                zP(
                        "attempt to access non-existent field %s'%s'%s of %s%s%s",
                        TERM(34),
                        M_NAME(z),
                        TERM(39),
                        TERM(97),
                        VSC(val),
                        TERM(39)
                );
        } else {
                zP(
                        "attempt to access non-existent member %s'%s'%s of %s%s%s",
                        TERM(34),
                        M_NAME(z),
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

        t->flags = ty->flags;
        t->sp    = vN(STACK);
        t->gc    = vN(RootSet);
        t->cs    = vN(CALLS);
        t->ts    = vN(TARGETS);
        t->ds    = vN(DROP_STACK);
        t->ctxs  = vN(FRAMES);
        t->nsp   = vN(SP_STACK);
        t->vs    = vN(VISITING);
        t->ed    = EXEC_DEPTH;
        t->ss    = SaveScratch(ty);
        t->state = TRY_TRY;
        v0(t->defer);

        return t;
}

TY_INSTR_INLINE static void
DoThrow(Ty *ty)
{
        Value ex = CurrentThrowCtx(ty)->exc;

        //if (ex.type == VALUE_OBJECT && ex.class == CLASS_RUNTIME_ERROR) {
        //        XXX("Throw: RuntimeError: %s", TY_TMP_C_STR(*itable_get(ty, ex.object, NAMES._what)));
        //} else {
        //        TY_START(DYING);
        //        XXX("Throw: %s", VSC(&ex));
        //        TY_STOP(DYING);
        //}
        //xprint_stack(ty, 5);

        for (;;) {
                while (
                        (vN(TRY_STACK) > 0)
                     && (vvL(TRY_STACK)[0]->state == TRY_FINALLY)
                ) {
                        vvX(TRY_STACK);
                }

                if (vN(TRY_STACK) > 0) {
                        struct try *t = *vvL(TRY_STACK);

                        switch (t->state) {
                        case TRY_TRY:
                                t->state = TRY_THROW;

                                while (vN(DROP_STACK) > t->ds) {
                                        DoDrop(ty);
                                }

                                EXEC_DEPTH   = t->ed;
                                vN(STACK)    = t->sp;
                                vN(SP_STACK) = t->nsp;
                                vN(FRAMES)   = t->ctxs;
                                vN(TARGETS)  = t->ts;
                                vN(CALLS)    = t->cs;
                                vN(RootSet)  = min(vN(RootSet), t->gc);
                                vN(VISITING) = t->vs;
                                IP           = t->catch;

                                RestoreScratch(ty, t->ss);

                                push(SENTINEL);
                                push(ex);

                                t->state = TRY_CATCH;

                                longjmp(t->jb, 1);
                                ////////////////////////////////////////////////

                        case TRY_CATCH:
                                t->state = TRY_THROW;
                                t->end = NULL;
                                IP = t->finally;
                                return;

                        case TRY_THROW:
                                zPxx(
                                        "an exception was thrown while handling another exception: %s%s%s",
                                        TERM(31), VSC(&ex), TERM(39)
                                );
                        }
                }

                if (!co_abort(ty)) {
                        zPxx("uncaught exception: %s%s%s", TERM(31), VSC(&ex), TERM(39));
                }
        }
}

TY_INSTR_INLINE static void
RaiseException(Ty *ty)
{
        ThrowCtx *ctx = PushThrowCtx(ty);
        ctx->exc = pop();
        DoThrow(ty);
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

TY_INSTR_INLINE static Value
ArraySubscript(Ty *ty, Value container, Value subscript, bool strict)
{
        char *ip;
        Value *vp;
        Array *a;

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
                        if (r.type == VALUE_NONE)
                                break;
                        if (UNLIKELY(r.type != VALUE_INTEGER))
                                zP("iterator yielded non-integer array index in subscript expression: %s", VSC(&r));
                        if (r.z < 0)
                                r.z += container.array->count;
                        if (r.z < 0 || r.z >= container.array->count) {
                                if (strict) goto Error;
                                vAp(a, None);
                        } else if (strict) {
                                vAp(a, container.array->items[r.z]);
                        } else {
                                vAp(a, Some(container.array->items[r.z]));
                        }
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
                        Value r = pop();
                        if (r.type == VALUE_NIL)
                                break;
                        if (UNLIKELY(r.type != VALUE_INTEGER))
                                zP("iterator yielded non-integer array index in subscript expression");
                        if (r.z < 0)
                                r.z += container.array->count;
                        if (r.z < 0 || r.z >= container.array->count) {
                                if (strict) goto Error;
                                vAp(a, None);
                        } else if (strict) {
                                vAp(a, container.array->items[r.z]);
                        } else {
                                vAp(a, Some(container.array->items[r.z]));
                        }
                }

                OKGC(a);
                gX();
                gX();

                return ARRAY(a);
        case VALUE_INTEGER:
                if (subscript.z < 0) {
                        subscript.z += container.array->count;
                }

                if (subscript.z < 0 || subscript.z >= container.array->count) {
                        if (strict) goto Error;
                        return None;
                } else if (strict) {
                        return container.array->items[subscript.z];
                } else {
                        return Some(container.array->items[subscript.z]);
                }
        default:
                zP(
                        "non-integer array index used in subscript expression: %s",
                        VSC(&subscript)
                );
        }

        Value e;
Error:
        e = tagged(ty, TAG_INDEX_ERR, container, subscript, NONE);
        vm_throw(ty, &e);
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

TY_INSTR_INLINE static bool
search_i32(int const *zs, i32 z)
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


static void
ExecCurrentCall(Ty *ty)
{
        char *ip = v_L(CALLS);
        v_L(CALLS) = &halt;

        vm_exec(ty, IP);

        IP = ip;
}

static void
CallMethod(Ty *ty, int i, int n, int nkw, bool b);

static Value
BuildKwargsDict(Ty *ty, int nkw)
{
        if (nkw == 0) {
                return NIL;
        }

        GC_STOP();
        Dict *kwargs = dict_new(ty);
        for (int i = 0; i < nkw; ++i, SKIPSTR()) {
                if (top()->type == VALUE_NONE) {
                        pop();
                        continue;
                }
                if (IP[0] == '*') {
                        if (top()->type == VALUE_DICT) {
                                DictUpdate(ty, kwargs, top()->dict);
                                pop();
                        } else if (
                                LIKELY(
                                        top()->type == VALUE_TUPLE
                                     && (top()->count == 0 || top()->ids != NULL)
                                )
                        ) {
                                for (int i = 0; i < top()->count; ++i) {
                                        if (top()->ids[i] != -1) {
                                                dict_put_member(
                                                        ty,
                                                        kwargs,
                                                        intern_entry(&xD.members, top()->ids[i])->name,
                                                        top()->items[i]
                                                );
                                        }
                                }
                                pop();
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
                        dict_put_member(ty, kwargs, IP, pop());
                }
        }
        GC_RESUME();

        return DICT(kwargs);
}

static bool
DoCall(Ty *ty, Value const *f, int n, int nkw, bool auto_this)
{
        Value v = *f;
        Value *vp;
        Value value;
        Value subscript;
        Value a, b;
        imax k;

        bool new_frame = false;

        if (n == -1) {
                n = vN(STACK) - *vvX(SP_STACK) - nkw;
        }

        /* TODO: optimize more tail calls */
#if 0
        if (tco) {
                vvX(FRAMES);
                IP = *vvX(CALLS);
                tco = false;
        }
#endif

        gP(auto_this ? v.this : &v);

        Value kwargs = BuildKwargsDict(ty, nkw);

        switch (v.type) {
        case VALUE_FUNCTION:
                new_frame = call(ty, &v, NULL, n, &kwargs);
                gX();
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
                gX();
                STACK.count = k;
                push(v);
                if (UNLIKELY(TAKE_PENDING_SIGNALS())) {
                        HandlePendingSignals(ty);
                }
                return false;

        case VALUE_FOREIGN_FUNCTION:
                k = vN(STACK) - n;
                v = cffi_fast_call(ty, &v, n, NULL);
                STACK.count = k;
                push(v);
                gX();
                if (UNLIKELY(TAKE_PENDING_SIGNALS())) {
                        HandlePendingSignals(ty);
                }
                return false;

        case VALUE_GENERATOR:
                gX();
                call_co(ty, &v, n);
                return false;

        case VALUE_OPERATOR:
                gX();
                switch (n) {
                case 1:
                        DoUnaryOp(ty, v.uop, false);
                        break;

                case 2:
                        b = pop();
                        a = pop();
                        push(vm_2op(ty, v.bop, &a, &b));
                        break;

                default:
                        push(TAG(TAG_DISPATCH_ERR));
                        RaiseException(ty);
                        break;
                }
                return false;

        case VALUE_TAG:
                gP(&kwargs);
                DoTag(ty, v.tag, n, &kwargs);
                gX();
                gX();
                return false;

        case VALUE_OBJECT:
                vp = class_lookup_method_i(ty, v.class, NAMES.call);
                if (vp == NULL) {
                        goto NotCallable;
                }
                new_frame = call(ty, vp, &v, n, &kwargs);
                gX();
                return new_frame;

        case VALUE_CLASS:
                gP(&kwargs);
                if (v.class <= CLASS_PRIMITIVE && v.class != CLASS_OBJECT) {
                        vp = class_lookup_method_i(ty, v.class, NAMES.init);
                        if (LIKELY(vp != NULL)) {
                                value = NONE;
                                exec_fn(ty, vp, &value, n, &kwargs);
                        } else {
                                zP("built-in class has no init method. Was prelude loaded?");
                        }
                } else {
                        value = OBJECT(object_new(ty, v.class), v.class);
                        vp = class_lookup_method_i(ty, v.class, NAMES.init);
                        if (LIKELY(vp != NULL)) {
                                gP(&value);
                                exec_fn(ty, vp, &value, n, &kwargs);
                                gX();
                                pop();
                        } else {
                                STACK.count -= n;
                        }
                        push(value);
                }
                gX();
                gX();
                return false;

        case VALUE_METHOD:
                if (v.name == NAMES.method_missing) {
                        push(NIL);
                        memmove(top() - (n - 1), top() - n, n * sizeof (Value));
                        top()[-n++] = v.this[1];
                }
                new_frame = call(ty, v.method, v.this, n, &kwargs);
                gX();
                return new_frame;

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
                *top() = v;
                gX();
                return false;

        case VALUE_BUILTIN_METHOD:
                gP(&kwargs);
                v = v.builtin_method(ty, v.this, n, &kwargs);
                gX();
                gX();
                STACK.count -= n;
                push(v);
                return false;

        case VALUE_NIL:
                STACK.count -= n;
                push(NIL);
                gX();
                return false;

        case VALUE_DICT:
                value = peek();
                push(v);
                vp = dict_get_value(ty, v.dict, &value);
                STACK.count -= (n + 1);
                if (vp == NULL) {
                        push(None);
                } else {
                        push(Some(*vp));
                }
                gX();
                return false;

        case VALUE_ARRAY:
                subscript = peek();
                push(v);
                value = ArraySubscript(ty, v, subscript, false);
                STACK.count -= (n + 1);
                push(value);
                gX();
                return false;

        NotCallable:
        default:
                zP("attempt to call non-callable value %s", VSC(&v));
        }
}

inline static i16
FastFieldOffset(Ty *ty, Value const *v, i32 id)
{
        if (v->type != VALUE_OBJECT || v->object->diverged) {
                return -1;
        }

        Class *class = class_get(ty, v->class);

        if (id >= vN(class->offsets)) {
                return -1;
        }

        return v__(class->offsets, id);
}

inline static Value *
TargetFieldFast(Ty *ty, Value *v, i32 id)
{
        i16 off = FastFieldOffset(ty, v, id);
        if (off < 0) {
                return NULL;
        }

        u8 type = (off >> 12);
        off &= 0x0FFF;

        switch (type) {
        case OFF_FIELD:
                return v_(v->object->values, off);

        default:
                return NULL;
        }
}

inline static Value
LoadFieldFast(Ty *ty, Value *v, i32 id)
{
        i16 off = FastFieldOffset(ty, v, id);
        if (off < 0) {
                return NONE;
        }

        u8 type = (off >> 12);
        off &= 0x0FFF;

        Value *vp;
        Value *this;

        Class *class = class_get(ty, v->class);

        switch (type) {
        case OFF_FIELD:
                return v__(v->object->values, off);

        case OFF_GETTER:
                vp = v_(class->getters.values, off);
                call(ty, vp, v, 0, NULL);
                return BREAK;

        case OFF_METHOD:
                vp = v_(class->methods.values, off);
                this = mAo(sizeof *this, GC_VALUE);
                *this = *v;
                return METHOD(id, vp, this);
        }

        UNREACHABLE();
}

inline static bool
DispatchMethodFast(Ty *ty, Value self, i32 id, int argc, int nkw)
{
        Value *v = &self;

        i16 off = FastFieldOffset(ty, v, id);
        if (off < 0) {
                return false;
        }

        u8 type = (off >> 12);
        off &= 0x0FFF;

        Value *vp;
        Value fn;
        Value kwargs;

        Class *class = class_get(ty, v->class);

        switch (type) {
        case OFF_FIELD:
                pop();
                DoCall(ty, v_(v->object->values, off), argc, nkw, false);
                break;

        case OFF_GETTER:
                vp = v_(class->getters.values, off);
                exec_fn(ty, vp, v, 0, NULL);
                fn = pop();
                pop();
                DoCall(ty, &fn, argc, nkw, false);
                break;

        case OFF_METHOD:
                vp = v_(class->methods.values, off);
                pop();
                kwargs = BuildKwargsDict(ty, nkw);
                call(ty, vp, v, argc, &kwargs);
                break;

        default:
                UNREACHABLE();
        }

        return true;
}

Value
GetMember(Ty *ty, Value v, int member, bool try_missing, bool exec)
{
        int n;
        Value *this;
        Value *vp = NULL;
        BuiltinMethod *func;

        if (v.type & VALUE_TAGGED) {
                vp = tags_lookup_method_i(ty, tags_first(ty, v.tags), member);
                if (vp != NULL)  {
                        Value *this = mAo(sizeof *this, GC_VALUE);
                        *this = unwrap(ty, &v);
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
                return *vp;

        case VALUE_DICT:
                func = get_dict_method_i(member);
                if (func == NULL) {
                        n = CLASS_DICT;
                        goto ClassLookup;
                }
                v.type = VALUE_DICT;
                v.tags = 0;
                this = mAo(sizeof *this, GC_VALUE);
                *this = v;
                return BUILTIN_METHOD(member, func, this);

        case VALUE_ARRAY:
                func = get_array_method_i(member);
                if (func == NULL) {
                        n = CLASS_ARRAY;
                        goto ClassLookup;
                }
                v.type = VALUE_ARRAY;
                v.tags = 0;
                this = mAo(sizeof *this, GC_VALUE);
                *this = v;
                return BUILTIN_METHOD(member, func, this);

        case VALUE_STRING:
                func = get_string_method_i(member);
                if (func == NULL) {
                        n = CLASS_STRING;
                        goto ClassLookup;
                }
                v.type = VALUE_STRING;
                v.tags = 0;
                this = mAo(sizeof *this, GC_VALUE);
                *this = v;
                return BUILTIN_METHOD(member, func, this);

        case VALUE_BLOB:
                func = get_blob_method_i(member);
                if (func == NULL) {
                        n = CLASS_BLOB;
                        goto ClassLookup;
                }
                v.type = VALUE_BLOB;
                v.tags = 0;
                this = mAo(sizeof *this, GC_VALUE);
                *this = v;
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

        case VALUE_FUNCTION:
        case VALUE_METHOD:
                if (member == NAMES._class_) {
                        return (class_of(&v) != -1) ? CLASS(class_of(&v)) : NIL;
                } else if (member == NAMES._name_) {
                        return xSz(name_of(&v));
                } else if (member == NAMES._def_) {
                        return FunDef(ty, &v);
                } else if (has_meta(&v)) {
                        return GetMember(ty, *meta_of(ty, &v), member, false, exec);
                }
        case VALUE_BUILTIN_FUNCTION:
        case VALUE_BUILTIN_METHOD:
        case VALUE_FOREIGN_FUNCTION:
                n = CLASS_FUNCTION;
                goto ClassLookup;

        case VALUE_CLASS:
                switch (v.class) {
                case CLASS_ARRAY:
                        if ((func = get_array_method_i(member)) != NULL) {
                                return PTR((void *)func);
                        }
                        break;

                case CLASS_STRING:
                        if ((func = get_string_method_i(member)) != NULL) {
                                return PTR((void *)func);
                        }
                        break;

                case CLASS_DICT:
                        if ((func = get_dict_method_i(member)) != NULL) {
                                return PTR((void *)func);
                        }
                        break;

                case CLASS_BLOB:
                        if ((func = get_blob_method_i(member)) != NULL) {
                                return PTR((void *)func);
                        }
                        break;
                }
                if ((vp = class_lookup_s_getter_i(ty, v.class, member)) != NULL) {
                        return !exec ? (call(ty, vp, &v, 0, NULL), BREAK)
                                     : (exec_fn(ty, vp, &v, 0, NULL), pop());
                }
                if ((vp = class_lookup_field(ty, v.class, member)) != NULL) {
                        return *vp;
                }
                if ((vp = class_lookup_s_method_i(ty, v.class, member)) != NULL) {
                        goto BoundMethod;
                }
                if ((vp = class_lookup_method_i(ty, v.class, member)) != NULL) {
                        return *vp;
                }
                if (member == NAMES._name_) {
                        return xSz(class_name(ty, v.class));
                }
                if (member == NAMES._super_) {
                        Class *super = class_get(ty, v.class)->super;
                        return (super != NULL) ? CLASS(super->i) : NIL;
                }
                if (member == NAMES._fields_) {
                        return itable_dict(ty, &class_get(ty, v.class)->fields);
                }
                if (member == NAMES._methods_) {
                        return itable_dict(ty, &class_get(ty, v.class)->methods);
                }
                if (member == NAMES._getters_) {
                        return itable_dict(ty, &class_get(ty, v.class)->getters);
                }
                if (member == NAMES._setters_) {
                        return itable_dict(ty, &class_get(ty, v.class)->setters);
                }
                if (member == NAMES._static_fields_) {
                        return itable_dict(ty, &class_get(ty, v.class)->s_fields);
                }
                if (member == NAMES._static_methods_) {
                        return itable_dict(ty, &class_get(ty, v.class)->s_methods);
                }
                if (member == NAMES._static_getters_) {
                        return itable_dict(ty, &class_get(ty, v.class)->s_getters);
                }
                n = CLASS_CLASS;
                goto ClassLookup;

        case VALUE_OBJECT:
                vp = itable_lookup(ty, v.object, member);
                if (vp != NULL) {
                        return *vp;
                }
                n = v.class;
ClassLookup:
                vp = class_lookup_getter_i(ty, n, member);
                if (vp != NULL) {
                        return !exec ? (call(ty, vp, &v, 0, NULL), BREAK)
                                     : (exec_fn(ty, vp, &v, 0, NULL), pop());
                }
                vp = class_lookup_method_i(ty, n, member);
                if (vp != NULL) {
BoundMethod:
                        this = mAo(sizeof *this, GC_VALUE);
                        *this = v;
                        return METHOD(member, vp, this);
                }
                if (!try_missing) {
                        break;
                }
                if ((vp = class_lookup_method_i(ty, n, NAMES.missing)) != NULL) {
                        return !exec ? (
                                push(xSz(M_NAME(member))),
                                call(ty, vp, &v, 1, NULL),
                                BREAK
                        ) : (
                                push(xSz(M_NAME(member))),
                                vmC(&METHOD(NAMES.missing, vp, &v), 1)
                        );
                }
                if ((vp = class_lookup_method_i(ty, n, NAMES.method_missing)) != NULL) {
                        this = mAo(sizeof (Value [3]), GC_VALUE);
                        this[0] = v;
                        this[1] = xSz(M_NAME(member));
                        return METHOD(NAMES.method_missing, vp, this);
                }
                if (v.type != VALUE_CLASS) {
                        break;
                }
                if ((vp = class_lookup_s_method_i(ty, v.class, NAMES.missing)) != NULL) {
                        return !exec ? (
                                push(xSz(M_NAME(member))),
                                call(ty, vp, &v, 1, NULL),
                                BREAK
                        ) : (
                                push(xSz(M_NAME(member))),
                                vmC(&METHOD(NAMES.missing, vp, &v), 1)
                        );
                }
                if ((vp = class_lookup_s_method_i(ty, v.class, NAMES.method_missing)) != NULL) {
                        this = mAo(sizeof (Value [3]), GC_VALUE);
                        this[0] = v;
                        this[1] = xSz(M_NAME(member));
                        return METHOD(NAMES.method_missing, vp, this);
                }
                break;

        case VALUE_TAG:
                vp = tags_lookup_static(ty, v.tag, member);
                if (vp == NULL) {
                        vp = tags_lookup_method_i(ty, v.tag, member);
                }
                return (vp == NULL) ? NONE : *vp;
        }

        return NONE;
}

static int
GetDynamicMemberId(Ty *ty, bool strict)
{
        Value v = peek();

        switch (v.type) {
        case VALUE_STRING:
        {
                byte_vector name = {0};
                InternEntry *member;

                SCRATCH_SAVE();

                svPn(name, ss(v), sN(v));
                svP(name, '\0');

                member = intern_get(&xD.members, v_(name, 0));
                if (member->id < 0) {
                        if (!strict) {
                                SCRATCH_RESTORE();
                                pop();
                                return -1;
                        } else {
                                int z = intern_put(member, NULL)->id;
                                SCRATCH_RESTORE();
                                pop();
                                return -(z + 1);
                        }
                } else {
                        SCRATCH_RESTORE();
                        pop();
                        return member->id;

                }

                break;
        }

        default:
                zP(
                        "dynamic member expression evaluated "
                        "to non-string value: %s",
                        VSC(&v)
                );
        }
}

static void
CallMethod(Ty *ty, int i, int n, int nkw, bool b)
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
                i = GetDynamicMemberId(ty, !b);
                if (i == -1) {
                        goto QuietFailure;
                }
                if (i < 0) {
                        i = -(i + 1);
                }
        }

        if (n == -1) {
                n = vN(STACK) - *vvX(SP_STACK) - nkw - 1;
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

        case VALUE_ARRAY:
                func = get_array_method_i(i);
                if (func == NULL) {
                        class = CLASS_ARRAY;
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

        case VALUE_FUNCTION:
        case VALUE_BUILTIN_FUNCTION:
        case VALUE_FOREIGN_FUNCTION:
        case VALUE_METHOD:
        case VALUE_BUILTIN_METHOD:
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
                if (DispatchMethodFast(ty, value, i, n, nkw)) {
                        return;
                }
                class = value.class;
ClassLookup:
                vp = class_lookup_method_i(ty, class, i);
                if (vp == NULL) {
                        attr = GetMember(ty, value, i, false, true);
                        vp = (attr.type == VALUE_NONE) ? NULL : &attr;
                        self = NULL;
                }
                break;

        case VALUE_NIL:
                STACK.count -= (n + 1 + nkw);
                push(NIL);
                return;

        default:
                class = CLASS_OBJECT;
                goto ClassLookup;

        }

        if (func != NULL) {
                pop();
                gP(&value);
                attr = BuildKwargsDict(ty, nkw);
                gP(&attr);
                v = (*func)(ty, &value, n, &attr);
                gX();
                gX();
                STACK.count -= n;
                push(v);
                return;
        }

        if (
                (vp == NULL)
             && (value.type == VALUE_OBJECT)
             && (vp = class_lookup_method_i(ty, value.class, NAMES.method_missing)) != NULL
        ) {
                method = M_NAME(i);
                v = pop();
                push(NIL);
                memmove(top() - (n - 1), top() - n, n * sizeof (Value));
                top()[-n++] = STRING_NOGC(method, strlen(method));
                push(v);
                self = &value;
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
                DoCall(ty, &v, n, nkw, false);
                return;
        }

DoCall:
        if (vp != NULL) {
                pop();
                if (self != NULL) {
                        v = METHOD(i, vp, self);
                        DoCall(ty, &v, n, nkw, true);
                } else {
                        v = *vp;
                        DoCall(ty, &v, n, nkw, false);
                }
        } else if (b) {
QuietFailure:
                STACK.count -= (n + 1 + nkw);
                push(NIL);
        } else {
                zP("call to non-existent method '%s' on %s", M_NAME(i), VSC(&value));
        }
}

// ===/ < > <= >= == != /=======================================================
#define DEFINE_RELATIONAL_OP(name, op, eop)                                     \
TY_INSTR_INLINE static void                                                     \
name(Ty *ty)                                                                    \
{                                                                               \
        Value v;                                                                \
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
        default:                                                                \
                v = vm_try_2op(ty, eop, top() - 1, top());                      \
                                                                                \
                if (v.type == VALUE_NONE) {                                     \
                        v = BOOLEAN(value_compare(ty, top() - 1, top()) op 0);  \
                }                                                               \
                                                                                \
                break;                                                          \
        }                                                                       \
                                                                                \
        pop();                                                                  \
        pop();                                                                  \
        push(v);                                                                \
}

inline static void
DoEq(Ty *ty)
{
        Value b = pop();
        Value a = pop();

        push(BOOLEAN(value_test_equality(ty, &a, &b)));
}

inline static void
DoNeq(Ty *ty)
{
        Value b = pop();
        Value a = pop();

        push(BOOLEAN(!value_test_equality(ty, &a, &b)));
}

DEFINE_RELATIONAL_OP(DoGeq, >=, OP_GEQ)
DEFINE_RELATIONAL_OP(DoGt,   >, OP_GT)
DEFINE_RELATIONAL_OP(DoLeq, <=, OP_LEQ)
DEFINE_RELATIONAL_OP(DoLt,   <, OP_LT)

#undef DEFINE_RELATIONAL_OP
// =============================================================================

TY_INSTR_INLINE static void
DoCmp(Ty *ty)
{

        int i = value_compare(ty, top() - 1, top());

        pop();
        pop();

        if (i < 0)
                push(INTEGER(-1));
        else if (i > 0)
                push(INTEGER(1));
        else
                push(INTEGER(0));
}

inline static void
DoNot(Ty *ty)
{
        Value v = pop();
        push(BOOLEAN(!value_truthy(ty, &v)));
}

TY_INSTR_INLINE static void
DoQuestion(Ty *ty, bool exec)
{
        if (top()->type == VALUE_NIL) {
                *top() = BOOLEAN(false);
        } else {
                CallMethod(ty, OP_QUESTION, 0, 0, false);
                if (exec) {
                        ExecCurrentCall(ty);
                }
        }
}

TY_INSTR_INLINE static void
DoNeg(Ty *ty, bool exec)
{
        Value v = pop();

        if (v.type == VALUE_INTEGER) {
                push(INTEGER(-v.z));
        } else if (v.type == VALUE_REAL) {
                push(REAL(-v.real));
        } else {
                CallMethod(ty, OP_NEG, 0, 0, false);
                if (exec) {
                        ExecCurrentCall(ty);
                }
        }
}

TY_INSTR_INLINE static void
DoCount(Ty *ty, bool exec)
{
        Value v = pop();

        if (v.type & VALUE_TAGGED) {
                push(unwrap(ty, &v));
                return;
        }

        switch (v.type) {
        case VALUE_BLOB:   push(INTEGER(v.blob->count));  break;
        case VALUE_ARRAY:  push(INTEGER(v.array->count)); break;
        case VALUE_DICT:   push(INTEGER(v.dict->count));  break;
        case VALUE_TUPLE:  push(INTEGER(v.count));        break;
        case VALUE_STRING:
                push(string_length(ty, &v, 0, NULL));
                break;

        case VALUE_OBJECT:
        case VALUE_CLASS:
                push(v);
                CallMethod(ty, NAMES._len_, 0, 0, false);
                if (exec) {
                        ExecCurrentCall(ty);
                }
                break;

        default:
                zP("# applied to operand of invalid type: %s", VSC(&v));
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

TY_INSTR_INLINE static void
DoBinaryOp(Ty *ty, int op, bool exec)
{
        int i = op_dispatch(ty, op, ClassOf(top() - 1), ClassOf(top()));

        if (i == -1) {
                op_dump(op);
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

TY_INSTR_INLINE static void
DoMutDiv(Ty *ty)
{
        uptr c, p = (uptr)poptarget();
        struct itable *o;
        Value *vp, *vp2, val, x;
        void *v = vp = (void *)pP(p);
        unsigned char b;

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
                push(*vp);
                break;

        case 1:
                if (UNLIKELY(top()->type != VALUE_INTEGER)) {
                        zP("attempt to divide byte by non-integer: %s", VSC(top()));
                }
                b = ((Blob *)vZ(TARGETS)->gc)->items[((uptr)vp) >> 3] /= pop().z;
                push(INTEGER(b));
                break;

        case 2:
                c = (uptr)poptarget();
                o = TARGETS.items[TARGETS.count].gc;
                vp = poptarget();
                exec_fn(ty, vp, &OBJECT(o, c), 0, NULL);
                top()[-1] = vm_2op(ty, OP_DIV, top(), top() - 1);
                pop();
                call(ty, v, &OBJECT(o, c), 1, NULL);
                break;

        default:
                zP("bad target pointer :(");
        }
}

TY_INSTR_INLINE static void
DoMutMod(Ty *ty)
{
        uptr c, p = (uptr)poptarget();
        struct itable *o;
        INT32_C(4);
        Value *vp, *vp2, val, x;
        void *v = vp = (void *)(p & ~PMASK3);
        unsigned char b;

        switch (p & PMASK3) {
        case 0:
                if (vp->type == VALUE_OBJECT && (vp2 = class_method(ty, vp->class, "%=")) != NULL) {
                        gP(vp);
                        exec_fn(ty, vp2, vp, 1, NULL);
                        gX();
                        pop();
                } else {
                        x = pop();
                        if ((val = vm_try_2op(ty, OP_MUT_MOD, vp, &x)).type != VALUE_NONE) {
                                vp = &val;
                        } else {
                                *vp = vm_2op(ty, OP_MOD, vp, &x);
                        }
                }
                push(*vp);
                break;

        case 1:
                if (UNLIKELY(top()->type != VALUE_INTEGER)) {
                        zP("attempt to divide byte by non-integer: %s", VSC(top()));
                }
                b = ((struct blob *)TARGETS.items[TARGETS.count].gc)->items[((uptr)vp) >> 3] %= pop().z;
                push(INTEGER(b));
                break;

        case 2:
                c = (uptr)poptarget();
                o = TARGETS.items[TARGETS.count].gc;
                vp = poptarget();
                exec_fn(ty, vp, &OBJECT(o, c), 0, NULL);
                top()[-1] = vm_2op(ty, OP_MOD, top(), top() - 1);
                pop();
                call(ty, v, &OBJECT(o, c), 1, NULL);
                break;

        default:
                zP("bad target pointer :(");
        }
}

TY_INSTR_INLINE static void
DoMutMul(Ty *ty)
{
        uptr c, p = (uptr)poptarget();
        struct itable *o;
        Value *vp, *vp2, val, x;
        void *v = vp = (void *)(p & ~PMASK3);
        unsigned char b;

        switch (p & PMASK3) {
        case 0:
                if (vp->type == VALUE_OBJECT && (vp2 = class_method(ty, vp->class, "*=")) != NULL) {
                        gP(vp);
                        exec_fn(ty, vp2, vp, 1, NULL);
                        gX();
                        pop();
                } else {
                        x = pop();
                        if ((val = vm_try_2op(ty, OP_MUT_MUL, vp, &x)).type != VALUE_NONE) {
                                vp = &val;
                        } else {
                                *vp = vm_2op(ty, OP_MUL, vp, &x);
                        }
                }
                push(*vp);
                break;

        case 1:
                if (UNLIKELY(top()->type != VALUE_INTEGER)) {
                        zP("attempt to multiply byte by non-integer");
                }
                b = ((struct blob *)TARGETS.items[TARGETS.count].gc)->items[((uptr)vp) >> 3] *= pop().z;
                push(INTEGER(b));
                break;

        case 2:
                c = (uptr)poptarget();
                o = TARGETS.items[TARGETS.count].gc;
                vp = poptarget();
                exec_fn(ty, vp, &OBJECT(o, c), 0, NULL);
                top()[-1] = vm_2op(ty, OP_MUL, top(), top() - 1);
                pop();
                call(ty, v, &OBJECT(o, c), 1, NULL);
                break;

        default:
                zP("bad target pointer :(");
        }
}

TY_INSTR_INLINE static void
DoMutSub(Ty *ty)
{
        uptr c, p = (uptr)poptarget();
        struct itable *o;
        Value *vp, x, val;
        void *v = vp = (void *)(p & ~PMASK3);
        unsigned char b;

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
                default:
                        x = pop();

                        if ((val = vm_try_2op(ty, OP_MUT_SUB, vp, &x)).type != VALUE_NONE) {
                                vp = &val;
                        } else {
                                *vp = vm_2op(ty, OP_SUB, vp, &x);
                        }

                        break;
                }
                push(*vp);
                break;

        case 1:
                if (UNLIKELY(top()->type != VALUE_INTEGER)) {
                        zP("attempt to subtract non-integer from byte");
                }
                b = ((struct blob *)TARGETS.items[TARGETS.count].gc)->items[((uptr)vp) >> 3] -= pop().z;
                push(INTEGER(b));
                break;

        case 2:
                c = (uptr)poptarget();
                o = TARGETS.items[TARGETS.count].gc;
                vp = poptarget();
                exec_fn(ty, vp, &OBJECT(o, c), 0, NULL);
                top()[-1] = vm_2op(ty, OP_SUB, top(), top() - 1);
                pop();
                call(ty, v, &OBJECT(o, c), 1, NULL);
                break;

        default:
                zP("bad target pointer :(");
        }
}

TY_INSTR_INLINE static void
DoMutAdd(Ty *ty)
{
        uptr c, p = (uptr)poptarget();
        struct itable *o;
        Value *vp, val, x;
        void *v = vp = (void *)(p & ~PMASK3);
        unsigned char b;

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

                push(*vp);

                break;

        case 1:
                if (UNLIKELY(top()->type != VALUE_INTEGER)) {
                        zP("attempt to add non-integer to byte");
                }
                b = ((struct blob *)TARGETS.items[TARGETS.count].gc)->items[((uptr)vp) >> 3] += pop().z;
                push(INTEGER(b));
                break;

        case 2:
                c = (uptr)poptarget();
                o = TARGETS.items[TARGETS.count].gc;
                vp = poptarget();
                exec_fn(ty, vp, &OBJECT(o, c), 0, NULL);
                top()[-1] = vm_2op(ty, OP_ADD, top(), top() - 1);
                pop();
                call(ty, v, &OBJECT(o, c), 1, NULL);
                break;

        default:
                zP("bad target pointer :(");
        }
}

TY_INSTR_INLINE static void
DoMutAnd(Ty *ty)
{
        uptr c, p = (uptr)poptarget();
        struct itable *o;
        Value *vp, val, x;
        void *v = vp = (void *)(p & ~PMASK3);
        unsigned char b;

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
                default:
                        x = pop();
                        val = vm_try_2op(ty, OP_MUT_AND, vp, &x);
                        if (val.type != VALUE_NONE) {
                                vp = &val;
                        } else {
                                *vp = vm_2op(ty, OP_BIT_AND, vp, &x);
                        }
                        push(*vp);
                        break;
                }
                break;

        case 1:
                if (UNLIKELY(top()->type != VALUE_INTEGER)) {
                        zP("attempt to AND byte with non-integer");
                }
                b = ((Blob *)TARGETS.items[TARGETS.count].gc)->items[((uptr)vp) >> 3] &= pop().z;
                push(INTEGER(b));
                break;

        case 2:
                c = (uptr)poptarget();
                o = TARGETS.items[TARGETS.count].gc;
                vp = poptarget();
                exec_fn(ty, vp, &OBJECT(o, c), 0, NULL);
                top()[-1] = vm_2op(ty, OP_BIT_AND, top(), top() - 1);
                pop();
                call(ty, v, &OBJECT(o, c), 1, NULL);
                break;

        default:
                zP("bad target pointer :(");
        }
}

TY_INSTR_INLINE static void
DoMutOr(Ty *ty)
{
        uptr c, p = (uptr)poptarget();
        struct itable *o;
        Value *vp, val, x;
        void *v = vp = (void *)(p & ~PMASK3);
        unsigned char b;

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
                default:
                        x = pop();
                        val = vm_try_2op(ty, OP_MUT_OR, vp, &x);
                        if (val.type != VALUE_NONE) {
                                vp = &val;
                        } else {
                                *vp = vm_2op(ty, OP_BIT_OR, vp, &x);
                        }
                        push(*vp);
                        break;
                }
                break;

        case 1:
                if (UNLIKELY(top()->type != VALUE_INTEGER)) {
                        zP("attempt to OR byte with non-integer");
                }
                b = ((Blob *)TARGETS.items[TARGETS.count].gc)->items[((uptr)vp) >> 3] |= pop().z;
                push(INTEGER(b));
                break;

        case 2:
                c = (uptr)poptarget();
                o = TARGETS.items[TARGETS.count].gc;
                vp = poptarget();
                exec_fn(ty, vp, &OBJECT(o, c), 0, NULL);
                top()[-1] = vm_2op(ty, OP_BIT_OR, top(), top() - 1);
                pop();
                call(ty, v, &OBJECT(o, c), 1, NULL);
                break;

        default:
                zP("bad target pointer :(");
        }
}

TY_INSTR_INLINE static void
DoMutXor(Ty *ty)
{
        uptr c, p = (uptr)poptarget();
        struct itable *o;
        Value *vp, val, x;
        void *v = vp = (void *)(p & ~PMASK3);
        unsigned char b;

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
                default:
                        x = pop();
                        val = vm_try_2op(ty, OP_MUT_XOR, vp, &x);
                        if (val.type != VALUE_NONE) {
                                vp = &val;
                        } else {
                                *vp = vm_2op(ty, OP_BIT_XOR, vp, &x);
                        }
                        push(*vp);
                        break;
                }
                break;

        case 1:
                if (UNLIKELY(top()->type != VALUE_INTEGER)) {
                        zP("attempt to XOR byte with non-integer");
                }
                b = ((Blob *)TARGETS.items[TARGETS.count].gc)->items[((uptr)vp) >> 3] ^= pop().z;
                push(INTEGER(b));
                break;

        case 2:
                c = (uptr)poptarget();
                o = TARGETS.items[TARGETS.count].gc;
                vp = poptarget();
                exec_fn(ty, vp, &OBJECT(o, c), 0, NULL);
                top()[-1] = vm_2op(ty, OP_BIT_XOR, top(), top() - 1);
                pop();
                call(ty, v, &OBJECT(o, c), 1, NULL);
                break;

        default:
                zP("bad target pointer :(");
        }
}

TY_INSTR_INLINE static void
DoMutShl(Ty *ty)
{
        uptr c, p = (uptr)poptarget();
        struct itable *o;
        Value *vp, val, x;
        void *v = vp = (void *)(p & ~PMASK3);
        unsigned char b;

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
                        push(*vp);
                        break;
                }
                break;

        case 1:
                if (UNLIKELY(top()->type != VALUE_INTEGER)) {
                        zP("attempt to left-shift byte by non-integer");
                }
                b = ((Blob *)TARGETS.items[TARGETS.count].gc)->items[((uptr)vp) >> 3] <<= pop().z;
                push(INTEGER(b));
                break;

        case 2:
                c = (uptr)poptarget();
                o = TARGETS.items[TARGETS.count].gc;
                vp = poptarget();
                exec_fn(ty, vp, &OBJECT(o, c), 0, NULL);
                top()[-1] = vm_2op(ty, OP_BIT_SHL, top(), top() - 1);
                pop();
                call(ty, v, &OBJECT(o, c), 1, NULL);
                break;

        default:
                zP("bad target pointer :(");
        }
}

TY_INSTR_INLINE static void
DoMutShr(Ty *ty)
{
        uptr c, p = (uptr)poptarget();
        struct itable *o;
        Value *vp, val, x;
        void *v = vp = (void *)(p & ~PMASK3);
        unsigned char b;

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
                        push(*vp);
                        break;
                }
                break;

        case 1:
                if (UNLIKELY(top()->type != VALUE_INTEGER)) {
                        zP("attempt to right-shift byte by non-integer");
                }
                b = ((Blob *)TARGETS.items[TARGETS.count].gc)->items[((uptr)vp) >> 3] >>= pop().z;
                push(INTEGER(b));
                break;

        case 2:
                c = (uptr)poptarget();
                o = TARGETS.items[TARGETS.count].gc;
                vp = poptarget();
                exec_fn(ty, vp, &OBJECT(o, c), 0, NULL);
                top()[-1] = vm_2op(ty, OP_BIT_SHR, top(), top() - 1);
                pop();
                call(ty, v, &OBJECT(o, c), 1, NULL);
                break;

        default:
                zP("bad target pointer :(");
        }
}

#ifndef TY_RELEASE
__attribute__((noinline))
#else
TY_INSTR_INLINE
#endif
static void
DoAssign(Ty *ty)
{
        uptr m, c, p = (uptr)poptarget();
        void *v = (void *)pP(p);
        struct itable *o;

        switch (pT(p)) {
        case 0:
                *(Value *)v = peek();
                break;

        case 1:
                ((Blob *)TARGETS.items[TARGETS.count].gc)->items[((uptr)v >> 3)] = peek().z;
                break;

        case 2:
                c = (uptr)poptarget();
                o = vZ(TARGETS)[0].gc;
                poptarget();
                call(ty, v, &OBJECT(o, c), 1, NULL);
                break;

        case 3:
                m = (p >> 3);
                c = (uptr)poptarget();
                o = vZ(TARGETS)[0].gc;
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

        default:
                zP("bad target pointer :(");
        }
}

static void
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
                vp = itable_lookup(ty, v.object, z);
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
                v.object->diverged = true;
                pushtarget(itable_get(ty, v.object, z), v.object);
                break;

        case VALUE_CLASS:
                vp = class_lookup_field(ty, v.class, z);
                if (vp != NULL) {
                        pushtarget(vp, NULL);
                        return;
                }
                vp = class_lookup_s_setter_i(ty, v.class, z);
                if (vp != NULL) {
                        pushtarget(vp, NULL);
                        pushtarget((Value *)(uptr)v.class, NULL);
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
                DoTargetMember(ty, *meta_of(ty, &v), z);
                break;

        default:
                zP("assignment to member of non-object: %s", VSC(&v));
        }
}

static void
DoTargetSubscript(Ty *ty)
{
        Value v;
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
                pushtarget(&container.array->items[subscript.z], container.array);
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
                pushtarget((Value *)((((uptr)(subscript.z)) << 3) | 1) , container.blob);
                break;

        case VALUE_PTR:
                if (IP[0] != INSTR_ASSIGN) {
                        goto BadContainer;
                }
                if (UNLIKELY(subscript.type != VALUE_INTEGER)) {
                        zP("non-integer pointer offset used in subscript assignment: %s", VSC(&subscript));
                }
                Value p = vm_2op(ty, OP_ADD, &container, &subscript);
                pop();
                pop();
                v = pop();
                push(p);
                push(v);
                v = cffi_store(ty, 2, NULL);
                pop();
                pop();
                push(v);
                IP += 1;
                return;

        default:
        BadContainer:
                zP(
                        "attempt to perform subscript assignment on "
                        "something other than an object or array: %s",
                        VSC(&container)
                );
        }

        pop();
        pop();
}

static void
DoAssignSubscript(Ty *ty)
{
        Value v;
        Value p;
        Value *f;
        Value subscript = top()[0];
        Value container = top()[-1];
        Value value = top()[-2];

        switch (container.type) {
        case VALUE_ARRAY:
                if (UNLIKELY(subscript.type != VALUE_INTEGER)) {
                        zP("non-integer index in subscript assignment to Array: %s", VSC(&subscript));
                }
                if (subscript.z < 0) {
                        subscript.z += container.array->count;
                }
                if (UNLIKELY(subscript.z < 0 || subscript.z >= container.array->count)) {
                        push(TAGGED(TAG_INDEX_ERR, container, subscript));
                        RaiseException(ty);
                }
                *v_(*container.array, subscript.z) = value;
                break;

        case VALUE_DICT:
                dict_put_value(ty, container.dict, subscript, value);
                break;

        case VALUE_BLOB:
                if (UNLIKELY(subscript.type != VALUE_INTEGER)) {
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
                if (UNLIKELY(subscript.type != VALUE_INTEGER)) {
                        zP("non-integer offset in pointer subscript assignment: %s", VSC(&subscript));
                }
                p = vm_2op(ty, OP_ADD, &container, &subscript);
                pop();
                pop();
                pop();
                push(p);
                push(value);
                v = cffi_store(ty, 2, NULL);
                pop();
                pop();
                push(v);
                return;

        case VALUE_OBJECT:
                swap();
                pop();
                swap();
                f = class_lookup_setter_i(ty, container.class, NAMES.subscript);
                if (f != NULL) {
                        call(ty, f, &container, 2, NULL);
                }
                return;

        case VALUE_CLASS:
                swap();
                pop();
                swap();
                f = class_lookup_s_setter_i(ty, container.class, NAMES.subscript);
                if (f != NULL) {
                        call(ty, f, &container, 2, NULL);
                }
                return;

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
        push(v);

        if (UNLIKELY(PACK_TYPES(a.type, b.type) != PAIR_OF(VALUE_INTEGER))) {
                zP(
                        "Range.init(): bad bounds:, (%s, %s)",
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

static void
DoDictLiteral(Ty *ty, Value const *dflt)
{
        Dict *dict = dict_new(ty);
        Value val  = DICT(dict);

        usize n = (vN(STACK) - *vvX(SP_STACK));

        gP(&val);

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

        gX();

        STACK.count -= n;

        push(val);
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
        Value v = TUPLE(mAo(k * sizeof (Value), GC_TUPLE), NULL, k, false);

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

static void
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

static void
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
IterGetNext(Ty *ty)
{
        Value v;
        Value *vp;

        ptrdiff_t off;

        int i;
        int n;

        v = top()[-1];
        i = top()[-2].i++;

        dont_printf("GET_NEXT: v = %s\n", VSC(&v));
        dont_printf("GET_NEXT: i = %d\n", i);
        print_stack(ty, 10);

        switch (v.type) {
        case VALUE_ARRAY:
                if (i < v.array->count) {
                        push(v.array->items[i]);
                } else {
                        push(NONE);
                }
                break;
        case VALUE_DICT:
                off = top()[-2].off;
                while (off < v.dict->size && v.dict->keys[off].type == 0) {
                        off += 1;
                }
                if (off < v.dict->size) {
                        top()[-2].off = off + 1;
                        push(v.dict->keys[off]);
                        push(v.dict->values[off]);
                        RC = 1;
                        pop();
                } else {
                        push(NONE);
                }
                break;
        case VALUE_FUNCTION:
                push(INTEGER(i));
                call(ty, &v, NULL, 1, NULL);
                break;
        case VALUE_OBJECT:
                if ((vp = class_method(ty, v.class, "__next__")) != NULL) {
                        push(INTEGER(i));
                        call6t(ty, vp, &v, 1, NULL, next_fix);
                } else if ((vp = class_lookup_method_i(ty, v.class, NAMES._iter_)) != NULL) {
                        pop();
                        pop();
                        --top()->i;
                        /* Have to repeat this instruction */
                        call6t(ty, vp, &v, 0, NULL, iter_fix);
                        return;
                } else {
                        goto NoIter;
                }
                break;
        case VALUE_BLOB:
                if (i < v.blob->count) {
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

static bool
LoopCheck(Ty *ty, i32 z, char *jump)
{
        imax k = top()[-3].z - 1;

        STACK.count += RC;

        push(INTEGER(k));

        bool done = (top()[-1].type == VALUE_NONE);
        if (done) {
                DOJUMP(jump);
        }

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

        return done;
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

static void
InstallMethods(Ty *ty, struct itable *table, i32 n)
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

        method.info = memcpy(mrealloc(NULL, size), fun->info, size);
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
                Scope *scope = func->scope;
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
        char *save = IP;

        IP = code;

        uptr s;

        double x;

        imax k;

        int n;
        int i;
        int j;
        int z;
        int tag;
        int nkw = 0;

        Value v;
        Value key;
        Value value;
        Value container;
        Value subscript;
        Value *vp;

        char *str;
        char *jump;

        bool b = false;

        struct try *t;

        PopulateGlobals(ty);

#ifdef TY_PROFILER
        char *StartIPLocal = LastIP;
#endif

        EXEC_DEPTH += 1;
        LOG("vm_exec(): ==> %d", EXEC_DEPTH);

        for (;;) {
NextInstruction:
                if (UNLIKELY(GC_IS_WAITING || AnySignalPending)) {
                        if (UNLIKELY(TAKE_PENDING_SIGNALS())) {
                                HandlePendingSignals(ty);
                        }
                        if (GC_IS_WAITING) {
                                WaitGC(ty);
                        }
                }

#ifdef TY_PROFILER
                if (Samples != NULL) {
                        u64 now = TyThreadTime();

                        if (LastThreadGCTime > 0) {
                                Value *count = dict_put_key_if_not_exists(ty, FuncSamples, PTR((void *)GC_ENTRY));
                                if (count->type == VALUE_NIL) {
                                        *count = INTEGER(LastThreadGCTime);
                                } else {
                                        count->z += LastThreadGCTime;
                                }
                                LastThreadGCTime = 0;
                        }

                        if (StartIPLocal != LastIP && LastThreadTime != 0 && *LastIP != INSTR_HALT &&
                            LastIP != next_fix && LastIP != iter_fix && LastIP != next_fix + 1 &&
                            LastIP != iter_fix + 1 && LastIP != &throw) {

                                u64 dt = now - LastThreadTime;

                                TySpinLockLock(&ProfileMutex);

                                istat_add(&prof, LastIP, dt);

                                Value *count = dict_put_key_if_not_exists(ty, Samples, PTR(LastIP));
                                if (count->type == VALUE_NIL) {
                                        *count = INTEGER(dt);
                                } else {
                                        count->z += dt;
                                }

                                int *func = (FRAMES.count > 0) ? ActiveFun(ty)->info : NULL;
                                count = dict_put_key_if_not_exists(ty, FuncSamples, PTR(func));
                                if (count->type == VALUE_NIL) {
                                        *count = INTEGER(dt);
                                } else {
                                        count->z += dt;
                                }

                                TySpinLockUnlock(&ProfileMutex);
                        }

                        if (WantReport) {
                                TySpinLockLock(&ProfileMutex);
                                ProfileReport(ty);
                                TySpinLockUnlock(&ProfileMutex);
                                WantReport = false;
                        }

                        LastIP = IP;
                        LastThreadTime = TyThreadTime();

                }
#endif
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
                        while (vN(THREAD_LOCALS) <= n) {
                                xvP(THREAD_LOCALS, NIL);
                        }
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
                        while (vN(THREAD_LOCALS) <= n) {
                                xvP(THREAD_LOCALS, NIL);
                        }
                        pushtarget(v_(THREAD_LOCALS, n), NULL);
                        break;
                CASE(TARGET_LOCAL)
                        READVALUE(n);
                        LOG("Targeting %d", n);
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
                        DoAssignSubscript(ty);
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
                        if ((vp = TargetFieldFast(ty, top(), z)) != NULL) {
                                pushtarget(vp, v.object);
                        } else {
                                DoTargetMember(ty, peek(), z);
                        }
                        pop();
                        break;
                CASE(TARGET_SELF_MEMBER)
                        READVALUE(z);
                        v = GetSelf(ty);
                        if ((vp = TargetFieldFast(ty, &v, z)) != NULL) {
                                pushtarget(vp, v.object);
                        } else {
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
                CASE(MAYBE_ASSIGN)
                        vp = poptarget();
                        if (vp->type == VALUE_NIL) {
                                *vp = peek();
                        }
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
                        if (top()->type != VALUE_ARRAY || top()->array->count < i + j) {
                                DOJUMP(jump);
                        } else {
                                Array *rest = vA();
                                uvPn(*rest, top()->array->items + i, top()->array->count - (i + j));
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
                                *vp = TUPLE(rest, NULL, count, false);
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
                CASE(UNTAG_OR_DIE)
                        READVALUE(tag);
                        if (UNLIKELY(!tags_same(ty, tags_first(ty, top()->tags), tag))) {
                                MatchError;
                        } else {
                                if ((top()->tags = tags_pop(ty, top()->tags)) == 0) {
                                        top()->type &= ~VALUE_TAGGED;
                                }
                        }
                        break;
                CASE(STEAL_TAG)
                        vp = poptarget();
                        if (LIKELY(top()->type & VALUE_TAGGED)) {
                                *vp = TAG(tags_first(ty, top()->tags));
                                if ((top()->tags = tags_pop(ty, top()->tags)) == 0) {
                                        top()->type &= ~VALUE_TAGGED;
                                }
                        } else {
                                MatchError;
                        }
                        break;
                CASE(TRY_STEAL_TAG)
                        READVALUE(n);
                        vp = poptarget();
                        if (top()->tags > 0) {
                                if (top() == vp) {
                                        zPx("cannot steal tag into self");
                                }
                                *vp = TAG(tags_first(ty, top()->tags));
                                if ((top()->tags = tags_pop(ty, top()->tags)) == 0) {
                                        top()->type &= ~VALUE_TAGGED;
                                }
                        } else {
                                IP += n;
                        }
                        break;
                CASE(BAD_MATCH)
                        MatchError;
                CASE(BAD_DISPATCH);
                        if (v_L(CALLS) == unapply) {
                                push(NONE);
                                goto Return;
                        } else {
                                push(TAG(TAG_DISPATCH_ERR));
                                vvX(FRAMES);
                                IP = *vvX(CALLS);
                                RaiseException(ty);
                        }
                        break;
                CASE(BAD_CALL)
                        v = peek();

                        READSTR(str);

                        if (v_L(CALLS) == unapply) {
                                *top() = NONE;
                                goto Return;
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
                        struct try *t = GetCurrentTry(ty);
                        t->state = TRY_THROW;
                        t->end = NULL;
                        IP = t->finally;
                        break;
                }
                CASE(FINALLY)
                {
                        struct try *t = GetCurrentTry(ty);
                        t->state = TRY_FINALLY;
                        t->end = IP;
                        IP = t->finally;
                        break;
                }
                CASE(END_TRY)
                {
                        struct try *t = *vvX(TRY_STACK);

                        if (t->end == NULL) {
                                DoThrow(ty);
                        } else {
                                IP = t->end;
                        }

                        break;
                }
                CASE(CATCH)
                        PopThrowCtx(ty);
                        v_L(TRY_STACK)->state = TRY_FINALLY;
                        break;
                CASE(TRY)
                {
                        struct try *t = PushTry(ty);

                        if (setjmp(t->jb) != 0) {
                                break;
                        }

                        READVALUE(n);
                        t->catch = IP + n;

                        READVALUE(n);
                        t->finally = (n == -1) ? NULL : IP + n;

                        READVALUE(n);
                        t->end = (n == -1) ? NULL : IP + n;
                        break;
                }
                CASE(TRACE)
                        push(ResolveTrace(ty, CurrentThrowCtx(ty)));
                        break;
                CASE(DROP)
                        DoDrop(ty);
                        break;
                CASE(DISCARD_DROP_GROUP)
                        vvX(DROP_STACK);
                        break;
                CASE(PUSH_DROP_GROUP)
                        xvP(DROP_STACK, ARRAY(vA()));
                        break;
                CASE(PUSH_DROP)
                        uvP(*vvL(DROP_STACK)->array, peek());
                        break;
                CASE(PUSH_DEFER_GROUP)
                        break;
                CASE(DEFER)
                        t = GetCurrentTry(ty);
                        xvP(t->defer, pop());
                        break;
                CASE(CLEANUP)
                        t = *vvL(TRY_STACK);
                        for (int i = 0; i < t->defer.count; ++i) {
                                vmC(&t->defer.items[i], 0);
                        }
                        break;
                CASE(ENTER)
                        if ((z = ClassOf(top())) < 0) {
                                break;
                        }
                        if ((vp = class_lookup_method_i(ty, z, NAMES._enter_)) == NULL) {
                                break;
                        }
                        v = pop();
                        call(ty, vp, &v, 0, NULL);
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
                CASE(ENSURE_EQUALS_VAR)
                        READVALUE(n);
                        v = pop();
                        if (!value_test_equality(ty, top(), &v)) {
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
                CASE(TRY_INDEX_TUPLE)
                        READJUMP(jump);
                        READVALUE(i);
                        if (top()->type != VALUE_TUPLE || top()->count <= i) {
                                DOJUMP(jump);
                        } else {
                                push(top()->items[i]);
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
                        if (!(top()->type & VALUE_TAGGED) || tags_first(ty, top()->tags) != tag) {
                                DOJUMP(jump);
                        } else {
                                top()->tags = tags_pop(ty, top()->tags);
                                if (top()->tags == 0) {
                                        top()->type &= ~VALUE_TAGGED;
                                }
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
                        n = STACK.count - *vvX(SP_STACK);

                        v = ARRAY(vAn(n));
                        v.array->count = n;

                        memcpy(
                                v.array->items,
                                topN(n),
                                n * sizeof (Value)
                        );

                        STACK.count -= n;

                        push(v);

                        break;
                CASE(TUPLE)
                        DoTupleLiteral(ty);
                        break;
                CASE(GATHER_TUPLE)
                        n = vN(STACK) - *vvX(SP_STACK);

                        vp = mAo(n * sizeof (Value), GC_TUPLE);
                        v = TUPLE(vp, NULL, n, false);

                        __builtin_memcpy(vp, topN(n), n * sizeof (Value));

                        STACK.count -= n;
                        push(v);

                        break;
                CASE(DICT)
                        DoDictLiteral(ty, NULL);
                        break;
                CASE(DEFAULT_DICT)
                        value = pop();
                        DoDictLiteral(ty, &value);
                        break;
                CASE(SELF)
                        if (FRAMES.count == 0) {
                        } else {
                                push(NIL);
                        }
                        break;
                CASE(NIL)
                        push(NIL);
                        break;
                CASE(TO_STRING)
                        if (top()->type == VALUE_STRING) {
                                break;
                        }
                        if (UNLIKELY(top()->type == VALUE_PTR)) {
                                char *s = VSC(top());
                                pop();
                                push(STRING_NOGC(s, strlen(s)));
                        } else {
                                CallMethod(ty, NAMES._str_, 0, 0, false);
                        }
                        break;
                CASE(YIELD)
Yield:
                {
                        Generator *gen = GetCurrentGenerator(ty);

                        if (UNLIKELY(gen == NULL)) {
                                zP("attempt to yield from outside of a generator context");
                        }

                        co_yield_value(ty);

                        break;
                }
                CASE(YIELD_NONE)
                        push(None);
                        goto Yield;
                CASE(YIELD_SOME)
                        *top() = Some(peek());
                        goto Yield;
                CASE(MAKE_GENERATOR)
                        v = GENERATOR(mAo0(sizeof *v.gen, GC_GENERATOR));

                        n = vN(STACK) - vvL(FRAMES)->fp;
                        xvPn(v.gen->frame, vZ(STACK) - n, n);

                        v.gen->ip = IP;
                        v.gen->f = *ActiveFun(ty);

                        push(v);

                        goto Return;
                CASE(TYPE)
                        READVALUE(s);
                        push(TYPE((Type *)s));
                        break;
                CASE(ASSIGN_TYPE)
                        READVALUE(s);
                        if (top()->type == VALUE_OBJECT) {
                        }
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
                        pop();
                        push(v);
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
                        if (DEBUGGING && !I_AM_TDB) {
                                tdb_go(ty);
                        } else if (DEBUGGING) {
                                DebugBreakpoint *breakpoint = tdb_get_break(ty, IP);
                                *IP = breakpoint->op;
                                goto NextInstruction;
                        } else {
                                UNREACHABLE("hopefully");
                        }
                        break;
                CASE(GET_NEXT)
                        IterGetNext(ty);
                        break;
                CASE(LOOP_ITER)
                        xvP(SP_STACK, STACK.count);
                        push(SENTINEL);
                        RC = 0;
                        IterGetNext(ty);
                        break;
                CASE(ARRAY_COMPR)
                        n = STACK.count - *vvX(SP_STACK);
                        v = top()[-(n + 2)];
                        for (int i = 0; i < n; ++i)
                                vAp(v.array, top()[-i]);
                        STACK.count -= n;
                        break;
                CASE(DICT_COMPR)
                        READVALUE(n);
                        v = top()[-(2*n + 2)];
                        for (i = 0; i < n; ++i) {
                                value = top()[-2*i];
                                key = top()[-(2*i + 1)];
                                dict_put_value(ty, v.dict, key, value);
                        }
                        STACK.count -= 2 * n;
                        break;
                CASE(LOOP_CHECK)
                        READJUMP(jump);
                        READVALUE(z);
                        LoopCheck(ty, z, jump);
                        break;
                CASE(SPREAD_CHECK)
                        READJUMP(jump);
                        READVALUE(b);
                        if (!LoopCheck(ty, 1, jump)) {
                                vvX(SP_STACK);
                        }
                        SpreadShuffle(ty, b);
                        break;
                CASE(PUSH_INDEX)
                        READVALUE(n);
                        push(INDEX(0, 0, n));
                        break;
                CASE(READ_INDEX)
                        k = top()[-3].z - 1;
                        STACK.count += RC;
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
                CASE(CLEAR_RC)
                        RC = 0;
                        break;
                CASE(GET_EXTRA)
                        STACK.count += RC;
                        RC = 0;
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
                CASE(MULTI_ASSIGN)
                        print_stack(ty, 5);
                        READVALUE(n);
                        for (i = 0, vp = top(); pop().type != VALUE_SENTINEL; ++i) {
                                ;
                        }
                        for (int j = TARGETS.count - n; n > 0; --n, poptarget()) {
                                if (i > 0) {
                                        *TARGETS.items[j++].t = vp[-(--i)];
                                } else {
                                        *TARGETS.items[j++].t = NIL;
                                }
                        }
                        push(top()[2]);
                        break;
                CASE(MAYBE_MULTI)
                        READVALUE(n);
                        for (i = 0, vp = top(); pop().type != VALUE_SENTINEL; ++i) {
                                ;
                        }
                        for (int j = TARGETS.count - n; n > 0; --n, poptarget()) {
                                if (i > 0) {
                                        if (TARGETS.items[j++].t->type == VALUE_NIL)
                                                *TARGETS.items[j - 1].t = vp[-(--i)];
                                } else {
                                        *TARGETS.items[j++].t = NIL;
                                }
                        }
                        push(top()[2]);
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
                                value = v;
                                goto BadTupleMember;
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

                        value = v;

                        goto BadTupleMember;
                CASE(CONCAT_STRINGS)
                        READVALUE(n);
                        k = 0;
                        for (i = vN(STACK) - n; i < vN(STACK); ++i) {
                                k += sN(v__(STACK, i));
                        }
                        str = value_string_alloc(ty, k);
                        v = STRING(str, k);
                        k = 0;
                        for (i = vN(STACK) - n; i < vN(STACK); ++i) {
                                if (sN(v__(STACK, i)) > 0) {
                                        memcpy(str + k, ss(v__(STACK, i)), sN(v__(STACK, i)));
                                        k += sN(v__(STACK, i));
                                }
                        }
                        STACK.count -= n;
                        vPx(STACK, v);
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
                                goto MemberAccess;
                        } else {
                                *top() = NIL;
                                continue;
                        }
                CASE(GET_MEMBER)
                        z = GetDynamicMemberId(ty, true);
                        if (z >= 0) {
                                goto MemberAccess;
                        } else {
                                z = -(z + 1);
                                value = pop();
                                goto BadMemberAccess;
                        }
                CASE(TARGET_DYN_MEMBER)
                        z = GetDynamicMemberId(ty, true);
                        goto TargetMember;
                CASE(SELF_MEMBER_ACCESS)
                        READVALUE(z);

                        value = GetSelf(ty);

                        if (UNLIKELY(IsNone((v = LoadFieldFast(ty, &value, z))))) {
                                v = GetMember(ty, value, z, false, false);
                        }

                        switch (v.type) {
                        case VALUE_BREAK:
                                continue;

                        default:
                                push(v);
                                continue;
                        }
                        break;
                CASE(SELF_STATIC_ACCESS)
                        READVALUE(z);

                        v = GetSelf(ty);
                        v = GetMember(ty, CLASS(ClassOf(&v)), z, false, false);

                        switch (v.type) {
                        case VALUE_BREAK:
                                continue;

                        default:
                                push(v);
                                continue;
                        }
                        break;
                CASE(STATIC_MEMBER_ACCESS)
                        READVALUE(i);
                        READVALUE(z);

                        v = GetMember(ty, CLASS(i), z, false, false);

                        switch (v.type) {
                        case VALUE_BREAK:
                                continue;

                        default:
                                push(v);
                                continue;
                        }
                        break;
                CASE(TRY_MEMBER_ACCESS)
                        READVALUE(z);

                        value = pop();
                        v = GetMember(ty, value, z, true, false);

                        switch (v.type) {
                        case VALUE_BREAK:
                                continue;

                        case VALUE_NONE:
                                push(NIL);
                                continue;

                        default:
                                push(v);
                                continue;
                        }
                        break;
                CASE(MEMBER_ACCESS)
                        READVALUE(z);
MemberAccess:
                        value = pop();

                        if (UNLIKELY(IsNone((v = LoadFieldFast(ty, &value, z))))) {
                                v = GetMember(ty, value, z, true, false);
                        }

                        switch (v.type) {
                        case VALUE_BREAK:
                                continue;

                        default:
                                push(v);
                                continue;

                        case VALUE_NONE:
                                break;
                        }
BadMemberAccess:
BadTupleMember:
                        BadFieldAccess(ty, &value, z);
                        UNREACHABLE();
                CASE(TRY_MEMBER)
                        READJUMP(jump);
                        READVALUE(z);

                        value = peek();
                        v = GetMember(ty, value, z, true, false);

                        switch (v.type) {
                        case VALUE_BREAK:
                                continue;

                        case VALUE_NONE:
                                DOJUMP(jump);
                                continue;

                        default:
                                push(v);
                                continue;
                        }
                        break;
                CASE(SLICE)
                        CallMethod(ty, NAMES.slice, 3, 0, false);
                        break;
                CASE(SUBSCRIPT)
                        subscript = top()[0];
                        container = top()[-1];
                        switch (container.type) {
                        case VALUE_TYPE:
                                break;
                        case VALUE_ARRAY:
                                v = ArraySubscript(ty, container, subscript, true);
                                pop();
                                pop();
                                push(v);
                                break;
                        case VALUE_TUPLE:
                                if (LIKELY(subscript.type == VALUE_INTEGER)) {
                                        if (subscript.z < 0) {
                                                subscript.z += container.count;
                                        }

                                        if (subscript.z < 0 || subscript.z >= container.count) {
                                                v = tagged(ty, TAG_INDEX_ERR, container, subscript, NONE);
                                                pop();
                                                pop();
                                                push(v);
                                                RaiseException(ty);
                                                break;
                                        }

                                        pop();
                                        pop();

                                        push(container.items[subscript.z]);
                                } else {
                                        zP(
                                                "non-integer index used in subscript expression: %s",
                                                VSC(&subscript)
                                        );
                                }
                                break;
                        case VALUE_STRING:
                                v = string_char(ty, &container, 1, NULL);
                                pop();
                                pop();
                                push(v);
                                break;
                        case VALUE_BLOB:
                                v = blob_get(ty, &container, 1, NULL);
                                pop();
                                pop();
                                push(v);
                                break;
                        case VALUE_DICT:
                                vp = dict_get_value(ty, container.dict, &subscript);
                                pop();
                                pop();
                                push((vp == NULL) ? NIL : *vp);
                                break;
                        case VALUE_BOOLEAN:
                                pop();
                                pop();
                                push(container);
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
                                        call(ty, vp, &container, 1, NULL);
                                } else {
                                        goto BadContainer;
                                }
                                break;
                        case VALUE_CLASS:
                        case VALUE_TAG:
                                swap();
                                CallMethod(ty, NAMES.subscript, 1, 0, false);
                                break;
                        case VALUE_PTR:
                                if (UNLIKELY(subscript.type != VALUE_INTEGER)) {
                                        zP("non-integer used to subscript pointer: %s", VSC(&subscript));
                                }
                                v = GCPTR((container.extra == NULL) ? &ffi_type_uint8 : container.extra, container.gcptr);
                                push(v);
                                push(PTR(((char *)container.ptr) + ((ffi_type *)v.ptr)->size * subscript.z));
                                v = cffi_load(ty, 2, NULL);
                                pop();
                                pop();
                                pop();
                                pop();
                                push(v);
                                break;
                        case VALUE_NIL:
                                pop();
                                pop();
                                push(NIL);
                                break;
                        default:
BadContainer:
                                zP("invalid container in subscript expression: %s", VSC(&container));
                                abort();
                        }
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
                CASE(CHECK_MATCH)
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
                                push(BOOLEAN(TypeCheck(ty, v.ptr, &value)));
                                break;

                        case VALUE_NIL:
                                v = pop();
                                *top() = BOOLEAN(top()->type == VALUE_NIL);
                                break;

                        default:
                                CallMethod(ty, NAMES.match, 1, 0, false);
                        }
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
                        if (v.tags == 0)
                                push(NIL);
                        else
                                push(TAG(tags_first(ty, v.tags)));
                        break;
                CASE(LEN)
                        v = pop();
                        push(INTEGER(v.array->count)); // TODO
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
                        DoMutAdd(ty);
                        break;
                CASE(MUT_MUL)
                        DoMutMul(ty);
                        break;
                CASE(MUT_DIV)
                        DoMutDiv(ty);
                        break;
                CASE(MUT_MOD)
                        DoMutMod(ty);
                        break;
                CASE(MUT_SUB)
                        DoMutSub(ty);
                        break;
                CASE(MUT_AND)
                        DoMutAnd(ty);
                        break;
                CASE(MUT_OR)
                        DoMutOr(ty);
                        break;
                CASE(MUT_XOR)
                        DoMutXor(ty);
                        break;
                CASE(MUT_SHL)
                        DoMutShl(ty);
                        break;
                CASE(MUT_SHR)
                        DoMutShr(ty);
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
                        int tag, super, n, c;
                        READVALUE(tag);
                        READVALUE(super);
                        READVALUE(n);
                        READVALUE(c);
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

                        InstallMethods(ty, &class->s_methods, s_m);
                        InstallMethods(ty, &class->s_getters, s_g);
                        InstallMethods(ty, &class->s_setters, s_s);
                        InstallMethods(ty, &class->methods, m);
                        InstallMethods(ty, &class->getters, g);
                        InstallMethods(ty, &class->setters, s);

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
                {
                        v = NONE;
                        v.type = VALUE_FUNCTION;

                        // n: bound_caps
                        READVALUE(n);

                        IP = ALIGNED_FOR(i64, IP);

                        v.info = (i32 *)IP;

                        int hs   = v.info[FUN_INFO_HEADER_SIZE];
                        int size = v.info[FUN_INFO_CODE_SIZE];
                        int nEnv = v.info[FUN_INFO_CAPTURES];

                        int ncaps = (n > 0) ? nEnv - n : nEnv;

                        LOG("Header size: %d", hs);
                        LOG("Code size: %d", size);
                        LOG("Bound: %d", v.info[4]);
                        LOG("ncaps: %d", ncaps);
                        LOG("Name: %s", VSC(&v));

                        if (from_eval(&v)) {
                                v.info = mAo(hs + size, GC_ANY);
                                memcpy(v.info, IP, hs + size);
                                NOGC(v.info);
                        }

                        IP += size + hs;

                        if (nEnv > 0) {
                                LOG("Allocating ENV for %d caps", nEnv);
                                v.env = mAo(nEnv * sizeof (Value *), GC_ENV);
                                memset(v.env, 0, nEnv * sizeof (Value *));
                        } else {
                                v.env = NULL;
                        }

                        GC_STOP();

                        for (int i = 0; i < ncaps; ++i) {
                                READVALUE(b);
                                READVALUE(j);
                                Value *p = poptarget();
                                if (b) {
                                        if (p->type == VALUE_REF) {
                                                /* This variable was already captured, just refer to the same object */
                                                v.env[j] = p->ptr;
                                        } else {
                                                // TODO: figure out if this is getting freed too early
                                                Value *new = mAo(sizeof (Value), GC_VALUE);
                                                *new = *p;
                                                *p = REF(new);
                                                v.env[j] = new;
                                        }
                                } else {
                                        v.env[j] = p;
                                }
                        }

                        push(v);

                        GC_RESUME();

                        if (from_eval(&v)) {
                                OKGC(v.info);
                        }

                        break;
                }
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
                        vp = class_lookup_method_i(ty, n, z);
                        *top() = BindMethod(ty, vp, top(), z);
                        break;
                CASE(BIND_GETTER)
                        READVALUE(n);
                        READVALUE(z);
                        vp = class_lookup_getter_i(ty, n, z);
                        *top() = BindMethod(ty, vp, top(), z);
                        break;
                CASE(BIND_SETTER)
                        READVALUE(n);
                        READVALUE(z);
                        vp = class_lookup_setter_i(ty, n, z);
                        *top() = BindMethod(ty, vp, top(), z);
                        break;
                CASE(BIND_STATIC)
                        READVALUE(n);
                        READVALUE(z);
                        vp = class_lookup_s_method_i(ty, n, z);
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

                        i = n;
                        n = ActiveFun(ty)->info[FUN_INFO_BOUND];

                        for (; i < n; ++i) {
                                *local(ty, i) = NIL;
                        }

                        STACK.count = vvL(FRAMES)->fp + n;
                        IP = code_of(ActiveFun(ty));

                        break;
                CASE(CALL)
                        v = pop();
                        READVALUE(n);
                        READVALUE(nkw);
                        DoCall(ty, &v, n, nkw, false);
                        nkw = 0;
                        break;
                CASE(CALL_GLOBAL)
                        READVALUE(i);
                        READVALUE(n);
                        READVALUE(nkw);
                        DoCall(ty, v_(Globals, i), n, nkw, false);
                        nkw = 0;
                        break;
                CASE(TRY_CALL_METHOD)
                        READVALUE(n);
                        READVALUE(i);
                        READVALUE(nkw);
                        CallMethod(ty, i, n, nkw, true);
                        break;
                CASE(CALL_METHOD)
                        READVALUE(n);
                        READVALUE(z);
                        READVALUE(nkw);
                        CallMethod(ty, z, n, nkw, false);
                        break;
                CASE(CALL_SELF_METHOD)
                        READVALUE(n);
                        READVALUE(z);
                        READVALUE(nkw);
                        push(GetSelf(ty));
                        CallMethod(ty, z, n, nkw, false);
                        break;
                CASE(CALL_SELF_STATIC)
                        READVALUE(n);
                        READVALUE(z);
                        READVALUE(nkw);
                        v = GetSelf(ty);
                        push(CLASS(ClassOf(&v)));
                        CallMethod(ty, z, n, nkw, false);
                        break;
                CASE(CALL_STATIC_METHOD)
                        READVALUE(i);
                        READVALUE(n);
                        READVALUE(z);
                        READVALUE(nkw);
                        push(CLASS(i));
                        CallMethod(ty, z, n, nkw, false);
                        break;
                CASE(SAVE_STACK_POS)
                        xvP(SP_STACK, STACK.count);
                        break;
                CASE(POP_STACK_POS)
                        STACK.count = *vvX(SP_STACK);
                        break;
                CASE(POP_STACK_POS_POP)
                        STACK.count = *vvX(SP_STACK) - 1;
                        break;
                CASE(POP_STACK_POS_POP2)
                        STACK.count = *vvX(SP_STACK) - 2;
                        break;
                CASE(RESTORE_STACK_POS)
                        STACK.count = *vvL(SP_STACK);
                        break;
                CASE(DROP_STACK_POS)
                        vvX(SP_STACK);
                        break;
                CASE(DEBUG)
                        fprintf(stderr, "%s\n", IP);
                        SKIPSTR();
                        break;
                CASE(RETURN_IF_NOT_NONE)
                        if (top()->type != VALUE_NONE) {
                                goto Return;
                        }
                        break;
                CASE(MULTI_RETURN)
                CASE(RETURN)
Return:
                        n = vvL(FRAMES)->fp;
                        if (IP[-1] == INSTR_MULTI_RETURN) {
                                READVALUE(RC);
                                STACK.count -= RC;
                                for (int i = 0; i <= RC; ++i) {
                                        STACK.items[n + i] = top()[i];
                                }
                        } else {
                                STACK.items[n] = peek();
                        }
                        STACK.count = n + 1;
                        LOG("POPPING FRAME");
                        vvX(FRAMES);
                CASE(RETURN_PRESERVE_CTX)
                        IP = *vvX(CALLS);
                        break;
                CASE(HALT)
                        EXEC_DEPTH -= 1;
                        IP = save;
                        LOG("vm_exec(): <== %d (HALT: IP=%p)", EXEC_DEPTH, (void *)IP);
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

#if defined(TY_PROFILER)
        ProfileReport(ty);
#endif

        if (
                (id == -1)
             || (Globals.items[id].type != VALUE_ARRAY)
        ) {
                return;
        }

        StringVector msgs = {0};
        Array      *hooks = v_(Globals, id)->array;
        char       *first = !TyHasError(ty) ? NULL : S2(TyError(ty));

        bool bReprintFirst = false;

        for (usize i = 0; i < vN(*hooks); ++i) {
                if (TY_CATCH_ERROR()) {
                        TY_CATCH();
                        xvP(msgs, S2(TyError(ty)));
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
                fprintf(stderr, "exit hook failed with error: %s\n", v__(msgs, i));
        }
}

bool
vm_init(Ty *ty, int ac, char **av)
{
        curl_global_init(CURL_GLOBAL_ALL);

        InitializeTY(ty);
        InitializeTy(ty);

        TY_IS_READY = false;

        MyTy = ty;
        MyId = 0;

        build_string_method_table();
        build_dict_method_table();
        build_array_method_table();
        build_blob_method_table();

        NAMES.a                = M_ID("a");
        NAMES.b                = M_ID("b");
        NAMES.call             = M_ID("__call__");
        NAMES._class_          = M_ID("__class__");
        NAMES.contains         = M_ID("contains?");
        NAMES.count            = M_ID("__count__");
        NAMES._def_            = M_ID("__def__");
        NAMES._drop_           = M_ID("__drop__");
        NAMES._enter_          = M_ID("__enter__");
        NAMES.fmt              = M_ID("__fmt__");
        NAMES._free_           = M_ID("__free__");
        NAMES.groups           = M_ID("groups");
        NAMES._hash_           = M_ID("__hash__");
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
        NAMES.ptr              = M_ID("__ptr__");
        NAMES.slice            = M_ID("[;;]");
        NAMES.str              = M_ID("str");
        NAMES._str_            = M_ID("__str__");
        NAMES.subscript        = M_ID("[]");
        NAMES.unapply          = M_ID("unapply");
        NAMES._what            = M_ID(sfmt("_what$%d", CLASS_RUNTIME_ERROR));

        NAMES._fields_         = M_ID("__fields__");
        NAMES._methods_        = M_ID("__methods__");
        NAMES._getters_        = M_ID("__getters__");
        NAMES._setters_        = M_ID("__setters__");
        NAMES._static_fields_  = M_ID("__static_fields__");
        NAMES._static_methods_ = M_ID("__static_methods__");
        NAMES._static_getters_ = M_ID("__static_getters__");
        NAMES._super_          = M_ID("__super__");

        GC_STOP();

        InitThreadGroup(ty, MyGroup = &MainGroup);

        NewArenaNoGC(ty, 1ULL << 25);

        compiler_init(ty);

        add_builtins(ty, ac, av);

        AddThread(ty, TyThreadSelf());

        if (TY_CATCH_ERROR()) {
                TY_CATCH();
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

#ifdef TY_PROFILER
        Samples = dict_new(ty);
        NOGC(Samples);
        FuncSamples = dict_new(ty);
        NOGC(FuncSamples);
        TySpinLockInit(&ProfileMutex);
#endif

        TY_IS_INITIALIZED = true;
        TY_IS_READY = true;

        return true;
}

static char *
truncate_to_fit(char *wide, int cols)
{
        int i = term_fit_cols(wide, -1, cols);
        char *trunc;

        if (wide[i] == '\0') {
                trunc = wide;
        } else {
                trunc = xfmt("%.*s%s%s%s", i, wide, TERM(1;90), "…", TERM(0));
                free(wide);
        }

        return trunc;
}

char *
FormatTrace(Ty *ty, ThrowCtx const *ctx, byte_vector *out)
{
        byte_vector message = {0};

        if (out == NULL) {
                out = &message;
        } else {
               // v0(*out);
        }

        int _rows;
        int cols;

        if (!get_terminal_size(-1, &_rows, &cols)) {
                cols = 80;
        }

        if (ctx == NULL) {
                ctx = CurrentThrowCtx(ty);
        }

        SCRATCH_SAVE();

        for (int i = 0; i < vN(*ctx); ++i) {
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

                        if (expr->origin != NULL) {
                                WriteExpressionOrigin(ty, out, expr->origin);
                        }

                        Expr const *func;
                        if (
                                DetailedExceptions
                             && ((func = compiler_find_func(ty, ip - 1)) != NULL)
                             && (func->scope != NULL)
                             && (vN(func->scope->owned) > 0)
                        ) {
                                ValueVector localv = v__(ctx->locals, i);
                                Scope *scope = func->scope;

                                int max_width = 0;
                                for (int i = 0; i < vN(scope->owned); ++i) {
                                        int width = term_width(v__(scope->owned, i)->identifier, -1);
                                        if (width > max_width) {
                                                max_width = width;
                                        }
                                }

                                for (int i = 0; i < vN(scope->owned) && i < vN(localv); ++i) {
                                        Value  val = v__(localv, i);
                                        char *show = NULL;
                                        bool  good = true;
                                        for (int fuel = 3; (show == NULL) && (fuel > 0); --fuel) {
                                                if (!VM_TRY()) {
                                                        val = vm_catch(ty);
                                                        good = false;
                                                } else {
                                                        show = truncate_to_fit(
                                                                VSC(&val),
                                                                max(1, cols - max_width - 16)
                                                        );
                                                        vm_finally(ty);
                                                }
                                        }
                                        if (good) {
                                                dump(
                                                        out,
                                                        "    %s%*s%s = %s\n",
                                                        TERM(1;93),
                                                        max_width + 2,
                                                        v__(scope->owned, i)->identifier,
                                                        TERM(22;39),
                                                        show
                                                );
                                        } else {
                                                dump(
                                                        out,
                                                        "    %s%*s%s = [failed to read: %s]\n",
                                                        TERM(1;91),
                                                        max_width + 2,
                                                        v__(scope->owned, i)->identifier,
                                                        TERM(22;39),
                                                        (show != NULL) ? show : "too many errors"
                                                );
                                        }
                                        if (show != NULL) {
                                                free(show);
                                        }
                                }

                                dump(out, "%s", TERM(38:2:74:74:74));
                                for (int i = 0; i < cols; ++i) {
                                        dump(out, "─");
                                }
                                dump(out, "%s\n", TERM(0));
                        }

                        WriteExpressionSourceContext(ty, out, expr);
                } else {
                        WriteExpressionTrace(ty, out, expr, -1, i == 0);
                        if (expr->origin != NULL) {
                                WriteExpressionOrigin(ty, out, expr->origin);
                        }
                }
        }

        SCRATCH_RESTORE();

        return vv(*out);
}

char const *
TyError(Ty *ty)
{
        if (vN(ty->err) > 0) {
                return vv(ty->err);
        }

        if (vC(ty->throw_stack) == 0) {
                return "(no error)";
        }

        isize i = (isize)vN(ty->throw_stack) - 1;
        ThrowCtx *ctx = v__(ty->throw_stack, (i != -1) ? i : 0);
        Value exc = ctx->exc;

        dump(&ty->err, "%sUncaught exception%s: %s\n", TERM(91;1), TERM(0), VSC(&exc));
        FormatTrace(ty, ctx, &ty->err);

        return vv(ty->err);
}

static void
xDcringe(Ty *ty)
{
        dump(&ErrorBuffer, "Stack trace:\n");

        for (int i = 0; IP != NULL; ++i) {
                if (vN(FRAMES) > 0 && is_hidden_fun(ActiveFun(ty))) {
                        goto Next;
                }

                Expr const *expr = compiler_find_expr(ty, IP - 1);

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
                IP = (char *)vvX(FRAMES)->ip;
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
        co_state st = ty->st;
        char const *ip = IP;
        char const *up;

        for (;;) {
                if (
                        (vN(st.frames) > 0)
                     && is_hidden_fun(FrameFun(ty, vvL(st.frames)))
                ) {
                        goto Next;
                }

                i32 fp;
                i32 nvar;
                if (vN(st.frames) > 0) {
                        Frame *frame = vvL(st.frames);
                        fp = frame->fp;
                        nvar = FrameFun(ty, frame)->info[FUN_INFO_BOUND];
                } else {
                        fp = 0;
                        nvar = 0;
                }

                ValueVector locals = {0};
                xvPn(locals, vv(STACK) + fp, nvar);

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

                if (vN(st.frames) == 0) {
                        break;
                }
Next:
                ip = vvX(st.frames)->ip;
        }
}

void
CaptureContext(Ty *ty, ThrowCtx *ctx)
{
        co_state st = ty->st;
        char const *ip = IP;
        char const *up;

        for (;;) {
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
                ip = vvX(st.frames)->ip;
        }

        xvP(*ctx, NULL);
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
        v0(ErrorBuffer);

        va_list ap;

        va_copy(ap, _ap);
        dump(&ErrorBuffer, "%s%sRuntimeError%s%s: ", TERM(1), TERM(31), TERM(22), TERM(39));
        vdump(&ErrorBuffer, fmt, ap);
        dump(&ErrorBuffer, "%c", '\n');
        va_end(ap);

        ThrowCtx *ctx = CurrentThrowCtx(ty);

        FormatTrace(ty, ctx, &ErrorBuffer);

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

        PopThrowCtx(ty);

        //XXX("VM Error: %s", vv(ErrorBuffer));

        TY_THROW_ERROR();
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
vm_error(Ty *ty, char const *fmt, ...)
{
        va_list ap;

        va_start(ap, fmt);
        Value msg = STRING_VFORMAT(ty, fmt, ap);
        va_end(ap);

        //XXX("VM Error: %.*s", (int)sN(msg), ss(msg));

        Value error = RawObject(CLASS_RUNTIME_ERROR);
        PutMember(error, NAMES._what, msg);

        vm_throw(ty, &error);
}

void
tdb_backtrace(Ty *ty)
{
        FrameStack frames = FRAMES;
        char const *ip = IP;

        byte_vector buf = {0};
        Generator *gen = NULL;

        int nf = vN(frames);

        for (int i = 0; ip != NULL; ++i) {
                if (nf > 0 && is_hidden_fun(FrameFun(ty, v_(frames, nf - 1)))) {
                        goto Next;
                }

                Expr const *expr = compiler_find_expr(ty, ip - 1);

                WriteExpressionTrace(ty, &buf, expr, 0, i == 0);
                if (expr != NULL && expr->origin != NULL) {
                        WriteExpressionOrigin(ty, &buf, expr->origin);
                }

                if (nf == 0) {
                        if (gen != NULL) {
                                frames = gen->st.frames;
                                nf = vN(frames);
                                gen = NULL;
                        } else {
                                break;
                        }
                } else {
                        gen = (nf == 0) ? NULL
                            : (v_(frames, nf - 1)->fp == 0) ? NULL
                            : (v_(STACK, v_(frames, nf - 1)->fp - 1)->type != VALUE_GENERATOR) ? NULL
                            :  v_(STACK, v_(frames, nf - 1)->fp - 1)->gen;
                }

Next:
                ip = (nf == 0) ? NULL : v_(frames, --nf)->ip;
        }

        xvP(buf, '\n');
        xvP(buf, '\0');

        fputs(buf.items, stdout);
}

bool
vm_execute_file(Ty *ty, char const *path)
{
        char *source = slurp(ty, path);
        if (source == NULL) {
                dump(
                        &ErrorBuffer,
                        "%s%s%s: failed to read source file: %s%s%s",
                        TERM(91;1), "Error", TERM(0),
                        TERM(95), path, TERM(0)
                );
                return false;
        }

        bool success = vm_execute(ty, source, path);

        GCLOG("Allocs before: %zu", ty->allocs.count);
        //DoGC(ty);
        GCLOG("Allocs after: %zu", ty->allocs.count);

        /*
         * When we read the file, we copy into an allocated buffer with a 0 byte at
         * the beginning, so we need to subtract 1 here to get something appropriate
         * for free().
         */
        mF(source - 1);

        return success;
}

#if defined(TY_PROFILER)
inline static int
ilerp(int lo, int hi, float a, float x, float b)
{
        if (x < a || x > b)
                return -1;

        float p = (x - a) / (b - a);

        return lo + p * (hi - lo);
}

void
color_sequence(float p, char *out)
{
        int r, g, b;

        if ((r = ilerp(0, 100, 0.0, p, 0.1)) != -1) {
                g = ilerp(255, 225, 0.0, p, 0.1);
                b = 65;
        } else if ((r = ilerp(130, 180, 0.1, p, 0.3)) != -1) {
                g = ilerp(200, 120, 0.1, p, 0.3);
                b = 40;
        } else if ((r = ilerp(180, 235, 0.3, p, 0.65)) != -1) {
                r += 20;
                g = ilerp(120, 60, 0.3, p, 0.65);
                b = 60;
        } else {
                r = 255;
                g = ilerp(50, 20, 0.65, p, 1.0);
                b = 60;
        }

        sprintf(out, "\033[38;2;%d;%d;%dm", r, g, b);
}

static void
ProfileReport(Ty *ty)
{
        vec(ProfileEntry) profile = {0};
        vec(ProfileEntry) func_profile = {0};

        char color_buffer[64] = {0};
        double total_ticks = 0.0;

        for (int i = 0; i < Samples->size; ++i) {
                if (Samples->keys[i].type == 0)
                        continue;
                ProfileEntry entry = {
                        .ctx = Samples->keys[i].ptr,
                        .count = Samples->values[i].z
                };
                vec_nogc_push(profile, entry);
                total_ticks += entry.count;
        }

        for (int i = 0; i < FuncSamples->size; ++i) {
                if (FuncSamples->keys[i].type == 0)
                        continue;
                ProfileEntry entry = {
                        .ctx = FuncSamples->keys[i].ptr,
                        .count = FuncSamples->values[i].z
                };
                vec_nogc_push(func_profile, entry);
        }

        qsort(func_profile.items, func_profile.count, sizeof (ProfileEntry), CompareProfileEntriesByWeight);

        fprintf(ProfileOut, "%s======= profile by function =======%s\n\n", PTERM(95), PTERM(0));
        for (int i = 0; i < func_profile.count; ++i) {
                ProfileEntry *entry = &func_profile.items[i];

                if (entry->count / total_ticks < 0.01) {
                        break;
                }

                if (*PTERM(0)) {
                        color_sequence(entry->count / total_ticks, color_buffer);
                }

                if (entry->ctx == NULL) {
                        fprintf(
                                ProfileOut,
                                "   %s%5.1f%%  %-14lld  %s%s(top)%s\n",
                                color_buffer,
                                entry->count / total_ticks * 100.0,
                                (long long)entry->count,
                                PTERM(92),
                                PTERM(1),
                                PTERM(0)
                        );
                } else if (entry->ctx == GC_ENTRY) {
                        fprintf(
                                ProfileOut,
                                "   %s%5.1f%%  %-14lld  %s%s%s%s\n",
                                color_buffer,
                                entry->count / total_ticks * 100.0,
                                (long long)entry->count,
                                PTERM(93),
                                PTERM(1),
                                GC_ENTRY,
                                PTERM(0)
                        );
                } else {
                        Value f = FUNCTION();
                        f.info = entry->ctx;
                        char *f_string = VSC(&f);
                        fprintf(
                                ProfileOut,
                                "   %s%5.1f%%  %-14lld  %s\n",
                                color_buffer,
                                entry->count / total_ticks * 100.0,
                                (long long)entry->count,
                                f_string
                        );
                        free(f_string);
                }
        }

        byte_vector prog_text = {0};

        for (int i = 0; i < func_profile.count; ++i) {
                ProfileEntry *entry = &func_profile.items[i];

                if (entry->count / total_ticks < 0.01) {
                        break;
                }

                if (entry->ctx == NULL || entry->ctx == GC_ENTRY) {
                        continue;
                }

                Value f = FUNCTION();
                f.info = entry->ctx;

                if (class_of(&f) == -1) {
                        dump(
                                &prog_text,
                                "%s==== %s%s%s%s by instruction %s====%s\n",
                                PTERM(92),
                                PTERM(34),
                                name_of(&f),
                                proto_of(&f),
                                PTERM(95),
                                PTERM(92),
                                PTERM(0)
                        );
                } else {
                        dump(
                                &prog_text,
                                "%s==== %s%s.%s%s%s by instruction %s====%s\n",
                                PTERM(92),
                                PTERM(34),
                                class_name(ty, class_of(&f)),
                                name_of(&f),
                                proto_of(&f),
                                PTERM(95),
                                PTERM(92),
                                PTERM(0)
                        );
                }

                void const *code = code_of(&f);
                usize       size = code_size_of(&f);

                DumpProgram(
                        ty,
                        &prog_text,
                        TyCompilerState(ty)->module->name,
                        code,
                        code + size,
                        false
                );

                dump(&prog_text, "\n");
        }

        fwrite(prog_text.items, 1, prog_text.count, ProfileOut);
        fputc('\n', ProfileOut);

#if 0
        qsort(profile.items, profile.count, sizeof (ProfileEntry), CompareProfileEntriesByLocation);

        int n = 1;
        for (int i = 1; i < profile.count; ++i) {
                if (compiler_find_expr(ty, profile.items[n - 1].ctx) == compiler_find_expr(ty, profile.items[i].ctx)) {
                        profile.items[n - 1].count += profile.items[i].count;
                } else {
                        profile.items[n++] = profile.items[i];
                }
        }

        if (profile.count > 0)
                profile.count = n;

        qsort(profile.items, profile.count, sizeof (ProfileEntry), CompareProfileEntriesByWeight);

        fprintf(ProfileOut, "\n\n%s===== profile by expression =====%s\n\n", PTERM(95), PTERM(0));
        u64 reported_ticks = 0;
        for (int i = 0; i < profile.count; ++i) {
                ProfileEntry *entry = profile.items + i;
                Expr const *expr = compiler_find_expr(ty, entry->ctx);

                if (*PTERM(0)) {
                        color_sequence(entry->count / total_ticks, color_buffer);
                }

                if (expr == NULL) {
                        fprintf(
                                ProfileOut,
                                "   %s%5.1f%%  %-13lld %s%16s %s%18s%6s%s  |  %s<no source available>%s %llu : %s\n",
                                color_buffer,
                                entry->count / total_ticks * 100.0,
                                entry->count,
                                PTERM(95),
                                "",
                                PTERM(91),
                                "(unknown)",
                                "",
                                PTERM(92),
                                PTERM(91),
                                PTERM(0),
                                (uptr)entry->ctx,
                                ""
                        );
                        fprintf(ProfileOut, "   &halt = %lu\n", (uptr)&halt);
                        fprintf(ProfileOut, "   &IP = %lu\n", (uptr)&IP);
                        fprintf(
                                ProfileOut,
                                "   %s%5.1f%%  %-13lld %s%16s %s%18s%6s%s  |  %s<no source available>%s %llu : %s\n",
                                color_buffer,
                                entry->count / total_ticks * 100.0,
                                entry->count,
                                PTERM(95),
                                "",
                                PTERM(91),
                                "(unknown)",
                                "",
                                PTERM(92),
                                PTERM(91),
                                PTERM(0),
                                (uptr)entry->ctx,
                                GetInstructionName(*(uint8_t const *)entry->ctx)
                        );
                        continue;
                }

                char const *etype = ExpressionTypeName(expr);

                if ((reported_ticks += entry->count) / total_ticks > 0.90 && i > 18) {
                        break;
                }

                char const *filename = strrchr(expr->mod->path, '/');
                Location start = expr->start;
                Location end = expr->end;

                if (filename == NULL) {
                        filename = expr->filename;
                } else {
                        filename += 1;
                }

                int name_len = strlen(filename);
                char name_buffer[32];

                if (name_len > 18) {
                        sprintf(name_buffer, "..%s", filename + (name_len - 18) + 2);
                } else {
                        strcpy(name_buffer, filename);
                }

                char code_buffer[1024];
                colorize_code(PTERM(93), PTERM(0), &start, &end, code_buffer, sizeof code_buffer);

                fprintf(
                        ProfileOut,
                        "   %s%5.1f%%  %-13lld %s%16s %s%18s%s:%s%-5d%s  |  %s\n",
                        color_buffer,
                        entry->count / total_ticks * 100.0,
                        entry->count,
                        PTERM(95),
                        etype,
                        PTERM(93),
                        name_buffer,
                        PTERM(0),
                        PTERM(94),
                        start.line + 1,
                        PTERM(92),
                        code_buffer
                );
        }

        fputc('\n', ProfileOut);

        byte_vector prog_text = {0};
        DumpProgram(ty, &prog_text, filename, NULL, NULL, true);
        fwrite(prog_text.items, 1, prog_text.count, ProfileOut);
        fputc('\n', ProfileOut);

#endif
        fputc('\n', ProfileOut);
}

static void
ProfilerSIGINT(int _)
{
        int64_t now = TyThreadWallTime();

        if (LastReportRequest > 0 && now - LastReportRequest < 3000000000LL) {
                exit(0);
        }

        LastReportRequest = now;
        WantReport = true;
}
#endif

#ifdef TY_CATCH_SIGSEGV
static void
cringe(int _)
{
        static u32 n;

        if (++n > 1) { return; }

        Ty *ty0 = ty;
        Ty *ty = (ty0->tdb == NULL || ty0->tdb->state == TDB_STATE_STOPPED) ? ty0 : ty0->tdb->ty;

#ifdef UNW_LOCAL_ONLY
        print_stack_trace();
#endif

        for (i32 i = 0; i < vN(MyGroup->TyList); ++i) {
                Ty *_ty = v__(MyGroup->TyList, i);
                if (_ty != ty) {
                        xDcringe(_ty);
                        fprintf(
                                stderr,
                                "============== Thread %d =====================\n"
                                "%s\n"
                                "==============================================\n",
                                i,
                                TyError(_ty)
                        );
                }
        }
        zP(
                "xdDDDDDD[%"PRIu64"]: TDB state: %s  Am I TDB? %d  Am I on the TDB thread? %d",
                MyId,
                TDB_STATE_NAME,
                (int)I_AM_TDB,
                TDB && TyThreadEqual(TyThreadSelf(), TDB->thread.thread->t)
        );
}
#endif

bool
vm_load_program(Ty *ty, char const *source, char const *file)
{
        TY_IS_READY = false;

        Module * volatile mod = NULL;

        if (TY_CATCH_ERROR()) {
                TY_CATCH();
                return false;
        }

        GC_STOP();

        mod = compiler_compile_source(ty, source, file);
        if (mod == NULL) {
                TY_CATCH_END();
                GC_RESUME();
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

        ty->code = mod->code;

        return true;
}

bool
vm_execute(Ty *ty, char const *source, char const *file)
{
        TY_IS_READY = false;

        if (source != NULL && !vm_load_program(ty, source, file)) {
                return false;
        }

        if (CompileOnly) {
                return true;
        }

        if (TY_CATCH_ERROR()) {
                char *trace = FormatTrace(ty, NULL, NULL);
                Value   exc = TY_CATCH();
                dump(
                        &ErrorBuffer,
                        "%sRuntimeError%s: uncaught exception: %s\n\n%s",
                        TERM(91;1),
                        TERM(0),
                        VSC(&exc),
                        trace
                );
                free(trace);
                return false;
        }

#ifdef TY_PROFILER
        void (*handler)(int) = signal(SIGINT, ProfilerSIGINT);
#endif

#ifdef TY_CATCH_SIGSEGV
        signal(SIGSEGV, cringe);
#endif

        if (DEBUGGING && !I_AM_TDB) {
                ty->ip = ty->code;
                tdb_go(ty);
        }

        TY_IS_READY = true;
        vm_exec(ty, ty->code);

#ifdef TY_PROFILER
        ProfileReport(ty);
#endif

        if (PrintResult && vC(STACK) > 0) {
                vN(STACK) += 1;
                printf("%s\n", VSC(top()));
        }

#if defined(TY_GC_STATS)
        printf("%.2f MB\n", TotalBytesAllocated / 1.0e6);
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
        DoThrow(ty);
        vm_exec(ty, IP);

        UNREACHABLE();
}

noreturn void
vm_throw_ty(Ty *ty)
{
        vm_error(ty, "%s", TyError(ty));
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
                exec_fn(ty, f, NULL, argc, kwargs);
                goto Collect;

        case VALUE_METHOD:
                exec_fn(ty, f->method, f->this, argc, kwargs);
                goto Collect;

        case VALUE_BUILTIN_FUNCTION:
                v = f->builtin_function(ty, argc, kwargs);
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
                init = class_lookup_method_i(ty, f->class, NAMES.init);
                if (f->class < CLASS_PRIMITIVE) {
                        if (LIKELY(init != NULL)) {
                                exec_fn(ty, init, NULL, argc, NULL);
                                return pop();
                        } else {
                                zP("Couldn't find init method for built-in class. Was prelude loaded?");
                        }
                } else {
                        v = OBJECT(object_new(ty, f->class), f->class);
                        if (init != NULL) {
                                exec_fn(ty, init, &v, argc, NULL);
                                pop();
                        } else {
                                STACK.count -= argc;
                        }
                        return v;
                }
                UNREACHABLE();

        case VALUE_DICT:
                vp = (argc >= 1) ? dict_get_value(ty, f->dict, top() - (argc - 1)) : NULL;
                STACK.count -= argc;
                return (vp == NULL) ? None : Some(*vp);

        case VALUE_ARRAY:
                v = (argc >= 1) ? ArraySubscript(ty, *f, top()[-(argc - 1)], false) : None;
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

        STACK.count += RC;
        RC = 0;

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
                exec_fn(ty, f, NULL, argc, NULL);
                return pop();

        case VALUE_METHOD:
                exec_fn(ty, f->method, f->this, argc, NULL);
                return pop();

        case VALUE_BUILTIN_FUNCTION:
                v = f->builtin_function(ty, argc, NULL);
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
                vp = class_lookup_method_i(ty, f->class, NAMES.init);
                if (f->class < CLASS_PRIMITIVE) {
                        if (LIKELY(vp != NULL)) {
                                exec_fn(ty, vp, NULL, argc, NULL);
                                return pop();
                        } else {
                                zP("Couldn't find init method for built-in class. Was prelude loaded?");
                        }
                } else {
                        v = OBJECT(object_new(ty, f->class), f->class);
                        if (vp != NULL) {
                                exec_fn(ty, vp, &v, argc, NULL);
                                pop();
                        } else {
                                STACK.count -= argc;
                        }
                        return v;
                }
                UNREACHABLE();

        case VALUE_DICT:
                vp = (argc >= 1) ? dict_get_value(ty, f->dict, top() - (argc - 1)) : NULL;
                STACK.count -= argc;
                return (vp == NULL) ? None : Some(*vp);

        case VALUE_ARRAY:
                v = (argc >= 1) ? ArraySubscript(ty, *f, top()[-(argc - 1)], false) : None;
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
                exec_fn(ty, f, NULL, argc, NULL);
                return pop();

        case VALUE_METHOD:
                exec_fn(ty, f->method, f->this, argc, NULL);
                return pop();

        case VALUE_BUILTIN_FUNCTION:
                r = f->builtin_function(ty, argc, NULL);
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

        switch (op) {
        case OP_CMP: DoCmp(ty); return pop();
        case OP_EQL: DoEq(ty);  return pop();
        case OP_NEQ: DoNeq(ty); return pop();
        case OP_GEQ: DoGeq(ty); return pop();
        case OP_LEQ: DoLeq(ty); return pop();
        case OP_GT:  DoGt(ty);  return pop();
        case OP_LT:  DoLt(ty);  return pop();

        case OP_ADD: if (op_builtin_add(ty)) return pop(); break;
        case OP_SUB: if (op_builtin_sub(ty)) return pop(); break;
        case OP_MUL: if (op_builtin_mul(ty)) return pop(); break;
        case OP_DIV: if (op_builtin_div(ty)) return pop(); break;
        case OP_MOD: if (op_builtin_mod(ty)) return pop(); break;

        case OP_BIT_AND: if (op_builtin_and(ty)) return pop(); break;
        case OP_BIT_OR:  if (op_builtin_or(ty))  return pop(); break;
        case OP_BIT_XOR: if (op_builtin_xor(ty)) return pop(); break;
        case OP_BIT_SHL: if (op_builtin_shl(ty)) return pop(); break;
        case OP_BIT_SHR: if (op_builtin_shr(ty)) return pop(); break;
        }

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
        for (int i = 0; i < vN(STACK) + RC && i < vC(STACK); ++i) {
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
        LOG_REACHED(" => throw_stack reached %llu", TotalReached);

        GCLOG("Marking drop stack");
        RESET_TOTAL_REACHED();
        for (int i = 0; i < vN(DROP_STACK); ++i) {
                value_mark(ty, v_(DROP_STACK, i));
        }
        LOG_REACHED(" => drop_stack reached %llu", TotalReached);

        GCLOG("Marking %zu targets", vN(TARGETS));
        RESET_TOTAL_REACHED();
        for (int i = 0; i < vN(TARGETS); ++i) {
                Target *target = v_(TARGETS, i);
                uptr t = (uptr)target->t;
                if (((t & PMASK3) == 0) && (t > 0x0FFF)) {
                        value_mark(ty, (Value *)t);
                }
                if (target->gc != NULL) {
                        value_mark(ty, target->gc);
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
#undef  SKIPSTR
#define SKIPSTR() (ip += strlen(ip) + 1)
#define SKIPVALUE(x) (memcpy(&x, ip, sizeof x), (ip += sizeof x))

        uptr s;
        imax k;
        bool b = false;
        double x;
        int n, nkw = 0, i, j, tag;

        switch ((u8)*ip++) {
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
                SKIPVALUE(n);
                break;
        CASE(JUMP_IF)
                SKIPVALUE(n);
                break;
        CASE(JUMP_IF_NOT)
                SKIPVALUE(n);
                break;
        CASE(JUMP_IF_NONE)
                SKIPVALUE(n);
                break;
        CASE(JUMP_IF_NIL)
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
        CASE(SKIP_CHECK)
                SKIPVALUE(n);
                break;
        CASE(TARGET_GLOBAL)
        CASE(ASSIGN_GLOBAL)
                SKIPVALUE(n);
                break;
        CASE(TARGET_LOCAL)
        CASE(ASSIGN_LOCAL)
                SKIPVALUE(n);
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
        CASE(MAYBE_ASSIGN)
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
                while (n --> 0) {
                        SKIPVALUE(i);
                }
                break;
        CASE(GATHER_TUPLE)
                break;
        CASE(DICT)
        CASE(DEFAULT_DICT)
                break;
        CASE(SELF)
                break;
        CASE(NIL)
                break;
        CASE(TO_STRING)
                break;
        CASE(YIELD)
        CASE(YIELD_SOME)
        CASE(YIELD_NONE)
                break;
        CASE(MAKE_GENERATOR)
                break;
        CASE(TYPE)
        CASE(ASSIGN_TYPE)
                SKIPVALUE(s);
                break;
        CASE(VALUE)
                SKIPVALUE(s);
                break;
        CASE(EVAL)
                SKIPVALUE(s);
                break;
        CASE(RENDER_TEMPLATE)
                SKIPVALUE(s);
                break;
        CASE(UNAPPLY)
                break;
        CASE(TRAP)
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
                break;
        CASE(DICT_COMPR)
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
        CASE(CLEAR_RC)
                break;
        CASE(GET_EXTRA)
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
        CASE(MULTI_ASSIGN)
                SKIPVALUE(n);
                break;
        CASE(MAYBE_MULTI)
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
        CASE(RANGE)
        CASE(INCRANGE)
                break;
        CASE(TRY_MEMBER_ACCESS)
        CASE(MEMBER_ACCESS)
        CASE(SELF_MEMBER_ACCESS)
        CASE(SELF_STATIC_ACCESS)
                SKIPVALUE(n);
                break;
        CASE(TRY_GET_MEMBER)
        CASE(GET_MEMBER)
                break;
        CASE(SLICE)
        CASE(SUBSCRIPT)
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
        CASE(LT)
        CASE(GT)
        CASE(LEQ)
        CASE(GEQ)
        CASE(CMP)
        CASE(GET_TAG)
        CASE(LEN)
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
                int tag, super, t, n;
                SKIPVALUE(tag);
                SKIPVALUE(super);
                SKIPVALUE(n);
                SKIPVALUE(t);
                while (n --> 0) {
                        SKIPSTR();
                }
                while (t --> 0) {
                        SKIPSTR();
                }
                break;
        }
        CASE(DEFINE_CLASS)
        {
                i32 class;
                i32   m,   g,   s;
                i32 s_m, s_g, s_s;

                SKIPVALUE(class);

                SKIPVALUE(s_m);
                SKIPVALUE(s_g);
                SKIPVALUE(s_s);
                SKIPVALUE(m);
                SKIPVALUE(g);
                SKIPVALUE(s);

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
        {
                Value v;

                SKIPVALUE(n);

                ip = ALIGNED_FOR(i64, ip);

                v.info = (int *) ip;

                int hs = v.info[0];
                int size  = v.info[1];
                int nEnv = v.info[2];

                int ncaps = (n > 0) ? nEnv - n : nEnv;

                ip += hs + size;

                for (int i = 0; i < ncaps; ++i) {
                        SKIPVALUE(b);
                        SKIPVALUE(j);
                }

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
                SKIPVALUE(nkw);
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
                SKIPVALUE(nkw);
                for (int i = 0; i < nkw; ++i) {
                        SKIPSTR();
                }
                break;
        CASE(SAVE_STACK_POS)
                break;
        CASE(POP_STACK_POS)
        CASE(POP_STACK_POS_POP)
                break;
        CASE(MULTI_RETURN)
                SKIPVALUE(n);
                break;
        CASE(RETURN_IF_NOT_NONE)
        CASE(RETURN)
        CASE(RETURN_PRESERVE_CTX)
        CASE(HALT)
                break;
        }

        return (char *)ip;
}

void
tdb_start(Ty *ty)
{
        if (TDB != NULL) {
                return;
        }

        atomic_bool created = false;

        Thread *t = alloc0(sizeof *t);
        t->i = NextThreadId();
        t->v = PTR(&created);

        TDB = alloc0(sizeof *TDB);
        TDB->hook = NONE;
        TDB->thread = THREAD(t);
        TDB->host = ty;

        lGv(true);

        TyMutexInit(&TDB_MUTEX);
        TyCondVarInit(&TDB_CONDVAR);
        t->alive = true;

        TyMutexLock(&TDB_MUTEX);
        TDB_IS_NOW(STOPPED);

        int err = TyThreadCreate(&t->t, vm_run_tdb, TDB);
        if (err != 0) {
                zP("TyThreadCreate(): %s", strerror(err));
        }

        while (!created) {
                continue;
        }

        lTk();
}

void
tdb_eval_hook(Ty *ty)
{
}

static Value
LocalsDict(Ty *ty)
{
        if (vN(FRAMES) == 0) {
                return NIL;
        }

        Expr const *fexp = compiler_find_func(ty, IP);

        if (fexp == NULL) {
                return NIL;
        }

        Scope *scope = fexp->scope;
        Dict *locals = dict_new(ty);

        for (int i = 0; i < vN(scope->owned); ++i) {
                dict_put_member(
                        ty,
                        locals,
                        v_(scope->owned, i)[0]->identifier,
                        *local(ty, i)
                );
        }

        return DICT(locals);
}

Value
tdb_locals(Ty *ty)
{
        return LocalsDict(TDB->host);
}

void
tdb_list(Ty *ty)
{
        char const *start = (FRAMES.count != 0)
                          ? code_of(ActiveFun(ty))
                          : ty->code;

        byte_vector *context = &TDB->context_buffer;

        vN(*context) = 0;
        DumpProgram(ty, context, "<debugger>", start, NULL, true);

        xprint_stack(ty, 10);

        fwrite(v_(*context, 0), 1, vN(*context), stdout);
}

void
tdb_set_break(Ty *ty, char *ip)
{
        xvP(TDB->breaks, ((DebugBreakpoint) {
                .ip = ip,
                .op = *ip
        }));

        *ip = (char)INSTR_TRAP_TY;
}

DebugBreakpoint *
tdb_get_break(Ty *ty, char const *ip)
{
        for (int i = 0; i < vN(TDB->breaks); ++i) {
                if (v_(TDB->breaks, i)->ip == ip) {
                        return v_(TDB->breaks, i);
                }
        }

        return NULL;
}

bool
tdb_step_expr(Ty *ty)
{
        ExprLocation *eloc = compiler_find_expr_x(ty, TDB->host->ip, false);

        if (eloc == NULL) {
                return false;
        }

        //tdb_set_trap(&TDB->next, ip);

        return true;
}

bool
tdb_step_line(Ty *ty)
{
        char *ip = compiler_find_next_line(ty, IP);

        if (ip == NULL) {
                return false;
        }

        tdb_set_trap(&TDB->next, ip);

        return true;
}

static bool
tdb_step_over_x(Ty *ty, char *ip, i32 i)
{
        if (
                (ip == &halt)
             || (ip == iter_fix)
             || (ip == next_fix)
        ) {
                return true;
        }

        switch ((u8)*ip) {
        CASE(HALT)
                return true;

        CASE(RETURN)
                return (i < vN(CALLS))
                    && tdb_step_over_x(ty, vvL(CALLS)[-i], i + 1);

        CASE(ARRAY_REST)
        CASE(ENSURE_CONTAINS)
        CASE(ENSURE_DICT)
        CASE(ENSURE_EQUALS_VAR)
        CASE(ENSURE_LEN)
        CASE(ENSURE_LEN_TUPLE)
        CASE(ENSURE_SAME_KEYS)
        CASE(JEQ)
        CASE(JGE)
        CASE(JGT)
        CASE(JLE)
        CASE(JLT)
        CASE(JNE)
        CASE(JNI)
        CASE(JII)
        CASE(JUMP)
        CASE(JUMP_AND)
        CASE(JUMP_IF)
        CASE(JUMP_IF_NIL)
        CASE(JUMP_IF_NONE)
        CASE(JUMP_IF_NOT)
        CASE(JUMP_IF_SENTINEL)
        CASE(JUMP_IF_TYPE)
        CASE(JUMP_OR)
        CASE(JUMP_WTF)
        CASE(SKIP_CHECK)
        CASE(LOOP_CHECK)
        CASE(NONE_IF_NOT)
        CASE(RECORD_REST)
        CASE(TRY_ASSIGN_NON_NIL)
        CASE(TRY_INDEX)
        CASE(TRY_INDEX_TUPLE)
        CASE(TRY_REGEX)
        CASE(TRY_STEAL_TAG)
        CASE(TRY_TAG_POP)
        CASE(TRY_TUPLE_MEMBER)
        CASE(TRY_MEMBER)
        CASE(TRY_UNAPPLY)
        CASE(TUPLE_REST)
                tdb_set_trap(&TDB->alt, ip + 1 + load_int(ip + 1) + sizeof (int));
        }

        tdb_set_trap(&TDB->next, StepInstruction(ip));

        return true;
}

bool
tdb_step_over(Ty *ty)
{
        bool ok = tdb_step_over_x(ty, IP, 0);

        if (!ok) {
                puts("no..");
        }

        return ok;
}

bool
tdb_step_into(Ty *ty)
{
        Value *vp;
        Value v = NONE;
        char *ip = IP;
        int i;
        int c;

        ty = TDB->host;

        switch ((u8)*IP) {
        CASE(CALL_GLOBAL)
                READVALUE(i);
                v = v__(Globals, i);
                break;

        CASE(CALL)
                v = peek();
                break;

        CASE(TRY_CALL_METHOD)
                READVALUE(i);
                READVALUE(i);
                v = GetMember(ty, peek(), i, false, true);
                break;

        CASE(CALL_METHOD)
                READVALUE(i);
                READVALUE(i);
                v = GetMember(ty, peek(), i, true, true);
                break;

        CASE(CALL_SELF_METHOD)
                READVALUE(i);
                READVALUE(i);
                v = GetMember(ty, GetSelf(ty), i, false, true);
                break;

        CASE(CALL_SELF_STATIC)
                READVALUE(i);
                READVALUE(i);
                v = GetSelf(ty);
                v = CLASS(ClassOf(&v));
                v = GetMember(ty, v, i, false, true);
                break;

        CASE(CALL_STATIC_METHOD)
                READVALUE(c);
                READVALUE(i);
                READVALUE(i);
                v = CLASS(c);
                v = GetMember(ty, v, i, false, true);
                break;
        }

        IP = ip;
        ip = NULL;

        switch (v.type) {
        case VALUE_FUNCTION:
                ip = code_of(&v);
                break;

        case VALUE_METHOD:
                ip = code_of(v.method);
                break;

        case VALUE_CLASS:
                vp = class_lookup_method_i(ty, v.class, NAMES.init);
                ip = (vp != NULL) ? code_of(vp) : NULL;
                break;

        case VALUE_GENERATOR:
                ip = v.gen->ip;
                break;

        case VALUE_NONE:
                break;
        }

        return (ip != NULL) && (tdb_set_trap(&TDB->next, ip), true);
}

void
tdb_go(Ty *ty)
{
        TDB_IS_NOW(STARTING);

        TyMutexUnlock(&TDB_MUTEX);
        TyCondVarSignal(&TDB_CONDVAR);

        lGv(true);

        TyMutexLock(&TDB_MUTEX);
        while (!TDB_IS(STEPPING) && !TDB_IS(STOPPED)) {
                TyCondVarWait(&TDB_CONDVAR, &TDB_MUTEX);
        }

        lTk();
}

void
tdb_go2(Ty *ty)
{
        DebugBreakpoint *breakpoint = tdb_get_break(ty, IP);

        if (breakpoint   != NULL) *breakpoint->ip = breakpoint->op;
        if (TDB->next.ip != NULL) *TDB->next.ip   = TDB->next.op;
        if (TDB->alt.ip  != NULL) *TDB->alt.ip    = TDB->alt.op;

        tdb_eval_hook(ty);
        //tdb_list(ty);

        //tdb_step_over(ty);
        TDB_IS_NOW(STEPPING);

        return;

        xprint_stack(ty, 16);
        tdb_list(ty);

        int ch;
        for (;;) switch ((ch = getchar()), (ch == '\n' || getchar()), ch) {
        case EOF:
        case 'c':
                TDB_IS_NOW(ACTIVE);
                return;

        case 'e':
                tdb_eval_hook(ty);
                return;

        case '\n':
        case 'n':
                tdb_step_over(ty);
                TDB_IS_NOW(STEPPING);
                return;

        case 'f':
                return;

        case 's':
                tdb_step_into(ty) ||
                tdb_step_over(ty);
                TDB_IS_NOW(STEPPING);
                return;

        case 'B':
                tdb_backtrace(ty);
                break;

        case 'b':
                tdb_set_break(ty, IP);
                break;

        case 'l':
                tdb_list(ty);
                break;
        }
}

Value
CompleteCurrentFunction(Ty *ty)
{
        xvP(CALLS, &halt);
        vm_exec(ty, IP);
        return pop();
}

Value *
vm_global(Ty *ty, int i)
{
        return (vN(Globals) > i) ? v_(Globals, i) : NULL;
}

Value *
vm_local(Ty *ty, int i)
{
        return local(ty, i);
}

bool
TyReloadModule(Ty *ty, char const *module)
{
        lGv(true);
        TySpinLockLock(&MyGroup->GCLock);
        lTk();

        TySpinLockLock(&MyGroup->Lock);

        MyGroup->WantGC = true;

        static int *blockedThreads;
        static int *runningThreads;
        static usize capacity;

        if (MyGroup->ThreadList.count > capacity) {
                blockedThreads = realloc(blockedThreads, MyGroup->ThreadList.count * sizeof *blockedThreads);
                runningThreads = realloc(runningThreads, MyGroup->ThreadList.count * sizeof *runningThreads);
                if (blockedThreads == NULL || runningThreads == NULL)
                        panic("Out of memory!");
                capacity = MyGroup->ThreadList.count;
        }

        int nBlocked = 0;
        int nRunning = 0;

        for (int i = 0; i < MyGroup->ThreadList.count; ++i) {
                if (MyLock == MyGroup->ThreadLocks.items[i]) {
                        continue;
                }
                TySpinLockLock(MyGroup->ThreadLocks.items[i]);
                if (TryFlipTo(MyGroup->ThreadStates.items[i], true)) {
                        runningThreads[nRunning++] = i;
                } else {
                        blockedThreads[nBlocked++] = i;
                }
        }

        bool ready = ty->ty->ready;

        TyBarrierInit(&MyGroup->GCBarrierStart, nRunning + 1);
        TyBarrierInit(&MyGroup->GCBarrierMark, nRunning + 1);
        TyBarrierInit(&MyGroup->GCBarrierSweep, nRunning + 1);
        TyBarrierInit(&MyGroup->GCBarrierDone, nRunning + 1);
        // ======================================================================================
        GC_STOP();
        ty->ty->ready = false;

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

        ty->ty->ready = ready;
        GC_RESUME();
        // ======================================================================================
        TyBarrierWait(&MyGroup->GCBarrierStart);
        TyBarrierWait(&MyGroup->GCBarrierMark);
        MyGroup->WantGC = false;
        UnlockThreads(ty, runningThreads, nRunning);
        TyBarrierWait(&MyGroup->GCBarrierSweep);
        UnlockThreads(ty, blockedThreads, nBlocked);
        TySpinLockUnlock(&MyGroup->Lock);
        TySpinLockUnlock(&MyGroup->GCLock);
        TyBarrierWait(&MyGroup->GCBarrierDone);

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
       t->catch = IP;
       t->end   = IP;
       return t;
}

Value
vm_catch(Ty *ty)
{
        Value exc = pop();

        while (pop().type != VALUE_SENTINEL) {
                continue;
        }

        vvX(TRY_STACK);
        vvX(THROW_STACK);

        return exc;
}

noreturn void
vm_rethrow(Ty *ty)
{
        Value exc = pop();

        while (pop().type != VALUE_SENTINEL) {
                continue;
        }

        push(exc);

        DoThrow(ty);
        vm_exec(ty, IP);

        UNREACHABLE();
}

void
vm_finally(Ty *ty)
{
        vvX(TRY_STACK);
}

void
TyPostFork(Ty *ty)
{
        TySpinLockInit(&MyGroup->GCLock);
        TySpinLockInit(&MyGroup->Lock);
        TySpinLockInit(&MyGroup->DLock);
        TySpinLockInit(MyLock);
        TySpinLockLock(MyLock);
}

Ty *
GetMyTy(void)
{
        return MyTy;
}

/* vim: set sts=8 sw=8 expandtab: */
