#ifdef _WIN32
#include <winsock2.h>
#include <ws2tcpip.h>
#endif

#include "ty.h"

#include <time.h>
#include <string.h>
#include <ctype.h>
#include <stdlib.h>
#include <stdbool.h>
#include <setjmp.h>
#include <stdarg.h>
#include <errno.h>
#include <stdnoreturn.h>
#include <locale.h>

#include <curl/curl.h>
#include <pcre2.h>

#include <fcntl.h>
#include <signal.h>

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
#include <sys/types.h>
#include <sys/ioctl.h>
#include <sys/socket.h>
#include <sys/un.h>
#include <netdb.h>
#include <sys/stat.h>
#include <sys/wait.h>
#include <netdb.h>
#include <netinet/ip.h>
#include <net/if.h>
#include <poll.h>
#include <termios.h>
#include <dirent.h>
#include <pthread.h>
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
#include "util.h"
#include "value.h"
#include "vm.h"

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

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
                (uintptr_t)(IP - 1) & 0xFFFFFFFF,        \
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
static char next_fix[] = { INSTR_NONE_IF_NIL, INSTR_RETURN_PRESERVE_CTX };
static char iter_fix[] = { INSTR_SENTINEL, INSTR_GET_NEXT, INSTR_RETURN_PRESERVE_CTX };

InternedNames NAMES;

static ValueVector Globals;
/* ========================================================================== */

struct sigfn {
        int sig;
        Value f;
};

#define FRAME(n, fn, from) ((Frame){ .fp = (n), .f = (fn), .ip = (from) })

static SigfnStack sigfns;

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


#define top()   ((top)(ty))
#define topN(i) ((topN)(ty, i))
#define pop()   ((pop)(ty))
#define peek()  ((peek)(ty))
#define push(x) ((push)(ty, (x)))
#define swap()  ((swap)(ty))

#define poptarget()      ((poptarget)(ty))
#define peektarget()     ((peektarget)(ty))
#define pushtarget(t, g) ((pushtarget)(ty, (t), (g)))

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

        //printf("Instruction(%lu) = %s\n", (uintptr_t)aIp, InstructionNames[(uint8_t)((char *)a->ctx)[0]]);
        Expr const *aExpr = compiler_find_expr(ty, a->ctx);

        //printf("Instruction(%lu) = %s\n", (uintptr_t)bIp, InstructionNames[(uint8_t)((char *)b->ctx)[0]]);
        Expr const *bExpr = compiler_find_expr(ty, b->ctx);

        if (aExpr == bExpr) return 0;
        if (aExpr == NULL) return -1;
        if (bExpr == NULL) return  1;

        uintptr_t aPtr = (uintptr_t)aExpr;
        uintptr_t bPtr = (uintptr_t)bExpr;

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

static char const *filename;

bool PrintResult = false;
FILE *DisassemblyOut = NULL;

#ifdef _WIN32
typedef volatile long TyThreadState;
#else
typedef atomic_bool TyThreadState;
#endif

typedef struct thread_group {
        TySpinLock Lock;
        TySpinLock GCLock;
        vec(TyThread) ThreadList;
        vec(Ty *) TyList;
        vec(TySpinLock *) ThreadLocks;
        vec(TyThreadState *) ThreadStates;
        atomic_bool WantGC;
        TyBarrier GCBarrierStart;
        TyBarrier GCBarrierMark;
        TyBarrier GCBarrierSweep;
        TyBarrier GCBarrierDone;
        TySpinLock DLock;
        AllocList DeadAllocs;
        isize DeadUsed;
} ThreadGroup;

typedef struct {
        atomic_bool *created;
        Value *ctx;
        Value *name;
        Thread *t;
        ThreadGroup *group;
        Ty *ty;
} NewThreadCtx;

static ThreadGroup MainGroup;

#ifndef _WIN32
static pthread_rwlock_t SigLock = PTHREAD_RWLOCK_INITIALIZER;
#endif

static _Thread_local Ty *co_ty;

static _Thread_local Ty *MyTy;
_Thread_local TySpinLock *MyLock;
static _Thread_local TyThreadState *MyState;
static _Thread_local bool GCInProgress;
static _Thread_local bool HaveLock = true;
static _Thread_local u64 MyId;

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

        srandom(TyThreadCPUTime() & 0xFFFFFFFF);

        xD.ty = ty;
}

int
AbortVM(void)
{
        vm_panic(ty, "oops!");
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
        if (GCInProgress)
                return;

        GCLOG("Waiting for GC on thread %llu", TID);

        lGv(false);

#ifdef TY_PROFILER
        u64 start = TyThreadTime();
#endif

        while (!*MyState) {
                if (!MyGroup->WantGC && TryFlipTo(MyState, true)) {
                        lTk();
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
        GCSweepOwn(ty);

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

        TySpinLockLock(&MyGroup->Lock);

        dont_printf(
                "[%.4f] [%s:%d] DoGC(): TDB_IS_%s\n",
                TyThreadCPUTime() / 1.0e9,
                I_AM_TDB ? "TDB" : "Ty",
                (int)(TDB && TyThreadEqual(TyThreadSelf(), TDB->thread.thread->t)),
                TDB_STATE_NAME
        );

        GCLOG("Doing GC: MyGroup = %p, (%zu threads)", MyGroup, MyGroup->ThreadList.count);

        GCLOG("Took threads lock on thread %llu to do GC", TID);

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
                        GCLOG("Thread %llu is running", (long long unsigned)MyGroup->ThreadList.items[i]);
                        runningThreads[nRunning++] = i;
                } else {
                        GCLOG("Thread %llu is blocked", (long long unsigned)MyGroup->ThreadList.items[i]);
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
                GCLOG("Marking thread %llu storage from thread %llu", (long long unsigned)MyGroup->ThreadList.items[blockedThreads[i]], TID);
                MarkStorage(v__(MyGroup->TyList, blockedThreads[i]));
        }

        GCLOG("Marking own storage on thread %llu", TID);
        MarkStorage(ty);

        if (MyGroup == &MainGroup) {
                for (int i = 0; i < vN(Globals); ++i) {
                        value_mark(ty, v_(Globals, i));
                }

                GCRootSet *immortal = GCImmortalSet(ty);

                for (int i = 0; i < vN(*immortal); ++i) {
                        value_mark(ty, v_(*immortal, i));
                }
        }

        TyBarrierWait(&MyGroup->GCBarrierMark);

        GCLOG("Storing false in WantGC on thread %llu", TID);
        MyGroup->WantGC = false;

        for (int i = 0; i < nBlocked; ++i) {
                GCLOG("Sweeping thread %llu storage from thread %llu", (long long unsigned)MyGroup->ThreadList.items[blockedThreads[i]], TID);
                GCSweepOwn(v__(MyGroup->TyList, blockedThreads[i]));
        }

        GCLOG("Sweeping own storage on thread %llu", TID);
        GCSweepOwn(ty);

        GCLOG("Sweeping objects from dead threads on thread %llu", TID);
        TySpinLockLock(&MyGroup->DLock);
        GCSweep(ty, &MyGroup->DeadAllocs, &MyGroup->DeadUsed);
        TySpinLockUnlock(&MyGroup->DLock);

        TyBarrierWait(&MyGroup->GCBarrierSweep);

        UnlockThreads(ty, blockedThreads, nBlocked);

        GCLOG("Unlocking ThreadsLock and GCLock. Used = %zu, DeadUsed = %zu", MemoryUsed, MyGroup->DeadUsed);

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

#define BUILTIN(f)    { .type = VALUE_BUILTIN_FUNCTION, .builtin_function = (f), .tags = 0 }
#define FLOAT(x)      { .type = VALUE_REAL,             .real             = (x), .tags = 0 }
#define INT(k)        { .type = VALUE_INTEGER,          .integer          = (k), .tags = 0 }
#define BOOL_(b)      { .type = VALUE_BOOLEAN,          .boolean          = (b), .tags = 0 }
#define POINTER(p)    { .type = VALUE_PTR,              .ptr              = (p), .tags = 0 }
#include "builtins.h"
#undef INT
#undef FLOAT
#undef BUILTIN
#undef BOOL_
#undef POINTER

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
                }
                xvP(Globals, builtins[i].value);
                switch (ClassOf(v)) {
                case CLASS_INT:
                        sym->type = type_integer(ty, v->integer);
                        break;
                case CLASS_STRING:
                case CLASS_BOOL:
                case CLASS_FLOAT:
                        sym->type = class_get(ty, ClassOf(v))->object_type;
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
#define BUILTIN_VAR(m, t, c)                 \
        compiler_introduce_symbol(ty, m, t); \
        NAMES.c = vN(Globals);               \
        *xvP(Globals, NIL)
//---------------------------------------------------------------------------
        BUILTIN_VAR(NULL,  "__env",          env       ) = DICT(env);
        BUILTIN_VAR(NULL,  "__EXIT_HOOKS__", exit_hooks) = ARRAY(vA());
        BUILTIN_VAR("tdb", "hook",           tdb_hook  ) = NIL;
        BUILTIN_VAR(NULL,  "_readln",        _readln   ) = NIL;
        BUILTIN_VAR(NULL,  "pretty",         pretty    ) = NIL;
        BUILTIN_VAR(NULL,  "pp",             pp        ) = NIL;
        BUILTIN_VAR("ty",  "q",              q         ) = BOOLEAN(!CheckTypes);
        BUILTIN_VAR("ty",  "executable",     exe       ) = this_executable(ty);
//---------------------------------------------------------------------------
#undef BUILTIN_VAR
//===========================================================================

#ifdef _WIN32
        // TODO
#else
        compiler_introduce_symbol(ty, "os", "PAGE_SIZE");
        xvP(Globals, INTEGER(sysconf(_SC_PAGESIZE)));
#endif

#ifdef SIGRTMIN
        /* Add this here because SIGRTMIN doesn't expand to a constant */
        compiler_introduce_symbol(ty, "os", "SIGRTMIN");
        vvP(Globals, INTEGER(SIGRTMIN));
#endif


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
        printf("STACK: (%zu)\n", STACK.count);
        for (int i = 0; i < n && i < STACK.count; ++i) {
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

inline static void
print_stack(Ty *ty, int n)
{
        return;
#ifndef TY_NO_LOG
        LOG("STACK: (%zu)", STACK.count);
        for (int i = 0; i < n && i < STACK.count; ++i) {
                if (FRAMES.count > 0 && STACK.count - (i + 1) == vvL(FRAMES)->fp) {
                        LOG(" -->  %s", VSC(top() - i));
                } else {
                        LOG("      %s", VSC(top() - i));
                }
        }
#endif
}
#ifdef TY_NO_LOG
  #define print_stack(...)
#endif

inline static Value
(pop)(Ty *ty)
{
        Value v = *vvX(STACK);
        //LOG("POP: %s", VSC(&v));
        print_stack(ty, 15);
        return v;
}

inline static Value
(peek)(Ty *ty)
{
        return *topN(1);
}

inline static void
(push)(Ty *ty, Value v)
{
        //LOG("PUSH: %s", VSC(&v));
        xvP(STACK, v);
        print_stack(ty, 10);
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
        Target t = *vvX(TARGETS);
        if (t.gc != NULL) OKGC(t.gc);
        //LOG("Popping Target: %p", (void *)t.t);
        return t.t;
}

inline static Value *
(peektarget)(Ty *ty)
{
        return TARGETS.items[TARGETS.count - 1].t;
}

inline static void
(pushtarget)(Ty *ty, Value *v, void *gc)
{
        Target t = { .t = v, .gc = gc };
        if (gc != NULL) NOGC(gc);
        xvP(TARGETS, t);
}

inline static bool
SpecialTarget(Ty *ty)
{
        return (((uintptr_t)TARGETS.items[TARGETS.count - 1].t) & PMASK3) != 0;
}

inline static Value
BindMethod(Value *f, Value *v, int id)
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
GetNextGenerator(Generator *gen)
{
        usize n = v_(gen->st.frames, 0)->fp;

        if (
                (n == 0)
             || (v_(STACK, n - 1)->type != VALUE_GENERATOR)
             || (v_(STACK, n - 1)->gen == gen)
        ) {
                return NULL;
        }

        return v_(STACK, n - 1)->gen;
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
        if (vN(CO_THREADS) == 0) {
                GCLOG("GetFreeCoThread(): new");
                return co_create(1u << 22, do_co);
        } else {
                GCLOG("GetFreeCoThread(): recycled");
                return co_derive(*vvX(CO_THREADS), 1u << 22, do_co);
        }
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

#ifdef TY_RELEASE
TY_INSTR_INLINE
#else
__attribute__((optnone, noinline))
#endif
static void
call(Ty *ty, Value const *f, Value const *pSelf, int n, int nkw, bool exec)
{
        int   argc    = n;
        int   np      = f->info[FUN_INFO_PARAM_COUNT];
        int   bound   = f->info[FUN_INFO_BOUND];

        int   irest   = *(i16 const *)info_of(f, FUN_REST_IDX);
        int   ikwargs = *(i16 const *)info_of(f, FUN_KWARGS_IDX);
        Value kwargs  = (nkw > 0) ? pop() : NIL;

        int   class   = class_of(f);
        Value self    = (pSelf == NULL) ? NONE : *pSelf;

        char  *code   = code_of(f);
        int   fp      = STACK.count - n;

        gP(&kwargs);

        /*
         * Default missing arguments to NIL and make space for all of this function's local variables.
         */
        while (n < bound) {
                push(NIL);
                n += 1;
        }

        /*
         * If the function was declared with the form f(..., *extra) then we
         * create an array and add any extra arguments to it.
         */
        if (irest != -1) {
                gP(&self);

                int nExtra = max(argc - irest, 0);
                Array *extra = vAn(nExtra);

                gX();

                memcpy(v_(*extra, 0), v_(STACK, fp + irest), nExtra * sizeof (Value));
                extra->count = nExtra;

                STACK.items[fp + irest] = ARRAY(extra);

                for (int i = irest + 1; i < argc; ++i) {
                        STACK.items[fp + i] = NIL;
                }
        }

        if (ikwargs != -1) {
                // FIXME: don't allocate a dict when there are no kwargs
                STACK.items[fp + ikwargs] = (nkw > 0) ? kwargs : DICT(dict_new(ty));
        }

        /*
         * Throw away extra arguments.
         */
        if (n > bound) {
                STACK.count -= (n - bound);
        }

        /*
         * Fill in 'self' as an implicit additional parameter.
         */
        if (self.type != VALUE_NONE && class != -1) {
                LOG("setting self = %s", VSC(&self));
                STACK.items[fp + np] = self;
        }

        xvP(FRAMES, FRAME(fp, *f, IP));

        /* Fill in keyword args (overwriting positional args) */
        if (kwargs.type != VALUE_NIL) {
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

        LOG("Calling %s with %d args, bound = %d, self = %s, env size = %d", VSC(f), argc, bound, VSC(&self), f->info[2]);
        print_stack(ty, max(bound + 2, 5));

        gX();

        if (exec) {
#ifndef TY_RELEASE
                Generator *gen = GetCurrentGenerator(ty);
                xvP(CALLS, &halt);
                vm_exec(ty, code);
                if (UNLIKELY(GetCurrentGenerator(ty) != gen)) {
                        zP("sus use of coroutine yield");
                }
#else
                xvP(CALLS, &halt);
                vm_exec(ty, code);
#endif
        } else {
                xvP(CALLS, IP);
                IP = code;
        }
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
        call(ty, &gen->f, NULL, 0, 0, false);
        *vvL(CALLS) = whence;
        STACK.count = vvL(FRAMES)->fp;

        if (vN(gen->st.frames) == 0) {
                xvP(gen->st.frames, *vvL(FRAMES));
        } else {
                gen->st.frames.items[0] = *vvL(FRAMES);
        }

        int diff = (int)vN(STACK) - gen->fp;
        for (int i = 1; i < vN(gen->st.frames); ++i) {
                gen->st.frames.items[i].fp += diff;
        }

        gen->fp = STACK.count;

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
                co_switch(co);
        } else {
                cothread_t co = GetFreeCoThread(ty);
                gen->co = co_active();
                GCLOG("co_call() [%p]: switch to %s on [%p] (NEW)", co_active(), name_of(&gen->f), (void *)co);
                co_ty = ty;
                co_switch(co);

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
MyThreadId(Ty *ty)
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
        if (r != 0)
                zP("TyThreadCreate(): %s", strerror(r));

        while (!created)
                ;

        lTk();
}

static void
AddThread(Ty *ty, TyThread self)
{
        GCLOG("AddThread(): %llu: taking lock", TID);

        TySpinLockLock(&MyGroup->Lock);

        GCLOG("AddThread(): %llu: took lock", TID);

        GC_STOP();

        vvP(MyGroup->TyList, ty);
        vvP(MyGroup->ThreadList, self);

        MyLock = mrealloc(NULL, sizeof *MyLock);
        TySpinLockInit(MyLock);
        TySpinLockLock(MyLock);
        vvP(MyGroup->ThreadLocks, MyLock);

        MyState = mrealloc(NULL, sizeof *MyState);
        *MyState = false;
        vvP(MyGroup->ThreadStates, MyState);

        GC_RESUME();

        TySpinLockUnlock(&MyGroup->Lock);

        GCLOG("AddThread(): %llu: finished", TID);
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

        uvPv(MyGroup->DeadAllocs, ty->allocs);
        MyGroup->DeadUsed += MemoryUsed;

        ty->allocs.count = 0;

        TySpinLockUnlock(&MyGroup->DLock);

        lGv(true);

        TySpinLockLock(&MyGroup->Lock);

        GCLOG("Got threads lock on thread: %llu -- ready to clean up. Group size = %zu", TID, vN(MyGroup->ThreadList));

        for (int i = 0; i < MyGroup->ThreadList.count; ++i) {
                if (MyLock == MyGroup->ThreadLocks.items[i]) {
                        *v_(MyGroup->ThreadList,   i) = *vvX(MyGroup->ThreadList);
                        *v_(MyGroup->TyList,       i) = *vvX(MyGroup->TyList);
                        *v_(MyGroup->ThreadLocks,  i) = *vvX(MyGroup->ThreadLocks);
                        *v_(MyGroup->ThreadStates, i) = *vvX(MyGroup->ThreadStates);
                        break;
                }
        }

        usize group_remaining = MyGroup->ThreadList.count;

        TySpinLockUnlock(&MyGroup->Lock);

        for (int i = 0; i < TRY_STACK.capacity; ++i) {
                struct try *t = *v_(TRY_STACK, i);
                xvF(t->defer);
                free(t);
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
        free(ty->allocs.items);
        pcre2_match_data_free(ty->pcre2.match);
        pcre2_match_context_free(ty->pcre2.ctx);
        pcre2_jit_stack_free(ty->pcre2.stack);

        if (group_remaining == 0) {
                GCLOG("Cleaning up group %p", (void*)MyGroup);
                TySpinLockDestroy(&MyGroup->Lock);
                TySpinLockDestroy(&MyGroup->GCLock);
                TySpinLockDestroy(&MyGroup->DLock);
                vvF(MyGroup->TyList);
                vvF(MyGroup->ThreadList);
                vvF(MyGroup->ThreadLocks);
                vvF(MyGroup->ThreadStates);
                vvF(MyGroup->DeadAllocs);
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
        MyId = t->i;

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
                // TODO: do something useful here
                fprintf(stderr, "Thread %lld dying with error: %s\n", TID, TyError(ty));
                OKGC(t);
                t->v = NIL;
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
                             && (state.integer >= 0)
                             && (state.integer < TDB_MAX_STATE)
                        ) {
                                next = state.integer;
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

void
vm_del_sigfn(Ty *ty, int sig)
{
#ifndef _WIN32
        pthread_rwlock_wrlock(&SigLock);

        for (int i = 0; i < sigfns.count; ++i) {
                if (sigfns.items[i].sig == sig) {
                        struct sigfn t = *vvL(sigfns);
                        *vvL(sigfns) = sigfns.items[i];
                        sigfns.items[i] = t;
                        vvX(sigfns);
                        break;
                }
        }

        pthread_rwlock_unlock(&SigLock);
#endif
}

void
vm_set_sigfn(Ty *ty, int sig, Value const *f)
{
#ifndef _WIN32
        pthread_rwlock_wrlock(&SigLock);

        for (int i = 0; i < sigfns.count; ++i) {
                if (sigfns.items[i].sig == sig) {
                        sigfns.items[i].f = *f;
                        goto End;
                }
        }

        vvP(sigfns, ((struct sigfn){ .sig = sig, .f = *f }));

End:
        pthread_rwlock_unlock(&SigLock);
#endif
}

Value
vm_get_sigfn(Ty *ty, int sig)
{
        Value f = NIL;
#ifndef _WIN32
        pthread_rwlock_rdlock(&SigLock);

        for (int i = 0; i < sigfns.count; ++i) {
                if (sigfns.items[i].sig == sig) {
                        f = sigfns.items[i].f;
                        break;
                }
        }

        pthread_rwlock_unlock(&SigLock);
#endif
        return f;
}

#ifndef _WIN32
void
vm_do_signal(int sig, siginfo_t *info, void *ctx)
{
        Ty *ty = MyTy;
        Value f = NIL;

        pthread_rwlock_rdlock(&SigLock);

        for (int i = 0; i < sigfns.count; ++i) {
                if (sigfns.items[i].sig == sig) {
                        f = sigfns.items[i].f;
                        break;
                }
        }

        pthread_rwlock_unlock(&SigLock);

        if (f.type == VALUE_NIL) {
                return;
        }

        switch (sig) {
#ifdef SIGIO
        case SIGIO:
#ifdef __APPLE__
                push(INTEGER(info->si_value.sival_int));
#else
                push(INTEGER(info->si_fd));
#endif
#endif
                vm_call(ty, &f, 1);
                break;
        default:
                vm_call(ty, &f, 0);
        }
}
#endif

#ifndef TY_RELEASE
__attribute__((noinline))
#else
TY_INSTR_INLINE
#endif
static void
DoDrop(Ty *ty)
{
        Value group = *vvL(DROP_STACK);

        for (int i = 0; i < group.array->count; ++i) {
                Value v = group.array->items[i];
                if (v.type != VALUE_OBJECT)
                        continue;
                Value *f = class_lookup_method_i(ty, v.class, NAMES._drop_);
                if (f == NULL)
                        continue;
                vm_call_method(ty, &v, f, 0);
        }

        vvX(DROP_STACK);
}

TY_INSTR_INLINE static struct try *
GetCurrentTry(Ty *ty)
{
        return *vvL(TRY_STACK);

        for (int i = vN(TRY_STACK) - 1; i >= 0; --i) {
                struct try *t = *v_(TRY_STACK, i);
                if (!t->executing) {
                        return t;
                }
        }

        return NULL;
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

TY_INSTR_INLINE static void
DoThrow(Ty *ty)
{
        Value ex = peek();

        //XXX("Throw: %s", VSC(&ex));
        //xprint_stack(ty, 10);

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
                                zPx(
                                        "an exception was thrown while handling another exception: %s%s%s",
                                        TERM(31), VSC(&ex), TERM(39)
                                );
                        }
                }

                if (!co_abort(ty)) {
                        ThrowCtx *ctx = PopThrowCtx(ty);
                        zPxx(ctx, "uncaught exception: %s%s%s", TERM(31), VSC(&ex), TERM(39));
                }
        }
}

TY_INSTR_INLINE static void
RaiseException(Ty *ty)
{
        PushThrowCtx(ty);
        DoThrow(ty);
}

static void
YieldFix(Ty *ty)
{
        if (top()->type == VALUE_TAG && top()->tag == TAG_NONE) {
                *top() = NONE;
        } else if (
                !LIKELY(
                        top()->tags != 0 &&
                        tags_first(ty, top()->tags) == TAG_SOME
                )
        ) {
                zP("iterator returned invalid type. Expected None or Some(...) but got %s", VSC(top()));
        } else {
                top()->tags = tags_pop(ty, top()->tags);
                if (top()->tags == 0) {
                        top()->type &= ~VALUE_TAGGED;
                }
        }
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
                        if (r.integer < 0)
                                r.integer += container.array->count;
                        if (r.integer < 0 || r.integer >= container.array->count) {
                                if (strict) goto Error;
                                vAp(a, None);
                        } else if (strict) {
                                vAp(a, container.array->items[r.integer]);
                        } else {
                                vAp(a, Some(container.array->items[r.integer]));
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
                        call(ty, vp, &subscript, 0, 0, true);
                        subscript = pop();
                        gX();
                        gX();
                        goto Start;
                }

                a = vA();
                NOGC(a);

                for (int i = 0; ; ++i) {
                        push(INTEGER(i));
                        call(ty, vp, &subscript, 1, 0, true);
                        Value r = pop();
                        if (r.type == VALUE_NIL)
                                break;
                        if (UNLIKELY(r.type != VALUE_INTEGER))
                                zP("iterator yielded non-integer array index in subscript expression");
                        if (r.integer < 0)
                                r.integer += container.array->count;
                        if (r.integer < 0 || r.integer >= container.array->count) {
                                if (strict) goto Error;
                                vAp(a, None);
                        } else if (strict) {
                                vAp(a, container.array->items[r.integer]);
                        } else {
                                vAp(a, Some(container.array->items[r.integer]));
                        }
                }

                OKGC(a);
                gX();
                gX();

                return ARRAY(a);
        case VALUE_INTEGER:
                if (subscript.integer < 0) {
                        subscript.integer += container.array->count;
                }

                if (subscript.integer < 0 || subscript.integer >= container.array->count) {
                        if (strict) goto Error;
                        return None;
                } else if (strict) {
                        return container.array->items[subscript.integer];
                } else {
                        return Some(container.array->items[subscript.integer]);
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
        int_vector *ids,
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
search_int(int const *zs, int z)
{
        while (*zs != -1) {
                if (*zs++ == z) return true;
        }

        return false;
}

TY_INSTR_INLINE static void
DoTag(Ty *ty, int tag, int n, Value *kws)
{
        if (n == 1 && kws == NULL) {
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

Value
GetMember(Ty *ty, Value v, int member, bool try_missing, bool exec)
{
        int n;
        Value *this;
        Value *vp = NULL;
        BuiltinMethod *func;

        if (v.type & VALUE_TAGGED) for (int tags = v.tags; tags != 0; tags = tags_pop(ty, tags)) {
                vp = tags_lookup_method_i(ty, tags_first(ty, tags), member);
                if (vp != NULL)  {
                        Value *this = mAo(sizeof *this, GC_VALUE);

                        *this = v;
                        this->tags = tags_pop(ty, tags);
                        if (this->tags == 0) {
                                this->type &= ~VALUE_TAGGED;
                        }

                        return METHOD(member, vp, this);
                }
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
                if (member == NAMES._name_) {
                        return xSz(name_of(&v));
                } else if (member == NAMES._def_) {
                        return FunDef(ty, &v);
                }
        case VALUE_BUILTIN_FUNCTION:
        case VALUE_BUILTIN_METHOD:
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
                        return !exec ? (call(ty, vp, &v, 0, 0, false), BREAK)
                                     : (call(ty, vp, &v, 0, 0, true), pop());
                }
                if ((vp = class_lookup_field(ty, v.class, member)) != NULL) {
                        return *vp;
                }
                if ((vp = class_lookup_s_method_i(ty, v.class, member)) != NULL) {
                        return *vp;
                }
                if ((vp = class_lookup_method_i(ty, v.class, member)) != NULL) {
                        return *vp;
                }
                if (member == NAMES._name_) {
                        return xSz(class_name(ty, v.class));
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
                        return !exec ? (call(ty, vp, &v, 0, 0, false), BREAK)
                                     : (call(ty, vp, &v, 0, 0, true), pop());
                }

                vp = class_lookup_method_i(ty, n, member);

                if (vp != NULL) {
                        this = mAo(sizeof *this, GC_VALUE);
                        *this = v;
                        return METHOD(member, vp, this);
                }

                if (try_missing && (vp = class_lookup_method_i(ty, n, NAMES.missing)) != NULL) {
                        return !exec ? (
                                pop(),
                                push(xSz(M_NAME(member))),
                                call(ty, vp, &v, 1, 0, false),
                                BREAK
                        ) : (
                                push(xSz(M_NAME(member))),
                                vmC(&METHOD(NAMES.missing, vp, &v), 1)
                        );
                }

                if (try_missing && (vp = class_lookup_method_i(ty, n, NAMES.method_missing)) != NULL) {
                        char const *name = M_NAME(member);
                        this = mAo(sizeof (Value [3]), GC_VALUE);
                        this[0] = v;
                        this[1] = STRING_NOGC(name, strlen(name));
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

static void
DoCall(Ty *ty, Value const *f, int n, int nkw, bool AutoThis)
{
        Value v = *f;
        Value *vp;
        Value value;
        Value container;
        Value subscript;
        Value a, b;
        imax k;

        if (n == -1) {
                n = STACK.count - *vvX(SP_STACK) - nkw;
        }

        /* TODO: optimize more tail calls */
#if 0
        if (tco) {
                vvX(FRAMES);
                IP = *vvX(CALLS);
                tco = false;
        }
#endif

        /*
         * Move all the keyword args into a dict.
         *
         *   TODO: find a better way of handling kwargs
         *
         *   Right now there's way too much branching on (nkw > 0), and we have
         *   to worry about popping the kwargs dict from the stack for any cases
         *   that don't use call()
         *
         *   Overall very cringe...
         */
        if (nkw > 0) {
                if (!AutoThis) {
                        gP(&v);
                } else {
                        gP(v.this);
                        AutoThis = false;
                }
                GC_STOP();
                container = DICT(dict_new(ty));
                for (int i = 0; i < nkw; ++i, SKIPSTR()) {
                        if (top()->type == VALUE_NONE) {
                                pop();
                                continue;
                        }
                        if (IP[0] == '*') {
                                if (top()->type == VALUE_DICT) {
                                        DictUpdate(ty, container.dict, top()->dict);
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
                                                                container.dict,
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
                                dict_put_member(ty, container.dict, IP, pop());
                        }
                }
                push(container);
                GC_RESUME();
        } else {
                container = NIL;
                if (!AutoThis) {
                        gP(&v);
                } else {
                        gP(v.this);
                        AutoThis = false;
                }
        }

        switch (v.type) {
        case VALUE_FUNCTION:
                call(ty, &v, NULL, n, nkw, false);
                break;
        case VALUE_BUILTIN_FUNCTION:
                /*
                 * Builtin functions may not preserve the stack size, so instead
                 * of subtracting `n` after calling the builtin function, we compute
                 * the desired final stack size in advance.
                 *
                 * XXX: ??
                 */
                if (nkw > 0) {
                        container = pop();
                        gP(&container);
                        k = vN(STACK) - n;
                        v = v.builtin_function(ty, n, &container);
                        gX();
                } else {
                        k = vN(STACK) - n;
                        v = v.builtin_function(ty, n, NULL);
                }

                STACK.count = k;
                push(v);

                break;
        case VALUE_GENERATOR:
                gX();
                if (nkw > 0) { pop(); }
                call_co(ty, &v, n);
                return;
        case VALUE_OPERATOR:
                gX();

                if (nkw > 0) pop();

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

                return;
        case VALUE_TAG:
                if (nkw > 0) {
                        container = pop();
                        DoTag(ty, v.tag, n, &container);
                } else {
                        DoTag(ty, v.tag, n, NULL);
                }
                break;
        case VALUE_OBJECT:
                vp = class_lookup_method_i(ty, v.class, NAMES.call);

                if (vp == NULL) {
                        goto NotCallable;
                }

                call(ty, vp, &v, n, nkw, false);

                break;
        case VALUE_CLASS:
                if (v.class < CLASS_PRIMITIVE && v.class != CLASS_OBJECT) {
                        vp = class_lookup_method_i(ty, v.class, NAMES.init);
                        if (LIKELY(vp != NULL)) {
                                call(ty, vp, NULL, n, nkw, true);
                        } else {
                                zP("built-in class has no init method. Was prelude loaded?");
                        }
                } else {
                        value = OBJECT(object_new(ty, v.class), v.class);
                        vp = class_lookup_method_i(ty, v.class, NAMES.init);
                        if (vp != NULL) {
                                gP(&value);
                                call(ty, vp, &value, n, nkw, true);
                                gX();
                                pop();
                        } else {
                                STACK.count -= n + (nkw > 0);
                        }
                        push(value);
                }

                break;
        case VALUE_METHOD:
                if (v.name == NAMES.method_missing) {
                        push(NIL);
                        memmove(top() - (n - 1), top() - n, n * sizeof (Value));
                        top()[-n++] = v.this[1];
                }

                call(ty, v.method, v.this, n, nkw, false);

                break;
        case VALUE_REGEX:
                if (nkw > 0) {
                        pop();
                }

                if (UNLIKELY(n != 1)) {
                        zP("attempt to apply a regex to an invalid number of values");
                }


                value = peek();

                if (UNLIKELY(value.type != VALUE_STRING)) {
                        zP("attempt to apply a regex to a non-string: %s", VSC(&value));
                }

                push(v);
                v = string_match(ty, &value, 1, NULL);
                pop();
                *top() = v;

                break;
        case VALUE_BUILTIN_METHOD:
                if (nkw > 0) {
                        container = pop();
                        gP(&container);
                        v = v.builtin_method(ty, v.this, n, &container);
                        gX();
                } else {
                        v = v.builtin_method(ty, v.this, n, NULL);
                }
                STACK.count -= n;
                push(v);

                break;
        case VALUE_NIL:
                STACK.count -= n + (nkw > 0);
                push(NIL);
                break;
        case VALUE_DICT:
                if (nkw > 0) { pop(); }
                value = peek();
                push(v);
                vp = dict_get_value(ty, v.dict, &value);
                STACK.count -= (n + 1);
                if (vp == NULL) {
                        push(None);
                } else {
                        push(Some(*vp));
                }
                break;
        case VALUE_ARRAY:
                if (nkw > 0) { pop(); }
                subscript = peek();
                push(v);
                value = ArraySubscript(ty, v, subscript, false);
                STACK.count -= (n + 1);
                push(value);
                break;
        default:
NotCallable:
                zP("attempt to call non-callable value %s", VSC(&v));
        }

        gX();
}

inline static Value
GetSelf(Ty *ty)
{
        u32   n = vvL(FRAMES)->f.info[FUN_INFO_PARAM_COUNT];
        Value v = v__(STACK, vvL(FRAMES)->fp + n);

        return (v.type == VALUE_REF) ? *v.ref : v;
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

                        svPn(name, v.str, v.bytes);
                        svP(name, '\0');

                        member = intern_get(&xD.members, v_(name, 0));
                        if (member->id < 0) {
                                if (!strict) {
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

                }
                break;

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
                n = STACK.count - *vvX(SP_STACK) - nkw - 1;
        }

        value = peek();
        vp = NULL;
        func = NULL;
        self = NULL;

        for (int tags = value.tags; tags != 0; tags = tags_pop(ty, tags)) {
                vp = tags_lookup_method_i(ty, tags_first(ty, tags), i);
                if (vp != NULL) {
                        value.tags = tags_pop(ty, tags);
                        if (value.tags == 0) {
                                value.type &= ~VALUE_TAGGED;
                        }
                        self = &value;
                        break;
                }
        }

        /*
         * If we get here and self is a null pointer, none of the value's tags (if it even had any)
         * supported the  method call, so we must now see if the inner value itself can handle the method
         * call.
         */
        if (self == NULL && (self = &value)) switch (value.type & ~VALUE_TAGGED) {
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
        }

        if (func != NULL) {
                pop();
                value.type &= ~VALUE_TAGGED;
                value.tags = 0;
                v = BUILTIN_METHOD(i, func, &value);
                DoCall(ty, &v, n, nkw, true);
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
             && (vp = class_lookup_method_i(ty, value.class, NAMES.missing)) != NULL
        ) {
                // TODO: Shouldn't need to recurse here
                push(xSz(M_NAME(i)));
                call(ty, vp, &value, 1, 0, true);
                v = pop();
                pop();
                DoCall(ty, &v, n, nkw, false);
                return;
        }

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
                v = BOOLEAN(top()[-1].integer op top()[0].integer);             \
                break;                                                          \
        case PAIR_OF(VALUE_REAL):                                               \
                v = BOOLEAN(top()[-1].real op top()[0].real);                   \
                break;                                                          \
        case PACK_TYPES(VALUE_INTEGER, VALUE_REAL):                             \
                v = BOOLEAN(top()[-1].integer op top()[0].real);                \
                break;                                                          \
        case PACK_TYPES(VALUE_REAL, VALUE_INTEGER):                             \
                v = BOOLEAN(top()[-1].real op top()[0].integer);                \
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
                push(INTEGER(-v.integer));
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

        call(ty, vp, &v, 0, 0, exec);
}

TY_INSTR_INLINE static void
DoBinaryOp(Ty *ty, int op, bool exec)
{
        int i = op_dispatch(op, ClassOf(top() - 1), ClassOf(top()));

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

        call(ty, &Globals.items[i], NULL, 2, 0, exec);
}

TY_INSTR_INLINE static void
DoMutDiv(Ty *ty)
{
        uintptr_t c, p = (uintptr_t)poptarget();
        struct itable *o;
        INT32_C(4);
        Value *vp, *vp2, val, x;
        void *v = vp = (void *)(p & ~PMASK3);
        unsigned char b;

        switch (p & PMASK3) {
        case 0:
                if (vp->type == VALUE_OBJECT && (vp2 = class_method(ty, vp->class, "/=")) != NULL) {
                        gP(vp);
                        call(ty, vp2, vp, 1, 0, true);
                        gX();
                        pop();
                } else {
                        x = pop();
                        if ((val = vm_try_2op(ty, OP_MUT_DIV, vp, &x)).type != VALUE_NONE) {
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
                b = ((struct blob *)TARGETS.items[TARGETS.count].gc)->items[((uintptr_t)vp) >> 3] /= pop().integer;
                push(INTEGER(b));
                break;
        case 2:
                c = (uintptr_t)poptarget();
                o = TARGETS.items[TARGETS.count].gc;
                vp = poptarget();
                call(ty, vp, &OBJECT(o, c), 0, 0, true);
                top()[-1] = vm_2op(ty, OP_DIV, top(), top() - 1);
                pop();
                call(ty, v, &OBJECT(o, c), 1, 0, false);
                break;
        default:
                zP("bad target pointer :(");
        }
}

TY_INSTR_INLINE static void
DoMutMod(Ty *ty)
{
        uintptr_t c, p = (uintptr_t)poptarget();
        struct itable *o;
        INT32_C(4);
        Value *vp, *vp2, val, x;
        void *v = vp = (void *)(p & ~PMASK3);
        unsigned char b;

        switch (p & PMASK3) {
        case 0:
                if (vp->type == VALUE_OBJECT && (vp2 = class_method(ty, vp->class, "%=")) != NULL) {
                        gP(vp);
                        call(ty, vp2, vp, 1, 0, true);
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
                b = ((struct blob *)TARGETS.items[TARGETS.count].gc)->items[((uintptr_t)vp) >> 3] %= pop().integer;
                push(INTEGER(b));
                break;
        case 2:
                c = (uintptr_t)poptarget();
                o = TARGETS.items[TARGETS.count].gc;
                vp = poptarget();
                call(ty, vp, &OBJECT(o, c), 0, 0, true);
                top()[-1] = vm_2op(ty, OP_MOD, top(), top() - 1);
                pop();
                call(ty, v, &OBJECT(o, c), 1, 0, false);
                break;
        default:
                zP("bad target pointer :(");
        }
}

TY_INSTR_INLINE static void
DoMutMul(Ty *ty)
{
        uintptr_t c, p = (uintptr_t)poptarget();
        struct itable *o;
        Value *vp, *vp2, val, x;
        void *v = vp = (void *)(p & ~PMASK3);
        unsigned char b;

        switch (p & PMASK3) {
        case 0:
                if (vp->type == VALUE_OBJECT && (vp2 = class_method(ty, vp->class, "*=")) != NULL) {
                        gP(vp);
                        call(ty, vp2, vp, 1, 0, true);
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
                b = ((struct blob *)TARGETS.items[TARGETS.count].gc)->items[((uintptr_t)vp) >> 3] *= pop().integer;
                push(INTEGER(b));
                break;
        case 2:
                c = (uintptr_t)poptarget();
                o = TARGETS.items[TARGETS.count].gc;
                vp = poptarget();
                call(ty, vp, &OBJECT(o, c), 0, 0, true);
                top()[-1] = vm_2op(ty, OP_MUL, top(), top() - 1);
                pop();
                call(ty, v, &OBJECT(o, c), 1, 0, false);
                break;
        default:
                zP("bad target pointer :(");
        }
}

TY_INSTR_INLINE static void
DoMutSub(Ty *ty)
{
        uintptr_t c, p = (uintptr_t)poptarget();
        struct itable *o;
        Value *vp, x, val;
        void *v = vp = (void *)(p & ~PMASK3);
        unsigned char b;

        switch (p & PMASK3) {
        case 0:
                switch (PACK_TYPES(vp->type, top()->type)) {
                case PAIR_OF(VALUE_INTEGER):
                        vp->integer -= top()->integer;
                        pop();
                        break;
                case PAIR_OF(VALUE_REAL):
                        vp->real -= top()->real;
                        pop();
                        break;
                case PACK_TYPES(VALUE_INTEGER, VALUE_REAL):
                        vp->type = VALUE_REAL;
                        vp->real = vp->integer;
                        vp->real -= top()->real;
                        pop();
                        break;
                case PACK_TYPES(VALUE_REAL, VALUE_INTEGER):
                        vp->real -= top()->integer;
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
                b = ((struct blob *)TARGETS.items[TARGETS.count].gc)->items[((uintptr_t)vp) >> 3] -= pop().integer;
                push(INTEGER(b));
                break;
        case 2:
                c = (uintptr_t)poptarget();
                o = TARGETS.items[TARGETS.count].gc;
                vp = poptarget();
                call(ty, vp, &OBJECT(o, c), 0, 0, true);
                top()[-1] = vm_2op(ty, OP_SUB, top(), top() - 1);
                pop();
                call(ty, v, &OBJECT(o, c), 1, 0, false);
                break;
        default:
                zP("bad target pointer :(");
        }
}

TY_INSTR_INLINE static void
DoMutAdd(Ty *ty)
{
        uintptr_t c, p = (uintptr_t)poptarget();
        struct itable *o;
        Value *vp, val, x;
        void *v = vp = (void *)(p & ~PMASK3);
        unsigned char b;

        switch (p & PMASK3) {
        case 0:
                switch (PACK_TYPES(vp->type, top()->type)) {
                case PAIR_OF(VALUE_INTEGER):
                        vp->integer += top()->integer;
                        pop();
                        break;
                case PAIR_OF(VALUE_REAL):
                        vp->real += top()->real;
                        pop();
                        break;
                case PACK_TYPES(VALUE_INTEGER, VALUE_REAL):
                        vp->type = VALUE_REAL;
                        vp->real = vp->integer;
                        vp->real += top()->real;
                        pop();
                        break;
                case PACK_TYPES(VALUE_REAL, VALUE_INTEGER):
                        vp->real += top()->integer;
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
                b = ((struct blob *)TARGETS.items[TARGETS.count].gc)->items[((uintptr_t)vp) >> 3] += pop().integer;
                push(INTEGER(b));
                break;
        case 2:
                c = (uintptr_t)poptarget();
                o = TARGETS.items[TARGETS.count].gc;
                vp = poptarget();
                call(ty, vp, &OBJECT(o, c), 0, 0, true);
                top()[-1] = vm_2op(ty, OP_ADD, top(), top() - 1);
                pop();
                call(ty, v, &OBJECT(o, c), 1, 0, false);
                break;
        default:
                zP("bad target pointer :(");
        }
}

TY_INSTR_INLINE static void
DoMutAnd(Ty *ty)
{
        uintptr_t c, p = (uintptr_t)poptarget();
        struct itable *o;
        Value *vp, val, x;
        void *v = vp = (void *)(p & ~PMASK3);
        unsigned char b;

        switch (p & PMASK3) {
        case 0:
                switch (PACK_TYPES(vp->type, top()->type)) {
                case PAIR_OF(VALUE_INTEGER):
                        vp->integer &= top()->integer;
                        top()->integer = vp->integer;
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
                b = ((Blob *)TARGETS.items[TARGETS.count].gc)->items[((uintptr_t)vp) >> 3] &= pop().integer;
                push(INTEGER(b));
                break;
        case 2:
                c = (uintptr_t)poptarget();
                o = TARGETS.items[TARGETS.count].gc;
                vp = poptarget();
                call(ty, vp, &OBJECT(o, c), 0, 0, true);
                top()[-1] = vm_2op(ty, OP_BIT_AND, top(), top() - 1);
                pop();
                call(ty, v, &OBJECT(o, c), 1, 0, false);
                break;
        default:
                zP("bad target pointer :(");
        }
}

TY_INSTR_INLINE static void
DoMutOr(Ty *ty)
{
        uintptr_t c, p = (uintptr_t)poptarget();
        struct itable *o;
        Value *vp, val, x;
        void *v = vp = (void *)(p & ~PMASK3);
        unsigned char b;

        switch (p & PMASK3) {
        case 0:
                switch (PACK_TYPES(vp->type, top()->type)) {
                case PAIR_OF(VALUE_INTEGER):
                        vp->integer |= top()->integer;
                        top()->integer = vp->integer;
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
                b = ((Blob *)TARGETS.items[TARGETS.count].gc)->items[((uintptr_t)vp) >> 3] |= pop().integer;
                push(INTEGER(b));
                break;

        case 2:
                c = (uintptr_t)poptarget();
                o = TARGETS.items[TARGETS.count].gc;
                vp = poptarget();
                call(ty, vp, &OBJECT(o, c), 0, 0, true);
                top()[-1] = vm_2op(ty, OP_BIT_OR, top(), top() - 1);
                pop();
                call(ty, v, &OBJECT(o, c), 1, 0, false);
                break;

        default:
                zP("bad target pointer :(");
        }
}

TY_INSTR_INLINE static void
DoMutXor(Ty *ty)
{
        uintptr_t c, p = (uintptr_t)poptarget();
        struct itable *o;
        Value *vp, val, x;
        void *v = vp = (void *)(p & ~PMASK3);
        unsigned char b;

        switch (p & PMASK3) {
        case 0:
                switch (PACK_TYPES(vp->type, top()->type)) {
                case PAIR_OF(VALUE_INTEGER):
                        vp->integer ^= top()->integer;
                        top()->integer = vp->integer;
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
                b = ((Blob *)TARGETS.items[TARGETS.count].gc)->items[((uintptr_t)vp) >> 3] ^= pop().integer;
                push(INTEGER(b));
                break;
        case 2:
                c = (uintptr_t)poptarget();
                o = TARGETS.items[TARGETS.count].gc;
                vp = poptarget();
                call(ty, vp, &OBJECT(o, c), 0, 0, true);
                top()[-1] = vm_2op(ty, OP_BIT_XOR, top(), top() - 1);
                pop();
                call(ty, v, &OBJECT(o, c), 1, 0, false);
                break;
        default:
                zP("bad target pointer :(");
        }
}

TY_INSTR_INLINE static void
DoMutShl(Ty *ty)
{
        uintptr_t c, p = (uintptr_t)poptarget();
        struct itable *o;
        Value *vp, val, x;
        void *v = vp = (void *)(p & ~PMASK3);
        unsigned char b;

        switch (p & PMASK3) {
        case 0:
                switch (PACK_TYPES(vp->type, top()->type)) {
                case PAIR_OF(VALUE_INTEGER):
                        vp->integer <<= top()->integer;
                        top()->integer = vp->integer;
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
                b = ((Blob *)TARGETS.items[TARGETS.count].gc)->items[((uintptr_t)vp) >> 3] <<= pop().integer;
                push(INTEGER(b));
                break;

        case 2:
                c = (uintptr_t)poptarget();
                o = TARGETS.items[TARGETS.count].gc;
                vp = poptarget();
                call(ty, vp, &OBJECT(o, c), 0, 0, true);
                top()[-1] = vm_2op(ty, OP_BIT_SHL, top(), top() - 1);
                pop();
                call(ty, v, &OBJECT(o, c), 1, 0, false);
                break;

        default:
                zP("bad target pointer :(");
        }
}

TY_INSTR_INLINE static void
DoMutShr(Ty *ty)
{
        uintptr_t c, p = (uintptr_t)poptarget();
        struct itable *o;
        Value *vp, val, x;
        void *v = vp = (void *)(p & ~PMASK3);
        unsigned char b;

        switch (p & PMASK3) {
        case 0:
                switch (PACK_TYPES(vp->type, top()->type)) {
                case PAIR_OF(VALUE_INTEGER):
                        vp->integer >>= top()->integer;
                        top()->integer = vp->integer;
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
                b = ((Blob *)TARGETS.items[TARGETS.count].gc)->items[((uintptr_t)vp) >> 3] >>= pop().integer;
                push(INTEGER(b));
                break;

        case 2:
                c = (uintptr_t)poptarget();
                o = TARGETS.items[TARGETS.count].gc;
                vp = poptarget();
                call(ty, vp, &OBJECT(o, c), 0, 0, true);
                top()[-1] = vm_2op(ty, OP_BIT_SHR, top(), top() - 1);
                pop();
                call(ty, v, &OBJECT(o, c), 1, 0, false);
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
        uintptr_t m, c, p = (uintptr_t)poptarget();
        void *v = (void *)(p & ~PMASK3);
        struct itable *o;

        switch (p & PMASK3) {
        case 0:
                *(Value *)v = peek();
                break;
        case 1:
                ((struct blob *)TARGETS.items[TARGETS.count].gc)->items[((uintptr_t)v >> 3)] = peek().integer;
                break;
        case 2:
                c = (uintptr_t)poptarget();
                o = vZ(TARGETS)[0].gc;
                poptarget();
                call(ty, v, &OBJECT(o, c), 1, 0, false);
                break;
        case 3:
                m = (p >> 3);
                c = (uintptr_t)poptarget();
                o = vZ(TARGETS)[0].gc;
                push(xSz(M_NAME(m)));
                swap();
                call(ty, class_lookup_setter_i(ty, c, NAMES.missing), &OBJECT(o, c), 2, 0, false);
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
                        pushtarget((Value *)(uintptr_t)v.class, v.object);
                        pushtarget((Value *)(((uintptr_t)vp) | 2), NULL);
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
                        pushtarget((Value *)(uintptr_t)v.class, v.object);
                        pushtarget((Value *)(((uintptr_t)z << 3) | 3), NULL);
                        return;
                }

                pushtarget(itable_get(ty, v.object, z), v.object);
                break;

        case VALUE_CLASS:
                vp = class_lookup_setter_i(ty, v.class, z);
                if (vp != NULL) {
                        pushtarget(vp, NULL);
                        pushtarget((Value *)(uintptr_t)v.class, NULL);
                        return;
                }
                vp = class_lookup_field(ty, v.class, z);
                if (vp != NULL) {
                        pushtarget(vp, NULL);
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
                if (UNLIKELY(subscript.type != VALUE_INTEGER))
                        zP("non-integer array index used in subscript assignment");
                if (subscript.integer < 0)
                        subscript.integer += container.array->count;
                if (UNLIKELY(subscript.integer < 0 || subscript.integer >= container.array->count)) {
                        push(
                                tagged(
                                        ty,
                                        TAG_INDEX_ERR,
                                        container,
                                        subscript,
                                        NONE
                                )
                        );
                        RaiseException(ty);
                        return;
                }
                pushtarget(&container.array->items[subscript.integer], container.array);
                break;

        case VALUE_DICT:
                pushtarget(dict_put_key_if_not_exists(ty, container.dict, subscript), container.dict);
                break;

        case VALUE_BLOB:
                if (UNLIKELY(subscript.type != VALUE_INTEGER)) {
                        zP("non-integer blob index used in subscript assignment");
                }
                if (subscript.integer < 0) {
                        subscript.integer += container.blob->count;
                }
                if (subscript.integer < 0 || subscript.integer >= container.blob->count) {
                        // TODO: Not sure which is the best behavior here
                        push(tagged(
                                ty,
                                TAG_INDEX_ERR,
                                container,
                                subscript,
                                NONE
                        ));
                        RaiseException(ty);
                }
                pushtarget((Value *)((((uintptr_t)(subscript.integer)) << 3) | 1) , container.blob);
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
                if (UNLIKELY(subscript.type != VALUE_INTEGER))
                        zP("non-integer array index used in subscript assignment");
                if (subscript.integer < 0)
                        subscript.integer += container.array->count;
                if (UNLIKELY(subscript.integer < 0 || subscript.integer >= container.array->count)) {
                        push(
                                tagged(
                                        ty,
                                        TAG_INDEX_ERR,
                                        container,
                                        subscript,
                                        NONE
                                )
                        );
                        RaiseException(ty);
                        return;
                }
                *v_(*container.array, subscript.integer) = value;
                break;

        case VALUE_DICT:
                *dict_put_key_if_not_exists(ty, container.dict, subscript) = value;
                break;

        case VALUE_BLOB:
                if (UNLIKELY(subscript.type != VALUE_INTEGER)) {
                        zP("non-integer blob index used in subscript assignment");
                }
                if (subscript.integer < 0) {
                        subscript.integer += container.blob->count;
                }
                if (subscript.integer < 0 || subscript.integer >= container.blob->count) {
                        // TODO: Not sure which is the best behavior here
                        push(tagged(
                                ty,
                                TAG_INDEX_ERR,
                                container,
                                subscript,
                                NONE
                        ));
                        RaiseException(ty);
                }
                if (UNLIKELY(value.type != VALUE_INTEGER)) {
                        zP("attempt to assign Blob element to non-integer value: %s", VSC(&value));
                }
                *v_(*container.blob, subscript.integer) = value.integer;
                break;

        case VALUE_PTR:
                if (UNLIKELY(subscript.type != VALUE_INTEGER)) {
                        zP("non-integer pointer offset used in subscript assignment: %s", VSC(&subscript));
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
                        call(ty, f, &container, 2, 0, false);
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

static void
IncValue(Ty *ty, Value *v)
{
        i32 n;
        i32 rune;
        Value *vp;
        ffi_type const *type;

        switch (EXPECT(v->type, VALUE_INTEGER)) {
        case VALUE_INTEGER:
                v->integer += 1;
                break;

        case VALUE_REAL:
                v->real += 1.0;
                break;

        case VALUE_PTR:
                type = (v->extra != NULL) ? v->extra : &ffi_type_uint8;
                v->ptr = ((char *)v->ptr) + type->size;
                break;

        case VALUE_STRING:
                if (v->bytes > 0) {
                        n = utf8proc_iterate(v->str, v->bytes, &rune);
                        n = max(1, n);
                        v->str += n;
                        v->bytes -= n;
                }
                break;

        case VALUE_OBJECT:
                vp = class_method(ty, v->class, "++");
                if (vp != NULL) {
                        call(ty, vp, v, 0, 0, true);
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
                v->integer -= 1;
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
                        call(ty, vp, v, 0, 0, true);
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
                call(ty, &v, NULL, 1, 0, false);
                break;
        case VALUE_OBJECT:
                if ((vp = class_method(ty, v.class, "__next__")) != NULL) {
                        push(INTEGER(i));
                        xvP(CALLS, IP);
                        call(ty, vp, &v, 1, 0, false);
                        *vvL(CALLS) = next_fix;
                } else if ((vp = class_lookup_method_i(ty, v.class, NAMES._iter_)) != NULL) {
                        pop();
                        pop();
                        --top()->i;
                        /* Have to repeat this instruction */
                        xvP(CALLS, IP);
                        call(ty, vp, &v, 0, 0, false);
                        *vvL(CALLS) = iter_fix;
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
                if ((off = vp->off) < v.bytes) {
                        vp->off += (n = u8_rune_sz(v.str + off));
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
        imax k = top()[-3].integer - 1;

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
                v = pop();
                READVALUE(i);
                vp = itable_get(ty, table, i);
                if (vp->type == VALUE_REF) {
                        *vp->ref = v;
                }
                *vp = v;
        }
}

static void
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

Value
vm_try_exec(Ty *_ty, char *code)
{
        Ty * volatile ty = _ty;

        usize volatile nframes = FRAMES.count;

        // FIXME: don't need to allocate a new stack
        TryStack ts = TRY_STACK;
        vec_init(TRY_STACK);

        usize volatile sp = vN(STACK);
        char * volatile save = IP;

        SCRATCH_SAVE();

        if (TY_CATCH_ERROR()) {
                SCRATCH_RESTORE();
                FRAMES.count = nframes;
                TRY_STACK = ts;
                STACK.count = sp;
                IP = save;
                return NONE;
        }

        vm_exec(ty, code);

        FRAMES.count = nframes;
        TRY_STACK = ts;
        IP = save;

        TY_CATCH_END();

        return pop();
}

void
vm_exec(Ty *ty, char *code)
{
        char *jump;
        char *save = IP;
        IP = code;

        uptr s;
        imax k;
        bool b = false;
        double x;
        int n, nkw = 0, i, j, z, tag;

        Value v, key, value, container, subscript, *vp, *vp2;
        char *str;

        struct try *t;

        PopulateGlobals(ty);

#ifdef TY_PROFILER
        char *StartIPLocal = LastIP;
#endif

        EXEC_DEPTH += 1;
        LOG("vm_exec(): ==> %d", EXEC_DEPTH);

        for (;;) {
        if (ty->GC_OFF_COUNT == 0 && MyGroup->WantGC) {
                WaitGC(ty);
        }

        //if (DEBUGGING && !I_AM_TDB && TY_IS_READY) {
        //        tdb_go(ty);
        //}

#if 0
        static u64 iii = 0;
        if ((iii & 0xFF) == 0) {
                Expr const *e = compiler_find_expr(ty, IP);
                if (e != NULL) {
                        fprintf(
                                stderr,
                                "[Thr%-2d:%s:%s] %s: %s:%d\n",
                                (int)MyId,
                                (I_AM_TDB ? "TDB" : "Ty"),
                                TDB_STATE_NAME,
                                GetInstructionName(*IP),
                                GetExpressionModule(e),
                                e->start.line + 1
                        );
                } else {
                        fprintf(
                                stderr,
                                "[Thr%-2d:%s:%s] %s\n",
                                (int)MyId,
                                (I_AM_TDB ? "TDB" : "Ty"),
                                TDB_STATE_NAME,
                                GetInstructionName(*IP)
                        );
                }
        }
#endif

        for (int N = 0; N < 32; ++N) {
        NextInstruction:
#ifdef TY_PROFILER
                if (Samples != NULL) {
                        u64 now = TyThreadTime();

                        if (LastThreadGCTime > 0) {
                                Value *count = dict_put_key_if_not_exists(ty, FuncSamples, PTR((void *)GC_ENTRY));
                                if (count->type == VALUE_NIL) {
                                        *count = INTEGER(LastThreadGCTime);
                                } else {
                                        count->integer += LastThreadGCTime;
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
                                        count->integer += dt;
                                }

                                int *func = (FRAMES.count > 0) ? vvL(FRAMES)->f.info : NULL;
                                count = dict_put_key_if_not_exists(ty, FuncSamples, PTR(func));
                                if (count->type == VALUE_NIL) {
                                        *count = INTEGER(dt);
                                } else {
                                        count->integer += dt;
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
                        vp = local(ty, n);
                        if (vp->type == VALUE_REF) {
                                push(*(Value *)vp->ptr);
                        } else {
                                push(*vp);
                        }
                        break;
                CASE(LOAD_CAPTURED)
                        READVALUE(n);
#ifndef TY_NO_LOG
                        LOG("Loading capture: %s (%d) of %s", IP, n, VSC(&vvL(FRAMES)->f));
                        SKIPSTR();
#endif

                        push(*vvL(FRAMES)->f.env[n]);
                        break;
                CASE(LOAD_GLOBAL)
                        READVALUE(n);
#ifndef TY_NO_LOG
                        LOG("Loading global: %s (%d)", IP, n);
                        SKIPSTR();
#endif
                        push(Globals.items[n]);
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
                        vvL(FRAMES)->f.env[j] = vp;
                        break;
                CASE(DECORATE)
                        READVALUE(s);
                        if (top()->type == VALUE_FUNCTION) {
                                top()->xinfo = (FunUserInfo *)s;
                        }
                        break;
                CASE(EXEC_CODE)
                        READVALUE(s);
                        vm_exec(ty, (char *) s);
                        break;
                CASE(DUP)
                        push(peek());
                        break;
                CASE(DUP2)
                        push(top()[-1]);
                        push(top()[-1]);
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
                        if (top()[-1].type == VALUE_NONE) {
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
                        if (!TY_IS_INITIALIZED) {
                                READVALUE(n);
                                IP += n;
                                *top() = BOOLEAN(true);
                                break;
                        }
                CASE(5NOP)
                        IP += 4;
                        break;
                CASE(TARGET_GLOBAL)
TargetGlobal:
                        READVALUE(n);
                        LOG("Global: %d", (int)n);
                        while (Globals.count <= n)
                                xvP(Globals, NIL);
                        pushtarget(&Globals.items[n], NULL);
                        break;
                CASE(TARGET_THREAD_LOCAL)
                        READVALUE(n);
                        while (vN(THREAD_LOCALS) <= n) {
                                xvP(THREAD_LOCALS, NIL);
                        }
                        pushtarget(v_(THREAD_LOCALS, n), NULL);
                        break;
                CASE(TARGET_LOCAL)
                        if (FRAMES.count == 0)
                                goto TargetGlobal;
                        READVALUE(n);
                        LOG("Targeting %d", n);
                        pushtarget(local(ty, n), NULL);
                        break;
                CASE(ASSIGN_GLOBAL)
AssignGlobal:
                        READVALUE(n);
                        LOG("Global: %d", (int)n);
                        while (Globals.count <= n)
                                xvP(Globals, NIL);
                        Globals.items[n] = pop();
                        break;
                CASE(ASSIGN_LOCAL)
                        if (FRAMES.count == 0)
                                goto AssignGlobal;
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
                        LOG("Loading capture: %s (%d) of %s", IP, n, VSC(&vvL(FRAMES)->f));
                        SKIPSTR();
#endif
                        pushtarget(vvL(FRAMES)->f.env[n], NULL);
                        break;
                CASE(TARGET_MEMBER)
                        READVALUE(z);
                        v = pop();
                        DoTargetMember(ty, v, z);
                        break;
                CASE(TARGET_SELF_MEMBER)
                        READVALUE(z);
                        value = GetSelf(ty);
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
                                NOGC(rest);
                                vvPn(*rest, top()->array->items + i, top()->array->count - (i + j));
                                *poptarget() = ARRAY(rest);
                                OKGC(rest);
                        }
                        break;
                CASE(TUPLE_REST)
                        READJUMP(jump);
                        READVALUE(i);
                        vp = poptarget();
                        if (top()->type != VALUE_TUPLE) {
                                DOJUMP(jump);
                        } else {
                                int count = top()->count - i;
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

                                vec(int) ids = {0};
                                vec(int) indices = {0};

                                SCRATCH_SAVE();

                                IP = ALIGNED_FOR(int, IP);

                                for (int i = 0; i < v.count; ++i) {
                                        if (v.ids == NULL || v.ids[i] == -1)
                                                continue;
                                        if (!search_int((int const *)IP, v.ids[i])) {
                                                svP(ids, v.ids[i]);
                                                svP(indices, i);
                                        }
                                }

                                value = vT(ids.count);

                                if (value.items != NULL) { NOGC(value.items); }
                                value.ids = mAo(value.count * sizeof (int), GC_TUPLE);
                                if (value.items != NULL) { NOGC(value.items); }

                                memcpy(value.ids, ids.items, value.count * sizeof (int));

                                for (int i = 0; i < value.count; ++i) {
                                        value.items[i] = v.items[indices.items[i]];
                                }

                                SCRATCH_RESTORE();

                                *poptarget() = value;

                                while (*(int const *)IP != -1) IP += sizeof (int);
                                IP += sizeof (int);
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
                        push(TAG(TAG_DISPATCH_ERR));
                        vvX(FRAMES);
                        IP = *vvX(CALLS);
                        RaiseException(ty);
                        break;
                CASE(BAD_CALL)
                        v = peek();

                        READSTR(str);

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
                        dont_printf("Finally: ntry=%zu  ndefer=%zu\n", vN(TRY_STACK), vN(t->defer));
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
                        vvL(TRY_STACK)[0]->state = TRY_FINALLY;
                        break;
                CASE(TRY)
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

                        if (setjmp(t->jb) != 0) {
                                break;
                        }

                        READVALUE(n);
                        t->catch = IP + n;

                        READVALUE(n);
                        t->finally = (n == -1) ? NULL : IP + n;

                        READVALUE(n);
                        t->end = (n == -1) ? NULL : IP + n;

                        t->sp = vN(STACK);
                        t->gc = vN(RootSet);
                        t->cs = vN(CALLS);
                        t->ts = vN(TARGETS);
                        t->ds = vN(DROP_STACK);
                        t->ctxs = vN(FRAMES);
                        t->nsp = vN(SP_STACK);
                        t->executing = false;
                        t->state = TRY_TRY;
                        t->ed = EXEC_DEPTH;
                        t->ss = SaveScratch(ty);
                        v0(t->defer);

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
                        //printf("Push defer: ntry=%zu  ndefer=%zu t=%p\n", vN(TRY_STACK), vN(t->defer), (void *)t);
                        break;
                CASE(CLEANUP)
                        t = *vvL(TRY_STACK);
                        //printf("Running %zu cleanup funcs ntry=%zu t=%p\n", vN(t->defer), vN(TRY_STACK), (void *)t);
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
                        call(ty, vp, &v, 0, 0, false);
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
                        v = REGEX((Regex *) s);
                        if (
                                top()->type != VALUE_STRING
                             || (value = value_apply_callable(ty, &v, top())).type == VALUE_NIL
                        ) {
                                DOJUMP(jump);
                        } else {
                                push(value);
                        }
                        break;
                CASE(ASSIGN_REGEX_MATCHES)
                        READVALUE(n);
                        vp = poptarget();
                        v = pop();
                        if (v.type == VALUE_ARRAY) {
                                for (i = 0; i < v.array->count; ++i) {
                                        vp[i] = v.array->items[i];
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
                        //LOG("trying to index: %s", VSC(top()));
                        if (top()->type != VALUE_ARRAY) {
                                DOJUMP(jump);
                                break;
                        }
                        if (i < 0) {
                                i += top()->array->count;
                        }
                        if (top()->array->count <= i) {
                                if (b) {
                                        DOJUMP(jump);
                                } else {
                                        push(NIL);
                                }
                        } else {
                                push(top()->array->items[i]);
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
                CASE(UNPOP)
                        STACK.count += 1;
                        break;
                CASE(DROP2)
                        v = v_L(STACK);
                        STACK.count -= 2;
                        v_L(STACK) = v;
                        break;
                CASE(INTEGER)
                        READVALUE(k);
                        push(INTEGER(k));
                        break;
                CASE(REAL)
                        READVALUE(x);
                        push(REAL(x));
                        break;
                CASE(BOOLEAN)
                        READVALUE(b);
                        push(BOOLEAN(b));
                        break;
                CASE(STRING)
                        n = strlen(IP);
                        push(STRING_NOGC(IP, n));
                        IP += n + 1;
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
                {
                        int_vector ids = {0};
                        ValueVector values = {0};

                        SCRATCH_SAVE();

                        bool have_names = false;

                        READVALUE(n);

                        for (int i = 0; i < n; ++i) {
                                Value *v = &STACK.items[STACK.count - n + i];
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

                        k  = vN(values);
                        vp = mAo(k * sizeof (Value), GC_TUPLE);
                        v  = TUPLE(vp, NULL, k, false);

                        GC_STOP();

                        if (k > 0) {
                                __builtin_memcpy(vp, values.items, k * sizeof (Value));
                                if (have_names) {
                                        v.ids = mAo(k * sizeof (int), GC_TUPLE);
                                        __builtin_memcpy(v.ids, ids.items, k * sizeof (int));
                                }
                        }

                        STACK.count -= n;
                        push(v);

                        GC_RESUME();
                        SCRATCH_RESTORE();
                        break;
                }
                CASE(GATHER_TUPLE)
                        n = vN(STACK) - *vvX(SP_STACK);

                        vp = mAo(n * sizeof (Value), GC_TUPLE);
                        v = TUPLE(vp, NULL, n, false);

                        __builtin_memcpy(vp, topN(n), n * sizeof (Value));

                        STACK.count -= n;
                        push(v);

                        break;
                CASE(DICT)
                        v = DICT(dict_new(ty));
                        gP(&v);

                        n = (STACK.count - *vvX(SP_STACK)) / 2;

                        for (i = 0; i < n; ++i) {
                                value = top()[0];
                                key = top()[-1];
                                if (value.type == VALUE_NONE) {
                                        pop();
                                        splat(ty, v.dict, &key);
                                        pop();
                                } else {
                                        dict_put_value(ty, v.dict, key, value);
                                        pop();
                                        pop();
                                }
                        }

                        push(v);
                        gX();

                        break;
                CASE(DICT_DEFAULT)
                        v = pop();
                        top()->dict->dflt = v;
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
                CASE(FMT1)
                        READVALUE(z);
                        v = pop();
                        push(INTEGER(z));
                        push(v);
                        CallMethod(ty, NAMES.fmt, 2, 0, false);
                        break;
                CASE(FMT2)
                        READVALUE(z);
                        v = pop();
                        value = pop();
                        push(xSz(str));
                        push(INTEGER(z));
                        push(value);
                        push(v);
                        CallMethod(ty, NAMES.fmt, 3, 0, false);
                        break;
                CASE(TO_STRING)
                        if (top()->type == VALUE_PTR) {
                                char *s = VSC(top());
                                pop();
                                push(STRING_NOGC(s, strlen(s)));
                        } else {
                                CallMethod(ty, NAMES.str, 0, 0, false);
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
                        v.gen->f = vvL(FRAMES)->f;

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
                CASE(EXPRESSION)
                        READVALUE(s);
                        push(tagged(ty, TyExpr, PTR((Expr *)s), NONE));
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
                        push(compiler_render_template(ty, (struct expression *)s));
                        break;
                CASE(TRAP)
#ifdef _WIN32
                        __debugbreak();
#else
                        *(char *)0 = 0;
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
                        k = top()[-3].integer - 1;
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
                        for (n = 0; top()[-n].type != VALUE_SENTINEL; ++n)
                                ;
                        for (i = 0, j = n - 1; i < j; ++i, --j) {
                                v = top()[-i];
                                top()[-i] = top()[-j];
                                top()[-j] = v;
                        }
                        break;
                CASE(FIX_TO)
                        READVALUE(n);
                        for (i = 0; top()[-i].type != VALUE_SENTINEL; ++i)
                                ;
                        while (i > n)
                                --i, pop();
                        while (i < n)
                                ++i, push(NIL);
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
                        for (i = 0, vp = top(); pop().type != VALUE_SENTINEL; ++i)
                                ;
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
                        for (i = 0, vp = top(); pop().type != VALUE_SENTINEL; ++i)
                                ;
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
                        if (top()->type == VALUE_SENTINEL)
                                IP += n;
                        break;
                CASE(CLEAR_EXTRA)
                        while (top()->type != VALUE_SENTINEL)
                                pop();
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
                CASE(PUSH_ALL)
                        v = pop();
                        gP(&v);
                        for (int i = 0; i < v.array->count; ++i) {
                                push(v.array->items[i]);
                        }
                        gX();
                        break;
                CASE(CONCAT_STRINGS)
                        READVALUE(n);
                        k = 0;
                        for (i = STACK.count - n; i < STACK.count; ++i)
                                k += STACK.items[i].bytes;
                        str = value_string_alloc(ty, k);
                        v = STRING(str, k);
                        k = 0;
                        for (i = STACK.count - n; i < STACK.count; ++i) {
                                if (STACK.items[i].bytes > 0) {
                                        memcpy(str + k, STACK.items[i].str, STACK.items[i].bytes);
                                        k += STACK.items[i].bytes;
                                }
                        }
                        STACK.count -= n - 1;
                        STACK.items[STACK.count - 1] = v;
                        break;
                CASE(RANGE)
                        vp = class_lookup_method_i(ty, CLASS_RANGE, NAMES.init);
                        if (UNLIKELY(vp == NULL)) {
                                zP("failed to load Range class. Was prelude loaded correctly?");
                        }

                        v = OBJECT(object_new(ty, CLASS_RANGE), CLASS_RANGE);
                        NOGC(v.object);
                        call(ty, vp, &v, 2, 0, true);
                        *top() = v;
                        OKGC(v.object);
                        break;
                CASE(INCRANGE)
                        vp = class_lookup_method_i(ty, CLASS_INC_RANGE, NAMES.init);
                        if (UNLIKELY (vp == NULL)) {
                                zP("failed to load InclusiveRange class. Was prelude loaded correctly?");
                        }

                        v = OBJECT(object_new(ty, CLASS_INC_RANGE), CLASS_INC_RANGE);
                        NOGC(v.object);
                        call(ty, vp, &v, 2, 0, true);
                        *top() = v;
                        OKGC(v.object);
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
                CASE(SELF_MEMBER_ACCESS)
                        READVALUE(z);

                        value = GetSelf(ty);
                        v = GetMember(ty, value, z, false, false);

                        switch (v.type) {
                        case VALUE_BREAK:
                                continue;

                        default:
                                push(v);
                                continue;
                        }
                        break;
                CASE(TRY_MEMBER_ACCESS)
                CASE(MEMBER_ACCESS)
                        b = (IP[-1] == INSTR_TRY_MEMBER_ACCESS);

                        READVALUE(z);
MemberAccess:
                        value = pop();
                        v = GetMember(ty, value, z, true, false);

                        switch (v.type) {
                        case VALUE_BREAK:
                                continue;

                        case VALUE_NONE:
                                if (b) {
                                        push(NIL);
                                        continue;
                                }
                                break;

                        default:
                                push(v);
                                continue;
                        }

BadMemberAccess:
BadTupleMember:
                        BadFieldAccess(ty, &value, z);
                        UNREACHABLE();
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
                                        if (subscript.integer < 0) {
                                                subscript.integer += container.count;
                                        }

                                        if (subscript.integer < 0 || subscript.integer >= container.count) {
                                                v = tagged(ty, TAG_INDEX_ERR, container, subscript, NONE);
                                                pop();
                                                pop();
                                                push(v);
                                                RaiseException(ty);
                                                break;
                                        }

                                        pop();
                                        pop();

                                        push(container.items[subscript.integer]);
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
                                        call(ty, vp, &container, 1, 0, false);
                                } else {
                                        goto BadContainer;
                                }
                                break;
                        case VALUE_OBJECT:
                                vp = class_lookup_method_i(ty, container.class, NAMES.subscript);
                                if (vp != NULL) {
                                        swap();
                                        pop();
                                        call(ty, vp, &container, 1, 0, false);
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
                                push(PTR(((char *)container.ptr) + ((ffi_type *)v.ptr)->size * subscript.integer));
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
                        READVALUE(m);
                        READVALUE(g);
                        READVALUE(s);

                        class = class_get(ty, class_id);

                        InstallMethods(ty, &class->s_getters, s_g);
                        InstallMethods(ty, &class->s_methods, s_m);
                        InstallMethods(ty, &class->methods, m);
                        InstallMethods(ty, &class->getters, g);
                        InstallMethods(ty, &class->setters, s);
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

                        IP = ALIGNED_FOR(int, IP);

                        // n: bound_caps
                        READVALUE(n);

                        v.info = (int *) IP;

                        int hs = v.info[0];
                        int size  = v.info[1];
                        int nEnv = v.info[2];

                        int ncaps = (n > 0) ? nEnv - n : nEnv;

                        LOG("Header size: %d", hs);
                        LOG("Code size: %d", size);
                        LOG("Bound: %d", v.info[4]);
                        LOG("ncaps: %d", ncaps);
                        LOG("Name: %s", VSC(&v));

                        if (*from_eval(&v)) {
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

                        if (*from_eval(&v)) {
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
                        *top() = BindMethod(vp, top(), z);
                        break;
                CASE(BIND_GETTER)
                        READVALUE(n);
                        READVALUE(z);
                        vp = class_lookup_getter_i(ty, n, z);
                        *top() = BindMethod(vp, top(), z);
                        break;
                CASE(BIND_SETTER)
                        READVALUE(n);
                        READVALUE(z);
                        vp = class_lookup_setter_i(ty, n, z);
                        *top() = BindMethod(vp, top(), z);
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
                CASE(TAIL_CALL)
                        n = vvL(FRAMES)->f.info[4];

                        memcpy(
                                local(ty, 0),
                                topN(n),
                                n * sizeof (Value)
                        );

                        i = n;
                        n = vvL(FRAMES)->f.info[3];

                        for (; i < n; ++i) {
                                *local(ty, i) = NIL;
                        }

                        STACK.count = vvL(FRAMES)->fp + n;
                        IP = code_of(&vvL(FRAMES)->f);

                        break;
                CASE(CALL)
                        v = pop();
                        READVALUE(n);
                        READVALUE(nkw);
                        DoCall(ty, &v, n, nkw, false);
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
                        READVALUE(i);
                        READVALUE(nkw);
                        CallMethod(ty, i, n, nkw, false);
                        break;
                CASE(CALL_SELF_METHOD)
                        READVALUE(n);
                        READVALUE(i);
                        READVALUE(nkw);
                        push(GetSelf(ty));
                        CallMethod(ty, i, n, nkw, false);
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

        Array *hooks = Globals.items[id].array;

        vec(char *) msgs = {0};
        char *first = !TyHasError(ty) ? NULL : S2(TyError(ty));

        bool bReprintFirst = false;

        for (usize i = 0; i < hooks->count; ++i) {
                if (TY_CATCH_ERROR()) {
                        vvP(msgs, S2(TyError(ty)));
                } else {
                        Value v = vmC(&hooks->items[i], 0);
                        bReprintFirst = bReprintFirst || value_truthy(ty, &v);
                        TY_CATCH_END();
                }
        }

        if (first != NULL && bReprintFirst) {
                fprintf(stderr, "%s\n", first);
        }

        for (usize i = 0; i < msgs.count; ++i) {
                fprintf(stderr, "Exit hook failed with error: %s\n", msgs.items[i]);
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

        NAMES.call             = M_ID("__call__");
        NAMES.contains         = M_ID("contains?");
        NAMES.count            = M_ID("__count__");
        NAMES._def_            = M_ID("__def__");
        NAMES._drop_           = M_ID("__drop__");
        NAMES._enter_          = M_ID("__enter__");
        NAMES.fmt              = M_ID("__fmt__");
        NAMES._free_           = M_ID("__free__");
        NAMES.init             = M_ID("init");
        NAMES._iter_           = M_ID("__iter__");
        NAMES.json             = M_ID("__json__");
        NAMES._len_            = M_ID("#");
        NAMES.len              = M_ID("len");
        NAMES.match            = M_ID("__match__");
        NAMES.missing          = M_ID("__missing__");
        NAMES.method_missing   = M_ID("__method_missing__");
        NAMES._name_           = M_ID("__name__");
        NAMES._next_           = M_ID("__next__");
        NAMES.ptr              = M_ID("__ptr__");
        NAMES.slice            = M_ID("[;;]");
        NAMES.str              = M_ID("__str__");
        NAMES.subscript        = M_ID("[]");

        GC_STOP();

        InitThreadGroup(ty, MyGroup = &MainGroup);

        NewArenaNoGC(ty, 1ULL << 22);

        compiler_init(ty);

        add_builtins(ty, ac, av);

        AddThread(ty, TyThreadSelf());

        if (TY_CATCH_ERROR()) {
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

        for (int i = 0; i < vN(*ctx); ++i) {
                char *ip = (char *)v__(*ctx, i);
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

                                for (int i = 0; i < vN(scope->owned); ++i) {
                                        dump(
                                                out,
                                                "    %s%*s%s = %s\n",
                                                TERM(1;93),
                                                max_width + 2,
                                                v__(scope->owned, i)->identifier,
                                                TERM(22;39),
                                                VSC(v_(localv, i))
                                        );
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

        return vv(*out);
}

static void
xDcringe(Ty *ty)
{
        dump(&ErrorBuffer, "Stack trace:\n");

        for (int i = 0; IP != NULL; ++i) {
                if (vN(FRAMES) > 0 && ((char *)vvL(FRAMES)->f.info)[FUN_HIDDEN]) {
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
                     && is_hidden_fun(&vvL(st.frames)->f)
                ) {
                        goto Next;
                }

                i32 fp;
                i32 nvar;
                if (vN(st.frames) > 0) {
                        Frame *frame = vvL(st.frames);
                        fp = frame->fp;
                        nvar = frame->f.info[FUN_INFO_BOUND];
                } else {
                        fp = 0;
                        nvar = 0;
                }

                ValueVector locals = {0};
                xvPn(locals, vv(STACK) + fp, nvar);

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
                     && is_hidden_fun(&vvL(st.frames)->f)
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
vm_vpanic_ex(Ty *ty, ThrowCtx const *ctx, char const *fmt, va_list _ap)
{
        va_list ap;

        ErrorBuffer.count = 0;

        va_copy(ap, _ap);
        dump(&ErrorBuffer, "%s%sRuntimeError%s%s: ", TERM(1), TERM(31), TERM(22), TERM(39));
        vdump(&ErrorBuffer, fmt, ap);
        va_end(ap);

        dump(&ErrorBuffer, "%c", '\n');

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

        XLOG("VM Error: %s", vv(ErrorBuffer));

        TY_THROW_ERROR();
}

noreturn void
vm_panic_ex(Ty *ty, ThrowCtx const *ctx, char const *fmt, ...)
{
        va_list ap;

        va_start(ap, fmt);
        vm_vpanic_ex(ty, ctx, fmt, ap);
        va_end(ap);

        UNREACHABLE();
}

noreturn void
vm_panic(Ty *ty, char const *fmt, ...)
{
        va_list ap;

        ThrowCtx *ctx = PushThrowCtx(ty);

        va_start(ap, fmt);
        vm_panic_ex(ty, ctx, fmt, ap);
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

        Class *class = class_get(ty, CLASS_ERROR);
        Value error = OBJECT(object_new(ty, CLASS_ERROR), CLASS_ERROR);
        *itable_get(ty, error.object, v_0(class->fields.ids)) = msg;

        vm_throw(ty, &error);

        UNREACHABLE();
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
                if (nf > 0 && ((char *)v_(frames, nf - 1)->f.info)[FUN_HIDDEN]) {
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
                        .count = Samples->values[i].integer
                };
                vec_nogc_push(profile, entry);
                total_ticks += entry.count;
        }

        for (int i = 0; i < FuncSamples->size; ++i) {
                if (FuncSamples->keys[i].type == 0)
                        continue;
                ProfileEntry entry = {
                        .ctx = FuncSamples->keys[i].ptr,
                        .count = FuncSamples->values[i].integer
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
                        mF(f_string);
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

                DumpProgram(ty, &prog_text, filename, code, code + size, false);

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
                                (uintptr_t)entry->ctx,
                                ""
                        );
                        fprintf(ProfileOut, "   &halt = %lu\n", (uintptr_t)&halt);
                        fprintf(ProfileOut, "   &IP = %lu\n", (uintptr_t)&IP);
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
                                (uintptr_t)entry->ctx,
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
vm_load_program(Ty *_ty, char const *source, char const *file)
{
        Ty * volatile ty = _ty;

        filename = file;

        TY_IS_READY = false;

        GC_STOP();

        v0(RootSet);
        v0(STACK);
        v0(SP_STACK);
        v0(TRY_STACK);
        v0(TARGETS);
        SCRATCH_RESET();

        TyClearError(ty);

        Module * volatile mod = NULL;

        if (TY_CATCH_ERROR()) {
                filename = NULL;
                GC_RESUME();
                return false;
        }

        mod = compiler_compile_source(ty, source, filename);
        if (mod == NULL) {
                filename = NULL;
                TY_CATCH_END();
                GC_RESUME();
                return false;
        }

        if (DisassemblyOut != NULL) {
                byte_vector out = {0};
                DumpProgram(ty, &out, filename, NULL, NULL, true);
                fwrite(out.items, 1, out.count, DisassemblyOut);
                free(out.items);
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
                filename = NULL;
                return true;
        }

        if (TY_CATCH_ERROR()) {
                filename = NULL;
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

        if (PrintResult && STACK.capacity > 0) {
                printf("%s\n", VSC(top() + 1));
        }

#if defined(TY_GC_STATS)
        printf("%.2f MB\n", TotalBytesAllocated / 1.0e6);
#endif

        TY_CATCH_END();

        filename = NULL;

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
        push(*v);

        PushThrowCtx(ty);
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
        call(ty, f, self, argc, 0, true);
        return pop();
}

Value
vm_call_ex(Ty *ty, Value const *f, int argc, Value *kwargs, bool collect)
{
        Value r, *init, *vp;
        usize n = STACK.count - argc;

        switch (f->type) {
        case VALUE_FUNCTION:
                if (kwargs != NULL) {
                        push(*kwargs);
                        call(ty, f, NULL, argc, 1, true);
                } else {
                        call(ty, f, NULL, argc, 0, true);
                }
                goto Collect;

        case VALUE_METHOD:
                if (kwargs != NULL) {
                        push(*kwargs);
                        call(ty, f->method, f->this, argc, 1, true);
                } else {
                        call(ty, f->method, f->this, argc, 0, true);
                }
                goto Collect;

        case VALUE_BUILTIN_FUNCTION:
                r = f->builtin_function(ty, argc, kwargs);
                STACK.count = n;
                return r;

        case VALUE_BUILTIN_METHOD:
                r = f->builtin_method(ty, f->this, argc, NULL);
                STACK.count = n;
                return r;

        case VALUE_TAG:
                DoTag(ty, f->tag, argc, (Value *)kwargs);
                return pop();

        case VALUE_CLASS:
                init = class_lookup_method_i(ty, f->class, NAMES.init);
                if (f->class < CLASS_PRIMITIVE) {
                        if (LIKELY(init != NULL)) {
                                call(ty, init, NULL, argc, 0, true);
                                return pop();
                        } else {
                                zP("Couldn't find init method for built-in class. Was prelude loaded?");
                        }
                } else {
                        r = OBJECT(object_new(ty, f->class), f->class);
                        if (init != NULL) {
                                call(ty, init, &r, argc, 0, true);
                                pop();
                        } else {
                                STACK.count -= argc;
                        }
                        return r;
                }
                UNREACHABLE();

        case VALUE_DICT:
                vp = (argc >= 1) ? dict_get_value(ty, f->dict, top() - (argc - 1)) : NULL;
                STACK.count -= argc;
                return (vp == NULL) ? None : Some(*vp);

        case VALUE_ARRAY:
                r = (argc >= 1) ? ArraySubscript(ty, *f, top()[-(argc - 1)], false) : None;
                STACK.count -= argc;
                return r;

        case VALUE_OBJECT:
                vp = class_lookup_method_i(ty, f->class, NAMES.call);

                if (vp == NULL) {
                        goto NotCallable;
                }

                if (kwargs != NULL) {
                        push(*kwargs);
                        call(ty, vp, f, argc, 1, true);
                } else {
                        call(ty, vp, f, argc, 0, true);
                }
                goto Collect;


        default:
        NotCallable:
                zP("Non-callable value passed to vm_call(): %s", VSC(f));
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
        Value a, b, r;
        Value *vp;
        usize n = STACK.count - argc;

        switch (f->type) {
        case VALUE_FUNCTION:
                call(ty, f, NULL, argc, 0, true);
                return pop();

        case VALUE_METHOD:
                call(ty, f->method, f->this, argc, 0, true);
                return pop();

        case VALUE_BUILTIN_FUNCTION:
                r = f->builtin_function(ty, argc, NULL);
                STACK.count = n;
                return r;

        case VALUE_BUILTIN_METHOD:
                r = f->builtin_method(ty, f->this, argc, NULL);
                STACK.count = n;
                return r;

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
                                call(ty, vp, NULL, argc, 0, true);
                                return pop();
                        } else {
                                zP("Couldn't find init method for built-in class. Was prelude loaded?");
                        }
                } else {
                        r = OBJECT(object_new(ty, f->class), f->class);
                        if (vp != NULL) {
                                call(ty, vp, &r, argc, 0, true);
                                pop();
                        } else {
                                STACK.count -= argc;
                        }
                        return r;
                }
                UNREACHABLE();

        case VALUE_DICT:
                vp = (argc >= 1) ? dict_get_value(ty, f->dict, top() - (argc - 1)) : NULL;
                STACK.count -= argc;
                return (vp == NULL) ? None : Some(*vp);

        case VALUE_ARRAY:
                r = (argc >= 1) ? ArraySubscript(ty, *f, top()[-(argc - 1)], false) : None;
                STACK.count -= argc;
                return r;

        case VALUE_OBJECT:
                vp = class_lookup_method_i(ty, f->class, NAMES.call);
                if (vp == NULL) {
                        goto NotCallable;
                }
                call(ty, vp, f, argc, 0, true);
                return pop();

        default:
        NotCallable:
                zP("Non-callable value passed to vm_call(): %s", VSC(f));
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
                call(ty, f, NULL, argc, 0, true);
                return pop();

        case VALUE_METHOD:
                call(ty, f->method, f->this, argc, 0, true);
                return pop();

        case VALUE_BUILTIN_FUNCTION:
                r = f->builtin_function(ty, argc, NULL);
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

                call(ty, v, f, argc, 0, true);
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
        int i = op_dispatch(op, ClassOf(a), ClassOf(b));

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

        call(ty, &Globals.items[i], NULL, 2, 0, true);

        return pop();
}


void
MarkStorage(Ty *ty)
{
        GCLOG("Marking root set (%zu items)", vN(RootSet));
        for (int i = 0; i < vN(RootSet); ++i) {
                value_mark(ty, v_(RootSet, i));
        }

        GCLOG("Marking thread-local storage");
        for (int i = 0; i < vN(THREAD_LOCALS); ++i) {
                value_mark(ty, v_(THREAD_LOCALS, i));
        }

        GCLOG("Marking stack");
        for (int i = 0; i < vN(STACK) + RC && i < vC(STACK); ++i) {
                value_mark(ty, v_(STACK, i));
        }

        GCLOG("Marking try stack");
        for (int i = 0; i < vN(TRY_STACK); ++i) {
                struct try *t = v__(TRY_STACK, i);
                for (int i = 0; i < vN(t->defer); ++i) {
                        value_mark(ty, v_(t->defer, i));
                }
        }

        GCLOG("Marking throw stack");
        for (int i = 0; i < vN(THROW_STACK); ++i) {
                ThrowCtx *ctx = v__(THROW_STACK, i);
                for (int i = 0; i < vN(ctx->locals); ++i) {
                        ValueVector const *locals = v_(ctx->locals, i);
                        for (int i = 0; i < vN(*locals); ++i) {
                                value_mark(ty, v_(*locals, i));
                        }
                }
        }

        GCLOG("Marking drop stack");
        for (int i = 0; i < vN(DROP_STACK); ++i) {
                value_mark(ty, v_(DROP_STACK, i));
        }

        GCLOG("Marking targets");
        for (int i = 0; i < vN(TARGETS); ++i) {
                Target *target = v_(TARGETS, i);
                if ((((uintptr_t)target->t) & 0x07) == 0) {
                        value_mark(ty, target->t);
                }
        }

        GCLOG("Marking frame functions");
        for (int i = 0; i < vN(FRAMES); ++i) {
                value_mark(ty, &v_(FRAMES, i)->f);
        }
}

char const *
GetInstructionName(uint8_t i)
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
        CASE(DUP2)
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
        CASE(TARGET_MEMBER)
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
        CASE(TRY_TAG_POP)
                SKIPVALUE(n);
                SKIPVALUE(tag);
                break;
        CASE(POP)
                break;
        CASE(UNPOP)
                break;
        CASE(INTEGER)
                SKIPVALUE(k);
                break;
        CASE(REAL)
                SKIPVALUE(x);
                break;
        CASE(BOOLEAN)
                SKIPVALUE(b);
                break;
        CASE(STRING)
                SKIPSTR();
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
                break;
        CASE(DICT_DEFAULT)
                break;
        CASE(SELF)
                break;
        CASE(NIL)
                break;
        CASE(FMT1)
        CASE(FMT2)
                SKIPSTR();
                SKIPVALUE(n);
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
        CASE(EXPRESSION)
                SKIPVALUE(s);
                break;
        CASE(EVAL)
                SKIPVALUE(s);
                break;
        CASE(RENDER_TEMPLATE)
                SKIPVALUE(s);
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
        CASE(PUSH_ALL)
                break;
        CASE(CONCAT_STRINGS)
                SKIPVALUE(n);
                break;
        CASE(RANGE)
        CASE(INCRANGE)
                break;
        CASE(TRY_MEMBER_ACCESS)
        CASE(MEMBER_ACCESS)
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

                READVALUE(class);

                READVALUE(s_m);
                READVALUE(s_g);
                READVALUE(m);
                READVALUE(g);
                READVALUE(s);

                while (s_m --> 0) { SKIPVALUE(i); }
                while (s_g --> 0) { SKIPVALUE(i); }
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

                ip = ALIGNED_FOR(int, ip);

                // n: bound_caps
                SKIPVALUE(n);

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
        CASE(CALL)
                SKIPVALUE(n);
                SKIPVALUE(nkw);
                for (int i = 0; i < nkw; ++i) {
                        SKIPSTR();
                }
                break;
        CASE(TRY_CALL_METHOD)
        CASE(CALL_METHOD)
        CASE(CALL_SELF_METHOD)
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

        int r = TyThreadCreate(&t->t, vm_run_tdb, TDB);
        if (r != 0) {
                zP("TyThreadCreate(): %s", strerror(r));
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
                          ? code_of(&vvL(FRAMES)->f)
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

        ty = TDB->host;

        switch ((u8)*IP) {
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
                goto End;
        }
        // ======================================================================================
        Module *mod = CompilerGetModule(ty, module);
        if (mod != NULL && CompilerReloadModule(ty, mod, NULL)) {
                vm_exec(ty, mod->code);
                ok = true;
        }
        // ======================================================================================
End:
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

/* vim: set sts=8 sw=8 expandtab: */
