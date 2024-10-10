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

#include <pcre.h>
#include <curl/curl.h>

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

#include "value.h"
#include "cffi.h"
#include "vm.h"
#include "util.h"
#include "gc.h"
#include "dict.h"
#include "alloc.h"
#include "compiler.h"
#include "test.h"
#include "log.h"
#include "operators.h"
#include "array.h"
#include "str.h"
#include "blob.h"
#include "tags.h"
#include "object.h"
#include "istat.h"
#include "class.h"
#include "utf8.h"
#include "functions.h"
#include "html.h"
#include "curl.h"
#include "sqlite.h"

#define TY_LOG_VERBOSE 1

#define SKIPSTR()    (IP += strlen(IP) + 1)
#define READSTR(s)   do { (s) = IP; SKIPSTR(); } while (0)
#define READVALUE(s) (memcpy(&s, IP, sizeof s), (IP += sizeof s))
#define READJUMP(c)  (((c) = IP), (IP += sizeof (int)))
#define DOJUMP(c)    (IP = (c) + load_int((c)) + sizeof (int))

#if defined(TY_LOG_VERBOSE) && !defined(TY_NO_LOG)
  #define CASE(i) case INSTR_ ## i: expr = compiler_find_expr(ty, IP - 1); LOG("%07ju:%s:%d:%d: " #i, (uintptr_t)(IP - 1) & 0xFFFFFF, expr ? expr->filename : "(unknown)", (expr ? expr->start.line : 0) + 1, (expr ? expr->start.col : 0) + 1);
#else
  #define XCASE(i) case INSTR_ ## i: expr = compiler_find_expr(ty, IP); XLOG("%s:%d:%d: " #i, expr ? expr->filename : "(unknown)", (expr ? expr->start.line : 0) + 1, (expr ? expr->start.col : 0) + 1);
  #define CASE(i) case INSTR_ ## i:
#endif

#define inline __attribute__((always_inline)) inline

#define MatchError \
        do { \
                top(ty)->tags = tags_push(ty, top(ty)->tags, TAG_MATCH_ERR); \
                top(ty)->type |= VALUE_TAGGED; \
                goto Throw; \
        } while (0)

#define X(i) #i
static char const *InstructionNames[] = {
        TY_INSTRUCTIONS
};
#undef X

static char halt = INSTR_HALT;
static char throw = INSTR_THROW;
static char next_fix[] = { INSTR_NONE_IF_NIL, INSTR_RETURN_PRESERVE_CTX };
static char iter_fix[] = { INSTR_SENTINEL, INSTR_RETURN_PRESERVE_CTX };

static char const *MISSING = "__missing__";
static int iExitHooks = -1;

static _Thread_local jmp_buf jb;

_Thread_local int EvalDepth = 0;

static ValueVector Globals;

struct sigfn {
        int sig;
        Value f;
};

#define FRAME(n, fn, from) ((Frame){ .fp = (n), .f = (fn), .ip = (from) })

static SigfnStack sigfns;

static _Thread_local SPStack sp_stack;
static _Thread_local TryStack try_stack;
static _Thread_local vec(ThrowCtx) throw_stack;
static _Thread_local ValueStack defer_stack;
static _Thread_local ValueStack drop_stack;
static _Thread_local int rc;

#define STACK   (ty->stack)
#define IP      (ty->ip)
#define CALLS   (ty->calls)
#define TARGETS (ty->targets)
#define FRAMES  (ty->frames)


#define topN(i) ((topN)(ty, i))

#ifdef TY_ENABLE_PROFILING

bool UseWallTime = false;
FILE *ProfileOut = NULL;

inline static uint64_t
TyThreadCPUTime(void)
{
#ifdef _WIN32
        ULONG64 cycles;
        QueryThreadCycleTime(GetCurrentThread(), &cycles);
        return cycles;
#else
        struct timespec t;
        clock_gettime(CLOCK_THREAD_CPUTIME_ID, &t);
        return 1000000000ULL * t.tv_sec + t.tv_nsec;
#endif
}

inline static uint64_t TyThreadWallTime()
{
#ifdef _WIN32
        LARGE_INTEGER counter;
        LARGE_INTEGER frequency;
        QueryPerformanceCounter(&counter);
        QueryPerformanceFrequency(&frequency);
        return (uint64_t)(counter.QuadPart * 1000000000ULL / frequency.QuadPart);
#else
        struct timespec t;
        clock_gettime(CLOCK_MONOTONIC, &t);
        return 1000000000ULL * t.tv_sec + t.tv_nsec;
#endif
}

inline static uint64_t
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
        Expr const *aExpr = compiler_find_expr(&MainTy, a->ctx);

        //printf("Instruction(%lu) = %s\n", (uintptr_t)bIp, InstructionNames[(uint8_t)((char *)b->ctx)[0]]);
        Expr const *bExpr = compiler_find_expr(&MainTy, b->ctx);

        if (aExpr == bExpr) return 0;
        if (aExpr == NULL) return -1;
        if (bExpr == NULL) return  1;

        uintptr_t aPtr = (uintptr_t)aExpr;
        uintptr_t bPtr = (uintptr_t)bExpr;

        if (aPtr < bPtr) return -1;
        if (aPtr > bPtr) return  1;

        return 0;
}

static _Thread_local char *LastIP;
static _Thread_local uint64_t LastThreadTime;
static _Thread_local uint64_t LastThreadGCTime;
static TyMutex ProfileMutex;
static Dict *Samples;
static Dict *FuncSamples;
istat prof;
#endif

typedef struct {
        ValueStack *stack;
        FrameStack *frames;
        TargetStack *targets;
        ValueStack *defer_stack;
        ValueStack *drop_stack;
        void *root_set;
        AllocList *allocs;
        size_t *memory_used;
} ThreadStorage;

static char const *filename;
static char const *Error;
bool CompileOnly = false;
bool PrintResult = false;

typedef struct thread_group {
        TyMutex Lock;
        TyMutex GCLock;
        vec(TyThread) ThreadList;
        vec(TyMutex *) ThreadLocks;
        vec(ThreadStorage) ThreadStorages;
        vec(atomic_bool *) ThreadStates;
        atomic_bool WantGC;
        TyBarrier GCBarrierStart;
        TyBarrier GCBarrierMark;
        TyBarrier GCBarrierSweep;
        TyBarrier GCBarrierDone;
        TyMutex DLock;
        AllocList DeadAllocs;
        size_t DeadUsed;
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

_Thread_local TyMutex *MyLock;
static _Thread_local atomic_bool *MyState;
static _Thread_local ThreadStorage MyStorage;
static _Thread_local bool GCInProgress;
static _Thread_local bool HaveLock = true;
static _Thread_local uint64_t MyId;

void
MarkStorage(Ty *ty, ThreadStorage const *storage);

static TyThreadReturnValue
vm_run_thread(void *p);

static void
InitializeTY(void)
{
#define X(op, id) intern(&xD.b_ops, id)
        TY_BINARY_OPERATORS;
#undef X
}

int
AbortVM(void)
{
        vm_panic(&MainTy, "oops!");
}

static void
InitializeTy(Ty *ty)
{
        memset(ty, 0, sizeof *ty);
        ty->memory_limit = GC_INITIAL_LIMIT;
}

static void
LockThreads(Ty *ty, int *threads, int n)
{
        for (int i = 0; i < n; ++i) {
                TyMutexLock(MyGroup->ThreadLocks.items[threads[i]]);
        }
}

inline static void
UnlockThreads(Ty *ty, int *threads, int n)
{
        for (int i = 0; i < n; ++i) {
                TyMutexUnlock(MyGroup->ThreadLocks.items[threads[i]]);
        }
}

inline static void
SetState(Ty *ty, bool blocking)
{
        *MyState = blocking;
}

inline static bool
TryFlipTo(atomic_bool *state, bool blocking)
{
        bool expected = !blocking;
        return atomic_compare_exchange_strong(state, &expected, blocking);
}

void
Forget(Ty *ty, Value *v, AllocList *allocs)
{
        size_t n = MyStorage.allocs->count;

        value_mark(ty, v);
        GCForget(ty, MyStorage.allocs, MyStorage.memory_used);

        for (size_t i = MyStorage.allocs->count; i < n; ++i) {
                vec_push_unchecked(ty, *allocs, MyStorage.allocs->items[i]);
        }
}

static void
InitThreadGroup(Ty *ty, ThreadGroup *g)
{
        vec_init(g->ThreadList);
        vec_init(g->ThreadStates);
        vec_init(g->ThreadStorages);
        vec_init(g->ThreadLocks);
        vec_init(g->DeadAllocs);
        TyMutexInit(&g->Lock);
        TyMutexInit(&g->GCLock);
        TyMutexInit(&g->DLock);
        g->WantGC = false;
        g->DeadUsed = 0;

}

static ThreadGroup *
NewThreadGroup(Ty *ty)
{
        ThreadGroup *g = mA(sizeof *g);
        InitThreadGroup(ty, g);
        return g;
}

static void
WaitGC(Ty *ty)
{
        if (GCInProgress)
                return;

        GCLOG("Waiting for GC on thread %llu", TID);

        lGv(false);

#ifdef TY_ENABLE_PROFILING
        uint64_t start = TyThreadTime();
#endif

        while (!*MyState) {
                if (!MyGroup->WantGC && TryFlipTo(MyState, true)) {
                        lTk();
#ifdef TY_ENABLE_PROFILING
                        LastThreadGCTime = TyThreadTime() - start;
#endif
                        return;
                }
        }

        lTk();

        GCLOG("Waiting to mark: %llu", TID);
        TyBarrierWait(&MyGroup->GCBarrierStart);
        GCLOG("Marking: %llu", TID);
        MarkStorage(ty, &MyStorage);

        GCLOG("Waiting to sweep: %llu", TID);
        TyBarrierWait(&MyGroup->GCBarrierMark);
        GCLOG("Sweeping: %llu", TID);
        GCSweep(ty, MyStorage.allocs, MyStorage.memory_used);

        GCLOG("Waiting to continue execution: %llu", TID);
        TyBarrierWait(&MyGroup->GCBarrierSweep);
        TyBarrierWait(&MyGroup->GCBarrierDone);
        GCLOG("Continuing execution: %llu", TID);

#ifdef TY_ENABLE_PROFILING
        LastThreadGCTime = TyThreadTime() - start;
#endif

        dont_printf("Thread %-3llu: %lluus\n", TID, (TyThreadTime() - start) / 1000);
}

void
DoGC(Ty *ty)
{
        GCLOG("Trying to do GC. Used = %zu, DeadUsed = %zu", MemoryUsed, MyGroup->DeadUsed);

        if (!TyMutexTryLock(&MyGroup->GCLock)) {
                GCLOG("Couldn't take GC lock: calling WaitGC(ty) on thread %llu", TID);
                WaitGC(ty);
                return;
        }

#ifdef TY_ENABLE_PROFILING
        uint64_t start = TyThreadTime();
#endif

        GCInProgress = true;

        TyMutexLock(&MyGroup->Lock);

        GCLOG("Doing GC: MyGroup = %p, (%zu threads)", MyGroup, MyGroup->ThreadList.count);

        GCLOG("Took threads lock on thread %llu to do GC", TID);

        GCLOG("Storing true in WantGC on thread %llu", TID);
        MyGroup->WantGC = true;

        static int *blockedThreads;
        static int *runningThreads;
        static size_t capacity;

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
                //GCLOG("Trying to take lock for thread %llu: %p", (long long unsigned)MyGroup->ThreadList.items[i], (void *)MyGroup->ThreadLocks.items[i]);
                TyMutexLock(MyGroup->ThreadLocks.items[i]);
                if (TryFlipTo(MyGroup->ThreadStates.items[i], true)) {
                        //GCLOG("Thread %llu is running", (long long unsigned)MyGroup->ThreadList.items[i]);
                        runningThreads[nRunning++] = i;
                } else {
                        //GCLOG("Thread %llu is blocked", (long long unsigned)MyGroup->ThreadList.items[i]);
                        blockedThreads[nBlocked++] = i;
                }
        }

        GCLOG("nBlocked = %d, nRunning = %d on thread %llu", nBlocked, nRunning, TID);

        TyBarrierInit(&MyGroup->GCBarrierStart, nRunning + 1);
        TyBarrierInit(&MyGroup->GCBarrierMark, nRunning + 1);
        TyBarrierInit(&MyGroup->GCBarrierSweep, nRunning + 1);
        TyBarrierInit(&MyGroup->GCBarrierDone, nRunning + 1);

        UnlockThreads(ty, runningThreads, nRunning);

        TyBarrierWait(&MyGroup->GCBarrierStart);

        for (int i = 0; i < nBlocked; ++i) {
                //GCLOG("Marking thread %llu storage from thread %llu", (long long unsigned)MyGroup->ThreadList.items[blockedThreads[i]], TID);
                MarkStorage(ty, &MyGroup->ThreadStorages.items[blockedThreads[i]]);
        }

        GCLOG("Marking own storage on thread %llu", TID);
        MarkStorage(ty, &MyStorage);

        if (MyGroup == &MainGroup) {
                for (int i = 0; i < Globals.count; ++i) {
                        value_mark(ty, &Globals.items[i]);
                }

                vec(Value const *) *immortal = GCImmortalSet(ty);

                for (int i = 0; i < immortal->count; ++i) {
                        value_mark(ty, immortal->items[i]);
                }
        }

        TyBarrierWait(&MyGroup->GCBarrierMark);

        GCLOG("Storing false in WantGC on thread %llu", TID);
        MyGroup->WantGC = false;

        for (int i = 0; i < nBlocked; ++i) {
                //GCLOG("Sweeping thread %llu storage from thread %llu", (long long unsigned)MyGroup->ThreadList.items[blockedThreads[i]], TID);
                GCSweep(
                        ty,
                        MyGroup->ThreadStorages.items[blockedThreads[i]].allocs,
                        MyGroup->ThreadStorages.items[blockedThreads[i]].memory_used
                );
        }

        GCLOG("Sweeping own storage on thread %llu", TID);
        GCSweep(ty, MyStorage.allocs, MyStorage.memory_used);

        GCLOG("Sweeping objects from dead threads on thread %llu", TID);
        TyMutexLock(&MyGroup->DLock);
        GCSweep(ty, &MyGroup->DeadAllocs, &MyGroup->DeadUsed);
        TyMutexUnlock(&MyGroup->DLock);

        TyBarrierWait(&MyGroup->GCBarrierSweep);

        UnlockThreads(ty, blockedThreads, nBlocked);

        GCLOG("Unlocking ThreadsLock and GCLock. Used = %zu, DeadUsed = %zu", MemoryUsed, MyGroup->DeadUsed);

        TyMutexUnlock(&MyGroup->Lock);
        TyMutexUnlock(&MyGroup->GCLock);

        GCLOG("Unlocked ThreadsLock and GCLock on thread %llu", TID);

        TyBarrierWait(&MyGroup->GCBarrierDone);

        GCInProgress = false;

#ifdef TY_ENABLE_PROFILING
        LastThreadGCTime = TyThreadTime() - start;
#endif

        dont_printf("Thread %-3llu: %lluus\n", TID, (TyThreadTime() - start) / 1000);
}

#define BUILTIN(f)    { .type = VALUE_BUILTIN_FUNCTION, .builtin_function = (f), .tags = 0 }
#define FLOAT(x)      { .type = VALUE_REAL,             .real             = (x), .tags = 0 }
#define INT(k)        { .type = VALUE_INTEGER,          .integer          = (k), .tags = 0 }
#define BOOL_(b)      { .type = VALUE_BOOLEAN,          .boolean          = (b), .tags = 0 }
#include "builtins.h"
#undef INT
#undef FLOAT
#undef BUILTIN
#undef BOOL_

static int builtin_count = sizeof builtins / sizeof builtins[0];

pcre_jit_stack *JITStack = NULL;

inline static void
PopulateGlobals(Ty *ty)
{
        int n = compiler_global_count(ty);

        while (Globals.count < n) {
                Symbol *sym = compiler_global_sym(ty, Globals.count);
                vec_push_unchecked(
                        ty,
                        Globals,
                        IsTopLevel(sym) ? UNINITIALIZED(sym) : NIL
                );
        }
}

static void
add_builtins(Ty *ty, int ac, char **av)
{
        for (int i = 0; i < builtin_count; ++i) {
                compiler_introduce_symbol(ty, builtins[i].module, builtins[i].name);
                if (builtins[i].value.type == VALUE_BUILTIN_FUNCTION) {
                        builtins[i].value.name = builtins[i].name;
                        builtins[i].value.module = builtins[i].module;
                }
                vvP(Globals, builtins[i].value);
        }

        Array *args = vA();
        NOGC(args);

        for (int i = 1; i < ac; ++i)
                vAp(args, STRING_NOGC(av[i], strlen(av[i])));

        compiler_introduce_symbol(ty, "os", "args");
        vvP(Globals, ARRAY(args));

        compiler_introduce_symbol(ty, NULL, "__EXIT_HOOKS__");
        iExitHooks = (int)Globals.count;
        vvP(Globals, ARRAY(vA()));

        compiler_introduce_symbol(ty, "ty", "executable");
        vvP(Globals, this_executable(ty));

#ifdef SIGRTMIN
        /* Add this here because SIGRTMIN doesn't expand to a constant */
        compiler_introduce_symbol(ty, "os", "SIGRTMIN");
        vvP(Globals, INTEGER(SIGRTMIN));
#endif

        /* Add FFI types here because they aren't constant expressions on Windows. */
        compiler_introduce_symbol(ty, "ffi", "char");
        vvP(Globals, PTR(&ffi_type_schar));
        compiler_introduce_symbol(ty, "ffi", "short");
        vvP(Globals, PTR(&ffi_type_sshort));
        compiler_introduce_symbol(ty, "ffi", "int");
        vvP(Globals, PTR(&ffi_type_sint));
        compiler_introduce_symbol(ty, "ffi", "long");
        vvP(Globals, PTR(&ffi_type_slong));
        compiler_introduce_symbol(ty, "ffi", "uchar");
        vvP(Globals, PTR(&ffi_type_uchar));
        compiler_introduce_symbol(ty, "ffi", "ushort");
        vvP(Globals, PTR(&ffi_type_ushort));
        compiler_introduce_symbol(ty, "ffi", "uint");
        vvP(Globals, PTR(&ffi_type_uint));
        compiler_introduce_symbol(ty, "ffi", "ulong");
        vvP(Globals, PTR(&ffi_type_ulong));
        compiler_introduce_symbol(ty, "ffi", "u8");
        vvP(Globals, PTR(&ffi_type_uint8));
        compiler_introduce_symbol(ty, "ffi", "u16");
        vvP(Globals, PTR(&ffi_type_uint16));
        compiler_introduce_symbol(ty, "ffi", "u32");
        vvP(Globals, PTR(&ffi_type_uint32));
        compiler_introduce_symbol(ty, "ffi", "u64");
        vvP(Globals, PTR(&ffi_type_uint64));
        compiler_introduce_symbol(ty, "ffi", "i8");
        vvP(Globals, PTR(&ffi_type_sint8));
        compiler_introduce_symbol(ty, "ffi", "i16");
        vvP(Globals, PTR(&ffi_type_sint16));
        compiler_introduce_symbol(ty, "ffi", "i32");
        vvP(Globals, PTR(&ffi_type_sint32));
        compiler_introduce_symbol(ty, "ffi", "i64");
        vvP(Globals, PTR(&ffi_type_sint64));
        compiler_introduce_symbol(ty, "ffi", "float");
        vvP(Globals, PTR(&ffi_type_float));
        compiler_introduce_symbol(ty, "ffi", "double");
        vvP(Globals, PTR(&ffi_type_double));
        compiler_introduce_symbol(ty, "ffi", "ptr");
        vvP(Globals, PTR(&ffi_type_pointer));
        compiler_introduce_symbol(ty, "ffi", "void");
        vvP(Globals, PTR(&ffi_type_void));

#define X(name) \
        do { \
                compiler_introduce_tag(ty, "ty", #name); \
                vvP(Globals, TAG(Ty ## name)); \
        } while (0);

        TY_AST_NODES

#undef X
}

void
vm_load_c_module(Ty *ty, char const *name, void *p)
{
        struct {
                char const *name;
                Value value;
        } *mod = p;

        int n = 0;
        while (mod[n].name != NULL)
                n += 1;

        for (int i = 0; i < n; ++i) {
                compiler_introduce_symbol(ty, name, mod[i].name);
                vvP(Globals, mod[i].value);
        }
}

inline static Value *
(topN)(Ty *ty, int n)
{
        return &STACK.items[STACK.count - n];
}

inline static Value *
top(Ty *ty)
{
        return topN(1);
}

inline static void
xprint_stack(Ty *ty, int n)
{
        XLOG("STACK: (%zu)", STACK.count);
        for (int i = 0; i < n && i < STACK.count; ++i) {
                if (FRAMES.count > 0 && STACK.count - (i + 1) == vvL(FRAMES)->fp) {
                        XLOG(" -->  %s", value_show(ty, top(ty) - i));
                } else {
                        XLOG("      %s", value_show(ty, top(ty) - i));
                }
        }
}

inline static void
print_stack(Ty *ty, int n)
{
#ifndef TY_NO_LOG
        LOG("STACK: (%zu)", STACK.count);
        for (int i = 0; i < n && i < STACK.count; ++i) {
                if (FRAMES.count > 0 && STACK.count - (i + 1) == vvL(FRAMES)->fp) {
                        LOG(" -->  %s", value_show(ty, top(ty) - i));
                } else {
                        LOG("      %s", value_show(ty, top(ty) - i));
                }
        }
#endif
}

inline static Value
pop(Ty *ty)
{
        Value v = *vvX(STACK);
        LOG("POP: %s", VSC(&v));
        print_stack(ty, 15);
        return v;
}

inline static Value
peek(Ty *ty)
{
        return *topN(1);
}

inline static void
push(Ty *ty, Value v)
{
        xvP(STACK, v);
        LOG("PUSH: %s", value_show(ty, &v));
        print_stack(ty, 10);
}

inline static Value *
local(Ty *ty, int i)
{
        return &STACK.items[vvL(FRAMES)->fp + i];
}

inline static Value *
poptarget(Ty *ty)
{
        Target t = *vvX(TARGETS);
        if (t.gc != NULL) OKGC(t.gc);
        LOG("Popping Target: %p", (void *)t.t);
        return t.t;
}

inline static Value *
peektarget(Ty *ty)
{
        return TARGETS.items[TARGETS.count - 1].t;
}

inline static void
pushtarget(Ty *ty, Value *v, void *gc)
{
        Target t = { .t = v, .gc = gc };
        if (gc != NULL) NOGC(gc);
        vvP(TARGETS, t);
        LOG("TARGETS: (%zu)", TARGETS.count);
        for (int i = 0; i < TARGETS.count; ++i) {
                LOG("    %d: %p", i + 1, (void *)TARGETS.items[i].t);
        }
}

inline static bool
SpecialTarget(Ty *ty)
{
        return (((uintptr_t)TARGETS.items[TARGETS.count - 1].t) & 0x07) != 0;
}


static bool
co_yield(Ty *ty)
{
        if (FRAMES.count == 0 || STACK.count == 0)
                return false;

        int n = FRAMES.items[0].fp;

        if (STACK.items[n - 1].type != VALUE_GENERATOR) {
                return false;
        }

        Generator *gen = STACK.items[n - 1].gen;
        gen->ip = IP;
        gen->frame.count = 0;

        SWAP(SPStack, gen->sps, sp_stack);
        SWAP(TargetStack, gen->targets, TARGETS);
        SWAP(CallStack, gen->calls, CALLS);
        SWAP(FrameStack, gen->frames, FRAMES);
        SWAP(ValueVector, gen->deferred, defer_stack);
        SWAP(ValueVector, gen->to_drop, drop_stack);

        xvPn(gen->frame, STACK.items + n, STACK.count - n - 1);

        STACK.items[n - 1] = peek(ty);
        STACK.count = n;

        vvX(FRAMES);

        IP = *vvX(CALLS);

        return true;
}


inline static Generator *
GetCurrentGenerator(Ty *ty)
{
        int n = FRAMES.items[0].fp;

        if (n == 0 || STACK.items[n - 1].type != VALUE_GENERATOR) {
                return NULL;
        }

        return STACK.items[n - 1].gen;
}

#ifdef TY_RELEASE
inline
#else
__attribute__((optnone, noinline))
#endif
static void
call(Ty *ty, Value const *f, Value const *pSelf, int n, int nkw, bool exec)
{
        int bound = f->info[3];
        int np = f->info[4];
        int irest = ((int16_t *)(f->info + 5))[0];
        int ikwargs = ((int16_t *)(f->info + 5))[1];
        int class = f->info[6];
        char *code = code_of(f);
        int argc = n;

        Value self = (pSelf == NULL) ? NONE : *pSelf;

        Value kwargs = (nkw > 0) ? pop(ty) : NIL;

        /*
         * This is the index of the beginning of the stack frame for this call to f.
         */
        int fp = STACK.count - n;

        /*
         * Default missing arguments to NIL and make space for all of this function's local variables.
         */
        while (n < bound) {
                push(ty, NIL);
                n += 1;
        }

        GC_STOP();

        /*
         * If the function was declared with the form f(..., *extra) then we
         * create an array and add any extra arguments to it.
         */
        if (irest != -1) {
                int nExtra = argc - irest;

                Array *extra = vAn(nExtra * (nExtra > 0));

                for (int i = irest; i < argc; ++i) {
                        extra->items[i - irest] = STACK.items[fp + i];
                }

                for (int i = irest; i < argc; ++i) {
                        STACK.items[fp + i] = NIL;
                }

                STACK.items[fp + irest] = ARRAY(extra);
        }

        if (ikwargs != -1) {
                // FIXME: don't allocate a dict when there are no kwargs
                STACK.items[fp + ikwargs] = (nkw > 0) ? kwargs : DICT(dict_new(ty));
        }

        GC_RESUME();

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
                LOG("setting self = %s", value_show(ty, &self));
                STACK.items[fp + np] = self;
        }

        vec_push_unchecked(ty, FRAMES, FRAME(fp, *f, IP));

        /* Fill in keyword args (overwriting positional args) */
        if (kwargs.type != VALUE_NIL) {
                // FIXME: intern parameter names!!!
                char const *name = name_of(f);
                for (int i = 0; i < np; ++i) {
                        name += strlen(name) + 1;
                        if (i == irest || i == ikwargs) {
                                continue;
                        }
                        Value *arg = dict_get_member(ty, kwargs.dict, name);
                        if (arg != NULL) {
                                *local(ty, i) = *arg;
                        }
                }
        }

        LOG("Calling %s with %d args, bound = %d, self = %s, env size = %d", value_show(ty, f), argc, bound, value_show(ty, &self), f->info[2]);
        print_stack(ty, max(bound + 2, 5));

        if (exec) {
                vec_push_unchecked(ty, CALLS, &halt);
                gP(f);
                Generator *gen = GetCurrentGenerator(ty);
                vm_exec(ty, code);
                if (GetCurrentGenerator(ty) != gen) {
                        zP("sus usage of coroutine yield");
                }
                gX();
        } else {
                vec_push_unchecked(ty, CALLS, IP);
                IP = code;
        }
}

inline static void
call_co(Ty *ty, Value *v, int n)
{
        if (v->gen->ip != code_of(&v->gen->f)) {
                if (n == 0) {
                        vec_push_unchecked(ty, v->gen->frame, NIL);
                } else {
                        vec_nogc_push_n(v->gen->frame, top(ty) - (n - 1), n);
                        STACK.count -= n;
                }
        }

        push(ty, *v);
        call(ty, &v->gen->f, NULL, 0, 0, false);
        STACK.count = vvL(FRAMES)->fp;

        if (v->gen->frames.count == 0) {
                vvP(v->gen->frames, *vvL(FRAMES));
        } else {
                v->gen->frames.items[0] = *vvL(FRAMES);
        }

        int diff = (int)STACK.count - v->gen->fp;
        for (int i = 1; i < v->gen->frames.count; ++i) {
                v->gen->frames.items[i].fp += diff;
        }

        v->gen->fp = STACK.count;

        SWAP(CallStack, v->gen->calls, CALLS);
        SWAP(TargetStack, v->gen->targets, TARGETS);
        SWAP(SPStack, v->gen->sps, sp_stack);
        SWAP(FrameStack, v->gen->frames, FRAMES);
        SWAP(ValueVector, v->gen->deferred, defer_stack);
        SWAP(ValueVector, v->gen->to_drop, drop_stack);

        for (int i = 0; i < v->gen->frame.count; ++i) {
                push(ty, v->gen->frame.items[i]);
        }

        IP = v->gen->ip;
}

uint64_t
MyThreadId(Ty *ty)
{
        return MyId;
}

void
TakeLock(Ty *ty)
{
        GCLOG("Taking MyLock%s", "");
        TyMutexLock(MyLock);
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
        TyMutexUnlock(MyLock);
        HaveLock = false;
}

void
NewThread(Ty *ty, Thread *t, Value *call, Value *name, bool isolated)
{
        lGv(true);

        static _Thread_local atomic_bool created;

        NewThreadCtx *ctx = mrealloc(NULL, sizeof *ctx);
        *ctx = (NewThreadCtx) {
                .ty = ty,
                .ctx = call,
                .name = name,
                .created = &created,
                .t = t,
                .group = isolated ? NewThreadGroup(ty) : MyGroup
        };
        created = false;

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
        GCLOG("AddThread(ty): %llu: taking lock", TID);

        TyMutexLock(&MyGroup->Lock);

        GCLOG("AddThread(ty): %llu: took lock", TID);

        GC_STOP();

        vvP(MyGroup->ThreadList, self);

        MyLock = mrealloc(NULL, sizeof *MyLock);
        TyMutexInit(MyLock);
        TyMutexLock(MyLock);
        vvP(MyGroup->ThreadLocks, MyLock);

        MyStorage = (ThreadStorage) {
                .stack = &STACK,
                .frames = &FRAMES,
                .defer_stack = &defer_stack,
                .drop_stack = &drop_stack,
                .targets = &TARGETS,
                .root_set = GCRootSet(ty),
                .allocs = &ty->allocs,
                .memory_used = &MemoryUsed
        };

        vvP(MyGroup->ThreadStorages, MyStorage);

        MyState = mrealloc(NULL, sizeof *MyState);
        *MyState = false;
        vvP(MyGroup->ThreadStates, MyState);

        GC_RESUME();

        TyMutexUnlock(&MyGroup->Lock);

        GCLOG("AddThread(ty): %llu: finished", TID);
}

static void
CleanupThread(void *ctx)
{
        Ty *ty = ctx;

        GCLOG("Cleaning up thread: %zu bytes in use. DeadUsed = %zu", MemoryUsed, MyGroup->DeadUsed);

        TyMutexLock(&MyGroup->DLock);

        if (MyGroup->DeadUsed + MemoryUsed > MemoryLimit) {
                TyMutexUnlock(&MyGroup->DLock);
                DoGC(ty);
                TyMutexLock(&MyGroup->DLock);
        }

        vec_push_n_unchecked(ty, MyGroup->DeadAllocs, ty->allocs.items, ty->allocs.count);
        MyGroup->DeadUsed += MemoryUsed;

        ty->allocs.count = 0;

        TyMutexUnlock(&MyGroup->DLock);

        lGv(true);

        TyMutexLock(&MyGroup->Lock);

        GCLOG("Got threads lock on thread: %llu -- ready to clean up. Group size = %llu", TID, MyGroup->ThreadList.count);

        for (int i = 0; i < MyGroup->ThreadList.count; ++i) {
                if (MyLock == MyGroup->ThreadLocks.items[i]) {
                        MyGroup->ThreadList.items[i] = *vvX(MyGroup->ThreadList);
                        MyGroup->ThreadLocks.items[i] = *vvX(MyGroup->ThreadLocks);
                        MyGroup->ThreadStorages.items[i] = *vvX(MyGroup->ThreadStorages);
                        MyGroup->ThreadStates.items[i] = *vvX(MyGroup->ThreadStates);
                        break;
                }
        }

        size_t group_remaining = MyGroup->ThreadList.count;

        TyMutexUnlock(&MyGroup->Lock);

        TyMutexDestroy(MyLock);
        free(MyLock);
        free((void *)MyState);
        free(STACK.items);
        mF(CALLS.items);
        mF(FRAMES.items);
        mF(sp_stack.items);
        mF(TARGETS.items);
        mF(try_stack.items);
        mF(throw_stack.items);
        mF(defer_stack.items);
        mF(drop_stack.items);
        free(ty->allocs.items);

        vec(Value const *) *root_set = GCRootSet(ty);
        free(root_set->items);

        if (group_remaining == 0) {
                GCLOG("Cleaning up group %p", (void*)MyGroup);
                TyMutexDestroy(&MyGroup->Lock);
                TyMutexDestroy(&MyGroup->GCLock);
                TyMutexDestroy(&MyGroup->DLock);
                mF(MyGroup->ThreadList.items);
                mF(MyGroup->ThreadLocks.items);
                mF(MyGroup->ThreadStates.items);
                mF(MyGroup->ThreadStorages.items);
                mF(MyGroup->DeadAllocs.items);
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

        MyId = t->i;

        int argc = 0;

        GCLOG("New thread: %llu", TID);

        while (call[argc + 1].type != VALUE_NONE) {
                push(ty, call[++argc]);
        }

        MyGroup = ctx->group;

        AddThread(ty, t->t);

        gP(&call[0]);

        if (name != NULL) {
                push(ty, *name);
                builtin_thread_setname(ty, 1, NULL);
                pop(ty);
        }

#ifndef _WIN32
        pthread_cleanup_push(CleanupThread, ty);
#endif

        *ctx->created = true;

        if (setjmp(jb) != 0) {
                // TODO: do something useful here
                fprintf(stderr, "Thread %llu dying with error: %s\n", TID, ERR);
                OKGC(t);
                t->v = NIL;
        } else {
                t->v = vmC(call, argc);
        }

#ifndef _WIN32
        pthread_cleanup_pop(1);
#else
        CleanupThread(NULL);
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
vm_do_signal(Ty *ty, int sig, siginfo_t *info, void *ctx)
{
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
                push(ty, INTEGER(info->si_value.sival_int));
#else
                push(ty, INTEGER(info->si_fd));
#endif
#endif
                vm_call(ty, &f, 1);
                break;
        default:
                vm_call(ty, &f, 0);
        }
}
#endif

inline static void
AddTupleEntry(Ty *ty, StringVector *names, ValueVector *values, char const *name, Value const *v)
{
        for (int i = 0; i < names->count; ++i) {
                if (names->items[i] != NULL && strcmp(names->items[i], name) == 0) {
                        values->items[i] = *v;
                        return;
                }
        }

        vvP(*names, name);
        vvP(*values, *v);
}

Value
GetMember(Ty *ty, Value v, char const *member, unsigned long h, bool b)
{

        int n;
        Value *vp = NULL, *this;
        BuiltinMethod *func;

        if (v.type & VALUE_TAGGED) for (int tags = v.tags; tags != 0; tags = tags_pop(ty, tags)) {
                vp = tags_lookup_method(ty, tags_first(ty, tags), member, h);
                if (vp != NULL)  {
                        Value *this = mAo(sizeof *this, GC_VALUE);
                        *this = v;
                        this->tags = tags;
                        return METHOD(member, vp, this);
                }
        }

        switch (v.type & ~VALUE_TAGGED) {
        case VALUE_TUPLE:
                vp = tuple_get(&v, member);
                return (vp == NULL) ? NONE : *vp;
        case VALUE_DICT:
                func = get_dict_method(member);
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
                func = get_array_method(member);
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
                func = get_string_method(member);
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
                func = get_blob_method(member);
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
        case VALUE_BUILTIN_FUNCTION:
        case VALUE_BUILTIN_METHOD:
                n = CLASS_FUNCTION;
                goto ClassLookup;
        case VALUE_CLASS:
                switch (v.class) {
                case CLASS_ARRAY:
                        if ((func = get_array_method(member)) != NULL) {
                                return PTR((void *)func);
                        }
                        break;
                case CLASS_STRING:
                        if ((func = get_string_method(member)) != NULL) {
                                return PTR((void *)func);
                        }
                        break;
                case CLASS_DICT:
                        if ((func = get_dict_method(member)) != NULL) {
                                return PTR((void *)func);
                        }
                        break;
                case CLASS_BLOB:
                        if ((func = get_blob_method(member)) != NULL) {
                                return PTR((void *)func);
                        }
                        break;
                }
                vp = class_lookup_static(ty, v.class, member, h);
                if (vp == NULL) {
                        vp = class_lookup_method(ty, v.class, member, h);
                }
                if (vp == NULL) {
                        n = CLASS_CLASS;
                        goto ClassLookup;
                } else {
                        return *vp;
                }
                break;
        case VALUE_OBJECT:
                vp = table_lookup(ty, v.object, member, h);
                if (vp != NULL) {
                        return *vp;
                }
                n = v.class;
ClassLookup:
                vp = class_lookup_getter(ty, n, member, h);
                if (vp != NULL) {
                        return vmC(&METHOD(member, vp, &v), 0);
                }
                vp = class_lookup_method(ty, n, member, h);
                if (vp != NULL) {
                        this = mAo(sizeof *this, GC_VALUE);
                        *this = v;
                        return METHOD(member, vp, this);
                }
                vp = b ? class_method(ty, n, MISSING) : NULL;
                if (vp != NULL) {
                        this = mAo(sizeof (Value [3]), GC_VALUE);
                        this[0] = v;
                        this[1] = STRING_NOGC(member, strlen(member));
                        return METHOD(MISSING, vp, this);
                }
                break;
        case VALUE_TAG:
                vp = tags_lookup_method(ty, v.tag, member, h);
                return (vp == NULL) ? NIL : *vp;
        }

        return NONE;
}

inline static void
DoGeq(Ty *ty)
{
        Value v = BOOLEAN(value_compare(ty, top(ty) - 1, top(ty)) >= 0);
        pop(ty);
        pop(ty);
        push(ty, v);
}

inline static void
DoGt(Ty *ty)
{
        Value v = BOOLEAN(value_compare(ty, top(ty) - 1, top(ty)) > 0);
        pop(ty);
        pop(ty);
        push(ty, v);
}

inline static void
DoLeq(Ty *ty)
{
        Value v = BOOLEAN(value_compare(ty, top(ty) - 1, top(ty)) <= 0);
        pop(ty);
        pop(ty);
        push(ty, v);
}

inline static void
DoLt(Ty *ty)
{
        Value v = BOOLEAN(value_compare(ty, top(ty) - 1, top(ty)) < 0);
        pop(ty);
        pop(ty);
        push(ty, v);
}

inline static void
DoCmp(Ty *ty)
{

        int i = value_compare(ty, top(ty) - 1, top(ty));

        pop(ty);
        pop(ty);

        if (i < 0)
                push(ty, INTEGER(-1));
        else if (i > 0)
                push(ty, INTEGER(1));
        else
                push(ty, INTEGER(0));
}

inline static void
DoEq(Ty *ty)
{
        Value v = BOOLEAN(value_test_equality(ty, top(ty) - 1, top(ty)));
        pop(ty);
        pop(ty);
        push(ty, v);
}

inline static void
DoNeq(Ty *ty)
{
        Value v = BOOLEAN(!value_test_equality(ty, top(ty) - 1, top(ty)));
        pop(ty);
        pop(ty);
        push(ty, v);
}

inline static void
DoBinaryOp(Ty *ty, int n, bool exec)
{
        int i = op_dispatch(n, ClassOf(top(ty) - 1), ClassOf(top(ty)));

        if (i == -1) zP(
                "no matching implementation of %s%s%s\n"
                FMT_MORE "%s left%s: %s"
                FMT_MORE "%sright%s: %s\n",
                TERM(95;1), intern_entry(&xD.b_ops, n)->name, TERM(0),
                TERM(95), TERM(0), VSC(top(ty) - 1),
                TERM(95), TERM(0), VSC(top(ty))
        );

        dont_printf(
                "matching implementation of %s%s%s: %d\n"
                FMT_MORE "%s left%s (%d): %s"
                FMT_MORE "%sright%s (%d): %s\n",
                TERM(95;1), intern_entry(&xD.b_ops, n)->name, TERM(0), i,
                TERM(95), TERM(0), ClassOf(top(ty) - 1), VSC(top(ty) - 1),
                TERM(95), TERM(0), ClassOf(top(ty)),     VSC(top(ty))
        );

        call(ty, &Globals.items[i], NULL, 2, 0, exec);
}

inline static void
DoMutDiv(Ty *ty)
{
        uintptr_t c, p = (uintptr_t)poptarget(ty);
        ValueTable *o;
        Value *vp, *vp2, val, x;
        void *v = vp = (void *)(p & ~0x07);
        unsigned char b;

        switch (p & 0x07) {
        case 0:
                if (vp->type == VALUE_OBJECT && (vp2 = class_method(ty, vp->class, "/=")) != NULL) {
                        gP(vp);
                        call(ty, vp2, vp, 1, 0, true);
                        gX();
                        pop(ty);
                } else {
                        x = pop(ty);
                        if ((val = vm_try_2op(ty, OP_MUT_DIV, vp, &x)).type != VALUE_NONE) {
                                vp = &val;
                        } else {
                                *vp = vm_2op(ty, OP_DIV, vp, &x);
                        }
                }
                push(ty, *vp);
                break;
        case 1:
                FALSE_OR (top(ty)->type != VALUE_INTEGER) {
                        zP("attempt to divide byte by non-integer: %s", value_show_color(ty, top(ty)));
                }
                b = ((struct blob *)TARGETS.items[TARGETS.count].gc)->items[((uintptr_t)vp) >> 3] /= pop(ty).integer;
                push(ty, INTEGER(b));
                break;
        case 2:
                c = (uintptr_t)poptarget(ty);
                o = TARGETS.items[TARGETS.count].gc;
                vp = poptarget(ty);
                call(ty, vp, &OBJECT(o, c), 0, 0, true);
                top(ty)[-1] = vm_2op(ty, OP_DIV, top(ty), top(ty) - 1);
                pop(ty);
                call(ty, v, &OBJECT(o, c), 1, 0, false);
                break;
        default:
                zP("bad target pointer :(");
        }
}
inline static void
DoMutMul(Ty *ty)
{
        uintptr_t c, p = (uintptr_t)poptarget(ty);
        ValueTable *o;
        Value *vp, *vp2, val, x;
        void *v = vp = (void *)(p & ~0x07);
        unsigned char b;

        switch (p & 0x07) {
        case 0:
                if (vp->type == VALUE_OBJECT && (vp2 = class_method(ty, vp->class, "*=")) != NULL) {
                        gP(vp);
                        call(ty, vp2, vp, 1, 0, true);
                        gX();
                        pop(ty);
                } else {
                        x = pop(ty);
                        if ((val = vm_try_2op(ty, OP_MUT_MUL, vp, &x)).type != VALUE_NONE) {
                                vp = &val;
                        } else {
                                *vp = vm_2op(ty, OP_MUL, vp, &x);
                        }
                }
                push(ty, *vp);
                break;
        case 1:
                FALSE_OR (top(ty)->type != VALUE_INTEGER) {
                        zP("attempt to multiply byte by non-integer");
                }
                b = ((struct blob *)TARGETS.items[TARGETS.count].gc)->items[((uintptr_t)vp) >> 3] *= pop(ty).integer;
                push(ty, INTEGER(b));
                break;
        case 2:
                c = (uintptr_t)poptarget(ty);
                o = TARGETS.items[TARGETS.count].gc;
                vp = poptarget(ty);
                call(ty, vp, &OBJECT(o, c), 0, 0, true);
                top(ty)[-1] = vm_2op(ty, OP_MUL, top(ty), top(ty) - 1);
                pop(ty);
                call(ty, v, &OBJECT(o, c), 1, 0, false);
                break;
        default:
                zP("bad target pointer :(");
        }
}

inline static void
DoMutSub(Ty *ty)
{
        uintptr_t c, p = (uintptr_t)poptarget(ty);
        ValueTable *o;
        Value *vp, *vp2, x, val;
        void *v = vp = (void *)(p & ~0x07);
        unsigned char b;

        switch (p & 0x07) {
        case 0:
                if (vp->type == VALUE_DICT) {
                        FALSE_OR (top(ty)->type != VALUE_DICT)
                                zP("attempt to subtract non-dict from dict");
                        dict_subtract(ty, vp, 1, NULL);
                        pop(ty);
                } else if (vp->type == VALUE_OBJECT && (vp2 = class_method(ty, vp->class, "-=")) != NULL) {
                        gP(vp);
                        call(ty, vp2, vp, 1, 0, true);
                        gX();
                        pop(ty);
                } else {
                        x = pop(ty);
                        if ((val = vm_try_2op(ty, OP_MUT_SUB, vp, &x)).type != VALUE_NONE) {
                                vp = &val;
                        } else {
                                *vp = vm_2op(ty, OP_SUB, vp, &x);
                        }
                }
                push(ty, *vp);
                break;
        case 1:
                FALSE_OR (top(ty)->type != VALUE_INTEGER) {
                        zP("attempt to subtract non-integer from byte");
                }
                b = ((struct blob *)TARGETS.items[TARGETS.count].gc)->items[((uintptr_t)vp) >> 3] -= pop(ty).integer;
                push(ty, INTEGER(b));
                break;
        case 2:
                c = (uintptr_t)poptarget(ty);
                o = TARGETS.items[TARGETS.count].gc;
                vp = poptarget(ty);
                call(ty, vp, &OBJECT(o, c), 0, 0, true);
                top(ty)[-1] = vm_2op(ty, OP_SUB, top(ty), top(ty) - 1);
                pop(ty);
                call(ty, v, &OBJECT(o, c), 1, 0, false);
                break;
        default:
                zP("bad target pointer :(");
        }
}

inline static void
DoMutAdd(Ty *ty)
{
        uintptr_t c, p = (uintptr_t)poptarget(ty);
        ValueTable *o;
        Value *vp, val, x;
        void *v = vp = (void *)(p & ~0x07);
        unsigned char b;

        switch (p & 0x07) {
        case 0:
                if (vp->type == VALUE_ARRAY) {
                        FALSE_OR (top(ty)->type != VALUE_ARRAY)
                                zP("attempt to add non-array to array");
                        value_array_extend(ty, vp->array, top(ty)->array);
                        pop(ty);
                } else if (vp->type == VALUE_DICT) {
                        FALSE_OR (top(ty)->type != VALUE_DICT)
                                zP("attempt to add non-dict to dict");
                        DictUpdate(ty, vp->dict, top(ty)->dict);
                        pop(ty);
                } else {
                        x = pop(ty);
                        if ((val = vm_try_2op(ty, OP_MUT_ADD, vp, &x)).type != VALUE_NONE) {
                                vp = &val;
                        } else {
                                *vp = vm_2op(ty, OP_ADD, vp, &x);
                        }
                }
                push(ty, *vp);
                break;
        case 1:
                FALSE_OR (top(ty)->type != VALUE_INTEGER) {
                        zP("attempt to add non-integer to byte");
                }
                b = ((struct blob *)TARGETS.items[TARGETS.count].gc)->items[((uintptr_t)vp) >> 3] += pop(ty).integer;
                push(ty, INTEGER(b));
                break;
        case 2:
                c = (uintptr_t)poptarget(ty);
                o = TARGETS.items[TARGETS.count].gc;
                vp = poptarget(ty);
                call(ty, vp, &OBJECT(o, c), 0, 0, true);
                top(ty)[-1] = vm_2op(ty, OP_ADD, top(ty), top(ty) - 1);
                pop(ty);
                call(ty, v, &OBJECT(o, c), 1, 0, false);
                break;
        default:
                zP("bad target pointer :(");
        }
}

#ifndef TY_RELEASE
__attribute__((noinline))
#else
inline
#endif
static void
DoAssign(Ty *ty)
{
        uintptr_t c, p = (uintptr_t)poptarget(ty);
        void *v = (void *)(p & ~0x07);
        ValueTable *o;

        switch (p & 0x07) {
        case 0:
                *(Value *)v = peek(ty);
                break;
        case 1:
                ((struct blob *)TARGETS.items[TARGETS.count].gc)->items[((uintptr_t)v >> 3)] = peek(ty).integer;
                break;
        case 2:
                c = (uintptr_t)poptarget(ty);
                o = TARGETS.items[TARGETS.count].gc;
                poptarget(ty);
                call(ty, v, &OBJECT(o, c), 1, 0, false);
                break;
        default:
                zP("bad target pointer :(");
        }
}

inline static void
DoTag(Ty *ty, int tag, int n, Value *kws)
{
        if (n == 1 && kws == NULL) {
                top(ty)->tags = tags_push(ty, top(ty)->tags, tag);
                top(ty)->type |= VALUE_TAGGED;
        } else {
                GC_STOP();
                Value v = builtin_tuple(ty, n, kws);
                STACK.count -= n;
                v.type |= VALUE_TAGGED;
                v.tags = tags_push(ty, v.tags, tag);
                push(ty, v);
                GC_RESUME();
        }
}

#ifndef TY_RELEASE
__attribute__((noinline))
#else
inline
#endif
static void
DoDrop(Ty *ty)
{
        Value group = *vvL(drop_stack);

        for (int i = 0; i < group.array->count; ++i) {
                Value v = group.array->items[i];
                if (v.type != VALUE_OBJECT)
                        continue;
                Value *f = class_method(ty, v.class, "__drop__");
                if (f == NULL)
                        continue;
                vm_call_method(ty, &v, f, 0);
        }

        vvX(drop_stack);
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
                        if (v->names == NULL || v->names[i] == NULL) {
                                dict_put_value(ty, d, INTEGER(i), v->items[i]);
                        } else {
                                dict_put_member(ty, d, v->names[i], v->items[i]);
                        }
                }
                return;
        }

        // FIXME: What else should be allowed here?
}

inline static struct try **
GetCurrentTry(Ty *ty)
{
        for (int i = 0; i < try_stack.count; ++i) {
                struct try **t = vvL(try_stack) - i;
                if ((*t)->state == TRY_TRY || (*t)->state == TRY_FINALLY) {
                        return t;
                }
        }

        return NULL;
}

Value
vm_try_exec(Ty *ty, char *code)
{
        jmp_buf jb_;
        memcpy(&jb_, &jb, sizeof jb_);

        size_t nframes = FRAMES.count;

        // FIXME: don't need to allocate a new STACK
        TryStack ts = try_stack;
        vec_init(try_stack);

        char *save = IP;

        if (setjmp(jb) != 0) {
                memcpy(&jb, &jb_, sizeof jb_);
                FRAMES.count = nframes;
                try_stack = ts;
                IP = save;
                push(ty, vSc(ERR, strlen(ERR)));
                top(ty)->tags = tags_push(ty, 0, gettag(ty, NULL, "Err"));
                top(ty)->type |= VALUE_TAGGED;
                vm_exec(ty, &throw);
                // unreachable
        }

        vm_exec(ty, code);

        memcpy(&jb, &jb_, sizeof jb_);
        FRAMES.count = nframes;
        try_stack = ts;
        IP = save;

        return pop(ty);
}

void
vm_exec(Ty *ty, char *code)
{
        char *save = IP;
        IP = code;

        uintptr_t s, off;
        intmax_t k;
        bool b = false, tco = false;
        float f;
        int n, nkw = 0, i, j, tag;
        unsigned long h;

        bool AutoThis = false;

        Value v, key, value, container, subscript, *vp, *vp2;
        char *str;
        char const *method, *member;

        BuiltinMethod *func;

#ifndef TY_RELEASE
        Expr *expr;
#endif

        PopulateGlobals(ty);

#ifdef TY_ENABLE_PROFILING
        char *StartIPLocal = LastIP;
#endif

        for (;;) {
        if (ty->GC_OFF_COUNT == 0 && MyGroup->WantGC) {
                WaitGC(ty);
        }
        for (int N = 0; N < 32; ++N) {
        NextInstruction:
#ifdef TY_ENABLE_PROFILING
                if (Samples != NULL) {
                        uint64_t now = TyThreadTime();

                        if (StartIPLocal != LastIP && LastThreadTime != 0 && *LastIP != INSTR_HALT &&
                            LastIP != next_fix && LastIP != iter_fix && LastIP != next_fix + 1 &&
                            LastIP != iter_fix + 1 && LastIP != &throw) {

                                uint64_t dt = now - LastThreadTime;

                                TyMutexLock(&ProfileMutex);

                                istat_add(&prof, LastIP, dt);

                                if (llabs((intptr_t)LastIP - (intptr_t)10754527022) > 10000000L) {
                                        //raise(SIGTRAP);
                                }

                                if (LastThreadGCTime > 0) {
                                        Value *count = dict_put_key_if_not_exists(ty, FuncSamples, PTR((void *)GC_ENTRY));
                                        if (count->type == VALUE_NIL) {
                                                *count = INTEGER(LastThreadGCTime);
                                        } else {
                                                count->integer += LastThreadGCTime;
                                        }
                                        LastThreadGCTime = 0;
                                }

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

                                TyMutexUnlock(&ProfileMutex);
                        }
                        LastIP = IP;
                        LastThreadTime = now;
                }
#endif
                switch ((unsigned char)*IP++) {
                CASE(NOP)
                        continue;
                CASE(LOAD_LOCAL)
                        READVALUE(n);
#ifndef TY_NO_LOG
                        LOG("Loading local: %s (%d)", IP, n);
                        SKIPSTR();
#endif
                        push(ty, *local(ty, n));
                        break;
                CASE(LOAD_REF)
                        READVALUE(n);
#ifndef TY_NO_LOG
                        LOG("Loading ref: %s (%d)", IP, n);
                        SKIPSTR();
#endif
                        vp = local(ty, n);
                        if (vp->type == VALUE_REF) {
                                push(ty, *(Value *)vp->ptr);
                        } else {
                                push(ty, *vp);
                        }
                        break;
                CASE(LOAD_CAPTURED)
                        READVALUE(n);
#ifndef TY_NO_LOG
                        LOG("Loading capture: %s (%d) of %s", IP, n, value_show(ty, &vvL(FRAMES)->f));
                        SKIPSTR();
#endif

                        push(ty, *vvL(FRAMES)->f.env[n]);
                        break;
                CASE(LOAD_GLOBAL)
                        READVALUE(n);
#ifndef TY_NO_LOG
                        LOG("Loading global: %s (%d)", IP, n);
                        SKIPSTR();
#endif
                        //printf("n=%d\n", n);
                        push(ty, Globals.items[n]);
                        break;
                CASE(CHECK_INIT)
                        if (top(ty)->type == VALUE_UNINITIALIZED) {
                                // This will panic
                                value_show(ty, top(ty));
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
                CASE(EXEC_CODE)
                        READVALUE(s);
                        vm_exec(ty, (char *) s);
                        break;
                CASE(DUP)
                        push(ty, peek(ty));
                        break;
                CASE(JUMP)
                        READVALUE(n);
                        IP += n;
                        break;
                CASE(JUMP_IF)
                        READVALUE(n);
                        v = pop(ty);
                        if (value_truthy(ty, &v)) {
                                IP += n;
                        }
                        break;
                CASE(JUMP_IF_NOT)
                        READVALUE(n);
                        v = pop(ty);
                        if (!value_truthy(ty, &v)) {
                                IP += n;
                        }
                        break;
                CASE(JUMP_IF_NONE)
                        READVALUE(n);
                        if (top(ty)[-1].type == VALUE_NONE) {
                                IP += n;
                        }
                        break;
                CASE(JUMP_IF_NIL)
                        READVALUE(n);
                        v = pop(ty);
                        if (v.type == VALUE_NIL) {
                                IP += n;
                        }
                        break;
                CASE(TARGET_GLOBAL)
                TargetGlobal:
                        READVALUE(n);
                        LOG("Global: %d", (int)n);
                        while (Globals.count <= n)
                                vec_push_unchecked(ty, Globals, NIL);
                        pushtarget(ty, &Globals.items[n], NULL);
                        break;
                CASE(TARGET_LOCAL)
                        if (FRAMES.count == 0)
                                goto TargetGlobal;
                        READVALUE(n);
                        LOG("Targeting %d", n);
                        pushtarget(ty, local(ty, n), NULL);
                        break;
                CASE(TARGET_REF)
                        READVALUE(n);
                        vp = local(ty, n);
                        if (vp->type == VALUE_REF) {
                                pushtarget(ty, (Value *)vp->ptr, NULL);
                        } else {
                                pushtarget(ty, vp, NULL);
                        }
                        break;
                CASE(TARGET_CAPTURED)
                        READVALUE(n);
#ifndef TY_NO_LOG
                        LOG("Loading capture: %s (%d) of %s", IP, n, value_show(ty, &vvL(FRAMES)->f));
                        SKIPSTR();
#endif
                        pushtarget(ty, vvL(FRAMES)->f.env[n], NULL);
                        break;
                CASE(TARGET_MEMBER)
                        READSTR(member);
                        READVALUE(h);

                        v = pop(ty);

                        if (v.type == VALUE_OBJECT) {
                                vp = class_lookup_setter(ty, v.class, member, h);
                                if (vp != NULL) {
                                        char const *pound = strchr(member, '#');
                                        if (pound == NULL) {
                                                vp2 = class_lookup_getter(ty, v.class, member, h);
                                        } else {
                                                char buffer[128];
                                                int n = min(pound - member, 127);
                                                memcpy(buffer, member, n);
                                                buffer[n] = '\0';
                                                vp2 = class_lookup_getter(ty, v.class, buffer, strhash(buffer));
                                        }
                                        FALSE_OR (vp2 == NULL) {
                                                zP(
                                                        "class %s%s%s needs a getter for %s%s%s!",
                                                        TERM(33),
                                                        class_name(ty, v.class),
                                                        TERM(0),
                                                        TERM(34),
                                                        member,
                                                        TERM(0)
                                                );
                                        }
                                        pushtarget(ty, vp2, NULL);
                                        pushtarget(ty, (Value *)(uintptr_t)v.class, v.object);
                                        pushtarget(ty, (Value *)(((uintptr_t)vp) | 2), NULL);
                                        break;
                                }
                                vp = table_lookup(ty, v.object, member, h);
                                if (vp != NULL) {
                                        pushtarget(ty, vp, v.object);
                                } else {
                                        pushtarget(ty, table_add(ty, v.object, member, h, NIL), v.object);
                                }
                        } else if (v.type == VALUE_TUPLE) {
                                vp = tuple_get(&v, member);
                                if (vp == NULL) {
                                        value = v;
                                        goto BadTupleMember;
                                }
                                pushtarget(ty, vp, v.items);
                        } else {
                                zP("assignment to member of non-object");
                        }
                        break;
                CASE(TARGET_SUBSCRIPT)
                        subscript = top(ty)[0];
                        container = top(ty)[-1];

                        if (container.type == VALUE_ARRAY) {
                                FALSE_OR (subscript.type != VALUE_INTEGER)
                                        zP("non-integer array index used in subscript assignment");
                                if (subscript.integer < 0)
                                        subscript.integer += container.array->count;
                                if (subscript.integer < 0 || subscript.integer >= container.array->count) {
                                        // TODO: Not sure which is the best behavior here
                                        push(ty, TAG(gettag(ty, NULL, "IndexError")));
                                        goto Throw;
                                        zP("array index out of range in subscript expression");
                                }
                                pushtarget(ty, &container.array->items[subscript.integer], container.array);
                        } else if (container.type == VALUE_DICT) {
                                pushtarget(ty, dict_put_key_if_not_exists(ty, container.dict, subscript), container.dict);
                        } else if (container.type == VALUE_BLOB) {
                                FALSE_OR (subscript.type != VALUE_INTEGER) {
                                        zP("non-integer blob index used in subscript assignment");
                                }
                                if (subscript.integer < 0) {
                                        subscript.integer += container.blob->count;
                                }
                                if (subscript.integer < 0 || subscript.integer >= container.blob->count) {
                                        // TODO: Not sure which is the best behavior here
                                        push(ty, TAG(gettag(ty, NULL, "IndexError")));
                                        goto Throw;
                                        zP("blob index out of range in subscript expression");
                                }
                                pushtarget(ty, (Value *)((((uintptr_t)(subscript.integer)) << 3) | 1) , container.blob);
                        } else if (container.type == VALUE_PTR && IP[0] == INSTR_ASSIGN) {
                                if (subscript.type != VALUE_INTEGER) {
                                        zP("non-integer pointer offset used in subscript assignment: %s", value_show_color(ty, &subscript));
                                }
                                Value p = vm_2op(ty, OP_ADD, &container, &subscript);
                                pop(ty);
                                pop(ty);
                                v = pop(ty);
                                push(ty, p);
                                push(ty, v);
                                v = cffi_store(ty, 2, NULL);
                                pop(ty);
                                pop(ty);
                                push(ty, v);
                                IP += 1;
                                break;
                        } else {
                                zP("attempt to perform subscript assignment on something other than an object or array: %s", value_show_color(ty, &container));
                        }

                        pop(ty);
                        pop(ty);

                        break;
                CASE(ASSIGN)
                        DoAssign(ty);
                        break;
                CASE(MAYBE_ASSIGN)
                        vp = poptarget(ty);
                        if (vp->type == VALUE_NIL)
                                *vp = peek(ty);
                        break;
                CASE(TAG_PUSH)
                        READVALUE(tag);
                        top(ty)->tags = tags_push(ty, top(ty)->tags, tag);
                        top(ty)->type |= VALUE_TAGGED;
                        break;
                CASE(ARRAY_REST)
                        READJUMP(code);
                        READVALUE(i);
                        READVALUE(j);
                        if (top(ty)->type != VALUE_ARRAY || top(ty)->array->count < i + j) {
                                DOJUMP(code);
                        } else {
                                Array *rest = vA();
                                NOGC(rest);
                                vvPn(*rest, top(ty)->array->items + i, top(ty)->array->count - (i + j));
                                *poptarget(ty) = ARRAY(rest);
                                OKGC(rest);
                        }
                        break;
                CASE(TUPLE_REST)
                        READJUMP(code);
                        READVALUE(i);
                        vp = poptarget(ty);
                        if (top(ty)->type != VALUE_TUPLE) {
                                DOJUMP(code);
                        } else {
                                int count = top(ty)->count - i;
                                Value *rest = mAo(count * sizeof (Value), GC_TUPLE);
                                memcpy(rest, top(ty)->items + i, count * sizeof (Value));
                                *vp = TUPLE(rest, NULL, count, false);
                        }
                        break;
                CASE(RECORD_REST)
                        READJUMP(code);
                        READVALUE(j);
                        if (top(ty)->type != VALUE_TUPLE) {
                                DOJUMP(code);
                        } else {
                                v = peek(ty);

                                vec(char const *) names = {0};
                                vec(int) indices = {0};

                                for (int i = 0; i < v.count; ++i) {
                                        if (v.names == NULL || v.names[i] == NULL)
                                                continue;
                                        char const *name = memmem(IP, j, v.names[i], strlen(v.names[i]) + 1);
                                        if (name == NULL) {
                                                vvP(names, v.names[i]);
                                                vvP(indices, i);
                                        }
                                }

                                value = vT(names.count);

                                if (value.items != NULL) { NOGC(value.items); }
                                value.names = mAo(value.count * sizeof (char *), GC_TUPLE);
                                if (value.items != NULL) { NOGC(value.items); }

                                memcpy(value.names, names.items, value.count * sizeof (char *));
                                // FIXME: i think we may need to clone all of the individual names

                                for (int i = 0; i < value.count; ++i) {
                                        value.items[i] = v.items[indices.items[i]];
                                }

                                *poptarget(ty) = value;

                                IP += j;
                        }
                        break;
                CASE(THROW_IF_NIL)
                        if (top(ty)->type == VALUE_NIL) {
                                MatchError;
                        }
                        break;
                CASE(UNTAG_OR_DIE)
                        READVALUE(tag);
                        if (!tags_same(ty, tags_first(ty, top(ty)->tags), tag)) {
                                MatchError;
                        } else {
                                top(ty)->tags = tags_pop(ty, top(ty)->tags);
                                top(ty)->type &= ~VALUE_TAGGED;
                        }
                        break;
                CASE(STEAL_TAG)
                        vp = poptarget(ty);
                        if (top(ty)->type & VALUE_TAGGED) {
                                *vp = TAG(tags_first(ty, top(ty)->tags));
                                if ((top(ty)->tags = tags_pop(ty, top(ty)->tags)) == 0) {
                                        top(ty)->type &= ~VALUE_TAGGED;
                                }
                        } else {
                                MatchError;
                        }
                        break;
                CASE(TRY_STEAL_TAG)
                        READVALUE(n);
                        vp = poptarget(ty);
                        if (top(ty)->type & VALUE_TAGGED) {
                                *vp = TAG(tags_first(ty, top(ty)->tags));
                                if ((top(ty)->tags = tags_pop(ty, top(ty)->tags)) == 0) {
                                        top(ty)->type &= ~VALUE_TAGGED;
                                }
                        } else {
                                IP += n;
                        }
                        break;
                CASE(BAD_MATCH)
                        MatchError;
                CASE(BAD_DISPATCH);
                        push(ty, TAG(gettag(ty, NULL, "DispatchError")));
                        vvX(FRAMES);
                        IP = *vvX(CALLS);
                        goto Throw;
                CASE(BAD_CALL)
                        v = peek(ty);

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
                                value_show(ty, &v),
                                TERM(22),
                                TERM(39)
                        );
                        break;
                CASE(BAD_ASSIGN)
                        v = peek(ty);
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
                                value_show(ty, &v),
                                TERM(22),
                                TERM(39)
                        );
                        break;
                CASE(THROW)
Throw:
                        vvP(throw_stack, ((ThrowCtx) {
                                .ctxs = FRAMES.count,
                                .ip = IP
                        }));
                        // Fallthrough
                CASE(RETHROW)
                {
                        struct try **tp = GetCurrentTry(ty);

                        if (tp == NULL) {
                                ThrowCtx c = *vvX(throw_stack);

                                FRAMES.count = c.ctxs;
                                IP = (char *)c.ip;

                                zP("uncaught exception: %s%s%s", TERM(31), value_show_color(ty, top(ty)), TERM(39));
                        }

                        struct try *t = *tp;

                        if (t->state == TRY_FINALLY) {
                                zP(
                                        "an exception was thrown while handling another exception: %s%s%s",
                                        TERM(31), value_show_color(ty, top(ty)), TERM(39)
                                );
                        }

                        t->state = TRY_THROW;
                        t->executing = true;

                        v = pop(ty);

                        for (struct try **t_ = vvL(try_stack); t_ != tp; --t_) {
                                t_[0]->state = TRY_FINALLY;
                                if (t_[0]->finally != NULL) {
                                        vm_exec(ty, t_[0]->finally);
                                }
                                while (drop_stack.count > t_[0]->ds) {
                                        DoDrop(ty);
                                }
                        }

                        while (drop_stack.count > t->ds) {
                                DoDrop(ty);
                        }

                        try_stack.count -= vvL(try_stack) - tp;

                        STACK.count = t->sp;

                        push(ty, SENTINEL);
                        push(ty, v);

                        sp_stack.count = t->nsp;
                        FRAMES.count = t->ctxs;
                        TARGETS.count = t->ts;
                        CALLS.count = t->cs;
                        IP = t->catch;


                        gc_truncate_root_set(ty, t->gc);

                        longjmp(t->jb, 1);
                        /* unreachable */
                }
                CASE(FINALLY)
                {
                        struct try *t = *vvX(try_stack);
                        t->state = TRY_FINALLY;
                        if (t->finally != NULL)
                                vm_exec(ty, t->finally);
                        break;
                }
                CASE(POP_TRY)
                        --try_stack.count;
                        break;
                CASE(RESUME_TRY)
                        vvL(try_stack)[0]->state = TRY_TRY;
                        break;
                CASE(CATCH)
                        --throw_stack.count;
                        vvL(try_stack)[0]->state = TRY_CATCH;
                        break;
                CASE(TRY)
                {
                        READVALUE(n);
                        struct try *t;
                        size_t n_tstk = try_stack.count;
                        if (n_tstk == try_stack.capacity) {
                                do {
                                        t = mrealloc(NULL, sizeof *t);
                                        vvP(try_stack, t);
                                } while (try_stack.count != try_stack.capacity);
                                try_stack.count = n_tstk;
                        }
                        t = try_stack.items[try_stack.count++];
                        if (setjmp(t->jb) != 0) {
                                break;
                        }
                        t->catch = IP + n;
                        READVALUE(n);
                        t->finally = (n == -1) ? NULL : IP + n;
                        READVALUE(n);
                        t->end = (n == -1) ? NULL : IP + n;
                        t->sp = STACK.count;
                        t->gc = gc_root_set_count(ty);
                        t->cs = CALLS.count;
                        t->ts = TARGETS.count;
                        t->ds = drop_stack.count;
                        t->ctxs = FRAMES.count;
                        t->nsp = sp_stack.count;
                        t->executing = false;
                        t->state = TRY_TRY;
                        break;
                }
                CASE(DROP)
                        DoDrop(ty);
                        break;
                CASE(PUSH_DROP_GROUP)
                        vec_push_unchecked(ty, drop_stack, ARRAY(vA()));
                        break;
                CASE(PUSH_DROP)
                        vec_push_unchecked(ty, *vvL(drop_stack)->array, peek(ty));
                        break;
                CASE(PUSH_DEFER_GROUP)
                        vec_push_unchecked(ty, defer_stack, ARRAY(vA()));
                        break;
                CASE(DEFER)
                        v = pop(ty);
                        vAp(vvL(defer_stack)->array, v);
                        break;
                CASE(CLEANUP)
                        v = *vvL(defer_stack);
                        for (int i = 0; i < v.array->count; ++i) {
                                vmC(&v.array->items[i], 0);
                        }
                        vvX(defer_stack);
                        break;
                CASE(ENSURE_LEN)
                        READJUMP(code);
                        READVALUE(i);
                        if (top(ty)->type != VALUE_ARRAY || top(ty)->array->count > i) {
                                DOJUMP(code);
                        }
                        break;
                CASE(ENSURE_LEN_TUPLE)
                        READJUMP(code);
                        READVALUE(i);
                        if (top(ty)->type != VALUE_TUPLE || top(ty)->count > i) {
                                DOJUMP(code);
                        }
                        break;
                CASE(ENSURE_EQUALS_VAR)
                        v = pop(ty);
                        READVALUE(n);
                        if (!value_test_equality(ty, top(ty), &v))
                                IP += n;
                        break;
                CASE(TRY_ASSIGN_NON_NIL)
                        READVALUE(n);
                        vp = poptarget(ty);
                        if (top(ty)->type == VALUE_NIL)
                                IP += n;
                        else
                                *vp = peek(ty);
                        break;
                CASE(TRY_REGEX)
                        READJUMP(code);
                        READVALUE(s);
                        v = REGEX((struct regex *) s);
                        value = value_apply_callable(ty, &v, top(ty));
                        vp = poptarget(ty);
                        if (value.type == VALUE_NIL) {
                                DOJUMP(code);
                        } else if (value.type == VALUE_STRING) {
                                *vp = value;
                        } else {
                                for (int i = 0; i < value.array->count; ++i) {
                                        vp[i] = value.array->items[i];
                                }
                        }
                        break;
                CASE(ENSURE_DICT)
                        READVALUE(n);
                        if (top(ty)->type != VALUE_DICT) {
                                IP += n;
                        }
                        break;
                CASE(ENSURE_CONTAINS)
                        READVALUE(n);
                        v = pop(ty);
                        if (!dict_has_value(ty, top(ty)->dict, &v)) {
                                IP += n;
                        }
                        break;
                CASE(ENSURE_SAME_KEYS)
                        READVALUE(n);
                        v = pop(ty);
                        if (!dict_same_keys(ty, top(ty)->dict, v.dict)) {
                                IP += n;
                        }
                        break;
                CASE(TRY_INDEX)
                        READJUMP(code);
                        READVALUE(i);
                        READVALUE(b);
                        //LOG("trying to index: %s", value_show(ty, top(ty)));
                        if (top(ty)->type != VALUE_ARRAY) {
                                DOJUMP(code);
                                break;
                        }
                        if (i < 0) {
                                i += top(ty)->array->count;
                        }
                        if (top(ty)->array->count <= i) {
                                if (b) {
                                        DOJUMP(code);
                                } else {
                                        push(ty, NIL);
                                }
                        } else {
                                push(ty, top(ty)->array->items[i]);
                        }
                        break;
                CASE(TRY_INDEX_TUPLE)
                        READJUMP(code);
                        READVALUE(i);
                        if (top(ty)->type != VALUE_TUPLE || top(ty)->count <= i) {
                                DOJUMP(code);
                        } else {
                                push(ty, top(ty)->items[i]);
                        }
                        break;
                CASE(TRY_TUPLE_MEMBER)
                        READJUMP(code);
                        READVALUE(b);
                        READSTR(str);

                        if (top(ty)->type != VALUE_TUPLE) {
                                DOJUMP(code);
                                break;
                        }

                        for (int i = 0; top(ty)->names != NULL && i < top(ty)->count; ++i) {
                                if (top(ty)->names[i] != NULL && strcmp(top(ty)->names[i], str) == 0) {
                                        push(ty, top(ty)->items[i]);
                                        goto NextInstruction;
                                }
                        }

                        if (!b) {
                                push(ty, NIL);
                                goto NextInstruction;
                        }

                        DOJUMP(code);

                        break;
                CASE(TRY_TAG_POP)
                        READJUMP(code);
                        READVALUE(tag);
                        if (!(top(ty)->type & VALUE_TAGGED) || tags_first(ty, top(ty)->tags) != tag) {
                                DOJUMP(code);
                        } else {
                                top(ty)->tags = tags_pop(ty, top(ty)->tags);
                                if (top(ty)->tags == 0) {
                                        top(ty)->type &= ~VALUE_TAGGED;
                                }
                        }
                        break;
                CASE(POP)
                        pop(ty);
                        break;
                CASE(UNPOP)
                        STACK.count += 1;
                        break;
                CASE(INTEGER)
                        READVALUE(k);
                        push(ty, INTEGER(k));
                        break;
                CASE(REAL)
                        READVALUE(f);
                        push(ty, REAL(f));
                        break;
                CASE(BOOLEAN)
                        READVALUE(b);
                        push(ty, BOOLEAN(b));
                        break;
                CASE(STRING)
                        n = strlen(IP);
                        push(ty, STRING_NOGC(IP, n));
                        IP += n + 1;
                        break;
                CASE(CLASS)
                        READVALUE(tag);
                        push(ty, CLASS(tag));
                        break;
                CASE(TAG)
                        READVALUE(tag);
                        push(ty, TAG(tag));
                        break;
                CASE(REGEX)
                        READVALUE(s);
                        v = REGEX((struct regex const *) s);
                        push(ty, v);
                        break;
                CASE(ARRAY)
                        n = STACK.count - *vvX(sp_stack);

                        v = ARRAY(n > 0 ? vAn(n) : vA());
                        v.array->count = n;

                        if (n > 0) memcpy(
                                v.array->items,
                                topN(n),
                                n * sizeof (Value)
                        );

                        STACK.count -= n;

                        push(ty, v);

                        break;
                CASE(TUPLE)
                {
                        static _Thread_local StringVector names;
                        static _Thread_local ValueVector values;

                        names.count = 0;
                        values.count = 0;

                        bool have_names = false;

                        READVALUE(n);

                        for (int i = 0; i < n; ++i, SKIPSTR()) {
                                Value *v = &STACK.items[STACK.count - n + i];
                                if (strcmp(IP, "*") == 0) {
                                        if (v->type != VALUE_TUPLE) {
                                                zP(
                                                        "attempt to spread non-tuple in tuple expression: %s",
                                                        value_show_color(ty, v)
                                                );
                                        }
                                        for (int j = 0; j < v->count; ++j) {
                                                if (v->names != NULL && v->names[j] != NULL) {
                                                        AddTupleEntry(ty, &names, &values, v->names[j], &v->items[j]);
                                                        have_names = true;
                                                } else {
                                                        vvP(names, NULL);
                                                        vvP(values, v->items[j]);
                                                }
                                        }
                                } else if (v->type != VALUE_NONE) {
                                        if (IP[0] == '\0') {
                                                vvP(names, NULL);
                                                vvP(values, *v);
                                        } else {
                                                AddTupleEntry(ty, &names, &values, IP, v);
                                                have_names = true;
                                        }
                                }
                        }

                        k = values.count;
                        vp = mAo(k * sizeof (Value), GC_TUPLE);

                        v = TUPLE(vp, NULL, k, false);

                        GC_STOP();

                        if (k > 0) {
                                memcpy(vp, values.items, k * sizeof (Value));
                                if (have_names) {
                                        v.names = mAo(k * sizeof (char *), GC_TUPLE);
                                        memcpy(v.names, names.items, k * sizeof (char *));
                                }
                        }

                        STACK.count -= n;

                        push(ty, v);

                        GC_RESUME();

                        break;
                }
                CASE(DICT)
                        v = DICT(dict_new(ty));

                        gP(&v);

                        n = (STACK.count - *vvX(sp_stack)) / 2;
                        for (i = 0; i < n; ++i) {
                                value = top(ty)[0];
                                key = top(ty)[-1];
                                if (value.type == VALUE_NONE) {
                                        pop(ty);
                                        splat(ty, v.dict, &key);
                                        pop(ty);
                                } else {
                                        dict_put_value(ty, v.dict, key, value);
                                        pop(ty);
                                        pop(ty);
                                }
                        }

                        push(ty, v);

                        gX();

                        break;
                CASE(DICT_DEFAULT)
                        v = pop(ty);
                        top(ty)->dict->dflt = v;
                        break;
                CASE(SELF)
                        if (FRAMES.count == 0) {
                        } else {
                                push(ty, NIL);
                        }
                        break;
                CASE(NIL)
                        push(ty, NIL);
                        break;
                CASE(TO_STRING)
                        str = IP;
                        n = strlen(str);
                        IP += n + 1;
                        if (top(ty)->type == VALUE_PTR) {
                            char *s = value_show(ty, top(ty));
                            pop(ty);
                            push(ty, STRING_NOGC(s, strlen(s)));
                            break;
                        } else if (n > 0) {
                                v = pop(ty);
                                push(ty, STRING_NOGC(str, n));
                                push(ty, v);
                                n = 1;
                                method = "__fmt__";
                        } else {
                                n = 0;
                                method = "__str__";
                        }
                        b = false;
                        h = strhash(method);
                        goto CallMethod;
                CASE(YIELD)
                        if (!co_yield(ty)) {
                                zP("attempt to yield from outside generator context");
                        }
                        break;
                CASE(MAKE_GENERATOR)
                        v.type = VALUE_GENERATOR;
                        v.tags = 0;
                        v.gen = mAo(sizeof *v.gen, GC_GENERATOR);
                        NOGC(v.gen);
                        v.gen->ip = IP;
                        v.gen->f = vvL(FRAMES)->f;
                        n = STACK.count - vvL(FRAMES)->fp;
                        vec_init(v.gen->frame);
                        vvPn(v.gen->frame, STACK.items + STACK.count - n, n);
                        vec_init(v.gen->sps);
                        vec_init(v.gen->targets);
                        vec_init(v.gen->calls);
                        vec_init(v.gen->frames);
                        vec_init(v.gen->deferred);
                        vec_init(v.gen->to_drop);
                        push(ty, v);
                        OKGC(v.gen);
                        goto Return;
                CASE(VALUE)
                        READVALUE(s);
                        push(ty, *(Value *)s);
                        break;
                CASE(EVAL)
                        READVALUE(s);
                        push(ty, PTR((void *)s));
                        v = builtin_eval(ty, 2, NULL);
                        pop(ty);
                        pop(ty);
                        push(ty, v);
                        break;
                CASE(RENDER_TEMPLATE)
                        READVALUE(s);
                        push(ty, compiler_render_template(ty, (struct expression *)s));
                        break;
                CASE(TRAP)
#ifdef _WIN32
                        __debugbreak();
#else
                        raise(SIGTRAP);
#endif
                        break;
                CASE(GET_NEXT)
                        v = top(ty)[-1];
                        i = top(ty)[-2].i++;
                        //LOG("GET_NEXT: v = %s\n", value_show(ty, &v));
                        //LOG("GET_NEXT: i = %d\n", i);
                        print_stack(ty, 10);
                        switch (v.type) {
                        case VALUE_ARRAY:
                                if (i < v.array->count) {
                                        push(ty, v.array->items[i]);
                                } else {
                                        push(ty, NONE);
                                }
                                break;
                        case VALUE_DICT:
                                off = top(ty)[-2].off;
                                while (off < v.dict->size && v.dict->keys[off].type == 0) {
                                        off += 1;
                                }
                                if (off < v.dict->size) {
                                        top(ty)[-2].off = off + 1;
                                        push(ty, v.dict->keys[off]);
                                        push(ty, v.dict->values[off]);
                                        rc = 1;
                                        pop(ty);
                                } else {
                                        push(ty, NONE);
                                }
                                break;
                        case VALUE_FUNCTION:
                                push(ty, INTEGER(i));
                                call(ty, &v, NULL, 1, 0, false);
                                break;
                        case VALUE_OBJECT:
                                if ((vp = class_method(ty, v.class, "__next__")) != NULL) {
                                        push(ty, INTEGER(i));
                                        vec_push_unchecked(ty, CALLS, IP);
                                        call(ty, vp, &v, 1, 0, false);
                                        *vvL(CALLS) = next_fix;
                                } else if ((vp = class_method(ty, v.class, "__iter__")) != NULL) {
                                        pop(ty);
                                        pop(ty);
                                        --top(ty)->i;
                                        /* Have to repeat this instruction */
                                        vec_push_unchecked(ty, CALLS, IP - 1);
                                        call(ty, vp, &v, 0, 0, false);
                                        *vvL(CALLS) = iter_fix;
                                        continue;
                                } else {
                                        goto NoIter;
                                }
                                break;
                        case VALUE_BLOB:
                                if (i < v.blob->count) {
                                        push(ty, INTEGER(v.blob->items[i]));
                                } else {
                                        push(ty, NONE);
                                }
                                break;
                        case VALUE_TUPLE:
                                if (i < v.count) {
                                        push(ty, v.items[i]);
                                } else {
                                        push(ty, NONE);
                                }
                                break;
                        case VALUE_STRING:
                                vp = top(ty) - 2;
                                if ((off = vp->off) < v.bytes) {
                                        vp->off += (n = utf8_char_len(v.string + off));
                                        push(ty, STRING_VIEW(v, off, n));
                                } else {
                                        push(ty, NONE);
                                }
                                break;
                        case VALUE_GENERATOR:
                                vec_push_unchecked(ty, CALLS, IP);
                                call_co(ty, &v, 0);
                                *vvL(v.gen->calls) = next_fix;
                                break;
                        default:
                        NoIter:
                                GC_STOP();
                                zP("for-each loop on non-iterable value: %s", value_show(ty, &v));
                        }
                        break;
                CASE(ARRAY_COMPR)
                        n = STACK.count - *vvX(sp_stack);
                        v = top(ty)[-(n + 2)];
                        for (int i = 0; i < n; ++i)
                                vAp(v.array, top(ty)[-i]);
                        STACK.count -= n;
                        break;
                CASE(DICT_COMPR)
                        READVALUE(n);
                        v = top(ty)[-(2*n + 2)];
                        for (i = 0; i < n; ++i) {
                                value = top(ty)[-2*i];
                                key = top(ty)[-(2*i + 1)];
                                dict_put_value(ty, v.dict, key, value);
                        }
                        STACK.count -= 2 * n;
                        break;
                CASE(PUSH_INDEX)
                        READVALUE(n);
                        push(ty, INDEX(0, 0, n));
                        break;
                CASE(READ_INDEX)
                        k = top(ty)[-3].integer - 1;
                        STACK.count += rc;
                        push(ty, INTEGER(k));
                        break;
                CASE(SENTINEL)
                        push(ty, SENTINEL);
                        break;
                CASE(NONE)
                        push(ty, NONE);
                        break;
                CASE(NONE_IF_NIL)
                        if (top(ty)->type == VALUE_TAG && top(ty)->tag == TAG_NONE) {
                                *top(ty) = NONE;
                        } else FALSE_OR (!(top(ty)->tags != 0 && tags_first(ty, top(ty)->tags) == TAG_SOME)) {
                                zP("iterator returned invalid type. expected None or Some(ty, x) but got %s", value_show(ty, top(ty)));
                        } else {
                                top(ty)->tags = tags_pop(ty, top(ty)->tags);
                                if (top(ty)->tags == 0) {
                                        top(ty)->type &= ~VALUE_TAGGED;
                                }
                        }
                        break;
                CASE(CLEAR_RC)
                        rc = 0;
                        break;
                CASE(GET_EXTRA)
                        LOG("GETTING %d EXTRA", rc);
                        STACK.count += rc;
                        break;
                CASE(FIX_EXTRA)
                        for (n = 0; top(ty)[-n].type != VALUE_SENTINEL; ++n)
                                ;
                        for (i = 0, j = n - 1; i < j; ++i, --j) {
                                v = top(ty)[-i];
                                top(ty)[-i] = top(ty)[-j];
                                top(ty)[-j] = v;
                        }
                        break;
                CASE(FIX_TO)
                        READVALUE(n);
                        for (i = 0; top(ty)[-i].type != VALUE_SENTINEL; ++i)
                                ;
                        while (i > n)
                                --i, pop(ty);
                        while (i < n)
                                ++i, push(ty, NIL);
                        for (i = 0, j = n - 1; i < j; ++i, --j) {
                                v = top(ty)[-i];
                                top(ty)[-i] = top(ty)[-j];
                                top(ty)[-j] = v;
                        }
                        break;
                CASE(SWAP)
                        v = top(ty)[-1];
                        top(ty)[-1] = top(ty)[0];
                        top(ty)[0] = v;
                        break;
                CASE(REVERSE)
                        READVALUE(n);
                        for (--n, i = 0; i < n; ++i, --n) {
                                v = top(ty)[-i];
                                top(ty)[-i] = top(ty)[-n];
                                top(ty)[-n] = v;
                        }
                        break;
                CASE(MULTI_ASSIGN)
                        print_stack(ty, 5);
                        READVALUE(n);
                        for (i = 0, vp = top(ty); pop(ty).type != VALUE_SENTINEL; ++i)
                                ;
                        for (int j = TARGETS.count - n; n > 0; --n, poptarget(ty)) {
                                if (i > 0) {
                                        *TARGETS.items[j++].t = vp[-(--i)];
                                } else {
                                        *TARGETS.items[j++].t = NIL;
                                }
                        }
                        push(ty, top(ty)[2]);
                        break;
                CASE(MAYBE_MULTI)
                        READVALUE(n);
                        for (i = 0, vp = top(ty); pop(ty).type != VALUE_SENTINEL; ++i)
                                ;
                        for (int j = TARGETS.count - n; n > 0; --n, poptarget(ty)) {
                                if (i > 0) {
                                        if (TARGETS.items[j++].t->type == VALUE_NIL)
                                                *TARGETS.items[j - 1].t = vp[-(--i)];
                                } else {
                                        *TARGETS.items[j++].t = NIL;
                                }
                        }
                        push(ty, top(ty)[2]);
                        break;
                CASE(JUMP_IF_SENTINEL)
                        READVALUE(n);
                        if (top(ty)->type == VALUE_SENTINEL)
                                IP += n;
                        break;
                CASE(CLEAR_EXTRA)
                        while (top(ty)->type != VALUE_SENTINEL)
                                pop(ty);
                        pop(ty);
                        break;
                CASE(PUSH_NTH)
                        READVALUE(n);
                        push(ty, top(ty)[-n]);
                        break;
                CASE(PUSH_ARRAY_ELEM)
                        READVALUE(n);
                        READVALUE(b);
                        if (top(ty)->type != VALUE_ARRAY) {
                                MatchError;
                                zP("attempt to destructure non-array as array in assignment");
                        }
                        if (n < 0) {
                                n += top(ty)->array->count;
                        }
                        if (n >= top(ty)->array->count) {
                                if (b) {
                                        MatchError;
                                        zP("elment index out of range in destructuring assignment");
                                } else {
                                        push(ty, NIL);
                                }
                        } else {
                                push(ty, top(ty)->array->items[n]);
                        }
                        break;
                CASE(PUSH_TUPLE_ELEM)
                        READVALUE(n);
                        FALSE_OR (top(ty)->type != VALUE_TUPLE) {
                                zP(
                                        "attempt to destructure non-tuple as tuple in assignment: %s",
                                        value_show_color(ty, top(ty))
                                );
                        }
                        FALSE_OR (n >= top(ty)->count) {
                                zP(
                                        "elment index %d out of range in destructuring assignment: %s",
                                        n,
                                        value_show_color(ty, top(ty))
                                );
                        }
                        push(ty, top(ty)->items[n]);
                        break;
                CASE(PUSH_TUPLE_MEMBER)
                        READVALUE(b);
                        READSTR(member);

                        v = peek(ty);

                        if (v.type != VALUE_TUPLE || v.names == NULL) {
                                value = v;
                                goto BadTupleMember;
                        }

                        for (int i = 0; i < v.count; ++i) {
                                if (v.names[i] != NULL && strcmp(v.names[i], member) == 0) {
                                        push(ty, v.items[i]);
                                        goto NextInstruction;
                                }
                        }

                        if (!b) {
                                push(ty, NIL);
                                goto NextInstruction;
                        }

                        value = v;

                        goto BadTupleMember;
                CASE(PUSH_ALL)
                        v = pop(ty);
                        gP(&v);
                        for (int i = 0; i < v.array->count; ++i) {
                                push(ty, v.array->items[i]);
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
                                        memcpy(str + k, STACK.items[i].string, STACK.items[i].bytes);
                                        k += STACK.items[i].bytes;
                                }
                        }
                        STACK.count -= n - 1;
                        STACK.items[STACK.count - 1] = v;
                        break;
                CASE(RANGE)
                        i = class_lookup(ty, "Range");
                        if (i == -1 || (vp = class_method(ty, i, "init")) == NULL) {
                                zP("failed to load Range class. was prelude loaded correctly?");
                        }

                        v = OBJECT(object_new(ty, i), i);
                        NOGC(v.object);
                        call(ty, vp, &v, 2, 0, true);
                        *top(ty) = v;
                        OKGC(v.object);
                        break;
                CASE(INCRANGE)
                        i = class_lookup(ty, "InclusiveRange");
                        if (i == -1 || (vp = class_method(ty, i, "init")) == NULL) {
                                zP("failed to load InclusiveRange class. was prelude loaded correctly?");
                        }

                        v = OBJECT(object_new(ty, i), i);
                        NOGC(v.object);
                        call(ty, vp, &v, 2, 0, true);
                        *top(ty) = v;
                        OKGC(v.object);
                        break;
                CASE(TRY_MEMBER_ACCESS)
                CASE(MEMBER_ACCESS)
                        b = IP[-1] == INSTR_TRY_MEMBER_ACCESS;

                        READSTR(member);
                        READVALUE(h);

                        v = GetMember(ty, peek(ty), member, h, true);

                        if (b || v.type != VALUE_NONE) {
                                *top(ty) = v;
                                break;
                        }

                        if (value.type == VALUE_TUPLE) {
                        BadTupleMember:
                                zP(
                                        "attempt to access non-existent field %s'%s'%s of %s%s%s",
                                        TERM(34),
                                        member,
                                        TERM(39),
                                        TERM(97),
                                        value_show_color(ty, &value),
                                        TERM(39)
                                );
                        } else {
                                zP(
                                        "attempt to access non-existent member %s'%s'%s of %s%s%s",
                                        TERM(34),
                                        member,
                                        TERM(39),
                                        TERM(97),
                                        value_show_color(ty, &value),
                                        TERM(39)
                                );
                        }

                        break;
                CASE(SLICE)
                        n = 3;
                        nkw = 0;
                        method = "__slice__";
                        h = strhash(method);
                        goto CallMethod;
                CASE(SUBSCRIPT)
                        subscript = pop(ty);
                        container = pop(ty);

                        switch (container.type) {
                        case VALUE_ARRAY:
                        ArraySubscript:
                                if (subscript.type == VALUE_GENERATOR) {
                                        gP(&subscript);
                                        gP(&container);
                                        Array *a = vA();
                                        NOGC(a);
                                        str = IP;
                                        for (;;) {
                                                call_co(ty, &subscript, 0);
                                                *vvL(subscript.gen->calls) = &halt;
                                                vec_push_unchecked(ty, subscript.gen->calls, next_fix);
                                                vm_exec(ty, IP);
                                                Value r = pop(ty);
                                                if (r.type == VALUE_NONE)
                                                        break;
                                                FALSE_OR (r.type != VALUE_INTEGER)
                                                        zP("iterator yielded non-integer array index in subscript expression");
                                                if (r.integer < 0)
                                                        r.integer += container.array->count;
                                                if (r.integer < 0 || r.integer >= container.array->count)
                                                        goto OutOfRange;
                                                vAp(a, container.array->items[r.integer]);
                                        }
                                        push(ty, ARRAY(a));
                                        OKGC(a);
                                        gX();
                                        gX();
                                        IP = str;
                                } else if (subscript.type == VALUE_OBJECT) {
                                        gP(&subscript);
                                        gP(&container);
                                        vp = class_method(ty, subscript.class, "__next__");
                                        if (vp == NULL) {
                                                vp = class_method(ty, subscript.class, "__iter__");
                                                FALSE_OR (vp == NULL) {
                                                        zP("non-iterable object used in subscript expression");
                                                }
                                                call(ty, vp, &subscript, 0, 0, true);
                                                subscript = pop(ty);
                                                gX();
                                                gX();
                                                goto ArraySubscript;
                                        }
                                        Array *a = vA();
                                        NOGC(a);
                                        for (int i = 0; ; ++i) {
                                                push(ty, INTEGER(i));
                                                call(ty, vp, &subscript, 1, 0, true);
                                                Value r = pop(ty);
                                                if (r.type == VALUE_NIL)
                                                        break;
                                                FALSE_OR (r.type != VALUE_INTEGER)
                                                        zP("iterator yielded non-integer array index in subscript expression");
                                                if (r.integer < 0)
                                                        r.integer += container.array->count;
                                                if (r.integer < 0 || r.integer >= container.array->count)
                                                        goto OutOfRange;
                                                vAp(a, container.array->items[r.integer]);
                                        }
                                        push(ty, ARRAY(a));
                                        OKGC(a);
                                        gX();
                                        gX();
                                } else if (subscript.type == VALUE_INTEGER) {
                                        if (subscript.integer < 0) {
                                                subscript.integer += container.array->count;
                                        }
                                        if (subscript.integer < 0 || subscript.integer >= container.array->count) {
                                OutOfRange:
                                                push(ty, TAG(gettag(ty, NULL, "IndexError")));
                                                goto Throw;
                                                zP("array index out of range in subscript expression");
                                        }
                                        push(ty, container.array->items[subscript.integer]);
                                } else {
                                        zP(
                                                "non-integer array index used in subscript expression: %s",
                                                value_show_color(ty, &subscript)
                                        );
                                }
                                break;
                        case VALUE_TUPLE:
                                if (subscript.type == VALUE_INTEGER) {
                                        if (subscript.integer < 0) {
                                                subscript.integer += container.count;
                                        }
                                        if (subscript.integer < 0 || subscript.integer >= container.count) {
                                                push(ty, TAG(gettag(ty, NULL, "IndexError")));
                                                goto Throw;
                                                zP("list index out of range in subscript expression");
                                        }
                                        push(ty, container.items[subscript.integer]);
                                } else {
                                        zP(
                                                "non-integer array index used in subscript expression: %s",
                                                value_show_color(ty, &subscript)
                                        );
                                }
                                break;
                        case VALUE_STRING:
                                push(ty, subscript);
                                v = get_string_method("char")(ty, &container, 1, NULL);
                                pop(ty);
                                push(ty, v);
                                break;
                        case VALUE_BLOB:
                                push(ty, subscript);
                                v = get_blob_method("get")(ty, &container, 1, NULL);
                                pop(ty);
                                push(ty, v);
                                break;
                        case VALUE_DICT:
                                vp = dict_get_value(ty, container.dict, &subscript);
                                push(ty, (vp == NULL) ? NIL : *vp);
                                break;
                        case VALUE_OBJECT:
                                vp = class_method(ty, container.class, "__subscript__");
                                if (vp != NULL) {
                                        push(ty, subscript);
                                        call(ty, vp, &container, 1, 0, false);
                                } else {
                                        goto BadContainer;
                                }
                                break;
                        case VALUE_CLASS:
                                push(ty, subscript);
                                push(ty, container);
                                n = 1;
                                b = false;
                                method = "__subscript__";
                                h = strhash(method);
                                goto CallMethod;
                        case VALUE_PTR:
                                FALSE_OR (subscript.type != VALUE_INTEGER) {
                                        zP("non-integer used to subscript pointer: %s", value_show(ty, &subscript));
                                }
                                v = GCPTR((container.extra == NULL) ? &ffi_type_uint8 : container.extra, container.gcptr);
                                push(ty, v);
                                push(ty, PTR(((char *)container.ptr) + ((ffi_type *)v.ptr)->size * subscript.integer));
                                v = cffi_load(ty, 2, NULL);
                                pop(ty);
                                pop(ty);
                                push(ty, v);
                                break;
                        case VALUE_NIL:
                                push(ty, NIL);
                                break;
                        default:
                        BadContainer:
                                zP("invalid container in subscript expression: %s", value_show(ty, &container));
                        }
                        break;
                CASE(NOT)
                        v = pop(ty);
                        push(ty, BOOLEAN(!value_truthy(ty, &v)));
                        break;
                CASE(QUESTION)
                        if (top(ty)->type == VALUE_NIL) {
                                *top(ty) = BOOLEAN(false);
                        } else {
                                n = 0;
                                b = false;
                                method = "__question__";
                                h = strhash(method);
                                goto CallMethod;
                        }
                        break;
                CASE(NEG)
                        v = pop(ty);
                        if (v.type == VALUE_INTEGER) {
                                push(ty, INTEGER(-v.integer));
                        } else if (v.type == VALUE_REAL) {
                                push(ty, REAL(-v.real));
                        } else {
                                zP("unary - applied to non-numeric operand: %s", VSC(&v));
                        }
                        break;
                CASE(COUNT)
                        v = pop(ty);
                        switch (v.type) {
                        case VALUE_BLOB:   push(ty, INTEGER(v.blob->count));  break;
                        case VALUE_ARRAY:  push(ty, INTEGER(v.array->count)); break;
                        case VALUE_DICT:   push(ty, INTEGER(v.dict->count));  break;
                        case VALUE_STRING:
                                push(ty, get_string_method("len")(ty, &v, 0, NULL));
                                break;
                        case VALUE_OBJECT:
                                push(ty, v);
                                n = 0;
                                b = false;
                                method = "__len__";
                                h = strhash(method);
                                goto CallMethod;
                        default: zP("# applied to operand of invalid type: %s", value_show(ty, &v));
                        }
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
                CASE(EQ)
                        DoEq(ty);
                        break;
                CASE(NEQ)
                        DoNeq(ty);
                        break;
                CASE(CHECK_MATCH)
                        if (top(ty)->type == VALUE_CLASS) {
                                v = pop(ty);
                                switch (top(ty)->type) {
                                case VALUE_OBJECT:
                                        *top(ty) = BOOLEAN(
                                                top(ty)->type == VALUE_OBJECT &&
                                                class_is_subclass(ty, top(ty)->class, v.class)
                                        );
                                        break;
                                case VALUE_INTEGER:   *top(ty) = BOOLEAN(class_is_subclass(ty, CLASS_INT, v.class));       break;
                                case VALUE_REAL:      *top(ty) = BOOLEAN(class_is_subclass(ty, CLASS_FLOAT, v.class));     break;
                                case VALUE_BOOLEAN:   *top(ty) = BOOLEAN(class_is_subclass(ty, CLASS_BOOL, v.class));      break;
                                case VALUE_ARRAY:     *top(ty) = BOOLEAN(class_is_subclass(ty, CLASS_ARRAY, v.class));     break;
                                case VALUE_STRING:    *top(ty) = BOOLEAN(class_is_subclass(ty, CLASS_STRING, v.class));    break;
                                case VALUE_BLOB:      *top(ty) = BOOLEAN(class_is_subclass(ty, CLASS_BLOB, v.class));      break;
                                case VALUE_DICT:      *top(ty) = BOOLEAN(class_is_subclass(ty, CLASS_DICT, v.class));      break;
                                case VALUE_TUPLE:     *top(ty) = BOOLEAN(class_is_subclass(ty, CLASS_TUPLE, v.class));     break;
                                case VALUE_METHOD:
                                case VALUE_BUILTIN_METHOD:
                                case VALUE_BUILTIN_FUNCTION:
                                case VALUE_FUNCTION:  *top(ty) = BOOLEAN(class_is_subclass(ty, CLASS_FUNCTION, v.class));  break;
                                case VALUE_GENERATOR: *top(ty) = BOOLEAN(class_is_subclass(ty, CLASS_GENERATOR, v.class)); break;
                                case VALUE_REGEX:     *top(ty) = BOOLEAN(class_is_subclass(ty, CLASS_REGEX, v.class));     break;
                                default:              *top(ty) = BOOLEAN(false);                                       break;
                                }
                        } else if (top(ty)->type == VALUE_BOOLEAN) {
                                v = pop(ty);
                                *top(ty) = v;
                        } else {
                                n = 1;
                                nkw = 0;
                                b = false;
                                method = "__match__";
                                h = strhash(method);
                                goto CallMethod;
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
                        v = pop(ty);
                        if (v.tags == 0)
                                push(ty, NIL);
                        else
                                push(ty, TAG(tags_first(ty, v.tags)));
                        break;
                CASE(LEN)
                        v = pop(ty);
                        push(ty, INTEGER(v.array->count)); // TODO
                        break;
                CASE(PRE_INC)
                        FALSE_OR (SpecialTarget(ty)) {
                                zP("pre-increment applied to invalid target");
                        }
                        switch (peektarget(ty)->type) {
                        case VALUE_INTEGER: ++peektarget(ty)->integer; break;
                        case VALUE_REAL:    ++peektarget(ty)->real;    break;
                        case VALUE_OBJECT:
                                vp = class_method(ty, peektarget(ty)->class, "++");
                                if (vp != NULL) {
                                        call(ty, vp, peektarget(ty), 0, 0, true);
                                        break;
                                }
                        case VALUE_PTR:
                                vp = peektarget(ty);
                                vp->ptr = ((char *)vp->ptr) + ((ffi_type *)(vp->extra == NULL ? &ffi_type_uint8 : vp->extra))->size;
                                break;
                        default:
                                zP("pre-increment applied to invalid type: %s", value_show(ty, peektarget(ty)));
                        }
                        push(ty, *poptarget(ty));
                        break;
                CASE(POST_INC)
                        FALSE_OR (SpecialTarget(ty)) {
                                zP("pre-increment applied to invalid target");
                        }
                        push(ty, *peektarget(ty));
                        switch (peektarget(ty)->type) {
                        case VALUE_INTEGER: ++peektarget(ty)->integer; break;
                        case VALUE_REAL:    ++peektarget(ty)->real;    break;
                        case VALUE_PTR:
                                vp = peektarget(ty);
                                vp->ptr = ((char *)vp->ptr) + ((ffi_type *)(vp->extra == NULL ? &ffi_type_uint8 : vp->extra))->size;
                                break;
                        default:            zP("post-increment applied to invalid type: %s", value_show(ty, peektarget(ty)));
                        }
                        poptarget(ty);
                        break;
                CASE(PRE_DEC)
                        if (SpecialTarget(ty)) {
                                zP("pre-decrement applied to invalid target");
                        }
                        switch (peektarget(ty)->type) {
                        case VALUE_INTEGER: --peektarget(ty)->integer; break;
                        case VALUE_REAL:    --peektarget(ty)->real;    break;
                        case VALUE_OBJECT:
                                vp = class_method(ty, peektarget(ty)->class, "--");
                                if (vp != NULL) {
                                        call(ty, vp, peektarget(ty), 0, 0, true);
                                        break;
                                }
                        case VALUE_PTR:
                                vp = peektarget(ty);
                                vp->ptr = ((char *)vp->ptr) - ((ffi_type *)(vp->extra == NULL ? &ffi_type_uint8 : vp->extra))->size;
                                break;
                        default:
                                zP("pre-decrement applied to invalid type: %s", value_show(ty, peektarget(ty)));
                        }
                        push(ty, *poptarget(ty));
                        break;
                CASE(POST_DEC)
                        if (SpecialTarget(ty)) {
                                zP("post-decrement applied to invalid target");
                        }
                        push(ty, *peektarget(ty));
                        switch (peektarget(ty)->type) {
                        case VALUE_INTEGER: --peektarget(ty)->integer; break;
                        case VALUE_REAL:    --peektarget(ty)->real;    break;
                        case VALUE_PTR:
                                vp = peektarget(ty);
                                vp->ptr = ((char *)vp->ptr) - ((ffi_type *)(vp->extra == NULL ? &ffi_type_uint8 : vp->extra))->size;
                                break;
                        default:            zP("post-decrement applied to invalid type: %s", value_show(ty, peektarget(ty)));
                        }
                        poptarget(ty);
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
                CASE(MUT_SUB)
                        DoMutSub(ty);
                        break;
                CASE(BINARY_OP)
                        READVALUE(n);
                BinaryOp:
                        DoBinaryOp(ty, n, false);
                        break;
                CASE(DEFINE_TAG)
                {
                        int tag, super, n;
                        READVALUE(tag);
                        READVALUE(super);
                        READVALUE(n);
                        while (n --> 0) {
                                v = pop(ty);
                                tags_add_method(ty, tag, IP, v);
                                SKIPSTR();
                        }
                        if (super != -1)
                                tags_copy_methods(ty, tag, super);
                        break;
                }
                CASE(DEFINE_CLASS)
                {
                        int class, c, n, g, s;
                        READVALUE(class);
                        READVALUE(c);
                        READVALUE(n);
                        READVALUE(g);
                        READVALUE(s);
                        while (c --> 0) {
                                v = pop(ty);
                                class_add_static(ty, class, IP, v);
                                SKIPSTR();
                        }
                        while (n --> 0) {
                                v = pop(ty);
                                class_add_method(ty, class, IP, v);
                                SKIPSTR();
                        }
                        while (g --> 0) {
                                v = pop(ty);
                                class_add_getter(ty, class, IP, v);
                                SKIPSTR();
                        }
                        while (s --> 0) {
                                v = pop(ty);
                                class_add_setter(ty, class, IP, v);
                                SKIPSTR();
                        }
                        break;
                }
                CASE(FUNCTION)
                {
                        v.tags = 0;
                        v.type = VALUE_FUNCTION;

                        IP = ALIGNED_FOR(int, IP);

                        // n: bound_caps
                        READVALUE(n);

                        v.info = (int *) IP;

                        int hs = v.info[0];
                        int size  = v.info[1];
                        int nEnv = v.info[2];
                        int bound = v.info[3];

                        int ncaps = (n > 0) ? nEnv - n : nEnv;

                        LOG("Header size: %d", hs);
                        LOG("Code size: %d", size);
                        LOG("Bound: %d", bound);
                        LOG("ncaps: %d", ncaps);
                        LOG("Name: %s", value_show(ty, &v));

                        if (EvalDepth > 0) {
                                v.info = mAo(hs + size, GC_ANY);
                                memcpy(v.info, IP, hs + size);
                                *from_eval(&v) = true;
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
                                Value *p = poptarget(ty);
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
                                LOG("env[%d] = %s", j, value_show(ty, v.env[j]));
                        }

                        push(ty, v);

                        GC_RESUME();

                        if (EvalDepth > 0) {
                                OKGC(v.info);
                        }

                        break;
                }
                CASE(PATCH_ENV)
                        READVALUE(n);
                        *top(ty)->env[n] = *top(ty);
                        break;
                CASE(TAIL_CALL)
                        tco = true;
                        break;
                CASE(CALL)
                        v = pop(ty);

                        READVALUE(n);
                        READVALUE(nkw);

                        if (n == -1) {
                                n = STACK.count - *vvX(sp_stack) - nkw;
                        }

                        if (tco) {
                                vvX(FRAMES);
                                IP = *vvX(CALLS);
                                tco = false;
                        }

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
                        CallKwArgs:
                                if (!AutoThis) {
                                        gP(&v);
                                } else {
                                        gP(v.this);
                                        AutoThis = false;
                                }
                                GC_STOP();
                                container = DICT(dict_new(ty));
                                for (int i = 0; i < nkw; ++i) {
                                        if (IP[0] == '*') {
                                                if (top(ty)->type == VALUE_DICT) {
                                                        DictUpdate(ty, container.dict, top(ty)->dict);
                                                        pop(ty);
                                                } else if (top(ty)->type == VALUE_TUPLE && top(ty)->names != NULL) {
                                                        for (int i = 0; i < top(ty)->count; ++i) {
                                                                if (top(ty)->names[i] != NULL) {
                                                                        dict_put_member(
                                                                                ty,
                                                                                container.dict,
                                                                                top(ty)->names[i],
                                                                                top(ty)->items[i]
                                                                        );
                                                                }
                                                        }
                                                        pop(ty);
                                                } else {
                                                        zP(
                                                                "attempt to splat invalid value in function call: %s%s%s%s%s",
                                                                TERM(34),
                                                                TERM(1),
                                                                value_show(ty, top(ty)),
                                                                TERM(22),
                                                                TERM(39)
                                                        );
                                                }
                                        } else {
                                                dict_put_member(ty, container.dict, IP, pop(ty));
                                        }
                                        SKIPSTR();
                                }
                                push(ty, container);
                                GC_RESUME();
                        } else {
                                container = NIL;
                        Call:
                                if (!AutoThis) {
                                        gP(&v);
                                } else {
                                        gP(v.this);
                                        AutoThis = false;
                                }
                        }

                        switch (v.type) {
                        case VALUE_FUNCTION:
                                LOG("CALLING %s with %d arguments", value_show(ty, &v), n);
                                print_stack(ty, n);
                                call(ty, &v, NULL, n, nkw, false);
                                break;
                        case VALUE_BUILTIN_FUNCTION:
                                /*
                                 * Builtin functions may not preserve the stack size, so instead
                                 * of subtracting `n` after calling the builtin function, we compute
                                 * the desired final stack size in advance.
                                 */
                                if (nkw > 0) {
                                        container = pop(ty);
                                        gP(&container);
                                        k = STACK.count - n;
                                        v = v.builtin_function(ty, n, &container);
                                        gX();
                                } else {
                                        k = STACK.count - n;
                                        v = v.builtin_function(ty, n, NULL);
                                }
                                STACK.count = k;
                                push(ty, v);
                                break;
                        case VALUE_GENERATOR:
                                if (nkw > 0) { pop(ty); }
                                call_co(ty, &v, n);
                                break;
                        case VALUE_TAG:
                                if (nkw > 0) {
                                        container = pop(ty);
                                        DoTag(ty, v.tag, n, &container);
                                } else {
                                        DoTag(ty, v.tag, n, NULL);
                                }
                                break;
                        case VALUE_CLASS:
                                vp = class_method(ty, v.class, "init");
                                if (v.class < CLASS_PRIMITIVE && v.class != CLASS_OBJECT) {
                                        if (vp != NULL) {
                                                call(ty, vp, NULL, n, nkw, true);
                                        } else {
                                                zP("primitive class has no init method. was prelude loaded?");
                                        }
                                } else {
                                        value = OBJECT(object_new(ty, v.class), v.class);
                                        if (vp != NULL) {
                                                gP(&value);
                                                call(ty, vp, &value, n, nkw, true);
                                                gX();
                                                pop(ty);
                                        } else {
                                                STACK.count -= n + (nkw > 0);
                                        }
                                        push(ty, value);
                                }
                                break;
                        case VALUE_METHOD:
                                if (v.name == MISSING) {
                                        push(ty, NIL);
                                        memmove(top(ty) - (n - 1), top(ty) - n, n * sizeof (Value));
                                        top(ty)[-n++] = v.this[1];
                                }
                                call(ty, v.method, v.this, n, nkw, false);
                                break;
                        case VALUE_REGEX:
                                if (nkw > 0) {
                                        pop(ty);
                                }
                                if (n != 1)
                                        zP("attempt to apply a regex to an invalid number of values");
                                value = peek(ty);
                                if (value.type != VALUE_STRING)
                                        zP("attempt to apply a regex to a non-string: %s", value_show(ty, &value));
                                push(ty, v);
                                v = get_string_method("match!")(ty, &value, 1, NULL);
                                pop(ty);
                                *top(ty) = v;
                                break;
                        case VALUE_BUILTIN_METHOD:
                                if (nkw > 0) {
                                        container = pop(ty);
                                        gP(&container);
                                        k = STACK.count - n;
                                        v = v.builtin_method(ty, v.this, n, &container);
                                        gX();
                                } else {
                                        k = STACK.count - n;
                                        v = v.builtin_method(ty, v.this, n, NULL);
                                }
                                STACK.count = k;
                                push(ty, v);
                                break;
                        case VALUE_NIL:
                                STACK.count -= n + (nkw > 0);
                                push(ty, NIL);
                                break;
                        default:
                                zP("attempt to call non-callable value %s", value_show(ty, &v));
                        }
                        gX();
                        nkw = 0;
                        break;
                CASE(TRY_CALL_METHOD)
                CASE(CALL_METHOD)
                        b = IP[-1] == INSTR_TRY_CALL_METHOD;

                        READVALUE(n);
                        READSTR(method);
                        READVALUE(h);
                        READVALUE(nkw);

                        if (n == -1) {
                                n = STACK.count - *vvX(sp_stack) - nkw - 1;
                        }

                /*
                 * b, n, nkw, h, and method must all be correctly set when jumping here
                 */
                CallMethod:
                        LOG("METHOD = %s, n = %d", method, n);
                        print_stack(ty, 5);

                        value = peek(ty);
                        vp = NULL;
                        func = NULL;
                        Value *self = NULL;

                        if (tco) {
                                vvX(FRAMES);
                                IP = *vvX(CALLS);
                                tco = false;
                        }

                        for (int tags = value.tags; tags != 0; tags = tags_pop(ty, tags)) {
                                vp = tags_lookup_method(ty, tags_first(ty, tags), method, h);
                                if (vp != NULL) {
                                        value.tags = tags_pop(ty, tags);
                                        if (value.tags == 0)
                                                value.type &= ~VALUE_TAGGED;
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
                                vp = tags_lookup_method(ty, value.tag, method, h);
                                if (vp == NULL) {
                                        vp = class_lookup_method(ty, CLASS_TAG, method, h);
                                } else {
                                        self = NULL;
                                }
                                break;
                        case VALUE_STRING:
                                func = get_string_method(method);
                                if (func == NULL)
                                        vp = class_lookup_method(ty, CLASS_STRING, method, h);
                                break;
                        case VALUE_DICT:
                                func = get_dict_method(method);
                                if (func == NULL)
                                        vp = class_lookup_method(ty, CLASS_DICT, method, h);
                                break;
                        case VALUE_ARRAY:
                                func = get_array_method(method);
                                if (func == NULL)
                                        vp = class_lookup_method(ty, CLASS_ARRAY, method, h);
                                break;
                        case VALUE_BLOB:
                                func = get_blob_method(method);
                                if (func == NULL)
                                        vp = class_lookup_method(ty, CLASS_BLOB, method, h);
                                break;
                        case VALUE_INTEGER:
                                vp = class_lookup_method(ty, CLASS_INT, method, h);
                                break;
                        case VALUE_REAL:
                                vp = class_lookup_method(ty, CLASS_FLOAT, method, h);
                                break;
                        case VALUE_BOOLEAN:
                                vp = class_lookup_method(ty, CLASS_BOOL, method, h);
                                break;
                        case VALUE_REGEX:
                                vp = class_lookup_method(ty, CLASS_REGEX, method, h);
                                break;
                        case VALUE_FUNCTION:
                        case VALUE_BUILTIN_FUNCTION:
                        case VALUE_METHOD:
                        case VALUE_BUILTIN_METHOD:
                                vp = class_lookup_method(ty, CLASS_FUNCTION, method, h);
                                break;
                        case VALUE_GENERATOR:
                                vp = class_lookup_method(ty, CLASS_GENERATOR, method, h);
                                break;
                        case VALUE_TUPLE:
                                vp = tuple_get(&value, method);
                                if (vp == NULL) {
                                        vp = class_lookup_method(ty, CLASS_TUPLE, method, h);
                                } else {
                                        self = NULL;
                                }
                                break;
                        case VALUE_CLASS: /* lol */
                                vp = class_lookup_immediate(ty, CLASS_CLASS, method, h);
                                if (vp == NULL) {
                                        vp = class_lookup_static(ty, value.class, method, h);
                                }
                                if (vp == NULL) {
                                        vp = class_lookup_method(ty, value.class, method, h);
                                }
                                break;
                        case VALUE_OBJECT:
                                vp = table_lookup(ty, value.object, method, h);
                                if (vp == NULL) {
                                        vp = class_lookup_method(ty, value.class, method, h);
                                } else {
                                        self = NULL;
                                }
                                break;
                        case VALUE_NIL:
                                STACK.count -= (n + 1 + nkw);
                                push(ty, NIL);
                                continue;
                        }

                        if (func != NULL) {
                                pop(ty);
                                value.type &= ~VALUE_TAGGED;
                                value.tags = 0;
                                AutoThis = true;
                                v = BUILTIN_METHOD(method, func, &value);
                                if (nkw > 0) {
                                        goto CallKwArgs;
                                } else {
                                        goto Call;
                                }
                        } else if (vp != NULL) {
                        SetupMethodCall:
                                pop(ty);
                                if (self != NULL) {
                                        AutoThis = true;
                                        v = METHOD(method, vp, self);
                                } else {
                                        v = *vp;
                                }
                                if (nkw > 0) {
                                        goto CallKwArgs;
                                } else {
                                        goto Call;
                                }
                        } else if (b) {
                                STACK.count -= (n + 1 + nkw);
                                push(ty, NIL);
                        } else {
                                if (value.type == VALUE_OBJECT) {
                                        vp = class_method(ty, value.class, MISSING);
                                        if (vp != NULL) {
                                                v = pop(ty);
                                                push(ty, NIL);
                                                memmove(top(ty) - (n - 1), top(ty) - n, n * sizeof (Value));
                                                top(ty)[-n++] = STRING_NOGC(method, strlen(method));
                                                push(ty, v);
                                                self = &value;
                                                goto SetupMethodCall;
                                        }
                                }
                                zP("call to non-existent method '%s' on %s", method, value_show(ty, &value));
                        }
                        break;
                CASE(SAVE_STACK_POS)
                        vvP(sp_stack, STACK.count);
                        break;
                CASE(RESTORE_STACK_POS)
                        STACK.count = *vvX(sp_stack);
                        break;
                CASE(RETURN_IF_NOT_NONE)
                        if (top(ty)->type != VALUE_NONE) {
                                goto Return;
                        }
                        break;
                CASE(MULTI_RETURN)
                CASE(RETURN)
                Return:
                        n = vvL(FRAMES)->fp;
                        if (IP[-1] == INSTR_MULTI_RETURN) {
                                READVALUE(rc);
                                STACK.count -= rc;
                                for (int i = 0; i <= rc; ++i) {
                                        STACK.items[n + i] = top(ty)[i];
                                }
                        } else {
                                STACK.items[n] = peek(ty);
                        }
                        STACK.count = n + 1;
                        LOG("POPPING FRAME");
                        vvX(FRAMES);
                CASE(RETURN_PRESERVE_CTX)
                        IP = *vvX(CALLS);
                        LOG("returning: IP = %p", IP);
                        break;
                CASE(HALT)
                        IP = save;
                        LOG("halting: IP = %p", IP);
                        return;
                }
        }

        }
}

char const *
vm_error(Ty *ty)
{
        return Error;
}

static void
RunExitHooks(void)
{
        Ty *ty = &MainTy;

        if (iExitHooks == -1 || Globals.items[iExitHooks].type != VALUE_ARRAY)
                return;

        Array *hooks = Globals.items[iExitHooks].array;

        vec(char *) msgs = {0};
        char *first = (Error == NULL) ? NULL : sclone_malloc(Error);

        bool bReprintFirst = false;

        for (size_t i = 0; i < hooks->count; ++i) {
                if (setjmp(jb) != 0) {
                        vvP(msgs, sclone_malloc(ERR));
                } else {
                        Value v = vmC(&hooks->items[i], 0);
                        bReprintFirst = bReprintFirst || value_truthy(ty, &v);
                }
        }

        if (first != NULL && bReprintFirst) {
                fprintf(stderr, "%s\n", first);
        }

        for (size_t i = 0; i < msgs.count; ++i) {
                fprintf(stderr, "Exit hook failed with error: %s\n", msgs.items[i]);
        }
}

bool
vm_init(Ty *ty, int ac, char **av)
{
        InitializeTY();
        InitializeTy(ty);

        GC_STOP();

        InitThreadGroup(ty, MyGroup = &MainGroup);

        pcre_malloc = malloc;
        JITStack = pcre_jit_stack_alloc(JIT_STACK_START, JIT_STACK_MAX);

        amN(1ULL << 32);

        curl_global_init(CURL_GLOBAL_ALL);

        srandom(time(NULL));

        compiler_init(ty);

        add_builtins(ty, ac, av);

        AddThread(ty, TyThreadSelf());

        if (setjmp(jb) != 0) {
                Error = ERR;
                return false;
        }

        char *prelude = compiler_load_prelude(ty);
        if (prelude == NULL) {
                Error = compiler_error(ty);
                return false;
        }

        atexit(RunExitHooks);

        vm_exec(ty, prelude);

        compiler_load_builtin_modules(ty);

        sqlite_load(ty);

        GC_RESUME();

#ifdef TY_ENABLE_PROFILING
        if (ProfileOut == NULL) {
                ProfileOut = stdout;
        }
        Samples = dict_new(ty);
        NOGC(Samples);
        FuncSamples = dict_new(ty);
        NOGC(FuncSamples);
        TyMutexInit(&ProfileMutex);
#endif

        return true;
}

noreturn void
vm_panic(Ty *ty, char const *fmt, ...)
{
        va_list ap;
        va_start(ap, fmt);

        int sz = ERR_SIZE - 1;

        int n = snprintf(ERR, sz, "%s%sRuntimeError%s%s: ", TERM(1), TERM(31), TERM(22), TERM(39));
        n += vsnprintf(ERR + n, max(sz - n, 0), fmt, ap);
        va_end(ap);

        if (n < sz)
                ERR[n++] = '\n';

        bool can_yield = false;

        for (int i = 0; IP != NULL && n < sz; ++i) {
                if (FRAMES.count > 0 && ((char *)vvL(FRAMES)->f.info)[FUN_HIDDEN]) {
                        /*
                         * This code is part of a hidden function; we don't want it
                         * to show up in stack traces.
                         */
                        goto Next;
                }

                Expr const *expr = compiler_find_expr(ty, IP - 1);

                n += WriteExpressionTrace(ty, ERR + n, sz - n, expr, 0, i == 0);
                if (expr != NULL && expr->origin != NULL) {
                        n += WriteExpressionOrigin(ty, ERR + n, sz - n, expr->origin);
                }

                if (FRAMES.count == 0) {
                        if (can_yield) {
                                FRAMES.count += 1;
                                co_yield(ty);
                        } else {
                                break;
                        }
                }

                can_yield = GetCurrentGenerator(ty) != NULL;
Next:
                IP = vvX(FRAMES)->ip;
        }

        if (n < sz && CompilationDepth(ty) > 1) {
                snprintf(
                        ERR + n,
                        sz - n,
                        "\n%s%sCompilation context:%s\n%s",
                        TERM(1),
                        TERM(34),
                        TERM(0),
                        CompilationTrace(ty)
                );
        }

        LOG("VM Error: %s", ERR);

        longjmp(jb, 1);
}

bool
vm_execute_file(Ty *ty, char const *path)
{
        char *source = slurp(ty, path);
        if (source == NULL) {
                snprintf(
                        ERR,
                        sizeof ERR,
                        "%s%s%s: failed to read source file: %s%s%s",
                        TERM(91;1), "Error", TERM(0),
                        TERM(95), path, TERM(0)
                );
                Error = ERR;
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

#ifdef TY_ENABLE_PROFILING
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
#endif

bool
vm_execute(Ty *ty, char const *source, char const *file)
{
        filename = file;

        GC_STOP();

        gc_clear_root_set(ty);
        STACK.count = 0;
        sp_stack.count = 0;
        try_stack.count = 0;
        TARGETS.count = 0;

        char * volatile code = NULL;

        if (setjmp(jb) != 0) {
                Error = ERR;
                filename = NULL;
                return false;
        }

        code = compiler_compile_source(ty, source, filename);
        if (code == NULL) {
                filename = NULL;
                Error = compiler_error(ty);
                LOG("compiler error was: %s", Error);
                return false;
        }

        GC_RESUME();

        if (CompileOnly) {
                filename = NULL;
                return true;
        }

        vm_exec(ty, code);

        if (PrintResult && STACK.capacity > 0) {
                printf("%s\n", value_show(ty, top(ty) + 1));
        }

#ifdef TY_ENABLE_PROFILING
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

        fprintf(ProfileOut, "%s===== profile by function =====%s\n\n", PTERM(95), PTERM(0));
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
                                entry->count,
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
                                entry->count,
                                PTERM(93),
                                PTERM(1),
                                GC_ENTRY,
                                PTERM(0)
                        );
                } else {
                        Value f = FUNCTION();
                        f.info = entry->ctx;
                        char *f_string = value_show_color(ty, &f);
                        fprintf(
                                ProfileOut,
                                "   %s%5.1f%%  %-14lld  %s\n",
                                color_buffer,
                                entry->count / total_ticks * 100.0,
                                entry->count,
                                f_string
                        );
                        mF(f_string);
                }
        }

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
        uint64_t reported_ticks = 0;
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

                char const *filename = strrchr(expr->filename, '/');
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
                        "   %s%5.1f%%  %-13lld %s%16s %s%18s%s:%s%-5d%s  |  %s  %lu\n",
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
                        code_buffer,
                        (uintptr_t)entry->ctx
                );
        }

        fputc('\n', ProfileOut);

        byte_vector prog_text = {0};
        DumpProgram(ty, &prog_text, filename, code, NULL);
        fwrite(prog_text.items, 1, prog_text.count, stdout);
        fputc('\n', ProfileOut);
        fputc('\n', ProfileOut);
#endif

        filename = NULL;

        return true;
}

void
vm_push(Ty *ty, Value const *v)
{
        push(ty, *v);
}

void
vm_pop(Ty *ty)
{
        STACK.count -= 1;
}

Value *
vm_get(Ty *ty, int i)
{
        return top(ty) - i;
}

_Noreturn void
vm_throw(Ty *ty, Value const *v)
{
        push(ty, *v);
        vm_exec(ty, (char[]){INSTR_THROW});
        // unreachable
        abort();
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
        return pop(ty);
}

Value
vm_call_ex(Ty *ty, Value const *f, int argc, Value const *kwargs, bool collect)
{
        Value r, *init;
        size_t n = STACK.count - argc;

        switch (f->type) {
        case VALUE_FUNCTION:
                if (kwargs != NULL) {
                        push(ty, *kwargs);
                        call(ty, f, NULL, argc, 1, true);
                } else {
                        call(ty, f, NULL, argc, 0, true);
                }
                goto Collect;
        case VALUE_METHOD:
                if (kwargs != NULL) {
                        push(ty, *kwargs);
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
                r = pop(ty);
                r.tags = tags_push(ty, r.tags, f->tag);
                r.type |= VALUE_TAGGED;
                return r;
        case VALUE_CLASS:
                init = class_method(ty, f->class, "init");
                if (f->class < CLASS_PRIMITIVE) {
                        if (init != NULL) {
                                call(ty, init, NULL, argc, 0, true);
                                return pop(ty);
                        } else {
                                zP("Couldn't find init method for built-in class. Was prelude loaded?");
                        }
                } else {
                        r = OBJECT(object_new(ty, f->class), f->class);
                        if (init != NULL) {
                                call(ty, init, &r, argc, 0, true);
                                pop(ty);
                        } else {
                                STACK.count -= (argc + 1);
                        }
                        return r;
                }
        default:
                zP("Non-callable value passed to vmC(): %s", value_show_color(ty, f));
        }

Collect:

        if (!collect) {
                STACK.count = n + 1;
                return pop(ty);
        }

        STACK.count += rc;
        rc = 0;

        Value xs = ARRAY(vA());
        NOGC(xs.array);
        for (size_t i = n; i < STACK.count; ++i) {
                vAp(xs.array, STACK.items[i]);
        }
        OKGC(xs.array);

        STACK.count = n;

        return xs;
}

Value
vm_call(Ty *ty, Value const *f, int argc)
{
        Value r, *init;
        size_t n = STACK.count - argc;

        switch (f->type) {
        case VALUE_FUNCTION:
                call(ty, f, NULL, argc, 0, true);
                return pop(ty);
        case VALUE_METHOD:
                call(ty, f->method, f->this, argc, 0, true);
                return pop(ty);
        case VALUE_BUILTIN_FUNCTION:
                r = f->builtin_function(ty, argc, NULL);
                STACK.count = n;
                return r;
        case VALUE_BUILTIN_METHOD:
                r = f->builtin_method(ty, f->this, argc, NULL);
                STACK.count = n;
                return r;
        case VALUE_TAG:
                r = pop(ty);
                r.tags = tags_push(ty, r.tags, f->tag);
                r.type |= VALUE_TAGGED;
                return r;
        case VALUE_CLASS:
                init = class_method(ty, f->class, "init");
                if (f->class < CLASS_PRIMITIVE) {
                        if (init != NULL) {
                                call(ty, init, NULL, argc, 0, true);
                                return pop(ty);
                        } else {
                                zP("Couldn't find init method for built-in class. Was prelude loaded?");
                        }
                } else {
                        r = OBJECT(object_new(ty, f->class), f->class);
                        if (init != NULL) {
                                call(ty, init, &r, argc, 0, true);
                                pop(ty);
                        } else {
                                STACK.count -= (argc + 1);
                        }
                        return r;
                }
        default:
                zP("Non-callable value passed to vmC(): %s", value_show_color(ty, f));
        }
}

Value
vm_eval_function(Ty *ty, Value const *f, ...)
{
        int argc;
        va_list ap;
        Value r;
        Value const *v;

        va_start(ap, f);
        argc = 0;

        while ((v = va_arg(ap, Value const *)) != NULL) {
                push(ty, *v);
                argc += 1;
        }

        va_end(ap);

        size_t n = STACK.count - argc;

        switch (f->type) {
        case VALUE_FUNCTION:
                call(ty, f, NULL, argc, 0, true);
                return pop(ty);
        case VALUE_METHOD:
                call(ty, f->method, f->this, argc, 0, true);
                return pop(ty);
        case VALUE_BUILTIN_FUNCTION:
                r = f->builtin_function(ty, argc, NULL);
                STACK.count = n;
                return r;
        case VALUE_BUILTIN_METHOD:
                r = f->builtin_method(ty, f->this, argc, NULL);
                STACK.count = n;
                return r;
        case VALUE_TAG:
                DoTag(ty, f->tag, argc, NULL);
                return pop(ty);
        default:
                zP("Non-callable value passed to vm_eval_function(ty): %s", value_show_color(ty, f));
        }
}

Value
vm_2op(Ty *ty, int op, Value const *a, Value const *b)
{
        push(ty, *a);
        push(ty, *b);

        switch (op) {
        case OP_CMP: DoCmp(ty); return pop(ty);
        case OP_EQL: DoEq(ty);  return pop(ty);
        case OP_NEQ: DoNeq(ty); return pop(ty);
        case OP_GEQ: DoGeq(ty); return pop(ty);
        case OP_LEQ: DoLeq(ty); return pop(ty);
        case OP_GT:  DoGt(ty);  return pop(ty);
        case OP_LT:  DoLt(ty);  return pop(ty);
        case OP_ADD: if (op_builtin_add(ty)) return pop(ty); break;
        case OP_SUB: if (op_builtin_sub(ty)) return pop(ty); break;
        case OP_MUL: if (op_builtin_mul(ty)) return pop(ty); break;
        case OP_DIV: if (op_builtin_div(ty)) return pop(ty); break;
        case OP_MOD: if (op_builtin_mod(ty)) return pop(ty); break;
        }

        DoBinaryOp(ty, op, true);

        return pop(ty);
}

Value
vm_try_2op(Ty *ty, int op, Value const *a, Value const *b)
{

        int i = op_dispatch(op, ClassOf(a), ClassOf(b));

        if (i == -1) {
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

        push(ty, *a);
        push(ty, *b);

        call(ty, &Globals.items[i], NULL, 2, 0, true);

        return pop(ty);
}

void
MarkStorage(Ty *ty, ThreadStorage const *storage)
{
        vec(Value const *) *root_set = storage->root_set;

        GCLOG("Marking root set (%zu items)", gc_root_set_count(ty));
        for (int i = 0; i < root_set->count; ++i) {
                value_mark(ty, root_set->items[i]);
        }

        GCLOG("Marking stack");
        for (int i = 0; i < storage->stack->count; ++i) {
                value_mark(ty, &storage->stack->items[i]);
        }

        GCLOG("Marking defer_stack");
        for (int i = 0; i < storage->defer_stack->count; ++i) {
                value_mark(ty, &storage->defer_stack->items[i]);
        }

        GCLOG("Marking drop stack");
        for (int i = 0; i < storage->drop_stack->count; ++i) {
                value_mark(ty, &storage->drop_stack->items[i]);
        }

        GCLOG("Marking targets");
        for (int i = 0; i < storage->targets->count; ++i) {
                if ((((uintptr_t)storage->targets->items[i].t) & 0x07) == 0) {
                        value_mark(ty, storage->targets->items[i].t);
                }
        }

        GCLOG("Marking frame functions");
        for (int i = 0; i < storage->frames->count; ++i) {
                value_mark(ty, &storage->frames->items[i].f);
        }

        // FIXME: should finalizers be allowed to keep things alive?
        return;

        GCLOG("Marking finalizers");
        for (int i = 0; i < storage->allocs->count; ++i) {
                if (storage->allocs->items[i]->type == GC_OBJECT) {
                        value_mark(ty, &((ValueTable *)storage->allocs->items[i]->data)->finalizer);
                }
        }
}

char const *
GetInstructionName(uint8_t i)
{
        return InstructionNames[i];
}

/* vim: set sts=8 sw=8 expandtab: */
