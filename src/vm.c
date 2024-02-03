#include <time.h>
#include <string.h>
#include <ctype.h>
#include <stdlib.h>
#include <stdbool.h>
#include <setjmp.h>
#include <stdarg.h>
#include <stdatomic.h>
#include <errno.h>
#include <stdnoreturn.h>
#include <locale.h>

#include <pcre.h>
#include <curl/curl.h>

#include <poll.h>
#include <fcntl.h>
#include <unistd.h>
#include <signal.h>
#include <dirent.h>
#include <pthread.h>
#include <termios.h>

#include "barrier.h"

#ifdef __linux__
#include <sys/epoll.h>
#endif

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
#include "class.h"
#include "utf8.h"
#include "functions.h"
#include "html.h"
#include "curl.h"
#include "sqlite.h"
#include "queue.h"

#define TY_LOG_VERBOSE 1

#define READVALUE(s) (memcpy(&s, ip, sizeof s), (ip += sizeof s))

#if defined(TY_LOG_VERBOSE) && !defined(TY_NO_LOG)
  #define CASE(i) case INSTR_ ## i: fname = compiler_get_location(ip, &loc, &loc); XLOG("%s:%d:%d: " #i, fname, loc.line + 1, loc.col + 1);
#else
  #define XCASE(i) case INSTR_ ## i: fname = compiler_get_location(ip, &loc, &loc); XLOG("%s:%d:%d: " #i, fname, loc.line + 1, loc.col + 1);
  #define CASE(i) case INSTR_ ## i:
#endif

#define inline __attribute__((always_inline)) inline

#define MatchError \
        push(TAG(gettag(NULL, "MatchError"))); \
        goto Throw;

static char halt = INSTR_HALT;
static char next_fix[] = { INSTR_NONE_IF_NIL, INSTR_RETURN_PRESERVE_CTX };
static char iter_fix[] = { INSTR_SENTINEL, INSTR_RETURN_PRESERVE_CTX };

static char const *MISSING = "__missing__";
static int iExitHooks = -1;

static _Thread_local jmp_buf jb;

typedef struct {
        int argc;
        struct value *argv;
        struct value (*f)(int);
} BuiltinCall;

static vec(BuiltinCall) builtin_calls;

struct try {
        jmp_buf jb;
        int sp;
        int gc;
        int cs;
        int ts;
        int ctxs;
        char *catch;
        char *finally;
        char *end;
        bool executing;
};

typedef struct ThrowCtx {
        int ctxs;
        char const *ip;
} ThrowCtx;

static vec(struct value) Globals;

struct sigfn {
        int sig;
        struct value f;
};

#define FRAME(n, fn, from) ((Frame){ .fp = (n), .f = (fn), .ip = (from) })

typedef vec(struct value) ValueStack;
typedef vec(char const *) StringVector;
typedef vec(struct try) TryStack;
typedef vec(struct sigfn) SigfnStack;

static SigfnStack sigfns;

static _Thread_local ValueStack stack;
static _Thread_local CallStack calls;
static _Thread_local FrameStack frames;
static _Thread_local SPStack sp_stack;
static _Thread_local TargetStack targets;
static _Thread_local TryStack try_stack;
static _Thread_local vec(ThrowCtx) throw_stack;
static _Thread_local ValueStack defer_stack;
static _Thread_local char *ip;

typedef struct {
        ValueStack stack;
        CallStack calls;
        FrameStack frames;
        SPStack sp_stack;
        TargetStack targets;
        TryStack try_stack;
        char *ip;
        bool waiting;
} TyThread;

typedef struct {
        ValueStack *stack;
        FrameStack *frames;
        TargetStack *targets;
        ValueStack *defer_stack;
        void *root_set;
        AllocList *allocs;
        size_t *MemoryUsed;
} ThreadStorage;

static vec(TyThread) Threads;
static int ThreadIndex;

static char const *filename;
static char const *Error;
bool CompileOnly = false;
bool PrintResult = false;

pthread_t BuiltinRunner;
pthread_t MainThread;

MessageQueue q1;
MessageQueue q2;

typedef struct thread_group {
        pthread_mutex_t Lock;
        pthread_mutex_t GCLock;
        vec(pthread_t) ThreadList;
        vec(pthread_mutex_t *) ThreadLocks;
        vec(ThreadStorage) ThreadStorages;
        vec(_Atomic bool *) ThreadStates;
        atomic_bool WantGC;
        pthread_barrier_t GCBarrierStart;
        pthread_barrier_t GCBarrierMark;
        pthread_barrier_t GCBarrierSweep;
        pthread_barrier_t GCBarrierDone;
        pthread_mutex_t DLock;
        AllocList DeadAllocs;
        size_t DeadUsed;
} ThreadGroup;

typedef struct {
        atomic_bool *created;
        struct value *ctx;
        struct value *name;
        Thread *t;
        ThreadGroup *group;
} NewThreadCtx;


static ThreadGroup MainGroup;

static pthread_rwlock_t SigLock = PTHREAD_RWLOCK_INITIALIZER;

_Thread_local pthread_mutex_t *MyLock;
static _Thread_local _Atomic bool *MyState;
static _Thread_local ThreadStorage MyStorage;
static _Thread_local ThreadGroup *MyGroup;
static _Thread_local bool GCInProgress;

void
MarkStorage(ThreadStorage const *storage);

static void
LockThreads(int *threads, int n)
{
        for (int i = 0; i < n; ++i) {
                pthread_mutex_lock(MyGroup->ThreadLocks.items[threads[i]]);
        }
}

inline static void
UnlockThreads(int *threads, int n)
{
        for (int i = 0; i < n; ++i) {
                pthread_mutex_unlock(MyGroup->ThreadLocks.items[threads[i]]);
        }
}

inline static void
SetState(bool blocking)
{
        atomic_store(MyState, blocking);
}

void
Forget(struct value *v, AllocList *allocs)
{
        size_t n = MyStorage.allocs->count;

        value_mark(v);
        GCForget(MyStorage.allocs, MyStorage.MemoryUsed);

        for (size_t i = MyStorage.allocs->count; i < n; ++i) {
                vec_push_unchecked(*allocs, MyStorage.allocs->items[i]);
        }
}

static void
InitThreadGroup(ThreadGroup *g)
{
        vec_init(g->ThreadList);
        vec_init(g->ThreadStates);
        vec_init(g->ThreadStorages);
        vec_init(g->ThreadLocks);
        vec_init(g->DeadAllocs);
        pthread_mutex_init(&g->Lock, NULL);
        pthread_mutex_init(&g->GCLock, NULL);
        pthread_mutex_init(&g->DLock, NULL);
        atomic_store(&g->WantGC, false);
        g->DeadUsed = 0;

}

static ThreadGroup *
NewThreadGroup(void)
{
        ThreadGroup *g = gc_alloc(sizeof *g);
        InitThreadGroup(g);
        return g;
}

static void
WaitGC()
{
        if (GCInProgress)
                return;

        GCLOG("Waiting for GC on thread %llu", TID);

        ReleaseLock(false);

        while (!atomic_load(MyState)) {
                if (!atomic_load(&MyGroup->WantGC)) {
                        SetState(true);
                        TakeLock();
                        return;
                }
        }

        TakeLock();

        GCLOG("Waiting to mark: %llu", TID);
        pthread_barrier_wait(&MyGroup->GCBarrierStart);
        GCLOG("Marking: %llu", TID);
        MarkStorage(&MyStorage);

        GCLOG("Waiting to sweep: %llu", TID);
        pthread_barrier_wait(&MyGroup->GCBarrierMark);
        GCLOG("Sweeping: %llu", TID);
        GCSweep(MyStorage.allocs, MyStorage.MemoryUsed);

        GCLOG("Waiting to continue execution: %llu", TID);
        pthread_barrier_wait(&MyGroup->GCBarrierSweep);
        pthread_barrier_wait(&MyGroup->GCBarrierDone);
        GCLOG("Continuing execution: %llu", TID);
}

void
DoGC()
{
        GCLOG("Trying to do GC. Used = %zu, DeadUsed = %zu", MemoryUsed, MyGroup->DeadUsed);

        if (pthread_mutex_trylock(&MyGroup->GCLock) != 0) {
                GCLOG("Couldn't take GC lock: calling WaitGC() on thread %llu", TID);
                WaitGC();
                return;
        }

        GCInProgress = true;

        pthread_mutex_lock(&MyGroup->Lock);

        GCLOG("Doing GC: MyGroup = %p, (%zu threads)", MyGroup, MyGroup->ThreadList.count);

        GCLOG("Took threads lock on thread %llu to do GC", TID);

        GCLOG("Storing true in WantGC on thread %llu", TID);
        atomic_store(&MyGroup->WantGC, true);

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

        pthread_t me = pthread_self();

        for (int i = 0; i < MyGroup->ThreadList.count; ++i) {
                if (pthread_equal(me, MyGroup->ThreadList.items[i])) {
                        continue;
                }
                GCLOG("Trying to take lock for thread %llu: %p", (long long unsigned)MyGroup->ThreadList.items[i], (void *)MyGroup->ThreadLocks.items[i]);
                pthread_mutex_lock(MyGroup->ThreadLocks.items[i]);
                if (atomic_load(MyGroup->ThreadStates.items[i])) {
                        GCLOG("Thread %llu is blocked", (long long unsigned)MyGroup->ThreadList.items[i]);
                        blockedThreads[nBlocked++] = i;
                } else {
                        GCLOG("Thread %llu is running", (long long unsigned)MyGroup->ThreadList.items[i]);
                        runningThreads[nRunning++] = i;
                        atomic_store(MyGroup->ThreadStates.items[i], true);
                }
        }

        GCLOG("nBlocked = %d, nRunning = %d on thread %llu", nBlocked, nRunning, TID);

        pthread_barrier_init(&MyGroup->GCBarrierStart, NULL, nRunning + 1);
        pthread_barrier_init(&MyGroup->GCBarrierMark, NULL, nRunning + 1);
        pthread_barrier_init(&MyGroup->GCBarrierSweep, NULL, nRunning + 1);
        pthread_barrier_init(&MyGroup->GCBarrierDone, NULL, nRunning + 1);

        UnlockThreads(runningThreads, nRunning);

        pthread_barrier_wait(&MyGroup->GCBarrierStart);

        for (int i = 0; i < nBlocked; ++i) {
                GCLOG("Marking thread %llu storage from thread %llu", (long long unsigned)MyGroup->ThreadList.items[blockedThreads[i]], TID);
                MarkStorage(&MyGroup->ThreadStorages.items[blockedThreads[i]]);
        }

        GCLOG("Marking own storage on thread %llu", TID);
        MarkStorage(&MyStorage);

        if (MyGroup == &MainGroup) {
                for (int i = 0; i < Globals.count; ++i) {
                        value_mark(&Globals.items[i]);
                }
        }

        pthread_barrier_wait(&MyGroup->GCBarrierMark);

        GCLOG("Storing false in WantGC on thread %llu", TID);
        atomic_store(&MyGroup->WantGC, false);

        for (int i = 0; i < nBlocked; ++i) {
                GCLOG("Sweeping thread %llu storage from thread %llu", (long long unsigned)MyGroup->ThreadList.items[blockedThreads[i]], TID);
                GCSweep(
                        MyGroup->ThreadStorages.items[blockedThreads[i]].allocs,
                        MyGroup->ThreadStorages.items[blockedThreads[i]].MemoryUsed
                );
        }

        GCLOG("Sweeping own storage on thread %llu", TID);
        GCSweep(MyStorage.allocs, MyStorage.MemoryUsed);

        GCLOG("Sweeping objects from dead threads on thread %llu", TID);
        pthread_mutex_lock(&MyGroup->DLock);
        GCSweep(&MyGroup->DeadAllocs, &MyGroup->DeadUsed);
        pthread_mutex_unlock(&MyGroup->DLock);

        pthread_barrier_wait(&MyGroup->GCBarrierSweep);

        UnlockThreads(blockedThreads, nBlocked);

        GCLOG("Unlocking ThreadsLock and GCLock. Used = %zu, DeadUsed = %zu", MemoryUsed, MyGroup->DeadUsed);

        pthread_mutex_unlock(&MyGroup->Lock);
        pthread_mutex_unlock(&MyGroup->GCLock);

        GCLOG("Unlocked ThreadsLock and GCLock on thread %llu", TID);

        pthread_barrier_wait(&MyGroup->GCBarrierDone);

        GCInProgress = false;
}

static struct {
        char const *module;
        char const *name;
        struct value value;
} builtins[] = {
#include "builtins.h"
};

static int builtin_count = sizeof builtins / sizeof builtins[0];

pcre_jit_stack *JITStack = NULL;

inline static void
PopulateGlobals(void)
{
        int n = compiler_global_count();

        while (Globals.count < n) {
                vec_push_unchecked(Globals, NIL);
        }
}

static void
add_builtins(int ac, char **av)
{
        for (int i = 0; i < builtin_count; ++i) {
                compiler_introduce_symbol(builtins[i].module, builtins[i].name);
                if (builtins[i].value.type == VALUE_BUILTIN_FUNCTION) {
                        builtins[i].value.name = builtins[i].name;
                        builtins[i].value.module = builtins[i].module;
                }
                vec_push(Globals, builtins[i].value);
        }

        struct array *args = value_array_new();
        NOGC(args);

        for (int i = 1; i < ac; ++i)
                value_array_push(args, STRING_NOGC(av[i], strlen(av[i])));

        compiler_introduce_symbol("os", "args");
        vec_push(Globals, ARRAY(args));

        compiler_introduce_symbol(NULL, "__EXIT_HOOKS__");
        iExitHooks = (int)Globals.count;
        vec_push(Globals, ARRAY(value_array_new()));

#ifdef SIGRTMIN
        /* Add this here because SIGRTMIN doesn't expand to a constant */
        compiler_introduce_symbol("os", "SIGRTMIN");
        vec_push(Globals, INTEGER(SIGRTMIN));
#endif

#define X(name) \
        do { \
                compiler_introduce_tag("ty", #name); \
                vec_push(Globals, TAG(Ty ## name)); \
        } while (0);

        TY_AST_NODES

#undef X
}

void
vm_load_c_module(char const *name, void *p)
{
        struct {
                char const *name;
                struct value value;
        } *mod = p;

        int n = 0;
        while (mod[n].name != NULL)
                n += 1;

        for (int i = 0; i < n; ++i) {
                compiler_introduce_symbol(name, mod[i].name);
                vec_push(Globals, mod[i].value);
        }
}

inline static struct value *
top(void)
{
        return &stack.items[stack.count] - 1;
}

static void
print_stack(int n)
{
#ifndef TY_NO_LOG
        LOG("STACK: (%zu)", stack.count);
        for (int i = 0; i < n && i < stack.count; ++i) {
                if (frames.count > 0 && stack.count - (i + 1) == vec_last(frames)->fp) {
                        LOG(" -->  %s", value_show(top() - i));
                } else {
                        LOG("      %s", value_show(top() - i));
                }
        }
#endif
}

inline static struct value
pop(void)
{
        LOG("POP: %s", value_show(top()));
        struct value v = *vec_pop(stack);
        print_stack(15);
        return v;
}

inline static struct value
peek(void)
{
        return stack.items[stack.count - 1];
}

inline static void
push(struct value v)
{
        vec_nogc_push(stack, v);
        LOG("PUSH: %s", value_show(&v));
        print_stack(10);
}

inline static struct value *
local(int i)
{
        return &stack.items[vec_last(frames)->fp + i];
}

inline static struct value *
poptarget(void)
{
        Target t = *vec_pop(targets);
        if (t.gc != NULL) OKGC(t.gc);
        LOG("Popping Target: %p", (void *)t.t);
        return t.t;
}

inline static struct value *
peektarget(void)
{
        return targets.items[targets.count - 1].t;
}

inline static void
pushtarget(struct value *v, void *gc)
{
        Target t = { .t = v, .gc = gc };
        if (gc != NULL) NOGC(gc);
        vec_push(targets, t);
        LOG("TARGETS: (%zu)", targets.count);
        for (int i = 0; i < targets.count; ++i) {
                LOG("\t%d: %p", i + 1, (void *)targets.items[i].t);
        }
}

inline static bool
SpecialTarget(void)
{
        return (((uintptr_t)targets.items[targets.count - 1].t) & 0x07) != 0;
}

#ifdef TY_RELEASE
inline
#else
__attribute__((optnone, noinline))
#endif
static void
call(struct value const *f, struct value const *pSelf, int n, int nkw, bool exec)
{
        int bound = f->info[3];
        int np = f->info[4];
        int irest = ((int16_t *)(f->info + 5))[0];
        int ikwargs = ((int16_t *)(f->info + 5))[1];
        int class = f->info[6];
        char *code = code_of(f);
        int argc = n;

        struct value self = (pSelf == NULL) ? NONE : *pSelf;

        struct value kwargs = (nkw > 0) ? pop() : NIL;

        /*
         * This is the index of the beginning of the stack frame for this call to f.
         */
        int fp = stack.count - n;

        /*
         * Default missing arguments to NIL and make space for all of this function's local variables.
         */
        while (n < bound) {
                push(NIL);
                n += 1;
        }

        GC_OFF_COUNT += 1;

        /*
         * If the function was declared with the form f(..., *extra) then we
         * create an array and add any extra arguments to it.
         */
        if (irest != -1) {
                struct array *extra = value_array_new();

                for (int i = irest; i < argc; ++i) {
                        value_array_push(extra, stack.items[fp + i]);
                }

                for (int i = irest; i < argc; ++i) {
                        stack.items[fp + i] = NIL;
                }

                stack.items[fp + irest] = ARRAY(extra);
        }

        if (ikwargs != -1) {
                stack.items[fp + ikwargs] = (nkw > 0) ? kwargs : DICT(dict_new());
        }

        GC_OFF_COUNT -= 1;

        /*
         * Throw away extra arguments.
         */
        while (n > bound) {
                pop();
                n -= 1;
        }

        /*
         * Fill in 'self' as an implicit additional parameter.
         */
        if (self.type != VALUE_NONE && class != -1) {
                LOG("setting self = %s", value_show(&self));
                stack.items[fp + np] = self;
        }

        vec_push_unchecked(frames, FRAME(fp, *f, ip));

        /* Fill in keyword args (overwriting positional args) */
        if (kwargs.type != VALUE_NIL) {
                char const *name = name_of(f);
                for (int i = 0; i < np; ++i) {
                        name += strlen(name) + 1;
                        if (i == irest || i == ikwargs) {
                                continue;
                        }
                        struct value *arg = dict_get_member(kwargs.dict, name);
                        if (arg != NULL) {
                                *local(i) = *arg;
                        }
                }
        }

        LOG("Calling %s with %d args, bound = %d, self = %s, env size = %d", value_show(f), argc, bound, value_show(&self), f->info[2]);
        print_stack(max(bound + 2, 5));

        if (exec) {
                vec_push_unchecked(calls, &halt);
                gc_push(f);
                vm_exec(code);
                gc_pop();
        } else {
                vec_push_unchecked(calls, ip);
                ip = code;
        }
}

inline static void
call_co(struct value *v, int n)
{
        if (v->gen->ip != code_of(&v->gen->f)) {
                if (n == 0) {
                        vec_push_unchecked(v->gen->frame, NIL);
                } else {
                        vec_nogc_push_n(v->gen->frame, top() - (n - 1), n);
                        stack.count -= n;
                }
        }

        push(*v);
        call(&v->gen->f, NULL, 0, 0, false);
        stack.count = vec_last(frames)->fp;

        if (v->gen->frames.count == 0) {
                vec_push(v->gen->frames, *vec_last(frames));
        } else {
                v->gen->frames.items[0] = *vec_last(frames);
        }

        int diff = (int)stack.count - v->gen->fp;
        for (int i = 1; i < v->gen->frames.count; ++i) {
                v->gen->frames.items[i].fp += diff;
        }

        v->gen->fp = stack.count;

        SWAP(CallStack, v->gen->calls, calls);
        SWAP(TargetStack, v->gen->targets, targets);
        SWAP(SPStack, v->gen->sps, sp_stack);
        SWAP(FrameStack, v->gen->frames, frames);

        for (int i = 0; i < v->gen->frame.count; ++i) {
                push(v->gen->frame.items[i]);
        }

        ip = v->gen->ip;
}

void
TakeLock(void)
{
        GCLOG("Taking MyLock%s", "");
        pthread_mutex_lock(MyLock);
        GCLOG("Took MyLock");
}

void
ReleaseLock(bool blocked)
{
        SetState(blocked);
        GCLOG("Releasing MyLock: %d", (int)blocked);
        pthread_mutex_unlock(MyLock);
}

void
NewThread(Thread *t, struct value *call, struct value *name, bool isolated)
{
        ReleaseLock(true);

        static _Thread_local atomic_bool created;

        NewThreadCtx *ctx = malloc(sizeof *ctx);
        *ctx = (NewThreadCtx) {
                .ctx = call,
                .name = name,
                .created = &created,
                .t = t,
                .group = isolated ? NewThreadGroup() : MyGroup
        };
        atomic_store(&created, false);

#if !defined(TY_RELEASE)
        pthread_attr_t attr;
        pthread_attr_init(&attr);
        int r = pthread_attr_setstacksize(&attr, 1ULL << 26);
        if (r != 0)
                vm_panic("pthread_attr_setstacksize(): %s", strerror(r));
        r = pthread_create(&t->t, &attr, vm_run_thread, ctx);
#else
        int r = pthread_create(&t->t, NULL, vm_run_thread, ctx);
#endif

        if (r != 0)
                vm_panic("pthread_create(): %s", strerror(r));

        while (!atomic_load(&created))
                ;

        TakeLock();
}

static void
AddThread(void)
{
        GCLOG("AddThread(): %llu: taking lock", (long long unsigned)pthread_self());

        pthread_mutex_lock(&MyGroup->Lock);

        GCLOG("AddThread(): %llu: took lock", (long long unsigned)pthread_self());

        ++GC_OFF_COUNT;

        vec_push(MyGroup->ThreadList, pthread_self());

        MyLock = malloc(sizeof *MyLock);
        pthread_mutex_init(MyLock, NULL);
        pthread_mutex_lock(MyLock);
        vec_push(MyGroup->ThreadLocks, MyLock);

        MyStorage = (ThreadStorage) {
                .stack = &stack,
                .frames = &frames,
                .defer_stack = &defer_stack,
                .targets = &targets,
                .root_set = GCRootSet(),
                .allocs = &allocs,
                .MemoryUsed = &MemoryUsed
        };

        vec_push(MyGroup->ThreadStorages, MyStorage);

        MyState = malloc(sizeof *MyState);
        *MyState = false;
        vec_push(MyGroup->ThreadStates, MyState);

        --GC_OFF_COUNT;

        pthread_mutex_unlock(&MyGroup->Lock);

        GCLOG("AddThread(): %llu: finished", (long long unsigned)pthread_self());
}

static void
CleanupThread(void *ctx)
{
        GCLOG("Cleaning up thread: %zu bytes in use. DeadUsed = %zu", MemoryUsed, MyGroup->DeadUsed);

        pthread_mutex_lock(&MyGroup->DLock);

        if (MyGroup->DeadUsed + MemoryUsed > MemoryLimit) {
                pthread_mutex_unlock(&MyGroup->DLock);
                DoGC();
                pthread_mutex_lock(&MyGroup->DLock);
        }

        vec_push_n_unchecked(MyGroup->DeadAllocs, allocs.items, allocs.count);
        MyGroup->DeadUsed += MemoryUsed;

        allocs.count = 0;

        pthread_mutex_unlock(&MyGroup->DLock);

        ReleaseLock(true);

        pthread_mutex_lock(&MyGroup->Lock);

        GCLOG("Got threads lock on thread: %llu -- ready to clean up", TID);

        for (int i = 0; i < MyGroup->ThreadList.count; ++i) {
                if (pthread_equal(MyGroup->ThreadList.items[i], pthread_self())) {
                        MyGroup->ThreadList.items[i] = *vec_pop(MyGroup->ThreadList);
                        MyGroup->ThreadLocks.items[i] = *vec_pop(MyGroup->ThreadLocks);
                        MyGroup->ThreadStorages.items[i] = *vec_pop(MyGroup->ThreadStorages);
                        MyGroup->ThreadStates.items[i] = *vec_pop(MyGroup->ThreadStates);
                }
        }

        pthread_mutex_unlock(&MyGroup->Lock);

        pthread_mutex_destroy(MyLock);
        free(MyLock);
        free(MyState);
        free(stack.items);
        gc_free(calls.items);
        gc_free(frames.items);
        gc_free(sp_stack.items);
        gc_free(targets.items);
        gc_free(try_stack.items);
        gc_free(throw_stack.items);
        gc_free(defer_stack.items);
        free(allocs.items);

        vec(struct value const *) *root_set = GCRootSet();
        free(root_set->items);

        if (MyGroup->ThreadList.count == 0) {
                pthread_mutex_destroy(&MyGroup->Lock);
                pthread_mutex_destroy(&MyGroup->GCLock);
                pthread_mutex_destroy(&MyGroup->DLock);
                gc_free(MyGroup->ThreadList.items);
                gc_free(MyGroup->ThreadLocks.items);
                gc_free(MyGroup->ThreadStates.items);
                gc_free(MyGroup->ThreadStorages.items);
                gc_free(MyGroup->DeadAllocs.items);
                gc_free(MyGroup);
        }

        GCLOG("Finished cleaning up on thread: %llu -- releasing threads lock", TID);
}

void *
vm_run_thread(void *p)
{
        NewThreadCtx *ctx = p;
        struct value *call = ctx->ctx;
        struct value *name = ctx->name;
        Thread *t = ctx->t;

        int argc = 0;

        GCLOG("New thread: %llu", (long long unsigned)pthread_self());

        while (call[argc + 1].type != VALUE_NONE) {
                push(call[++argc]);
        }

        MyGroup = ctx->group;

        AddThread();

        gc_push(&call[0]);

        if (name != NULL) {
                push(*name);
                builtin_thread_setname(1, NULL);
                pop();
        }

        pthread_cleanup_push(CleanupThread, NULL);

        atomic_store(ctx->created, true);

        if (setjmp(jb) != 0) {
                // TODO: do something useful here
                fprintf(stderr, "Thread %p dying with error: %s\n", (void *)pthread_self(), ERR);
                t->v = NIL;
        } else {
                t->v = vm_call(call, argc);
        }

        pthread_cleanup_pop(1);

        free(ctx);
        gc_free(call);
        OKGC(t);

        return &t->v;
}


void
vm_del_sigfn(int sig)
{
        pthread_rwlock_wrlock(&SigLock);

        for (int i = 0; i < sigfns.count; ++i) {
                if (sigfns.items[i].sig == sig) {
                        struct sigfn t = *vec_last(sigfns);
                        *vec_last(sigfns) = sigfns.items[i];
                        sigfns.items[i] = t;
                        vec_pop(sigfns);
                        break;
                }
        }

        pthread_rwlock_unlock(&SigLock);
}

void
vm_set_sigfn(int sig, struct value const *f)
{
        pthread_rwlock_wrlock(&SigLock);

        for (int i = 0; i < sigfns.count; ++i) {
                if (sigfns.items[i].sig == sig) {
                        sigfns.items[i].f = *f;
                        goto End;
                }
        }

        vec_push(sigfns, ((struct sigfn){ .sig = sig, .f = *f }));

End:
        pthread_rwlock_unlock(&SigLock);
}

struct value
vm_get_sigfn(int sig)
{
        struct value f = NIL;

        pthread_rwlock_rdlock(&SigLock);

        for (int i = 0; i < sigfns.count; ++i) {
                if (sigfns.items[i].sig == sig) {
                        f = sigfns.items[i].f;
                        break;
                }
        }

        pthread_rwlock_unlock(&SigLock);

        return f;
}

void
vm_do_signal(int sig, siginfo_t *info, void *ctx)
{
        struct value f = NIL;

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
        case SIGIO:
#ifdef __APPLE__
                push(INTEGER(info->si_value.sival_int));
#else
                push(INTEGER(info->si_fd));
#endif
                vm_call(&f, 1);
                break;
        default:
                vm_call(&f, 0);
        }
}

inline static void
AddTupleEntry(StringVector *names, ValueVector *values, char const *name, struct value const *v)
{
        for (int i = 0; i < names->count; ++i) {
                if (names->items[i] != NULL && strcmp(names->items[i], name) == 0) {
                        values->items[i] = *v;
                        return;
                }
        }

        vec_push(*names, name);
        vec_push(*values, *v);
}

struct value
GetMember(struct value v, char const *member, unsigned long h, bool b)
{

        int n;
        struct value *vp = NULL, *this;
        struct value (*func)(struct value *, int, struct value *);

        if (v.type & VALUE_TAGGED) for (int tags = v.tags; tags != 0; tags = tags_pop(tags)) {
                vp = tags_lookup_method(tags_first(tags), member, h);
                if (vp != NULL)  {
                        struct value *this = gc_alloc_object(sizeof *this, GC_VALUE);
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
                this = gc_alloc_object(sizeof *this, GC_VALUE);
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
                this = gc_alloc_object(sizeof *this, GC_VALUE);
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
                this = gc_alloc_object(sizeof *this, GC_VALUE);
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
                this = gc_alloc_object(sizeof *this, GC_VALUE);
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
                vp = class_lookup_static(v.class, member, h);
                if (vp == NULL) {
                        vp = class_lookup_method(v.class, member, h);
                }
                if (vp == NULL) {
                        n = CLASS_CLASS;
                        goto ClassLookup;
                } else {
                        return *vp;
                }
                break;
        case VALUE_OBJECT:
                vp = class_lookup_getter(v.class, member, h);
                if (vp != NULL) {
                        return vm_call(&METHOD(member, vp, &v), 0);
                }
                vp = table_lookup(v.object, member, h);
                if (vp != NULL) {
                        return *vp;
                }
                n = v.class;
ClassLookup:
                vp = class_lookup_method(n, member, h);
                if (vp != NULL) {
                        this = gc_alloc_object(sizeof *this, GC_VALUE);
                        *this = v;
                        return METHOD(member, vp, this);
                }
                vp = b ? class_method(n, MISSING) : NULL;
                if (vp != NULL) {
                        this = gc_alloc_object(sizeof (struct value [3]), GC_VALUE);
                        this[0] = v;
                        this[1] = STRING_NOGC(member, strlen(member));
                        return METHOD(MISSING, vp, this);
                }
                break;
        case VALUE_TAG:
                vp = tags_lookup_method(v.tag, member, h);
                return (vp == NULL) ? NIL : *vp;
        }

        return NONE;
}

inline static void
DoMutDiv(void)
{
        uintptr_t c, p = (uintptr_t)poptarget();
        struct table *o;
        struct value *vp, *vp2, x;
        void *v = vp = (void *)(p & ~0x07);
        unsigned char b;

        switch (p & 0x07) {
        case 0:
                if (vp->type == VALUE_OBJECT && (vp2 = class_method(vp->class, "/=")) != NULL) {
                        gc_push(vp);
                        call(vp2, vp, 1, 0, true);
                        gc_pop();
                        pop();
                } else {
                        x = pop();
                        *vp = binary_operator_division(vp, &x);
                }
                push(*vp);
                break;
        case 1:
                FALSE_OR (top()->type != VALUE_INTEGER) {
                        vm_panic("attempt to divide byte by non-integer");
                }
                b = ((struct blob *)targets.items[targets.count].gc)->items[((uintptr_t)vp) >> 3] /= pop().integer;
                push(INTEGER(b));
                break;
        case 2:
                c = (uintptr_t)poptarget();
                o = targets.items[targets.count].gc;
                vp = poptarget();
                call(vp, &OBJECT(o, c), 0, 0, true);
                top()[-1] = binary_operator_division(top(), top() - 1);
                pop();
                call(v, &OBJECT(o, c), 1, 0, false);
                break;
        default:
                vm_panic("bad target pointer :(");
        }
}
inline static void
DoMutMul(void)
{
        uintptr_t c, p = (uintptr_t)poptarget();
        struct table *o;
        struct value *vp, *vp2, x;
        void *v = vp = (void *)(p & ~0x07);
        unsigned char b;

        switch (p & 0x07) {
        case 0:
                if (vp->type == VALUE_OBJECT && (vp2 = class_method(vp->class, "*=")) != NULL) {
                        gc_push(vp);
                        call(vp2, vp, 1, 0, true);
                        gc_pop();
                        pop();
                } else {
                        x = pop();
                        *vp = binary_operator_multiplication(vp, &x);
                }
                push(*vp);
                break;
        case 1:
                FALSE_OR (top()->type != VALUE_INTEGER) {
                        vm_panic("attempt to multiply byte by non-integer");
                }
                b = ((struct blob *)targets.items[targets.count].gc)->items[((uintptr_t)vp) >> 3] *= pop().integer;
                push(INTEGER(b));
                break;
        case 2:
                c = (uintptr_t)poptarget();
                o = targets.items[targets.count].gc;
                vp = poptarget();
                call(vp, &OBJECT(o, c), 0, 0, true);
                top()[-1] = binary_operator_multiplication(top(), top() - 1);
                pop();
                call(v, &OBJECT(o, c), 1, 0, false);
                break;
        default:
                vm_panic("bad target pointer :(");
        }
}

inline static void
DoMutSub(void)
{
        uintptr_t c, p = (uintptr_t)poptarget();
        struct table *o;
        struct value *vp, *vp2, x;
        void *v = vp = (void *)(p & ~0x07);
        unsigned char b;

        switch (p & 0x07) {
        case 0:
                if (vp->type == VALUE_DICT) {
                        FALSE_OR (top()->type != VALUE_DICT)
                                vm_panic("attempt to subtract non-dict from dict");
                        dict_subtract(vp, 1, NULL);
                        pop();
                } else if (vp->type == VALUE_OBJECT && (vp2 = class_method(vp->class, "-=")) != NULL) {
                        gc_push(vp);
                        call(vp2, vp, 1, 0, true);
                        gc_pop();
                        pop();
                } else {
                        x = pop();
                        *vp = binary_operator_subtraction(vp, &x);
                }
                push(*vp);
                break;
        case 1:
                FALSE_OR (top()->type != VALUE_INTEGER) {
                        vm_panic("attempt to subtract non-integer from byte");
                }
                b = ((struct blob *)targets.items[targets.count].gc)->items[((uintptr_t)vp) >> 3] -= pop().integer;
                push(INTEGER(b));
                break;
        case 2:
                c = (uintptr_t)poptarget();
                o = targets.items[targets.count].gc;
                vp = poptarget();
                call(vp, &OBJECT(o, c), 0, 0, true);
                top()[-1] = binary_operator_subtraction(top(), top() - 1);
                pop();
                call(v, &OBJECT(o, c), 1, 0, false);
                break;
        default:
                vm_panic("bad target pointer :(");
        }
}

inline static void
DoMutAdd(void)
{
        uintptr_t c, p = (uintptr_t)poptarget();
        struct table *o;
        struct value *vp, *vp2, x;
        void *v = vp = (void *)(p & ~0x07);
        unsigned char b;

        switch (p & 0x07) {
        case 0:
                if (vp->type == VALUE_ARRAY) {
                        FALSE_OR (top()->type != VALUE_ARRAY)
                                vm_panic("attempt to add non-array to array");
                        value_array_extend(vp->array, top()->array);
                        pop();
                } else if (vp->type == VALUE_DICT) {
                        FALSE_OR (top()->type != VALUE_DICT)
                                vm_panic("attempt to add non-dict to dict");
                        dict_update(vp, 1, NULL);
                        pop();
                } else if (vp->type == VALUE_OBJECT && (vp2 = class_method(vp->class, "+=")) != NULL) {
                        gc_push(vp);
                        call(vp2, vp, 1, 0, true);
                        gc_pop();
                        pop();
                } else {
                        x = pop();
                        *vp = binary_operator_addition(vp, &x);
                }
                push(*vp);
                break;
        case 1:
                FALSE_OR (top()->type != VALUE_INTEGER) {
                        vm_panic("attempt to add non-integer to byte");
                }
                b = ((struct blob *)targets.items[targets.count].gc)->items[((uintptr_t)vp) >> 3] += pop().integer;
                push(INTEGER(b));
                break;
        case 2:
                c = (uintptr_t)poptarget();
                o = targets.items[targets.count].gc;
                vp = poptarget();
                call(vp, &OBJECT(o, c), 0, 0, true);
                top()[-1] = binary_operator_addition(top(), top() - 1);
                pop();
                call(v, &OBJECT(o, c), 1, 0, false);
                break;
        default:
                vm_panic("bad target pointer :(");
        }
}

inline static void
DoAssign(void)
{
        uintptr_t c, p = (uintptr_t)poptarget();
        void *v = (void *)(p & ~0x07);
        struct table *o;

        switch (p & 0x07) {
        case 0:
                *(struct value *)v = peek();
                break;
        case 1:
                ((struct blob *)targets.items[targets.count].gc)->items[((uintptr_t)v >> 3)] = peek().integer;
                break;
        case 2:
                c = (uintptr_t)poptarget();
                o = targets.items[targets.count].gc;
                poptarget();
                call(v, &OBJECT(o, c), 1, 0, false);
                break;
        default:
                vm_panic("bad target pointer :(");
        }
}

struct value
vm_try_exec(char *code)
{
        jmp_buf jb_;
        memcpy(&jb_, &jb, sizeof jb_);

        size_t nframes = frames.count;
        size_t ntry = try_stack.count;
        try_stack.count = 0;

        char *save = ip;

        if (setjmp(jb) != 0) {
                memcpy(&jb, &jb_, sizeof jb_);
                frames.count = nframes;
                try_stack.count = ntry;
                ip = save;
                push(STRING_CLONE(ERR, strlen(ERR)));
                top()->tags = tags_push(0, gettag(NULL, "Err"));
                top()->type |= VALUE_TAGGED;
                vm_exec((char[]){INSTR_THROW});
                // unreachable
        }

        vm_exec(code);

        memcpy(&jb, &jb_, sizeof jb_);
        frames.count = nframes;
        try_stack.count = ntry;
        ip = save;

        return pop();
}

void
vm_exec(char *code)
{
        char *save = ip;
        ip = code;

        uintptr_t s, off;
        intmax_t k;
        bool b = false, tco = false;
        float f;
        int n, nkw = 0, i, j, tag, rc = 0;
        unsigned long h;

        bool AutoThis = false;

        struct value left, right, v, key, value, container, subscript, *vp, *vp2;
        char *str;
        char const *method, *member;

        struct value (*func)(struct value *, int, struct value *);

#ifdef TY_LOG_VERBOSE
        struct location loc;
        char const *fname;
#endif

        PopulateGlobals();

        for (;;) {
        if (GC_OFF_COUNT == 0 && atomic_load(&MyGroup->WantGC)) {
                WaitGC();
        }
        for (int N = 0; N < 10; ++N) {
        NextInstruction:
                switch ((unsigned char)*ip++) {
                CASE(NOP)
                        continue;
                CASE(LOAD_LOCAL)
                        READVALUE(n);
#ifndef TY_NO_LOG
                        LOG("Loading local: %s (%d)", ip, n);
                        ip += strlen(ip) + 1;
#endif
                        push(*local(n));
                        break;
                CASE(LOAD_REF)
                        READVALUE(n);
#ifndef TY_NO_LOG
                        LOG("Loading ref: %s (%d)", ip, n);
                        ip += strlen(ip) + 1;
#endif
                        vp = local(n);
                        if (vp->type == VALUE_REF) {
                                push(*(struct value *)vp->ptr);
                        } else {
                                push(*vp);
                        }
                        break;
                CASE(LOAD_CAPTURED)
                        READVALUE(n);
#ifndef TY_NO_LOG
                        LOG("Loading capture: %s (%d) of %s", ip, n, value_show(&vec_last(frames)->f));
                        ip += strlen(ip) + 1;
#endif
                        if (vec_last(frames)->f.env == NULL) {
                            puts(value_show(&vec_last(frames)->f));
                        }
                        push(*vec_last(frames)->f.env[n]);
                        break;
                CASE(LOAD_GLOBAL)
                        READVALUE(n);
#ifndef TY_NO_LOG
                        LOG("Loading global: %s (%d)", ip, n);
                        ip += strlen(ip) + 1;
#endif
                        push(Globals.items[n]);
                        break;
                CASE(CAPTURE)
                        READVALUE(i);
                        READVALUE(j);
                        vp = gc_alloc_object(sizeof (struct value), GC_VALUE);
                        *vp = *local(i);
                        *local(i) = REF(vp);
                        vec_last(frames)->f.env[j] = vp;
                        break;
                CASE(EXEC_CODE)
                        READVALUE(s);
                        vm_exec((char *) s);
                        break;
                CASE(DUP)
                        push(peek());
                        break;
                CASE(JUMP)
                        READVALUE(n);
                        ip += n;
                        break;
                CASE(JUMP_IF)
                        READVALUE(n);
                        v = pop();
                        if (value_truthy(&v)) {
                                ip += n;
                        }
                        break;
                CASE(JUMP_IF_NOT)
                        READVALUE(n);
                        v = pop();
                        if (!value_truthy(&v)) {
                                ip += n;
                        }
                        break;
                CASE(JUMP_IF_NONE)
                        READVALUE(n);
                        if (top()[-1].type == VALUE_NONE) {
                                ip += n;
                        }
                        break;
                CASE(JUMP_IF_NIL)
                        READVALUE(n);
                        v = pop();
                        if (v.type == VALUE_NIL) {
                                ip += n;
                        }
                        break;
                CASE(TARGET_GLOBAL)
                TargetGlobal:
                        READVALUE(n);
                        LOG("Global: %d", (int)n);
                        while (Globals.count <= n)
                                vec_push_unchecked(Globals, NIL);
                        pushtarget(&Globals.items[n], NULL);
                        break;
                CASE(TARGET_LOCAL)
                        if (frames.count == 0)
                                goto TargetGlobal;
                        READVALUE(n);
                        LOG("Targeting %d", n);
                        pushtarget(local(n), NULL);
                        break;
                CASE(TARGET_REF)
                        READVALUE(n);
                        vp = local(n);
                        if (vp->type == VALUE_REF) {
                                pushtarget((struct value *)vp->ptr, NULL);
                        } else {
                                pushtarget(vp, NULL);
                        }
                        break;
                CASE(TARGET_CAPTURED)
                        READVALUE(n);
#ifndef TY_NO_LOG
                        LOG("Loading capture: %s (%d) of %s", ip, n, value_show(&vec_last(frames)->f));
                        ip += strlen(ip) + 1;
#endif
                        pushtarget(vec_last(frames)->f.env[n], NULL);
                        break;
                CASE(TARGET_MEMBER)
                        v = pop();
                        member = ip;
                        ip += strlen(ip) + 1;
                        READVALUE(h);
                        if (v.type == VALUE_OBJECT) {
                                vp = class_lookup_setter(v.class, member, h);
                                if (vp != NULL) {
                                        vp2 = class_lookup_getter(v.class, member, h);
                                        FALSE_OR (vp2 == NULL) {
                                                vm_panic(
                                                        "class %s%s%s needs a getter for %s%s%s!",
                                                        TERM(33),
                                                        class_name(v.class),
                                                        TERM(0),
                                                        TERM(34),
                                                        member,
                                                        TERM(0)
                                                );
                                        }
                                        pushtarget(vp2, NULL);
                                        pushtarget((struct value *)(uintptr_t)v.class, v.object);
                                        pushtarget((struct value *)(((uintptr_t)vp) | 2), NULL);
                                        break;
                                }
                                vp = table_lookup(v.object, member, h);
                                if (vp != NULL) {
                                        pushtarget(vp, v.object);
                                } else {
                                        pushtarget(table_add(v.object, member, h, NIL), v.object);
                                }
                        } else if (v.type == VALUE_TUPLE) {
                                vp = tuple_get(&v, member);
                                if (vp == NULL) {
                                        goto BadTupleMember;
                                }
                                pushtarget(vp, v.items);
                        } else {
                                vm_panic("assignment to member of non-object");
                        }
                        break;
                CASE(TARGET_SUBSCRIPT)
                        subscript = top()[0];
                        container = top()[-1];

                        if (container.type == VALUE_ARRAY) {
                                FALSE_OR (subscript.type != VALUE_INTEGER)
                                        vm_panic("non-integer array index used in subscript assignment");
                                if (subscript.integer < 0)
                                        subscript.integer += container.array->count;
                                if (subscript.integer < 0 || subscript.integer >= container.array->count) {
                                        // TODO: Not sure which is the best behavior here
                                        push(TAG(gettag(NULL, "IndexError")));
                                        goto Throw;
                                        vm_panic("array index out of range in subscript expression");
                                }
                                pushtarget(&container.array->items[subscript.integer], container.array);
                        } else if (container.type == VALUE_DICT) {
                                pushtarget(dict_put_key_if_not_exists(container.dict, subscript), container.dict);
                        } else if (container.type == VALUE_BLOB) {
                                FALSE_OR (subscript.type != VALUE_INTEGER) {
                                        vm_panic("non-integer blob index used in subscript assignment");
                                }
                                if (subscript.integer < 0) {
                                        subscript.integer += container.blob->count;
                                }
                                if (subscript.integer < 0 || subscript.integer >= container.blob->count) {
                                        // TODO: Not sure which is the best behavior here
                                        push(TAG(gettag(NULL, "IndexError")));
                                        goto Throw;
                                        vm_panic("blob index out of range in subscript expression");
                                }
                                pushtarget((struct value *)((((uintptr_t)(subscript.integer)) << 3) | 1) , container.blob);
                        } else if (container.type == VALUE_PTR && ip[0] == INSTR_ASSIGN) {
                                if (subscript.type != VALUE_INTEGER) {
                                        vm_panic("non-integer pointer offset used in subscript assignment: %s", value_show_color(&subscript));
                                }
                                struct value p = binary_operator_addition(&container, &subscript);
                                pop();
                                pop();
                                v = pop();
                                push(p);
                                push(v);
                                v = cffi_store(2, NULL);
                                pop();
                                pop();
                                push(v);
                                ip += 1;
                                break;
                        } else {
                                vm_panic("attempt to perform subscript assignment on something other than an object or array");
                        }

                        pop();
                        pop();

                        break;
                CASE(ASSIGN)
                        DoAssign();
                        break;
                CASE(MAYBE_ASSIGN)
                        vp = poptarget();
                        if (vp->type == VALUE_NIL)
                                *vp = peek();
                        break;
                CASE(TAG_PUSH)
                        READVALUE(tag);
                        top()->tags = tags_push(top()->tags, tag);
                        top()->type |= VALUE_TAGGED;
                        break;
                CASE(ARRAY_REST)
                        READVALUE(i);
                        READVALUE(j);
                        READVALUE(n);
                        if (top()->type != VALUE_ARRAY || top()->array->count < i + j) {
                                ip += n;
                        } else {
                                struct array *rest = value_array_new();
                                NOGC(rest);
                                vec_push_n(*rest, top()->array->items + i, top()->array->count - (i + j));
                                *poptarget() = ARRAY(rest);
                                OKGC(rest);
                        }
                        break;
                CASE(TUPLE_REST)
                        READVALUE(i);
                        READVALUE(n);
                        vp = poptarget();
                        if (top()->type != VALUE_TUPLE) {
                                ip += n;
                        } else {
                                int count = top()->count - i;
                                struct value *rest = gc_alloc_object(sizeof (struct value[count]), GC_TUPLE);
                                memcpy(rest, top()->items + i, count * sizeof (struct value));
                                *vp = TUPLE(rest, NULL, count, false);
                        }
                        break;
                CASE(THROW_IF_NIL)
                        if (top()->type == VALUE_NIL) {
                                MatchError;
                        }
                        break;
                CASE(UNTAG_OR_DIE)
                        READVALUE(tag);
                        if (!tags_same(tags_first(top()->tags), tag)) {
                                MatchError;
                        } else {
                                top()->tags = tags_pop(top()->tags);
                                top()->type &= ~VALUE_TAGGED;
                        }
                        break;
                CASE(BAD_MATCH)
                        MatchError;
                CASE(BAD_CALL)
                        v = pop();
                        str = ip;
                        ip += strlen(ip) + 1;
                        vm_panic(
                                "constraint on %s%s%s%s%s violated in call to %s%s%s%s%s: %s%s%s = %s%s%s",
                                TERM(34),
                                TERM(1),
                                ip,
                                TERM(22),
                                TERM(39),

                                TERM(34),
                                TERM(1),
                                str,
                                TERM(22),
                                TERM(39),

                                TERM(34),
                                TERM(1),
                                ip,
                                value_show(&v),
                                TERM(22),
                                TERM(39)
                        );
                        break;
                CASE(BAD_ASSIGN)
                        v = pop();
                        str = ip;
                        vm_panic(
                                "constraint on %s%s%s%s%s violated in assignment: %s%s%s = %s%s%s",
                                TERM(34),
                                TERM(1),
                                ip,
                                TERM(22),
                                TERM(39),

                                TERM(34),
                                TERM(1),
                                ip,
                                value_show(&v),
                                TERM(22),
                                TERM(39)
                        );
                        break;
                CASE(THROW)
Throw:
                        vec_push(throw_stack, ((ThrowCtx) {
                                .ctxs = frames.count,
                                .ip = ip
                        }));
                        // Fallthrough
                CASE(RETHROW)
                {
                        if (try_stack.count == 0) {
                                ThrowCtx c = *vec_pop(throw_stack);

                                frames.count = c.ctxs;
                                ip = (char *)c.ip;

                                vm_panic("uncaught exception: %s%s%s", TERM(31), value_show(top()), TERM(39));
                        }

                        struct try *t = vec_last(try_stack);

                        FALSE_OR (t->executing) {
                                vm_panic(
                                        "an exception was thrown while handling another exception: %s%s%s",
                                        TERM(31), value_show(top()), TERM(39)
                                );
                        }

                        t->executing = true;

                        v = pop();

                        stack.count = t->sp;

                        push(SENTINEL);
                        push(v);

                        frames.count = t->ctxs;
                        targets.count = t->ts;
                        calls.count = t->cs;
                        ip = t->catch;

                        gc_truncate_root_set(t->gc);

                        longjmp(t->jb, 1);
                        /* unreachable */
                }
                CASE(FINALLY)
                {
                        struct try *t = vec_pop(try_stack);
                        if (t->finally == NULL)
                                break;
                        *t->end = INSTR_HALT;
                        vm_exec(t->finally);
                        *t->end = INSTR_NOP;
                        break;
                }
                CASE(POP_TRY)
                        --try_stack.count;
                        break;
                CASE(RESUME_TRY)
                        vec_last(try_stack)->executing = true;
                        break;
                CASE(CATCH)
                        --throw_stack.count;
                        vec_last(try_stack)->executing = false;
                        break;
                CASE(TRY)
                {
                        READVALUE(n);
                        struct try t;
                        if (setjmp(t.jb) != 0)
                                break;
                        t.catch = ip + n;
                        READVALUE(n);
                        t.finally = (n == -1) ? NULL : ip + n;
                        READVALUE(n);
                        t.end = (n == -1) ? NULL : ip + n;
                        t.sp = stack.count;
                        t.gc = gc_root_set_count();
                        t.cs = calls.count;
                        t.ts = targets.count;
                        t.ctxs = frames.count;
                        t.executing = false;
                        vec_push(try_stack, t);
                        break;
                }
                CASE(PUSH_DEFER_GROUP)
                        vec_push_unchecked(defer_stack, ARRAY(value_array_new()));
                        break;
                CASE(DEFER)
                        v = pop();
                        value_array_push(vec_last(defer_stack)->array, v);
                        break;
                CASE(CLEANUP)
                        v = *vec_last(defer_stack);
                        for (int i = 0; i < v.array->count; ++i) {
                                vm_call(&v.array->items[i], 0);
                        }
                        vec_pop(defer_stack);
                        break;
                CASE(ENSURE_LEN)
                        READVALUE(n);
                        b = top()->type == VALUE_ARRAY && top()->array->count <= n;
                        READVALUE(n);
                        if (!b)
                                ip += n;
                        break;
                CASE(ENSURE_LEN_TUPLE)
                        READVALUE(n);
                        b = top()->type == VALUE_TUPLE && top()->count <= n;
                        READVALUE(n);
                        if (!b)
                                ip += n;
                        break;
                CASE(ENSURE_EQUALS_VAR)
                        v = pop();
                        READVALUE(n);
                        if (!value_test_equality(top(), &v))
                                ip += n;
                        break;
                CASE(TRY_ASSIGN_NON_NIL)
                        READVALUE(n);
                        vp = poptarget();
                        if (top()->type == VALUE_NIL)
                                ip += n;
                        else
                                *vp = peek();
                        break;
                CASE(TRY_REGEX)
                        READVALUE(s);
                        READVALUE(n);
                        v = REGEX((struct regex const *) s);
                        value = value_apply_callable(&v, top());
                        vp = poptarget();
                        if (value.type == VALUE_NIL) {
                                ip += n;
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
                        if (top()->type != VALUE_DICT) {
                                ip += n;
                        }
                        break;
                CASE(ENSURE_CONTAINS)
                        READVALUE(n);
                        v = pop();
                        if (!dict_has_value(top()->dict, &v)) {
                                ip += n;
                        }
                        break;
                CASE(ENSURE_SAME_KEYS)
                        READVALUE(n);
                        v = pop();
                        if (!dict_same_keys(top()->dict, v.dict)) {
                                ip += n;
                        }
                        break;
                CASE(TRY_INDEX)
                        READVALUE(i);
                        READVALUE(b);
                        READVALUE(n);
                        //LOG("trying to index: %s", value_show(top()));
                        if (top()->type != VALUE_ARRAY) {
                                ip += n;
                                break;
                        }
                        if (i < 0) {
                                i += top()->array->count;
                        }
                        if (top()->array->count <= i) {
                                if (b) {
                                        ip += n;
                                } else {
                                        push(NIL);
                                }
                        } else {
                                push(top()->array->items[i]);
                        }
                        break;
                CASE(TRY_INDEX_TUPLE)
                        READVALUE(i);
                        READVALUE(n);
                        if (top()->type != VALUE_TUPLE || top()->count <= i) {
                                ip += n;
                        } else {
                                push(top()->items[i]);
                        }
                        break;
                CASE(TRY_TUPLE_MEMBER)
                        // b => required
                        READVALUE(b);

                        str = ip;
                        ip += strlen(str) + 1;

                        READVALUE(n);

                        if (top()->type != VALUE_TUPLE) {
                                ip += n;
                                break;
                        }

                        for (int i = 0; top()->names != NULL && i < top()->count; ++i) {
                                if (top()->names[i] != NULL && strcmp(top()->names[i], str) == 0) {
                                        push(top()->items[i]);
                                        goto NextInstruction;
                                }
                        }

                        if (!b) {
                                push(NIL);
                                goto NextInstruction;
                        }

                        ip += n;

                        break;
                CASE(TRY_TAG_POP)
                        READVALUE(tag);
                        READVALUE(n);
                        if (!(top()->type & VALUE_TAGGED) || tags_first(top()->tags) != tag) {
                                ip += n;
                        } else {
                                top()->tags = tags_pop(top()->tags);
                                if (top()->tags == 0) {
                                        top()->type &= ~VALUE_TAGGED;
                                }
                        }
                        break;
                CASE(POP)
                        pop();
                        break;
                CASE(UNPOP)
                        stack.count += 1;
                        break;
                CASE(INTEGER)
                        READVALUE(k);
                        push(INTEGER(k));
                        break;
                CASE(REAL)
                        READVALUE(f);
                        push(REAL(f));
                        break;
                CASE(BOOLEAN)
                        READVALUE(b);
                        push(BOOLEAN(b));
                        break;
                CASE(STRING)
                        n = strlen(ip);
                        push(STRING_NOGC(ip, n));
                        ip += n + 1;
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
                CASE(ARRAY)
                        v = ARRAY(value_array_new());
                        n = stack.count - *vec_pop(sp_stack);

                        NOGC(v.array);

                        if (n > 0) {
                                vec_reserve(*v.array, n);

                                memcpy(
                                        v.array->items,
                                        stack.items + stack.count - n,
                                        sizeof (struct value [n])
                                );

                                v.array->count = n;

                                stack.count -= n;
                        }

                        push(v);
                        OKGC(v.array);

                        break;
                CASE(TUPLE)
                {
                        static _Thread_local StringVector names;
                        static _Thread_local ValueVector values;

                        names.count = 0;
                        values.count = 0;

                        bool have_names = false;

                        n = stack.count - *vec_pop(sp_stack);

                        for (int i = 0; i < n; ++i, ip += strlen(ip) + 1) {
                                struct value *v = &stack.items[stack.count - n + i];
                                if (v->type == VALUE_TUPLE && strcmp(ip, "*") == 0) {
                                        for (int j = 0; j < v->count; ++j) {
                                                if (v->names != NULL && v->names[j] != NULL) {
                                                        AddTupleEntry(&names, &values, v->names[j], &v->items[j]);
                                                        have_names = true;
                                                } else {
                                                        vec_push(names, NULL);
                                                        vec_push(values, v->items[j]);
                                                }
                                        }
                                } else if (v->type != VALUE_NONE) {
                                        if (ip[0] == '\0') {
                                                vec_push(names, NULL);
                                                vec_push(values, *v);
                                        } else {
                                                AddTupleEntry(&names, &values, ip, v);
                                                have_names = true;
                                        }
                                }
                        }

                        k = values.count;
                        vp = gc_alloc_object(sizeof (struct value[k]), GC_TUPLE);

                        v = TUPLE(vp, NULL, k, false);

                        GC_OFF_COUNT += 1;

                        if (k > 0) {
                                memcpy(vp, values.items, sizeof (struct value[k]));
                                if (have_names) {
                                        v.names = gc_alloc_object(sizeof (char *[k]), GC_TUPLE);
                                        memcpy(v.names, names.items, sizeof (char *[k]));
                                }
                        }

                        stack.count -= n;

                        push(v);

                        GC_OFF_COUNT -= 1;

                        break;
                }
                CASE(DICT)
                        v = DICT(dict_new());
                        NOGC(v.dict);

                        n = (stack.count - *vec_pop(sp_stack)) / 2;
                        for (i = 0; i < n; ++i) {
                                value = top()[0];
                                key = top()[-1];
                                dict_put_value(v.dict, key, value);
                                pop();
                                pop();
                        }

                        OKGC(v.dict);
                        push(v);
                        break;
                CASE(DICT_DEFAULT)
                        v = pop();
                        top()->dict->dflt = v;
                        break;
                CASE(SELF)
                        if (frames.count == 0) {
                        } else {
                                push(NIL);
                        }
                        break;
                CASE(NIL)
                        push(NIL);
                        break;
                CASE(TO_STRING)
                        str = ip;
                        n = strlen(str);
                        ip += n + 1;
                        if (top()->type == VALUE_PTR) {
                            char *s = value_show(top());
                            pop();
                            push(STRING_NOGC(s, strlen(s)));
                            break;
                        } else if (n > 0) {
                                v = pop();
                                push(STRING_NOGC(str, n));
                                push(v);
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
                        n = frames.items[0].fp;

                        FALSE_OR (stack.items[n - 1].type != VALUE_GENERATOR) {
                                vm_panic("attempt to yield from outside generator context");
                        }

                        v.gen = stack.items[n - 1].gen;
                        v.gen->ip = ip;
                        v.gen->frame.count = 0;

                        SWAP(SPStack, v.gen->sps, sp_stack);
                        SWAP(TargetStack, v.gen->targets, targets);
                        SWAP(CallStack, v.gen->calls, calls);
                        SWAP(FrameStack, v.gen->frames, frames);

                        vec_nogc_push_n(v.gen->frame, stack.items + n, stack.count - n - 1);

                        stack.items[n - 1] = peek();
                        stack.count = n;

                        vec_pop(frames);

                        ip = *vec_pop(calls);

                        break;
                CASE(MAKE_GENERATOR)
                        v.type = VALUE_GENERATOR;
                        v.tags = 0;
                        v.gen = gc_alloc_object(sizeof *v.gen, GC_GENERATOR);
                        NOGC(v.gen);
                        v.gen->ip = ip;
                        v.gen->f = vec_last(frames)->f;
                        n = stack.count - vec_last(frames)->fp;
                        vec_init(v.gen->frame);
                        vec_push_n(v.gen->frame, stack.items + stack.count - n, n);
                        vec_init(v.gen->sps);
                        vec_init(v.gen->targets);
                        vec_init(v.gen->calls);
                        vec_init(v.gen->frames);
                        push(v);
                        OKGC(v.gen);
                        goto Return;
                CASE(VALUE)
                        READVALUE(s);
                        push(*(struct value *)s);
                        break;
                CASE(EVAL)
                        READVALUE(s);
                        push(PTR((void *)s));
                        v = builtin_eval(2, NULL);
                        pop();
                        pop();
                        push(v);
                        break;
                CASE(RENDER_TEMPLATE)
                        READVALUE(s);
                        push(compiler_render_template((struct expression *)s));
                        break;
                CASE(FUCK)
                        printf("Build: %s\n", ip);
                        ip += strlen(ip) + 1;
                CASE(FUCK2)
                CASE(FUCK3)
                        break;
                CASE(GET_NEXT)
                        v = top()[-1];
                        i = top()[-2].i++;
                        //LOG("GET_NEXT: v = %s\n", value_show(&v));
                        //LOG("GET_NEXT: i = %d\n", i);
                        print_stack(10);
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
                                        rc = 1;
                                        pop();
                                } else {
                                        push(NONE);
                                }
                                break;
                        case VALUE_OBJECT:
                                if ((vp = class_method(v.class, "__next__")) != NULL) {
                                        push(INTEGER(i));
                                        vec_push_unchecked(calls, ip);
                                        call(vp, &v, 1, 0, false);
                                        *vec_last(calls) = next_fix;
                                } else if ((vp = class_method(v.class, "__iter__")) != NULL) {
                                        pop();
                                        pop();
                                        --top()->i;
                                        /* Have to repeat this instruction */
                                        vec_push_unchecked(calls, ip - 1);
                                        call(vp, &v, 0, 0, false);
                                        *vec_last(calls) = iter_fix;
                                        continue;
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
                        case VALUE_STRING:
                                vp = top() - 2;
                                if ((off = vp->off) < v.bytes) {
                                        vp->off += (n = utf8_char_len(v.string + off));
                                        push(STRING_VIEW(v, off, n));
                                } else {
                                        push(NONE);
                                }
                                break;
                        case VALUE_GENERATOR:
                                vec_push_unchecked(calls, ip);
                                call_co(&v, 0);
                                *vec_last(v.gen->calls) = next_fix;
                                break;
                        default:
                        NoIter:
                                GC_OFF_COUNT += 1;
                                vm_panic("for-each loop on non-iterable value: %s", value_show(&v));
                        }
                        break;
                CASE(ARRAY_COMPR)
                        n = stack.count - *vec_pop(sp_stack);
                        v = top()[-(n + 2)];
                        for (int i = 0; i < n; ++i)
                                value_array_push(v.array, top()[-i]);
                        stack.count -= n;
                        break;
                CASE(DICT_COMPR)
                        READVALUE(n);
                        v = top()[-(2*n + 2)];
                        for (i = 0; i < n; ++i) {
                                value = top()[-2*i];
                                key = top()[-(2*i + 1)];
                                dict_put_value(v.dict, key, value);
                        }
                        stack.count -= 2 * n;
                        break;
                CASE(PUSH_INDEX)
                        READVALUE(n);
                        push(INDEX(0, 0, n));
                        break;
                CASE(READ_INDEX)
                        k = top()[-3].integer - 1;
                        stack.count += rc;
                        push(INTEGER(k));
                        break;
                CASE(SENTINEL)
                        push(SENTINEL);
                        break;
                CASE(NONE)
                        push(NONE);
                        break;
                CASE(NONE_IF_NIL)
                        if (top()->type == VALUE_TAG && top()->tag == TAG_NONE) {
                                *top() = NONE;
                        } else FALSE_OR (!(top()->tags != 0 && tags_first(top()->tags) == TAG_SOME)) {
                                vm_panic("iterator returned invalid type. expected None or Some(x) but got %s", value_show(top()));
                        } else {
                                top()->tags = tags_pop(top()->tags);
                                if (top()->tags == 0) {
                                        top()->type &= ~VALUE_TAGGED;
                                }
                        }
                        break;
                CASE(CLEAR_RC)
                        rc = 0;
                        break;
                CASE(GET_EXTRA)
                        LOG("GETTING %d EXTRA", rc);
                        stack.count += rc;
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
                        v = top()[-1];
                        top()[-1] = top()[0];
                        top()[0] = v;
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
                        print_stack(5);
                        READVALUE(n);
                        for (i = 0, vp = top(); pop().type != VALUE_SENTINEL; ++i)
                                ;
                        for (int j = targets.count - n; n > 0; --n, poptarget()) {
                                if (i > 0) {
                                        *targets.items[j++].t = vp[-(--i)];
                                } else {
                                        *targets.items[j++].t = NIL;
                                }
                        }
                        push(top()[2]);
                        break;
                CASE(MAYBE_MULTI)
                        READVALUE(n);
                        for (i = 0, vp = top(); pop().type != VALUE_SENTINEL; ++i)
                                ;
                        for (int j = targets.count - n; n > 0; --n, poptarget()) {
                                if (i > 0) {
                                        if (targets.items[j++].t->type == VALUE_NIL)
                                                *targets.items[j - 1].t = vp[-(--i)];
                                } else {
                                        *targets.items[j++].t = NIL;
                                }
                        }
                        push(top()[2]);
                        break;
                CASE(JUMP_IF_SENTINEL)
                        READVALUE(n);
                        if (top()->type == VALUE_SENTINEL)
                                ip += n;
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
                        if (top()->type != VALUE_ARRAY) {
                                MatchError;
                                vm_panic("attempt to destructure non-array as array in assignment");
                        }
                        if (n < 0) {
                                n += top()->array->count;
                        }
                        if (n >= top()->array->count) {
                                if (b) {
                                        MatchError;
                                        vm_panic("elment index out of range in destructuring assignment");
                                } else {
                                        push(NIL);
                                }
                        } else {
                                push(top()->array->items[n]);
                        }
                        break;
                CASE(PUSH_TUPLE_ELEM)
                        READVALUE(n);
                        FALSE_OR (top()->type != VALUE_TUPLE) {
                                vm_panic("attempt to destructure non-tuple as tuple in assignment");
                        }
                        FALSE_OR (n >= top()->count) {
                                vm_panic("elment index out of range in destructuring assignment");
                        }
                        push(top()->items[n]);
                        break;
                CASE(PUSH_TUPLE_MEMBER)
                        READVALUE(b);

                        member = ip;
                        ip += strlen(member) + 1;

                        v = peek();

                        if (v.type != VALUE_TUPLE || v.names == NULL) {
                                goto BadTupleMember;
                        }

                        for (int i = 0; i < v.count; ++i) {
                                if (v.names[i] != NULL && strcmp(v.names[i], member) == 0) {
                                        push(v.items[i]);
                                        goto NextInstruction;
                                }
                        }

                        if (!b) {
                                push(NIL);
                                goto NextInstruction;
                        }

                        goto BadTupleMember;
                CASE(PUSH_ALL)
                        v = pop();
                        gc_push(&v);
                        for (int i = 0; i < v.array->count; ++i) {
                                push(v.array->items[i]);
                        }
                        gc_pop();
                        break;
                CASE(CONCAT_STRINGS)
                        READVALUE(n);
                        k = 0;
                        for (i = stack.count - n; i < stack.count; ++i)
                                k += stack.items[i].bytes;
                        str = value_string_alloc(k);
                        v = STRING(str, k);
                        k = 0;
                        for (i = stack.count - n; i < stack.count; ++i) {
                                if (stack.items[i].bytes > 0) {
                                        memcpy(str + k, stack.items[i].string, stack.items[i].bytes);
                                        k += stack.items[i].bytes;
                                }
                        }
                        stack.count -= n - 1;
                        stack.items[stack.count - 1] = v;
                        break;
                CASE(RANGE)
                        i = class_lookup("Range");
                        if (i == -1 || (vp = class_method(i, "init")) == NULL) {
                                vm_panic("failed to load Range class. was prelude loaded correctly?");
                        }

                        v = OBJECT(object_new(i), i);
                        NOGC(v.object);
                        call(vp, &v, 2, 0, true);
                        *top() = v;
                        OKGC(v.object);
                        break;
                CASE(INCRANGE)
                        i = class_lookup("InclusiveRange");
                        if (i == -1 || (vp = class_method(i, "init")) == NULL) {
                                vm_panic("failed to load InclusiveRange class. was prelude loaded correctly?");
                        }

                        v = OBJECT(object_new(i), i);
                        NOGC(v.object);
                        call(vp, &v, 2, 0, true);
                        *top() = v;
                        OKGC(v.object);
                        break;
                CASE(TRY_MEMBER_ACCESS)
                CASE(MEMBER_ACCESS)
                        value = pop();

                        b = ip[-1] == INSTR_TRY_MEMBER_ACCESS;

                        member = ip;
                        ip += strlen(ip) + 1;

                        READVALUE(h);

                        push(NIL);
                        v = GetMember(value, member, h, true);

                        if (v.type != VALUE_NONE) {
                                *top() = v;
                                break;
                        } else if (b) {
                                break;
                        }

                        if (value.type == VALUE_TUPLE) {
                        BadTupleMember:
                                vm_panic(
                                        "attempt to access non-existent field %s'%s'%s of %s%s%s",
                                        TERM(34),
                                        member,
                                        TERM(39),
                                        TERM(97),
                                        value_show(&value),
                                        TERM(39)
                                );
                        } else {
                                vm_panic(
                                        "attempt to access non-existent member %s'%s'%s of %s%s%s",
                                        TERM(34),
                                        member,
                                        TERM(39),
                                        TERM(97),
                                        value_show(&value),
                                        TERM(39)
                                );
                        }

                        break;
                CASE(SUBSCRIPT)
                        subscript = pop();
                        container = pop();

                        switch (container.type) {
                        case VALUE_ARRAY:
                                if (subscript.type == VALUE_OBJECT) {
ObjectSubscript:
                                        vp = class_method(subscript.class, "__next__");
                                        if (vp == NULL) {
                                                vp = class_method(subscript.class, "__iter__");
                                                FALSE_OR (vp == NULL) {
                                                        vm_panic("non-iterable object used in subscript expression");
                                                }
                                                call(vp, &subscript, 0, 0, true);
                                                subscript = pop();
                                                goto ObjectSubscript;
                                        }
                                        struct array *a = value_array_new();
                                        NOGC(a);
                                        for (int i = 0; ; ++i) {
                                                push(INTEGER(i));
                                                call(vp, &subscript, 1, 0, true);
                                                struct value r = pop();
                                                if (r.type == VALUE_NIL)
                                                        break;
                                                FALSE_OR (r.type != VALUE_INTEGER)
                                                        vm_panic("iterator yielded non-integer array index in subscript expression");
                                                if (r.integer < 0)
                                                        r.integer += container.array->count;
                                                if (r.integer < 0 || r.integer >= container.array->count)
                                                        goto OutOfRange;
                                                value_array_push(a, container.array->items[r.integer]);
                                        }
                                        push(ARRAY(a));
                                        OKGC(a);
                                } else if (subscript.type == VALUE_INTEGER) {
                                        if (subscript.integer < 0) {
                                                subscript.integer += container.array->count;
                                        }
                                        if (subscript.integer < 0 || subscript.integer >= container.array->count) {
                        OutOfRange:
                                                push(TAG(gettag(NULL, "IndexError")));
                                                goto Throw;
                                                vm_panic("array index out of range in subscript expression");
                                        }
                                        push(container.array->items[subscript.integer]);
                                } else {
                                        vm_panic("non-integer array index used in subscript expression");
                                }
                                break;
                        case VALUE_TUPLE:
                                if (subscript.type == VALUE_INTEGER) {
                                        if (subscript.integer < 0) {
                                                subscript.integer += container.count;
                                        }
                                        if (subscript.integer < 0 || subscript.integer >= container.count) {
                                                push(TAG(gettag(NULL, "IndexError")));
                                                goto Throw;
                                                vm_panic("list index out of range in subscript expression");
                                        }
                                        push(container.items[subscript.integer]);
                                } else {
                                        vm_panic("non-integer array index used in subscript expression");
                                }
                                break;
                        case VALUE_STRING:
                                push(subscript);
                                v = get_string_method("char")(&container, 1, NULL);
                                pop();
                                push(v);
                                break;
                        case VALUE_BLOB:
                                push(subscript);
                                v = get_blob_method("get")(&container, 1, NULL);
                                pop();
                                push(v);
                                break;
                        case VALUE_DICT:
                                vp = dict_get_value(container.dict, &subscript);
                                push((vp == NULL) ? NIL : *vp);
                                break;
                        case VALUE_OBJECT:
                                vp = class_method(container.class, "__subscript__");
                                if (vp != NULL) {
                                        push(subscript);
                                        call(vp, &container, 1, 0, false);
                                } else {
                                        goto BadContainer;
                                }
                                break;
                        case VALUE_CLASS:
                                push(subscript);
                                push(container);
                                n = 1;
                                b = false;
                                method = "__subscript__";
                                h = strhash(method);
                                goto CallMethod;
                        case VALUE_PTR:
                                FALSE_OR (subscript.type != VALUE_INTEGER) {
                                        vm_panic("non-integer used to subscript pointer: %s", value_show(&subscript));
                                }
                                v = GCPTR((container.extra == NULL) ? &ffi_type_uint8 : container.extra, container.gcptr);
                                push(v);
                                push(PTR(((char *)container.ptr) + ((ffi_type *)v.ptr)->size * subscript.integer));
                                v = cffi_load(2, NULL);
                                pop();
                                pop();
                                push(v);
                                break;
                        case VALUE_NIL:
                                push(NIL);
                                break;
                        default:
BadContainer:
                                vm_panic("invalid container in subscript expression: %s", value_show(&container));
                        }
                        break;
                CASE(NOT)
                        v = pop();
                        push(unary_operator_not(&v));
                        break;
                CASE(QUESTION)
                        if (top()->type == VALUE_NIL) {
                                *top() = BOOLEAN(false);
                        } else {
                                n = 0;
                                b = false;
                                method = "__question__";
                                h = strhash(method);
                                goto CallMethod;
                        }
                        break;
                CASE(NEG)
                        v = pop();
                        push(unary_operator_negate(&v));
                        break;
                CASE(COUNT)
                        v = pop();
                        switch (v.type) {
                        case VALUE_BLOB:   push(INTEGER(v.blob->count));  break;
                        case VALUE_ARRAY:  push(INTEGER(v.array->count)); break;
                        case VALUE_DICT:   push(INTEGER(v.dict->count));  break;
                        case VALUE_STRING:
                                push(get_string_method("len")(&v, 0, NULL));
                                break;
                        case VALUE_OBJECT:
                                push(v);
                                n = 0;
                                b = false;
                                method = "__len__";
                                h = strhash(method);
                                goto CallMethod;
                        default: vm_panic("# applied to operand of invalid type: %s", value_show(&v));
                        }
                        break;
                CASE(ADD)
                        v = binary_operator_addition(top() - 1, top());
                        pop();
                        pop();
                        push(v);
                        break;
                CASE(SUB)
                        v = binary_operator_subtraction(top() - 1, top());
                        pop();
                        pop();
                        push(v);
                        break;
                CASE(MUL)
                        v = binary_operator_multiplication(top() - 1, top());
                        pop();
                        pop();
                        push(v);
                        break;
                CASE(DIV)
                        v = binary_operator_division(top() - 1, top());
                        pop();
                        pop();
                        push(v);
                        break;
                CASE(MOD)
                        v = binary_operator_remainder(top() - 1, top());
                        pop();
                        pop();
                        push(v);
                        break;
                CASE(EQ)
                        v = binary_operator_equality(top() - 1, top());
                        pop();
                        pop();
                        push(v);
                        break;
                CASE(NEQ)
                        v = binary_operator_equality(top() - 1, top());
                        pop();
                        pop();
                        push(v);
                        --top()->boolean;
                        break;
                CASE(CHECK_MATCH)
                        if (top()->type == VALUE_CLASS) {
                                v = pop();
                                switch (top()->type) {
                                case VALUE_OBJECT:
                                        *top() = BOOLEAN(
                                                top()->type == VALUE_OBJECT &&
                                                class_is_subclass(top()->class, v.class)
                                        );
                                        break;
                                case VALUE_INTEGER:   *top() = BOOLEAN(class_is_subclass(CLASS_INT, v.class));       break;
                                case VALUE_REAL:      *top() = BOOLEAN(class_is_subclass(CLASS_FLOAT, v.class));     break;
                                case VALUE_BOOLEAN:   *top() = BOOLEAN(class_is_subclass(CLASS_BOOL, v.class));      break;
                                case VALUE_ARRAY:     *top() = BOOLEAN(class_is_subclass(CLASS_ARRAY, v.class));     break;
                                case VALUE_STRING:    *top() = BOOLEAN(class_is_subclass(CLASS_STRING, v.class));    break;
                                case VALUE_BLOB:      *top() = BOOLEAN(class_is_subclass(CLASS_BLOB, v.class));      break;
                                case VALUE_DICT:      *top() = BOOLEAN(class_is_subclass(CLASS_DICT, v.class));      break;
                                case VALUE_METHOD:
                                case VALUE_BUILTIN_METHOD:
                                case VALUE_BUILTIN_FUNCTION:
                                case VALUE_FUNCTION:  *top() = BOOLEAN(class_is_subclass(CLASS_FUNCTION, v.class));  break;
                                case VALUE_GENERATOR: *top() = BOOLEAN(class_is_subclass(CLASS_GENERATOR, v.class)); break;
                                case VALUE_REGEX:     *top() = BOOLEAN(class_is_subclass(CLASS_REGEX, v.class));     break;
                                default:              *top() = BOOLEAN(false);                                       break;
                                }
                        } else if (top()->type == VALUE_BOOLEAN) {
                                v = pop();
                                *top() = v;
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
                        v = BOOLEAN(value_compare(top() - 1, top()) < 0);
                        pop();
                        pop();
                        push(v);
                        break;
                CASE(GT)
                        v = BOOLEAN(value_compare(top() - 1, top()) > 0);
                        pop();
                        pop();
                        push(v);
                        break;
                CASE(LEQ)
                        v = BOOLEAN(value_compare(top() - 1, top()) <= 0);
                        pop();
                        pop();
                        push(v);
                        break;
                CASE(GEQ)
                        v = BOOLEAN(value_compare(top() - 1, top()) >= 0);
                        pop();
                        pop();
                        push(v);
                        break;
                CASE(CMP)
                        i = value_compare(top() - 1, top());
                        pop();
                        pop();
                        if (i < 0)
                                push(INTEGER(-1));
                        else if (i > 0)
                                push(INTEGER(1));
                        else
                                push(INTEGER(0));
                        break;
                CASE(GET_TAG)
                        v = pop();
                        if (v.tags == 0)
                                push(NIL);
                        else
                                push(TAG(tags_first(v.tags)));
                        break;
                CASE(LEN)
                        v = pop();
                        push(INTEGER(v.array->count)); // TODO
                        break;
                CASE(PRE_INC)
                        FALSE_OR (SpecialTarget()) {
                                vm_panic("pre-increment applied to invalid target");
                        }
                        switch (peektarget()->type) {
                        case VALUE_INTEGER: ++peektarget()->integer; break;
                        case VALUE_REAL:    ++peektarget()->real;    break;
                        case VALUE_OBJECT:
                                vp = class_method(peektarget()->class, "++");
                                if (vp != NULL) {
                                        call(vp, peektarget(), 0, 0, true);
                                        break;
                                }
                        case VALUE_PTR:
                                vp = peektarget();
                                vp->ptr = ((char *)vp->ptr) + ((ffi_type *)(vp->extra == NULL ? &ffi_type_uint8 : vp->extra))->size;
                                break;
                        default:
                                vm_panic("pre-increment applied to invalid type: %s", value_show(peektarget()));
                        }
                        push(*poptarget());
                        break;
                CASE(POST_INC)
                        FALSE_OR (SpecialTarget()) {
                                vm_panic("pre-increment applied to invalid target");
                        }
                        push(*peektarget());
                        switch (peektarget()->type) {
                        case VALUE_INTEGER: ++peektarget()->integer; break;
                        case VALUE_REAL:    ++peektarget()->real;    break;
                        case VALUE_PTR:
                                vp = peektarget();
                                vp->ptr = ((char *)vp->ptr) + ((ffi_type *)(vp->extra == NULL ? &ffi_type_uint8 : vp->extra))->size;
                                break;
                        default:            vm_panic("post-increment applied to invalid type: %s", value_show(peektarget()));
                        }
                        poptarget();
                        break;
                CASE(PRE_DEC)
                        if (SpecialTarget()) {
                                vm_panic("pre-decrement applied to invalid target");
                        }
                        switch (peektarget()->type) {
                        case VALUE_INTEGER: --peektarget()->integer; break;
                        case VALUE_REAL:    --peektarget()->real;    break;
                        case VALUE_OBJECT:
                                vp = class_method(peektarget()->class, "--");
                                if (vp != NULL) {
                                        call(vp, peektarget(), 0, 0, true);
                                        break;
                                }
                        case VALUE_PTR:
                                vp = peektarget();
                                vp->ptr = ((char *)vp->ptr) - ((ffi_type *)(vp->extra == NULL ? &ffi_type_uint8 : vp->extra))->size;
                                break;
                        default:
                                vm_panic("pre-decrement applied to invalid type: %s", value_show(peektarget()));
                        }
                        push(*poptarget());
                        break;
                CASE(POST_DEC)
                        if (SpecialTarget()) {
                                vm_panic("post-decrement applied to invalid target");
                        }
                        push(*peektarget());
                        switch (peektarget()->type) {
                        case VALUE_INTEGER: --peektarget()->integer; break;
                        case VALUE_REAL:    --peektarget()->real;    break;
                        case VALUE_PTR:
                                vp = peektarget();
                                vp->ptr = ((char *)vp->ptr) - ((ffi_type *)(vp->extra == NULL ? &ffi_type_uint8 : vp->extra))->size;
                                break;
                        default:            vm_panic("post-decrement applied to invalid type: %s", value_show(peektarget()));
                        }
                        poptarget();
                        break;
                CASE(MUT_ADD)
                        DoMutAdd();
                        break;
                CASE(MUT_MUL)
                        DoMutMul();
                        break;
                CASE(MUT_DIV)
                        DoMutDiv();
                        break;
                CASE(MUT_SUB)
                        DoMutSub();
                        break;
                CASE(DEFINE_TAG)
                {
                        int tag, super, n;
                        READVALUE(tag);
                        READVALUE(super);
                        READVALUE(n);
                        while (n --> 0) {
                                v = pop();
                                tags_add_method(tag, ip, v);
                                ip += strlen(ip) + 1;
                        }
                        if (super != -1)
                                tags_copy_methods(tag, super);
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
                                v = pop();
                                class_add_static(class, ip, v);
                                ip += strlen(ip) + 1;
                        }
                        while (n --> 0) {
                                v = pop();
                                class_add_method(class, ip, v);
                                ip += strlen(ip) + 1;
                        }
                        while (g --> 0) {
                                v = pop();
                                class_add_getter(class, ip, v);
                                ip += strlen(ip) + 1;
                        }
                        while (s --> 0) {
                                v = pop();
                                class_add_setter(class, ip, v);
                                ip += strlen(ip) + 1;
                        }
                        break;
                }
                CASE(FUNCTION)
                {
                        READVALUE(b);

                        v.tags = 0;
                        v.type = VALUE_FUNCTION;

                        while (*ip != ((char)0xFF))
                                ++ip;
                        ++ip;

                        v.info = (int *) ip;

                        int hs = v.info[0];
                        int size  = v.info[1];
                        int nEnv = v.info[2];
                        int bound = v.info[3];

                        int ncaps = b ? nEnv - bound : nEnv;

                        LOG("Header size: %d", hs);
                        LOG("Code size: %d", size);
                        LOG("Bound: %d", bound);
                        LOG("ncaps: %d", ncaps);
                        LOG("Name: %s", value_show(&v));

                        ip += size + hs;

                        if (nEnv > 0) {
                                LOG("Allocating ENV for %d caps", nEnv);
                                v.env = gc_alloc_object(nEnv * sizeof (struct value *), GC_ENV);
                                memset(v.env, 0, nEnv * sizeof (struct value *));
                        } else {
                                v.env = NULL;
                        }

                        ++GC_OFF_COUNT;

                        if (ncaps > 0) {
                                for (int i = 0; i < ncaps; ++i) {
                                        READVALUE(b);
                                        READVALUE(j);
                                        struct value *p = poptarget();
                                        if (b) {
                                                if (p->type == VALUE_REF) {
                                                        /* This variable was already captured, just refer to the same object */
                                                        v.env[j] = p->ptr;
                                                } else {
                                                        // TODO: figure out if this is getting freed too early
                                                        struct value *new = gc_alloc_object(sizeof (struct value), GC_VALUE);
                                                        *new = *p;
                                                        *p = REF(new);
                                                        v.env[j] = new;
                                                }
                                        } else {
                                                v.env[j] = p;
                                        }
                                        LOG("env[%d] = %s", j, value_show(v.env[j]));
                                }
                        }

                        push(v);

                        --GC_OFF_COUNT;

                        break;
                }
                CASE(TAIL_CALL)
                        tco = true;
                        break;
                CASE(CALL)
                        v = pop();

                        READVALUE(n);
                        READVALUE(nkw);

                        if (n == -1) {
                                n = stack.count - *vec_pop(sp_stack) - nkw;
                        }

                        if (tco) {
                                vec_pop(frames);
                                ip = *vec_pop(calls);
                                tco = false;
                        }

                        /*
                         * Move all the keyword args into a dict.
                         */
                        if (nkw > 0) {
        CallKwArgs:
                                if (!AutoThis) {
                                        gc_push(&v);
                                } else {
                                        gc_push(v.this);
                                        AutoThis = false;
                                }
                                GC_OFF_COUNT += 1;
                                container = DICT(dict_new());
                                for (int i = 0; i < nkw; ++i) {
                                        if (ip[0] == '*') {
                                                if (top()->type == VALUE_DICT) {
                                                        dict_update(&container, 1, NULL);
                                                        pop();
                                                } else if (top()->type == VALUE_TUPLE && top()->names != NULL) {
                                                        for (int i = 0; i < top()->count; ++i) {
                                                                if (top()->names[i] != NULL) {
                                                                        dict_put_member(
                                                                                container.dict,
                                                                                top()->names[i],
                                                                                top()->items[i]
                                                                        );
                                                                }
                                                        }
                                                        pop();
                                                } else {
                                                        vm_panic(
                                                                "Attempt to splat invalid value in function call: %s%s%s%s%s",
                                                                TERM(34),
                                                                TERM(1),
                                                                value_show(top()),
                                                                TERM(22),
                                                                TERM(39)
                                                        );
                                                }
                                        } else {
                                                dict_put_member(container.dict, ip, pop());
                                        }
                                        ip += strlen(ip) + 1;
                                }
                                push(container);
                                GC_OFF_COUNT -= 1;
                        } else {
                                container = NIL;
        Call:
                                if (!AutoThis) {
                                        gc_push(&v);
                                } else {
                                        gc_push(v.this);
                                        AutoThis = false;
                                }
                        }

                        switch (v.type) {
                        case VALUE_FUNCTION:
                                LOG("CALLING %s with %d arguments", value_show(&v), n);
                                print_stack(n);
                                call(&v, NULL, n, nkw, false);
                                break;
                        case VALUE_BUILTIN_FUNCTION:
                                /*
                                 * Builtin functions may not preserve the stack size, so instead
                                 * of subtracting `n` after calling the builtin function, we compute
                                 * the desired final stack size in advance.
                                 */
                                if (nkw > 0) {
                                        container = pop();
                                        gc_push(&container);
                                        k = stack.count - n;
                                        v = v.builtin_function(n, &container);
                                        gc_pop();
                                } else {
                                        k = stack.count - n;
                                        v = v.builtin_function(n, NULL);
                                }
                                stack.count = k;
                                push(v);
                                break;
                        case VALUE_GENERATOR:
                                call_co(&v, n);
                                break;
                        case VALUE_TAG:
                                if (n == 1 && nkw == 0) {
                                        top()->tags = tags_push(top()->tags, v.tag);
                                        top()->type |= VALUE_TAGGED;
                                } else if (nkw > 0) {
                                        GC_OFF_COUNT += 1;
                                        container = pop();
                                        value = builtin_tuple(n, &container);
                                        stack.count -= n;
                                        value.type |= VALUE_TAGGED;
                                        value.tags = tags_push(value.tags, v.tag);
                                        push(value);
                                        GC_OFF_COUNT -= 1;
                                } else {
                                        GC_OFF_COUNT += 1;
                                        value = builtin_tuple(n, NULL);
                                        stack.count -= n;
                                        value.type |= VALUE_TAGGED;
                                        value.tags = tags_push(value.tags, v.tag);
                                        push(value);
                                        GC_OFF_COUNT -= 1;
                                }
                                break;
                        case VALUE_CLASS:
                                vp = class_method(v.class, "init");
                                if (v.class < CLASS_PRIMITIVE && v.class != CLASS_OBJECT) {
                                        if (vp != NULL) {
                                                call(vp, NULL, n, nkw, true);
                                        } else {
                                                vm_panic("primitive class has no init method. was prelude loaded?");
                                        }
                                } else {
                                        value = OBJECT(object_new(v.class), v.class);
                                        if (vp != NULL) {
                                                gc_push(&value);
                                                call(vp, &value, n, nkw, true);
                                                gc_pop();
                                                pop();
                                        } else {
                                                stack.count -= n;
                                        }
                                        push(value);
                                }
                                break;
                        case VALUE_METHOD:
                                if (v.name == MISSING) {
                                        push(NIL);
                                        memmove(top() - (n - 1), top() - n, n * sizeof (struct value));
                                        top()[-n++] = v.this[1];
                                }
                                call(v.method, v.this, n, nkw, false);
                                break;
                        case VALUE_REGEX:
                                if (n != 1)
                                        vm_panic("attempt to apply a regex to an invalid number of values");
                                value = peek();
                                if (value.type != VALUE_STRING)
                                        vm_panic("attempt to apply a regex to a non-string: %s", value_show(&value));
                                push(v);
                                v = get_string_method("match!")(&value, 1, NULL);
                                pop();
                                *top() = v;
                                break;
                        case VALUE_BUILTIN_METHOD:
                                if (nkw > 0) {
                                        container = pop();
                                        gc_push(&container);
                                        k = stack.count - n;
                                        v = v.builtin_method(v.this, n, &container);
                                        gc_pop();
                                } else {
                                        k = stack.count - n;
                                        v = v.builtin_method(v.this, n, NULL);
                                }
                                stack.count = k;
                                push(v);
                                break;
                        case VALUE_NIL:
                                stack.count -= n;
                                push(NIL);
                                break;
                        default:
                                vm_panic("attempt to call non-callable value %s", value_show(&v));
                        }
                        gc_pop();
                        nkw = 0;
                        break;
                CASE(TRY_CALL_METHOD)
                CASE(CALL_METHOD)
                        b = ip[-1] == INSTR_TRY_CALL_METHOD;

                        READVALUE(n);

                        method = ip;
                        ip += strlen(ip) + 1;

                        READVALUE(h);

                        READVALUE(nkw);

                        if (n == -1) {
                                n = stack.count - *vec_pop(sp_stack) - nkw - 1;
                        }

                /*
                 * b, n, nkw, h, and method must all be correctly set when jumping here
                 */
                CallMethod:
                        LOG("METHOD = %s, n = %d", method, n);
                        print_stack(5);

                        value = peek();
                        vp = NULL;
                        func = NULL;
                        struct value *self = NULL;

                        if (tco) {
                                vec_pop(frames);
                                ip = *vec_pop(calls);
                                tco = false;
                        }

                        for (int tags = value.tags; tags != 0; tags = tags_pop(tags)) {
                                vp = tags_lookup_method(tags_first(tags), method, h);
                                if (vp != NULL) {
                                        value.tags = tags_pop(tags);
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
                                vp = tags_lookup_method(value.tag, method, h);
                                if (vp == NULL) {
                                        vp = class_lookup_method(CLASS_TAG, method, h);
                                } else {
                                        self = NULL;
                                }
                                break;
                        case VALUE_STRING:
                                func = get_string_method(method);
                                if (func == NULL)
                                        vp = class_lookup_method(CLASS_STRING, method, h);
                                break;
                        case VALUE_DICT:
                                func = get_dict_method(method);
                                if (func == NULL)
                                        vp = class_lookup_method(CLASS_DICT, method, h);
                                break;
                        case VALUE_ARRAY:
                                func = get_array_method(method);
                                if (func == NULL)
                                        vp = class_lookup_method(CLASS_ARRAY, method, h);
                                break;
                        case VALUE_BLOB:
                                func = get_blob_method(method);
                                if (func == NULL)
                                        vp = class_lookup_method(CLASS_BLOB, method, h);
                                break;
                        case VALUE_INTEGER:
                                vp = class_lookup_method(CLASS_INT, method, h);
                                break;
                        case VALUE_REAL:
                                vp = class_lookup_method(CLASS_FLOAT, method, h);
                                break;
                        case VALUE_BOOLEAN:
                                vp = class_lookup_method(CLASS_BOOL, method, h);
                                break;
                        case VALUE_REGEX:
                                vp = class_lookup_method(CLASS_REGEX, method, h);
                                break;
                        case VALUE_FUNCTION:
                        case VALUE_BUILTIN_FUNCTION:
                        case VALUE_METHOD:
                        case VALUE_BUILTIN_METHOD:
                                vp = class_lookup_method(CLASS_FUNCTION, method, h);
                                break;
                        case VALUE_GENERATOR:
                                vp = class_lookup_method(CLASS_GENERATOR, method, h);
                                break;
                        case VALUE_TUPLE:
                                vp = tuple_get(&value, method);
                                if (vp == NULL) {
                                        vp = class_lookup_method(CLASS_TUPLE, method, h);
                                } else {
                                        self = NULL;
                                }
                                break;
                        case VALUE_CLASS: /* lol */
                                vp = class_lookup_immediate(CLASS_CLASS, method, h);
                                if (vp == NULL) {
                                        vp = class_lookup_static(value.class, method, h);
                                }
                                if (vp == NULL) {
                                        vp = class_lookup_method(value.class, method, h);
                                }
                                break;
                        case VALUE_OBJECT:
                                vp = table_lookup(value.object, method, h);
                                if (vp == NULL) {
                                        vp = class_lookup_method(value.class, method, h);
                                } else {
                                        self = NULL;
                                }
                                break;
                        case VALUE_NIL:
                                stack.count -= (n + 1 + nkw);
                                push(NIL);
                                continue;
                        }

                        if (func != NULL) {
                                pop();
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
                                pop();
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
                                stack.count -= (n + 1 + nkw);
                                push(NIL);
                        } else {
                                if (value.type == VALUE_OBJECT) {
                                        vp = class_method(value.class, MISSING);
                                        if (vp != NULL) {
                                                v = pop();
                                                push(NIL);
                                                memmove(top() - (n - 1), top() - n, n * sizeof (struct value));
                                                top()[-n++] = STRING_NOGC(method, strlen(method));
                                                push(v);
                                                self = &value;
                                                goto SetupMethodCall;
                                        }
                                }
                                vm_panic("call to non-existent method '%s' on %s", method, value_show(&value));
                        }
                        break;
                CASE(SAVE_STACK_POS)
                        vec_push(sp_stack, stack.count);
                        break;
                CASE(RESTORE_STACK_POS)
                        stack.count = *vec_pop(sp_stack);
                        break;
                CASE(MULTI_RETURN)
                CASE(RETURN)
                Return:
                        n = vec_last(frames)->fp;
                        if (ip[-1] == INSTR_MULTI_RETURN) {
                                READVALUE(rc);
                                stack.count -= rc;
                                for (int i = 0; i <= rc; ++i) {
                                        stack.items[n + i] = top()[i];
                                }
                        } else {
                                stack.items[n] = peek();
                        }
                        stack.count = n + 1;
                        LOG("POPPING FRAME");
                        vec_pop(frames);
                CASE(RETURN_PRESERVE_CTX)
                        ip = *vec_pop(calls);
                        LOG("returning: ip = %p", ip);
                        break;
                CASE(HALT)
                        ip = save;
                        LOG("halting: ip = %p", ip);
                        return;
                }
        }

        while (q1.n != 0) {
                ;
        }

        continue;

        TyThread *current = &Threads.items[ThreadIndex];

        for (int i = 1; i < Threads.count; ++i) {
                int j = (i + ThreadIndex) % Threads.count;

                TyThread *t = &Threads.items[j];

                if (!t->waiting) {
                        current->stack = stack;
                        current->calls = calls;
                        current->frames = frames;
                        current->targets = targets;
                        current->try_stack = try_stack;
                        current->sp_stack = sp_stack;
                        current->ip = ip;

                        stack = t->stack;
                        calls = t->calls;
                        frames = t->frames;
                        targets = t->targets;
                        try_stack = t->try_stack;
                        sp_stack = t->sp_stack;
                        ip = t->ip;
                }
        }

        }
}

static pthread_mutex_t mutex = PTHREAD_MUTEX_INITIALIZER;
static pthread_cond_t cond = PTHREAD_COND_INITIALIZER;
static struct value *builtin_argv;

void *
run_builtin_thread(void *ctx)
{
        struct value v;

        for (;;) {
                while (q2.n == 0) {
                        ;
                }

                Message *msg = queue_take(&q2);

                switch (msg->type) {
                case TYMSG_CALL:
                        v = msg->f->builtin_function(msg->n, NULL);
                        msg->type = TYMSG_RESULT;
                        msg->v = v;
                        queue_add(&q1, msg);
                        break;
                }
        }

        return NULL;
}

char const *
vm_error(void)
{
        return Error;
}

static void
RunExitHooks(void)
{
        if (iExitHooks == -1 || Globals.items[iExitHooks].type != VALUE_ARRAY)
                return;

        struct array *hooks = Globals.items[iExitHooks].array;

        vec(char *) msgs = {0};
        char *first = (Error == NULL) ? NULL : sclone_malloc(Error);

        bool bReprintFirst = false;

        for (size_t i = 0; i < hooks->count; ++i) {
                if (setjmp(jb) != 0) {
                        vec_push(msgs, sclone_malloc(ERR));
                } else {
                        struct value v = vm_call(&hooks->items[i], 0);
                        bReprintFirst = bReprintFirst || value_truthy(&v);
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
vm_init(int ac, char **av)
{
        GC_OFF_COUNT += 1;

        vec_init(stack);
        vec_init(calls);
        vec_init(targets);

        InitThreadGroup(MyGroup = &MainGroup);

        MainThread = pthread_self();

        pcre_malloc = malloc;
        JITStack = pcre_jit_stack_alloc(JIT_STACK_START, JIT_STACK_MAX);

        NewArena(1 << 28);

        curl_global_init(CURL_GLOBAL_ALL);

        srandom(time(NULL));

        compiler_init();

        add_builtins(ac, av);

        char *prelude = compiler_load_prelude();
        if (prelude == NULL) {
                Error = compiler_error();
                return false;
        }

        if (setjmp(jb) != 0) {
                Error = ERR;
                return false;
        }

        queue_init(&q1);
        queue_init(&q2);

        AddThread();

        --GC_OFF_COUNT;

//        int e;
//        if (e = pthread_create(&BuiltinRunner, NULL, run_builtin_thread, NULL), e != 0) {
//                vm_panic("Failed to create thread: %s", strerror(e));
//        }

        atexit(RunExitHooks);

        vm_exec(prelude);

        compiler_load_builtin_modules();

        sqlite_load();

        return true;
}

noreturn void
vm_panic(char const *fmt, ...)
{
        va_list ap;
        va_start(ap, fmt);

        struct location start;
        struct location end;

        int sz = ERR_SIZE - 1;

        int n = snprintf(ERR, sz, "%s%sRuntimeError%s%s: ", TERM(1), TERM(31), TERM(22), TERM(39));
        n += vsnprintf(ERR + n, max(sz - n, 0), fmt, ap);
        va_end(ap);

        if (n < sz)
                ERR[n++] = '\n';

        for (int i = 0; n < sz; ++i) {
                char const *file = compiler_get_location(ip, &start, &end);
                char buffer[512];

                snprintf(
                        buffer,
                        sizeof buffer - 1,
                        "%36s %s%s%s:%s%d%s:%s%d%s",
                        (i == 0) ? "at" : "from",
                        TERM(34),
                        file,
                        TERM(39),
                        TERM(33),
                        start.line + 1,
                        TERM(39),
                        TERM(33),
                        start.col + 1,
                        TERM(39)
                );

                char const *where = buffer;
                int m = strlen(buffer) - 6*strlen(TERM(00));

                while (m > 36) {
                        m -= 1;
                        where += 1;
                }

                n += snprintf(
                        ERR + n,
                        sz - n,
                        "\n%s near: ",
                        where
                );

                if (start.s == NULL) {
                        start.s = "\n(unknown location)" + 1;
                        end.s = start.s;
                }

                char const *prefix = start.s;
                while (prefix[-1] != '\0' && prefix[-1] != '\n')
                        --prefix;

                while (isspace(prefix[0]))
                        ++prefix;

                int before = start.s - prefix;
                int length = end.s - start.s;
                int after = strcspn(end.s, "\n");

                n += snprintf(
                        ERR + n,
                        sz - n,
                        "%s%.*s%s%s%.*s%s%s%.*s%s",
                        TERM(32),
                        before,
                        prefix,
                        (i == 0) ? TERM(1) : "",
                        (i == 0) ? TERM(91) : TERM(31),
                        length,
                        start.s,
                        TERM(32),
                        TERM(22),
                        after,
                        end.s,
                        TERM(39)
                );

                n += snprintf(
                        ERR + n,
                        sz - n,
                        "\n\t%*s%s%s",
                        before + 35,
                        "",
                        (i == 0) ? TERM(1) : "",
                        (i == 0) ? TERM(91) : TERM(31)
                );

                for (int i = 0; i < length && n < sz; ++i)
                        ERR[n++] = '^';

                n += snprintf(
                        ERR + n,
                        sz - n,
                        "%s%s",
                        TERM(39),
                        TERM(22)
                );
Next:
                if (frames.count == 0) {
                        break;
                }

                ip = vec_pop(frames)->ip;
        }

        LOG("VM Error: %s", ERR);

        longjmp(jb, 1);
}

bool
vm_execute_file(char const *path)
{
        char *source = slurp(path);
        if (source == NULL) {
                Error = "failed to read source file";
                return false;
        }

        filename = path;

        bool success = vm_execute(source);

        GCLOG("Allocs before: %zu", allocs.count);
        //DoGC();
        GCLOG("Allocs after: %zu", allocs.count);

        /*
         * When we read the file, we copy into an allocated buffer with a 0 byte at
         * the beginning, so we need to subtract 1 here to get something appropriate
         * for free().
         */
        gc_free(source - 1);

        filename = NULL;

        return success;
}

bool
vm_execute(char const *source)
{
        if (filename == NULL)
                filename = "(repl)";

        ++GC_OFF_COUNT;

        gc_clear_root_set();
        stack.count = 0;
        sp_stack.count = 0;
        try_stack.count = 0;
        targets.count = 0;

        if (setjmp(jb) != 0) {
                Error = ERR;
                return false;
        }

        char *code = compiler_compile_source(source, filename);
        if (code == NULL) {
                Error = compiler_error();
                LOG("compiler error was: %s", Error);
                return false;
        }

        --GC_OFF_COUNT;

        if (CompileOnly) {
                return true;
        }

        vm_exec(code);

        if (PrintResult && stack.capacity > 0) {
                printf("%s\n", value_show(top() + 1));
        }

        return true;
}

void
vm_push(struct value const *v)
{
        push(*v);
}

void
vm_pop(void)
{
        stack.count -= 1;
}

struct value *
vm_get(int i)
{
        return top() - i;
}

_Noreturn void
vm_throw(struct value const *v)
{
        push(*v);
        vm_exec((char[]){INSTR_THROW});
        // unreachable
        abort();
}

FrameStack *
vm_get_frames(void)
{
        return &frames;
}

struct value
vm_call2(struct value const *f, int argc)
{
        struct value v;
        Message *msg = gc_alloc(sizeof *msg);

        msg->args = gc_alloc(sizeof *msg->args * argc);
        msg->f = gc_alloc(sizeof *msg->f);
        *msg->f = *f;

        for (int i = 0; i < argc; ++i) {
                msg->args[i] = top()[i - argc + 1];
        }

        queue_add(&q1, msg);

        for (;;) {
                while (q2.n == 0) {
                        ;
                }

                msg = queue_take(&q2);

                switch (msg->type) {
                case TYMSG_RESULT:
                        v = msg->v;
                        gc_free(msg);
                        return v;
                case TYMSG_CALL:
                        v = msg->f->builtin_function(msg->n, NULL);
                        msg->type = TYMSG_RESULT;
                        msg->v = v;
                        queue_add(&q1, msg);
                        break;
                }
        }
}

struct value
vm_call_method(struct value const *self, struct value const *f, int argc)
{
        call(f, self, argc, 0, true);
        return pop();
}

struct value
vm_call(struct value const *f, int argc)
{
        struct value r, *init;
        size_t n = stack.count - argc;

        switch (f->type) {
        case VALUE_FUNCTION:
                call(f, NULL, argc, 0, true);
                return pop();
        case VALUE_METHOD:
                call(f->method, f->this, argc, 0, true);
                return pop();
        case VALUE_BUILTIN_FUNCTION:
                r = f->builtin_function(argc, NULL);
                stack.count = n;
                return r;
        case VALUE_BUILTIN_METHOD:
                r = f->builtin_method(f->this, argc, NULL);
                stack.count = n;
                return r;
        case VALUE_TAG:
                r = pop();
                r.tags = tags_push(r.tags, f->tag);
                r.type |= VALUE_TAGGED;
                return r;
        case VALUE_CLASS:
                init = class_method(f->class, "init");
                if (f->class < CLASS_PRIMITIVE) {
                        if (init != NULL) {
                                call(init, NULL, argc, 0, true);
                                return pop();
                        } else {
                                vm_panic("Couldn't find init method for built-in class. Was prelude loaded?");
                        }
                } else {
                        r = OBJECT(object_new(f->class), f->class);
                        if (init != NULL) {
                                call(init, &r, argc, 0, true);
                                pop();
                        } else {
                                stack.count -= (argc + 1);
                        }
                        return r;
                }
        default:
                vm_panic("Non-callable value passed to vm_call(): %s", value_show_color(f));
        }
}

struct value
vm_eval_function(struct value const *f, ...)
{
        int argc;
        va_list ap;
        struct value r;
        struct value const *v;

        va_start(ap, f);
        argc = 0;

        while ((v = va_arg(ap, struct value const *)) != NULL) {
                push(*v);
                argc += 1;
        }

        va_end(ap);

        size_t n = stack.count - argc;

        switch (f->type) {
        case VALUE_FUNCTION:
                call(f, NULL, argc, 0, true);
                return pop();
        case VALUE_METHOD:
                call(f->method, f->this, argc, 0, true);
                return pop();
        case VALUE_BUILTIN_FUNCTION:
                r = f->builtin_function(argc, NULL);
                stack.count = n;
                return r;
        case VALUE_BUILTIN_METHOD:
                r = f->builtin_method(f->this, argc, NULL);
                stack.count = n;
                return r;
        default:
                abort();
        }
}

void
MarkStorage(ThreadStorage const *storage)
{
        vec(struct value const *) *root_set = storage->root_set;

        GCLOG("Marking root set");
        for (int i = 0; i < root_set->count; ++i) {
                value_mark(root_set->items[i]);
        }

        GCLOG("Marking stack");
        for (int i = 0; i < storage->stack->count; ++i) {
                value_mark(&storage->stack->items[i]);
        }

        GCLOG("Marking defer_stack");
        for (int i = 0; i < storage->defer_stack->count; ++i) {
                value_mark(&storage->defer_stack->items[i]);
        }

        GCLOG("Marking targets");
        for (int i = 0; i < storage->targets->count; ++i) {
                if ((((uintptr_t)storage->targets->items[i].t) & 0x07) == 0) {
                        value_mark(storage->targets->items[i].t);
                }
        }

        GCLOG("Marking frame functions");
        for (int i = 0; i < storage->frames->count; ++i) {
                value_mark(&storage->frames->items[i].f);
        }

        // FIXME: should finalizers be allowed to keep things alive?
        return;

        GCLOG("Marking finalizers");
        for (int i = 0; i < storage->allocs->count; ++i) {
                if (storage->allocs->items[i]->type == GC_OBJECT) {
                        value_mark(&((struct table *)storage->allocs->items[i]->data)->finalizer);
                }
        }
}

/* vim: set sts=8 sw=8 expandtab: */
