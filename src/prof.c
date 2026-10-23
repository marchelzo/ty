#include "prof.h"

#define X(name) TY_USDT_DEFINE(name);
TY_USDT_PROBES
#undef X

bool ProfMode;

#ifdef TY_HAVE_SAMPLER

#include <dlfcn.h>
#include <errno.h>
#include <math.h>
#include <pthread.h>
#include <signal.h>
#include <ctype.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <sys/resource.h>
#include <sys/stat.h>
#include <time.h>
#include <unistd.h>

#include "ty.h"
#include "vm.h"
#include "value.h"
#include "compiler.h"
#include "parse.h"
#include "class.h"
#include "ty/debug.h"
#include "gc.h"
#include "istat.h"
#include "xd.h"
#include "jit/jit.h"
#include "jit/lir.h"
#include "dict.h"
#include "dirs.h"
#include "token.h"
#include "highlight.h"
#include "title.h"
#include "jit/jit_impl.h"
#include "prof/platform.h"

enum {
        MAX_FRAMES   = 160,
        HDR_WORDS    = 5,
        RING_WORDS   = 1 << 20,
        MAX_THREADS  = 1024
};

enum {
        SYM_NONE,
        SYM_JIT,
        SYM_FIRST
};

enum {
        CAT_JIT,
        CAT_INTERP,
        CAT_VMOPS,
        CAT_JIT_RT,
        CAT_CALLS,
        CAT_ITER,
        CAT_ALLOC,
        CAT_NATIVE,
        CAT_GC,
        CAT_COMPILE,
        CAT_JIT_COMPILE,
        CAT_BLOCKED,
        CAT_COUNT
};

static char const *CatNames[CAT_COUNT] = {
        [CAT_JIT]         = "JIT-compiled code",
        [CAT_INTERP]      = "Interpreter",
        [CAT_VMOPS]       = "Generic operations",
        [CAT_JIT_RT]      = "JIT slow paths",
        [CAT_CALLS]       = "Calls",
        [CAT_ITER]        = "Generators",
        [CAT_ALLOC]       = "Allocation",
        [CAT_NATIVE]      = "Builtins",
        [CAT_GC]          = "GC",
        [CAT_COMPILE]     = "Compilation",
        [CAT_JIT_COMPILE] = "JIT compilation",
        [CAT_BLOCKED]     = "Blocking calls"
};

static char const CatGlyph[CAT_COUNT] = {
        [CAT_JIT]         = 'J',
        [CAT_INTERP]      = 'i',
        [CAT_VMOPS]       = 'o',
        [CAT_JIT_RT]      = 'r',
        [CAT_CALLS]       = 'f',
        [CAT_ITER]        = 'g',
        [CAT_ALLOC]       = 'a',
        [CAT_NATIVE]      = 'n',
        [CAT_GC]          = 'G',
        [CAT_COMPILE]     = 'C',
        [CAT_JIT_COMPILE] = 'c',
        [CAT_BLOCKED]     = '.'
};

static struct {
        int cat;
        char const *pat;
} const SymClasses[] = {
        { CAT_GC,     "DoGC*" },
        { CAT_GC,     "GCSweep*" },
        { CAT_GC,     "GCMark*" },
        { CAT_GC,     "value_mark*" },
        { CAT_GC,     "_value_mark*" },
        { CAT_GC,     "MarkStorage*" },
        { CAT_GC,     "collect" },
        { CAT_GC,     "WaitGC*" },
        { CAT_ITER,   "SetupGenerator" },
        { CAT_ITER,   "DoYield" },
        { CAT_ITER,   "YieldFix" },
        { CAT_ITER,   "DoGenerator" },
        { CAT_ITER,   "NewGenerator" },
        { CAT_ITER,   "call_co*" },
        { CAT_ITER,   "co_*" },
        { CAT_ITER,   "IterGetNext" },
        { CAT_ITER,   "jit_rt_loop_*" },
        { CAT_ITER,   "vm_jit_loop_*" },
        { CAT_ITER,   "jit_rt_yield*" },
        { CAT_ITER,   "jit_rt_generator" },
        { CAT_ITER,   "vm_iter_*" },
        { CAT_ITER,   "vm_jit_yield_from" },
        { CAT_ITER,   "tags_push" },
        { CAT_ITER,   "tags_pop" },
        { CAT_ITER,   "tags_try_pop" },
        { CAT_ITER,   "jit_rt_tag_push" },
        { CAT_ITER,   "jit_rt_try_tag_pop" },
        { CAT_CALLS,  "xcall" },
        { CAT_CALLS,  "xjit*" },
        { CAT_CALLS,  "call_jit" },
        { CAT_CALLS,  "call_enter" },
        { CAT_CALLS,  "call_leave" },
        { CAT_CALLS,  "call_with" },
        { CAT_CALLS,  "call_builtin" },
        { CAT_CALLS,  "call_init" },
        { CAT_CALLS,  "call" },
        { CAT_CALLS,  "vm_call*" },
        { CAT_CALLS,  "vm_xcall" },
        { CAT_CALLS,  "push_frame" },
        { CAT_CALLS,  "method_enter" },
        { CAT_CALLS,  "DoCall*" },
        { CAT_CALLS,  "vm_trampoline*" },
        { CAT_CALLS,  "jit_rt_call_*" },
        { CAT_CALLS,  "jit_rt_tail_loop" },
        { CAT_CALLS,  "jit_rt_capture" },
        { CAT_CALLS,  "jit_rt_function" },
        { CAT_CALLS,  "jit_rt_patch_env" },
        { CAT_CALLS,  "DoFunction" },
        { CAT_CALLS,  "vm_jit_bind*" },
        { CAT_ALLOC,  "raw_object" },
        { CAT_ALLOC,  "mi_*" },
        { CAT_ALLOC,  "_mi_*" },
        { CAT_ALLOC,  "malloc" },
        { CAT_ALLOC,  "calloc" },
        { CAT_ALLOC,  "realloc" },
        { CAT_ALLOC,  "free" },
        { CAT_ALLOC,  "cfree" },
        { CAT_ALLOC,  "_int_*" },
        { CAT_ALLOC,  "NewInstance" },
        { CAT_ALLOC,  "value_array_new*" },
        { CAT_ALLOC,  "value_record" },
        { CAT_ALLOC,  "value_tuple" },
        { CAT_ALLOC,  "value_named_tuple" },
        { CAT_ALLOC,  "jit_rt_tuple*" },
        { CAT_ALLOC,  "jit_rt_array*" },
        { CAT_ALLOC,  "DoTupleLiteral" },
        { CAT_ALLOC,  "DoDictLiteral" },
        { CAT_ALLOC,  "DoSetLiteral" },
        { CAT_ALLOC,  "comprehend" },
        { CAT_ALLOC,  "gc_alloc*" },
        { CAT_INTERP, "vm_exec" },
        { CAT_JIT_RT, "jit_rt_*" },
        { CAT_JIT_RT, "vm_jit_*" },
        { CAT_VMOPS,  "op_*" },
        { CAT_VMOPS,  "DoGeq" },
        { CAT_VMOPS,  "DoGt" },
        { CAT_VMOPS,  "DoLeq" },
        { CAT_VMOPS,  "DoLt" },
        { CAT_VMOPS,  "DoEq" },
        { CAT_VMOPS,  "DoNeq" },
        { CAT_VMOPS,  "DoCmp" },
        { CAT_VMOPS,  "DoNot" },
        { CAT_VMOPS,  "DoNeg" },
        { CAT_VMOPS,  "DoBinaryOp" },
        { CAT_VMOPS,  "DoUnaryOp" },
        { CAT_VMOPS,  "DoMut*" },
        { CAT_VMOPS,  "DoPtrMutOp" },
        { CAT_VMOPS,  "DoSetterMutOp" },
        { CAT_VMOPS,  "DoSubscript" },
        { CAT_VMOPS,  "DoSafeSubscript" },
        { CAT_VMOPS,  "DoAssignSubscript" },
        { CAT_VMOPS,  "DoTargetSubscript" },
        { CAT_VMOPS,  "DoTargetMember" },
        { CAT_VMOPS,  "DoAssign*" },
        { CAT_VMOPS,  "DoCheckMatch" },
        { CAT_VMOPS,  "DoMatchString" },
        { CAT_VMOPS,  "DoRange" },
        { CAT_VMOPS,  "DoTag" },
        { CAT_VMOPS,  "DoQuestion" },
        { CAT_VMOPS,  "DoDrop" },
        { CAT_VMOPS,  "IncValue" },
        { CAT_VMOPS,  "DecValue" },
        { CAT_VMOPS,  "push" },
        { CAT_VMOPS,  "pushtarget" },
        { CAT_VMOPS,  "check_value" },
        { CAT_VMOPS,  "vm_2op" },
        { CAT_VMOPS,  "vm_try_2op" },
        { CAT_VMOPS,  "value_compare" },
        { CAT_VMOPS,  "value_test_equality" },
        { CAT_VMOPS,  "value_truthy" },
        { CAT_VMOPS,  "record_slot" },
        { CAT_VMOPS,  "GetMember*" },
        { CAT_VMOPS,  "vm_get_self" },
};

static u8 *SymCat;
static u32 SymCatN;

static char const *KindNames[PK_COUNT] = {
        [PK_CPU]   = "cpu",
        [PK_WALL]  = "wall",
        [PK_EVENT] = "event",
        [PK_OPS]   = "ops",
        [PK_ALLOC] = "alloc",
        [PK_THROW] = "throw"
};

static char const *GcTypeNames[] = {
        [GC_STRING]       = "String",
        [GC_ARRAY]        = "Array",
        [GC_TUPLE]        = "Tuple",
        [GC_OBJECT]       = "Object",
        [GC_DICT]         = "Dict",
        [GC_SET]          = "Set",
        [GC_HEAP]         = "Heap",
        [GC_BLOB]         = "Blob",
        [GC_QUEUE]        = "Queue",
        [GC_SHARED_QUEUE] = "SharedQueue",
        [GC_VALUE]        = "Value",
        [GC_ENV]          = "closure env",
        [GC_GENERATOR]    = "Generator",
        [GC_THREAD]       = "Thread",
        [GC_REGEX]        = "Regex",
        [GC_ARENA]        = "arena",
        [GC_FUN_INFO]     = "function",
        [GC_JIT_CODE]     = "JIT code",
        [GC_LIR]          = "LIR",
        [GC_FFI_AUTO]     = "FFI",
        [GC_MUTEX]        = "Mutex",
        [GC_SPINLOCK]     = "SpinLock",
        [GC_CONDVAR]      = "CondVar",
        [GC_NOTE]         = "note",
        [GC_COUNTER]      = "counter",
        [GC_CHANNEL]      = "Channel",
        [GC_SCREEN]       = "Screen",
        [GC_ANY]          = "buffer"
};

typedef struct {
        u32 off;
        u16 n;
        u8 kind;
        u8 state;
        u32 sym;
        u32 thread;
        u64 mask;
        u64 hash;
        u64 count;
        u64 weight;
} Stack;

typedef struct {
        Expr const *expr;
        char const *why;
        i32 off;
        char const *code;
} JitDecline;

#define DEOPT_NOTES  6
#define DEOPT_SHOTS  6
#define SHOT_FRAMES 24

typedef struct {
        u64 t;
        u64 hash;
        u64 count;
        u32 nframes;
        u64 ips[SHOT_FRAMES];
        char *vars;
} DeoptShot;

typedef struct {
        Expr const *expr;
        char const *code;
        i32 off;
        i32 why;
        u32 guard;
        u64 n;
        u64 first;
        u64 last;
        struct {
                char text[96];
                u64  n;
        } notes[DEOPT_NOTES];
        u32 nshots;
        DeoptShot shots[DEOPT_SHOTS];
} DeoptSite;

typedef struct {
        Expr const *expr;
        u64 at;
        u32 deopts;
} Despec;

_Thread_local u8 volatile ProfState;
_Thread_local u64 ProfPending;
_Atomic u64 ProfLiveN;
_Thread_local i64 ProfAllocLeft = INT64_MAX;
_Thread_local i64 ProfOpsLeft = INT64_MAX;
bool ProfCountOps;

FILE *ProfileOut;
bool UseWallTime;
u64 ProfileSampleInterval;
istat prof;

bool ColorProfile;

static _Thread_local ProfThread *MyProf;

static ProfThread *Threads[MAX_THREADS];
static _Atomic u32 NThreads;
static _Atomic bool Running;
static _Atomic bool Stopping;
static bool Started;
static bool Reported;
_Atomic bool ProfWantReport;

static int         Mode         = PK_CPU;
static u64         Hz           = 999;
static u64         Period;
static u64         AllocEvery   = 512 * 1024;
static u64         OpsEvery     = 97;
static char const *EventName    = "cycles";
static char const *EventSpec;
static bool        JitCounts    = true;
static u64         EventPeriod;
static int         TopN         = 8;
static double      MinPct       = 2.0;
static int         HotLines     = 6;
static double      HotMinPct    = 2.0;
static bool        Quiet;
static char const *DataPath     = "ty-prof.data";
static u64         DataSize;
static int         Cols         = 100;
static time_t      StartUnix;
static char        AttachRecord[1024];
static bool        AttachColor;
static int         AttachCols;
static bool        FollowChildren;

static _Atomic u64 HandlerNs;
static _Atomic u64 Dropped;
static _Atomic u64 Busy;
static u64         StartWall;
static u64         StopWall;
static struct rusage StartUsage;

static pthread_t   WallThread;
static pthread_t   DrainThread;
static bool        HaveWallThread;
static bool        HaveDrainThread;
static pthread_mutex_t DrainLock = PTHREAD_MUTEX_INITIALIZER;
static pthread_mutex_t ThreadsLock = PTHREAD_MUTEX_INITIALIZER;

static vec(u64)    Keys;
static vec(Stack)  Stacks;
static u32        *Table;
static u32         TableCap;

static struct {
        u64 *t;
        u32 *s;
        usize n;
        usize cap;
} Timeline;

static ExeSym     *Syms;
static usize       NSyms;
static uptr        ExeLo;
static uptr        ExeHi;
static vec(char const *) SymNames;
static struct {
        uptr *rip;
        u32 *id;
        u32 cap;
        u32 n;
} RipCache;

static TySpinLock  JitLock;
static vec(JitDecline) Declines;
static vec(DeoptSite)   Deopts;
static vec(Despec)      Despecs;

static char const *ProfTarget;
static bool Attached;

typedef struct {
        char const *name;
        char const *path;
        u32 lines;
        int parent;
        u64 t0;
        u64 t1;
        u64 t2;
        u64 child_compile;
        u64 child_total;
} ModLoad;

static vec(ModLoad) Mods;

static int **Infos;
static u64 InfoCap;
static u64 InfoN;
static pthread_mutex_t InfoLock = PTHREAD_MUTEX_INITIALIZER;

typedef struct {
        struct alloc *a;
        u64 seq;
        u64 epoch;
} LiveObj;

static LiveObj *Live;
static u64 LiveCap;
static u64 LiveUsed;
static pthread_mutex_t LiveLock = PTHREAD_MUTEX_INITIALIZER;
static _Atomic u64 AllocSeq;
static u64 GcEpoch;
static vec(u32) SeqStack;
static vec(u64) HeapTimeT;
static vec(u64) HeapTimeB;

#define LIVE_TOMB ((struct alloc *)1)
static int ModTop = -1;

static struct {
        u64 n;
        u64 total;
        u64 max;
        u64 freed;
        u64 peak;
} GcStats;

inline static u64
NowNs(void)
{
        struct timespec t;
        clock_gettime(CLOCK_MONOTONIC, &t);
        return 1000000000ULL * t.tv_sec + t.tv_nsec;
}

inline static u64
MaxRssBytes(struct rusage const *ru)
{
#ifdef __APPLE__
        return (u64)ru->ru_maxrss;
#else
        return (u64)ru->ru_maxrss * 1024;
#endif
}

inline static u64
Mix(u64 h, u64 x)
{
        h ^= x + 0x9E3779B97F4A7C15ULL + (h << 6) + (h >> 2);
        h *= 0xFF51AFD7ED558CCDULL;
        return h ^ (h >> 32);
}

static bool
ParseSize(char const *s, u64 *out)
{
        char *end;
        double v = strtod(s, &end);

        if (end == s || v < 0) {
                return false;
        }

        switch (*end) {
        case 'k': case 'K': v *= 1024.0;               ++end; break;
        case 'm': case 'M': v *= 1024.0 * 1024.0;      ++end; break;
        case 'g': case 'G': v *= 1024.0 * 1024 * 1024; ++end; break;
        }

        if (*end == 'b' || *end == 'B') {
                ++end;
        }

        if (*end != '\0') {
                return false;
        }

        *out = (u64)v;

        return true;
}

static char const *
EventUsage(void)
{
        static char buf[1024];
        char const *const *names = prof_os_events();
        usize n = 0;
        int col = 37;

        if (names == NULL || names[0] == NULL) {
                return "";
        }

        n += ty_snprintf(
                buf + n,
                sizeof buf - n,
                "                          EVENT[:N]  Every Nth occurrence of perf event EVENT:\n"
                "                                    "
        );

        for (int i = 0; names[i] != NULL && n < sizeof buf; ++i) {
                char const *sep = (names[i + 1] == NULL) ? " or " : (i > 0) ? ", " : " ";
                int len = strlen(sep) + strlen(names[i]);
                if (col + len > 92) {
                        n += ty_snprintf(buf + n, sizeof buf - n, "%s\n                                    ", (i > 0 && names[i + 1] != NULL) ? "," : "");
                        sep = (names[i + 1] == NULL) ? " or " : " ";
                        col = 37;
                }
                n += ty_snprintf(buf + n, sizeof buf - n, "%s%s", sep, names[i]);
                col += len;
        }

        if (n < sizeof buf) {
                ty_snprintf(buf + n, sizeof buf - n, "\n");
        }

        return buf;
}

void
prof_usage(FILE *out)
{
        fprintf(
                out,
                "Profiling:\n"
                "    --prof[=MODE]       Run the program under the sampling profiler, record the profile\n"
                "                        to ty-prof.data and print a summary when it exits. MODE is:\n"
                "                          cpu[:HZ]   On-CPU time of every thread, sampled HZ times per\n"
                "                                     second per thread (default; HZ defaults to 999)\n"
                "                          wall[:HZ]  Wall-clock time, including time spent blocked on\n"
                "                                     I/O, sleeping or waiting for locks\n"
                "                          count[:N]  Every Nth executed bytecode op (default: 97).\n"
                "                                     Deterministic; disables the JIT\n"
                "%s"
                "    --prof-alloc=SIZE   Record an allocation stack once per SIZE bytes allocated\n"
                "                        (default: 512K; off disables allocation sampling)\n"
                "    --prof-jit-stats=off\n"
                "                        Don't count fast and slow paths in JIT-compiled code\n"
                "    --prof-follow       Also profile child processes started by the program. Each one\n"
                "                        records to ty-prof.PID.data and prints no summary\n"
                "    --prof-out=FILE     Record the profile to FILE (default: ty-prof.data). An existing\n"
                "                        FILE is renamed to FILE.old\n"
                "    --prof-summary=FILE Write the summary to FILE (- is stdout, @ is stderr, off prints\n"
                "                        no summary; default: stdout)\n"
                "    --prof-top=N        List at most N functions in the summary (default: 8)\n"
                "    --prof-min-pct=P    Leave functions below P%% self time out of the summary\n"
                "                        (default: 2)\n"
                "    --prof-report [FILE] [--stdio | --tui]\n"
                "                        Browse a recorded profile (default: ty-prof.data)\n"
                "    --prof-diff OLD NEW Compare two recorded profiles\n"
                "    --prof-attach PID [SECONDS]\n"
                "                        Profile a running ty process for SECONDS (default: 10), then\n"
                "                        record and summarize it like a normal run. Accepts --prof=cpu,\n"
                "                        --prof=wall, --prof=EVENT, --prof-out and --prof-summary.\n"
                "                        Set TY_ATTACH=0 in a process's environment to refuse\n"
                "\n"
                "Every --prof-* option implies --prof. While a profiled program runs, Ctrl-C prints a\n"
                "summary of the profile so far, and a second Ctrl-C within 3 seconds exits.\n",
                EventUsage()
        );
}

#ifdef TY_HAVE_USDT
void
prof_usdt_usage(FILE *out)
{
        char exe[1024];
        isize n = readlink("/proc/self/exe", exe, sizeof exe - 1);

        exe[(n > 0) ? n : 0] = '\0';

        fprintf(
                out,
                "USDT probes (provider \"ty\"), for bpftrace, perf, SystemTap and other tracers:\n"
                "    function__entry(file, name, line, depth)\n"
                "    function__return(file, name, line, depth)\n"
                "    gc__start(heap_bytes)\n"
                "    gc__done(heap_before, heap_after, ns)\n"
                "    alloc(bytes, type)\n"
                "    throw(class, file, line)\n"
                "    jit__compile(name, file, line, native_bytes, ns, tier)\n"
                "    jit__decline(name, reason, offset)\n"
                "    jit__deopt(name, offset)\n"
                "    import__start(module, path)\n"
                "    import__done(module, path, ns)\n"
                "    thread__start(id, tid)\n"
                "    thread__stop(id)\n"
                "    sample(kind, ip)          Fires when the profiler takes a sample\n"
                "Strings are passed as pointers (str(argN) in bpftrace). For example, a histogram of GC\n"
                "pauses in microseconds:\n"
                "    sudo bpftrace -p PID -e 'usdt:%s:ty:gc__done { @us = hist(arg2 / 1000) }'\n",
                (exe[0] != '\0') ? exe : "/path/to/ty"
        );
}
#endif

static char const *
OptArg(char const *arg, char const *name)
{
        usize n = strlen(name);

        if (strncmp(arg, name, n) != 0) {
                return NULL;
        }

        if (arg[n] == '=') {
                return arg + n + 1;
        }

        if (arg[n] == '\0') {
                return "";
        }

        return NULL;
}

static bool
SetEvent(char const *spec)
{
        char name[64];
        char const *colon = strchr(spec, ':');
        usize n = (colon != NULL) ? (usize)(colon - spec) : strlen(spec);

        if (n == 0 || n >= sizeof name) {
                return false;
        }

        memcpy(name, spec, n);
        name[n] = '\0';

        char const *event = prof_os_event(name, &EventPeriod);

        if (event == NULL) {
                return false;
        }

        if (colon != NULL && !ParseSize(colon + 1, &EventPeriod)) {
                return false;
        }

        EventName   = event;
        EventSpec   = spec;
        EventPeriod = (EventPeriod == 0) ? 1 : EventPeriod;
        Mode        = PK_EVENT;

        return true;
}

static bool
SetHz(char const *s)
{
        char *end;
        long hz;

        if (*s == '\0') {
                return true;
        }

        if (*s == ':') {
                ++s;
        }

        hz = strtol(s, &end, 10);

        if (end == s || *end != '\0' || hz <= 0) {
                return false;
        }

        ProfileSampleInterval = 1000000000ULL / (u64)hz;

        return true;
}

static bool
SetMode(char const *mode)
{
        if (*mode == '\0') {
                Mode = PK_CPU;
                return true;
        }

        if (*mode >= '0' && *mode <= '9') {
                Mode = PK_CPU;
                return SetHz(mode);
        }

        if (strncmp(mode, "cpu", 3) == 0 && (mode[3] == '\0' || mode[3] == ':')) {
                Mode = PK_CPU;
                return SetHz(mode + 3);
        }

        if (strncmp(mode, "wall", 4) == 0 && (mode[4] == '\0' || mode[4] == ':')) {
                Mode        = PK_WALL;
                UseWallTime = true;
                return SetHz(mode + 4);
        }

        if (strncmp(mode, "count", 5) == 0 && (mode[5] == '\0' || mode[5] == ':')) {
                Mode         = PK_OPS;
                NoJIT        = true;
                ProfCountOps = true;
                return (mode[5] == '\0')
                    || (ParseSize(mode + 6, &OpsEvery) && OpsEvery > 0);
        }

        return SetEvent(mode);
}

static noreturn void
BadValue(char const *arg)
{
        fprintf(stderr, "ty: bad value for %s\n", arg);
        exit(1);
}

static char const *
ProfArg(char const *arg, char const *name)
{
        char const *v = OptArg(arg, name);

        if (v != NULL && *v == '\0') {
                fprintf(stderr, "ty: %s needs a value (%s=...)\n", name, name);
                exit(1);
        }

        return v;
}

int
prof_option(char const *arg)
{
        char const *v;

        if (strncmp(arg, "--prof", 6) != 0) {
                return 0;
        }

        ProfMode = true;

        if ((v = OptArg(arg, "--prof")) != NULL) {
                if (!SetMode(v)) {
                        BadValue(arg);
                }
        } else if ((v = ProfArg(arg, "--prof-alloc")) != NULL) {
                if (strcmp(v, "off") == 0) {
                        AllocEvery = 0;
                } else if (!ParseSize(v, &AllocEvery) || AllocEvery == 0) {
                        BadValue(arg);
                }
        } else if ((v = ProfArg(arg, "--prof-jit-stats")) != NULL) {
                if (strcmp(v, "on") != 0 && strcmp(v, "off") != 0) {
                        BadValue(arg);
                }
                JitCounts = (strcmp(v, "on") == 0);
        } else if (strcmp(arg, "--prof-follow") == 0) {
                FollowChildren = true;
        } else if ((v = ProfArg(arg, "--prof-out")) != NULL) {
                DataPath = v;
        } else if ((v = ProfArg(arg, "--prof-summary")) != NULL) {
                if (strcmp(v, "off") == 0) {
                        Quiet = true;
                } else if (strcmp(v, "-") == 0) {
                        ProfileOut = stdout;
                } else if (strcmp(v, "@") == 0) {
                        ProfileOut = stderr;
                } else if ((ProfileOut = fopen(v, "w")) == NULL) {
                        fprintf(stderr, "ty: cannot write %s: %s\n", v, strerror(errno));
                        exit(1);
                }
        } else if ((v = ProfArg(arg, "--prof-top")) != NULL) {
                TopN = atoi(v);
                TopN = (TopN < 1) ? 1 : TopN;
        } else if ((v = ProfArg(arg, "--prof-min-pct")) != NULL) {
                MinPct = atof(v);
        } else {
                return 0;
        }

        return 1;
}

static bool
ColorFor(FILE *f)
{
        switch (ColorMode) {
        case TY_COLOR_ALWAYS: return true;
        case TY_COLOR_NEVER:  return false;
        default:              return isatty(fileno(f));
        }
}

static bool
ColorOption(char const *arg)
{
        char const *v = OptArg(arg, "--color");

        if (v == NULL || *v == '\0') {
                return false;
        }

        if (strcmp(v, "always") == 0) {
                ColorMode = TY_COLOR_ALWAYS;
        } else if (strcmp(v, "never") == 0) {
                ColorMode = TY_COLOR_NEVER;
        } else {
                ColorMode = TY_COLOR_AUTO;
        }

        return true;
}

void
prof_setup(void)
{
        ProfMode = ProfMode || (getenv("TY_PROF_FOLLOW") != NULL);

        if (ProfMode) {
                ProfileOut   = (ProfileOut != NULL) ? ProfileOut : stdout;
                ColorProfile = ColorFor(ProfileOut);
                JitStatsOn   = JitCounts;
        }
}

static u32
InternName(char const *name)
{
        for (usize i = SYM_FIRST; i < vN(SymNames); ++i) {
                if (strcmp(v__(SymNames, i), name) == 0) {
                        return i;
                }
        }

        xvP(SymNames, strdup(name));

        return vN(SymNames) - 1;
}

static u32
ResolveRip(uptr rip)
{
        if (rip == 0) {
                return SYM_NONE;
        }

        if (rip >= ExeLo && rip < ExeHi) {
                usize lo = 0;
                usize hi = NSyms;
                while (lo < hi) {
                        usize mid = lo + (hi - lo) / 2;
                        if (Syms[mid].lo <= rip) {
                                lo = mid + 1;
                        } else {
                                hi = mid;
                        }
                }
                if (lo > 0 && rip < Syms[lo - 1].hi) {
                        return InternName(Syms[lo - 1].name);
                }
                return InternName("[ty]");
        }

        if (RipCache.n * 2 >= RipCache.cap) {
                u32 cap = (RipCache.cap == 0) ? 1024 : RipCache.cap * 2;
                uptr *rips = calloc(cap, sizeof *rips);
                u32 *ids = calloc(cap, sizeof *ids);
                for (u32 i = 0; i < RipCache.cap; ++i) {
                        if (RipCache.rip[i] != 0) {
                                u32 j = Mix(0, RipCache.rip[i]) & (cap - 1);
                                while (rips[j] != 0) {
                                        j = (j + 1) & (cap - 1);
                                }
                                rips[j] = RipCache.rip[i];
                                ids[j] = RipCache.id[i];
                        }
                }
                free(RipCache.rip);
                free(RipCache.id);
                RipCache.rip = rips;
                RipCache.id = ids;
                RipCache.cap = cap;
        }

        u32 j = Mix(0, rip) & (RipCache.cap - 1);

        while (RipCache.rip[j] != 0) {
                if (RipCache.rip[j] == rip) {
                        return RipCache.id[j];
                }
                j = (j + 1) & (RipCache.cap - 1);
        }

        Dl_info dl;
        u32 id;

        if (dladdr((void *)rip, &dl) == 0 || dl.dli_fname == NULL) {
                id = SYM_JIT;
        } else if (dl.dli_sname != NULL) {
                id = InternName(dl.dli_sname);
        } else {
                char const *base = strrchr(dl.dli_fname, '/');
                char buf[256];
                ty_snprintf(buf, sizeof buf, "[%s]", (base != NULL) ? base + 1 : dl.dli_fname);
                id = InternName(buf);
        }

        RipCache.rip[j] = rip;
        RipCache.id[j] = id;
        RipCache.n += 1;

        return id;
}

static char const *
JitIP(Frame const *frame, uptr rip, bool leaf)
{
        Value const *f = &frame->f;
        char const *entry = (frame->jit_code != NULL) ? frame->jit_code : jit_of(f);
        char const *bc = code_of(f);

        if (entry == NULL || jit_pending(entry)) {
                return bc + 1;
        }

        LirImage const *img = (void const *)(entry - sizeof *img);
        LirSite const *sites = (void const *)(entry + img->table);
        uptr pc;
        bool late;

        if (leaf && rip >= (uptr)entry && rip < (uptr)entry + img->size) {
                pc = rip - (uptr)entry;
                late = true;
        } else if (frame->jit_pc != NULL) {
                pc = *frame->jit_pc - (uptr)entry;
                late = false;
        } else if (frame->jit_resume > 0 && frame->jit_resume <= (i32)img->nresume) {
                u32 const *resumes = (void const *)(sites + img->nsites);
                return bc + resumes[frame->jit_resume - 1];
        } else {
                return bc + 1;
        }

        i64 best  = -1;
        u32 tag   = 1;
        i64 first = INT64_MAX;
        u32 head  = 0;

        for (u32 i = 0; i < img->nsites; ++i) {
                i64 spc = sites[i].pc;
                if (sites[i].tag != 0 && spc < first) {
                        first = spc;
                        head  = sites[i].tag;
                }
                if (spc > (i64)pc) {
                        continue;
                }
                if (spc > best || (late && spc == best)) {
                        best = spc;
                        tag = sites[i].tag;
                }
        }

        if (best >= 0 && tag != 0) {
                return bc + tag;
        }

        if (frame->jit_resume > 0 && frame->jit_resume <= (i32)img->nresume) {
                u32 const *resumes = (void const *)(sites + img->nsites);
                return bc + resumes[frame->jit_resume - 1];
        }

        return bc + ((head == 0) ? 1 : head);
}

static char const *
CoUp(co_state *st)
{
        if (
                (vN(st->frames) == 0)
             || (vN(st->stack) == 0)
             || (vv(st->stack)->type != VALUE_GENERATOR)
        ) {
                return NULL;
        }

        Generator *gen = vv(st->stack)->gen;
        *st = *gen->st;

        return gen->ip;
}

static int
Walk(Ty *ty, uptr rip, u64 *out, u64 *mask)
{
        co_state st = *ty->st;
        char const *ip = ty->ip;
        char const *up;
        bool leaf = true;
        int n = 0;

        *mask = 0;

        while (ip != NULL && n < MAX_FRAMES) {
                Frame const *frame = (vN(st.frames) > 0) ? vvL(st.frames) : NULL;

                if (ip == &JIT) {
                        if (frame == NULL) {
                                break;
                        }
                        ip = JitIP(frame, rip, leaf);
                        if (n < 64) {
                                *mask |= 1ULL << n;
                        }
                } else if (frame != NULL && frame->jit_resume > 0) {
                        ip = JitIP(frame, 0, false);
                }

                out[n++] = (uptr)ip;
                leaf = false;

                if (vN(st.frames) == 1 && (up = CoUp(&st)) != NULL) {
                        ip = up;
                        continue;
                }

                if (vN(st.frames) == 0) {
                        break;
                }

                ip = v__(st.frames, --vN(st.frames)).ip;
        }

        return n;
}

inline static void
RingPut(Ring *r, u64 at, u64 w)
{
        r->buf[at & r->mask] = w;
}

static void
Record(ProfThread *pt, Ring *r, int kind, int state, u64 weight, uptr rip, u64 aux, u64 now)
{
        u64 frames[MAX_FRAMES];
        u64 mask;

        if (r->buf == NULL) {
                return;
        }

        int n = Walk(pt->ty, rip, frames, &mask);
        u64 need = HDR_WORDS + n;
        u64 head = atomic_load_explicit(&r->head, memory_order_relaxed);
        u64 tail = atomic_load_explicit(&r->tail, memory_order_acquire);

        if (head - tail + need > r->mask + 1) {
                atomic_fetch_add_explicit(&Dropped, 1, memory_order_relaxed);
                return;
        }

        RingPut(r, head + 0, (u64)n | ((u64)kind << 16) | ((u64)state << 24) | ((u64)pt->slot << 32));
        RingPut(r, head + 1, weight);
        RingPut(r, head + 2, now);
        RingPut(r, head + 3, (rip != 0) ? rip : aux);
        RingPut(r, head + 4, mask);

        for (int i = 0; i < n; ++i) {
                RingPut(r, head + HDR_WORDS + i, frames[i]);
        }

        atomic_store_explicit(&r->head, head + need, memory_order_release);
}

inline static int
StateOf(ProfThread *pt)
{
        int s = *pt->state;

        if (s == PS_RUN && !pt->ty->locked) {
                s = PS_BLOCKED;
        }

        if (s == PS_RUN && GetCompilerContext(pt->ty) != NULL) {
                s = PS_COMPILE;
        }

        return s;
}

static void
Sample(ProfThread *pt, uptr rip, u64 weight)
{
        u64 t0 = NowNs();

        if (!atomic_load_explicit(&Running, memory_order_relaxed)) {
                return;
        }

        if (pt->busy) {
                atomic_fetch_add_explicit(&Busy, 1, memory_order_relaxed);
                return;
        }

        pt->busy = 1;
        atomic_signal_fence(memory_order_seq_cst);

        Record(pt, &pt->ring[0], Mode, StateOf(pt), weight, rip, 0, t0);
        TY_PROBE_IF(sample, Mode, rip);

        atomic_signal_fence(memory_order_seq_cst);
        pt->busy = 0;

        atomic_fetch_add_explicit(&HandlerNs, NowNs() - t0, memory_order_relaxed);
}

static void
OnSample(int sig, siginfo_t *si, void *uc)
{
        ProfThread *pt = MyProf;
        int saved = errno;

        if (pt == NULL) {
                errno = saved;
                return;
        }

        u64 weight = (Mode == PK_EVENT) ? EventPeriod
                   : (Mode == PK_CPU)   ? prof_os_weight(pt, Period)
                   :                      Period;

        Sample(pt, prof_os_context_pc(uc), weight);
        prof_os_sampled(pt);

        errno = saved;
}

static void
Synchronous(int kind, u64 weight, u64 aux)
{
        ProfThread *pt = MyProf;

        if (pt == NULL || pt->busy || !atomic_load_explicit(&Running, memory_order_relaxed)) {
                return;
        }

        pt->busy = 1;
        atomic_signal_fence(memory_order_seq_cst);

        Record(pt, &pt->ring[0], kind, StateOf(pt), weight, 0, aux, NowNs());

        atomic_signal_fence(memory_order_seq_cst);
        pt->busy = 0;
}

void
prof_alloc_slow(Ty *ty, usize n, int type)
{
        if (AllocEvery == 0 || MyProf == NULL || MyProf->ty != ty) {
                ProfAllocLeft = INT64_MAX;
                return;
        }

        u64 k = 0;

        while (ProfAllocLeft < 0) {
                ProfAllocLeft += AllocEvery;
                k += 1;
        }

        u64 seq = atomic_fetch_add_explicit(&AllocSeq, 1, memory_order_relaxed) + 1;

        Synchronous(PK_ALLOC, k * AllocEvery, (u64)type | (seq << 8));

        ProfPending = (type != GC_ANY) ? seq : 0;
}

void
prof_ops_slow(Ty *ty, char const *ip)
{
        if (Mode != PK_OPS || MyProf == NULL || MyProf->ty != ty) {
                ProfOpsLeft = INT64_MAX;
                return;
        }

        ProfOpsLeft = OpsEvery - 1;
        Synchronous(PK_OPS, OpsEvery, 0);
}

void
prof_throw(Ty *ty, char const *ip)
{
        Value const *exc = &ty->exc;
        u64 cls = (exc->type == VALUE_OBJECT) ? (u64)exc->class : (u64)(1ULL << 31) | exc->type;

        Synchronous(PK_THROW, 1, cls);
}

static Expr const *
FunExpr(Value const *f)
{
        return from_eval(f) ? NULL : expr_of(f);
}

void
prof_jit_decline(Value const *f, char const *why, i32 off)
{
        if (!Started) {
                return;
        }

        TySpinLockLock(&JitLock);
        xvP(Declines, ((JitDecline) {
                .expr = FunExpr(f),
                .why  = strdup(why),
                .off  = off,
                .code = code_of(f)
        }));
        TySpinLockUnlock(&JitLock);
}

static void
DeoptNote(DeoptSite *d, char const *text)
{
        int slot = 0;
        u64 low  = UINT64_MAX;

        for (int i = 0; i < DEOPT_NOTES; ++i) {
                if (d->notes[i].n > 0 && strcmp(d->notes[i].text, text) == 0) {
                        d->notes[i].n += 1;
                        return;
                }
                if (d->notes[i].n < low) {
                        low  = d->notes[i].n;
                        slot = i;
                }
        }

        ty_snprintf(d->notes[slot].text, sizeof d->notes[slot].text, "%s", text);
        d->notes[slot].n = 1;
}

static char const *
SlotName(Expr const *fe, int slot)
{
        if (
                (fe == NULL)
             || (fe->fn->scope == NULL)
             || (slot < 0)
             || (slot >= vN(fe->fn->scope->owned))
             || (v__(fe->fn->scope->owned, slot) == NULL)
        ) {
                return NULL;
        }

        return v__(fe->fn->scope->owned, slot)->identifier;
}

static void
DeoptNotes(Ty *ty, Frame const *frame, DeoptSite *d, i32 why, u64 slots)
{
        Expr const *fe = FunExpr(&frame->f);
        char text[96];
        bool any = false;

        for (int i = 0; i < 4; ++i) {
                u32 e = (slots >> (16 * i)) & 0xFFFF;
                int slot = (int)(e & 0x7FFF) - 1;
                bool real = (e & 0x8000) != 0;

                if (slot < 0 || frame->fp + slot >= vN(STACK)) {
                        continue;
                }

                Value const *v = v_(STACK, frame->fp + slot);
                int want = real ? CLASS_FLOAT : CLASS_INT;

                if (ClassOf(v) == want) {
                        continue;
                }

                char const *name = SlotName(fe, slot);

                ty_snprintf(
                        text,
                        sizeof text,
                        "%s: %s → %s",
                        (name != NULL) ? name : "?",
                        real ? "Float" : "Int",
                        class_name(ty, ClassOf(v))
                );

                DeoptNote(d, text);
                any = true;
        }

        if (!any && d->off >= 0) {
                char const *op = GetInstructionName((u8)d->code[d->off]);
                char lower[64];
                int n = 0;

                if (strncmp(op, "INSTR_", 6) == 0) {
                        op += 6;
                }

                for (; op[n] != '\0' && n < (int)sizeof lower - 1; ++n) {
                        lower[n] = (op[n] == '_') ? ' ' : (char)tolower((u8)op[n]);
                }

                lower[n] = '\0';

                ty_snprintf(text, sizeof text, "at %s", lower);
                DeoptNote(d, text);
        }
}

static void
JsonStr(FILE *f, char const *s);

static char const *
GuardText(u32 guard)
{
        char const *text = jit_guard_text(guard);
        return (text != NULL) ? text : "";
}

static int
Brief(Ty *ty, Value const *v, char *out, int cap, int depth)
{
        Value x = *v;
        char *s = NULL;
        int n = 0;

        for (int i = 0; i < 64 && x.type == VALUE_REF && x.ref != NULL; ++i) {
                x = *x.ref;
        }

        if (cap <= 4) {
                return 0;
        }

        if (x.type == VALUE_OBJECT && depth == 0 && x.object->nslot > 0) {
                Class const *class = x.object->class;
                n += ty_snprintf(out + n, cap - n, "%s{", class_name(ty, x.class));
                for (u32 i = 0; i < x.object->nslot && i < vN(class->fields.ids) && n < cap - 8; ++i) {
                        n += ty_snprintf(out + n, cap - n, "%s%s: ", (i > 0) ? ", " : "", M_NAME(v__(class->fields.ids, i)));
                        if (n < cap - 8) {
                                n += Brief(ty, &x.object->slots[i], out + n, cap - n - 4, depth + 1);
                        }
                }
                n = min(n, cap - 2);
                out[n++] = '}';
                out[n] = '\0';
                return n;
        }

        if (TY_CATCH_ERROR()) {
                (void)TY_CATCH();
                s = NULL;
        } else {
                s = value_show(ty, &x, TY_SHOW_BASIC | TY_SHOW_REPR | TY_SHOW_ABBREV);
                TY_CATCH_END();
        }

        for (char const *p = (s != NULL) ? s : "<unprintable>"; *p != '\0'; ++p) {
                if (*p == '\x1b') {
                        while (p[1] != '\0' && *p != 'm') {
                                p += 1;
                        }
                        continue;
                }
                if (n >= cap - 4) {
                        memcpy(out + n, "...", 3);
                        n += 3;
                        break;
                }
                out[n++] = *p;
        }

        out[n] = '\0';

        if (s != NULL) {
                ty_free(s);
        }

        return n;
}

static void
ShotValue(Ty *ty, FILE *f, char const *name, char const *where, Value const *v)
{
        Value x = *v;
        char text[192];

        for (int i = 0; i < 64 && x.type == VALUE_REF && x.ref != NULL; ++i) {
                x = *x.ref;
        }

        fputc('[', f);
        JsonStr(f, name);
        fputc(',', f);

        if (x.type == VALUE_UNINITIALIZED || x.type == VALUE_ZERO) {
                fputs("\"\",\"<unset>\",", f);
        } else {
                Brief(ty, &x, text, sizeof text, 0);
                JsonStr(f, (x.type == VALUE_NIL) ? "nil" : class_name(ty, ClassOf(&x)));
                fputc(',', f);
                JsonStr(f, text);
                fputc(',', f);
        }

        JsonStr(f, where);
        fputc(']', f);
}

static char *
ShotVars(Ty *ty, Frame const *frame)
{
        Expr const *fe = FunExpr(&frame->f);
        i32 bound = frame->f.info[FUN_INFO_BOUND];
        usize top = vN(STACK);
        char *out = NULL;
        size_t len = 0;
        FILE *f = open_memstream(&out, &len);
        bool first = true;
        char name[32];

        if (f == NULL) {
                return NULL;
        }

        fputc('[', f);

        for (i32 slot = 0; slot < bound && slot < 32 && frame->fp + slot < top; ++slot) {
                char const *id = SlotName(fe, slot);
                if (id == NULL) {
                        ty_snprintf(name, sizeof name, "$%d", slot);
                        id = name;
                }
                if (!first) {
                        fputc(',', f);
                }
                ShotValue(ty, f, id, "local", v_(STACK, frame->fp + slot));
                first = false;
        }

        usize base = frame->fp + (usize)max(bound, 0);

        for (usize i = top, k = 0; i > base && k < 6; --i, ++k) {
                ty_snprintf(name, sizeof name, (k == 0) ? "top" : "top-%zu", k);
                if (!first) {
                        fputc(',', f);
                }
                ShotValue(ty, f, name, "stack", v_(STACK, i - 1));
                first = false;
        }

        fputc(']', f);
        fclose(f);

        return out;
}

void
prof_jit_deopt(Ty *ty, Frame const *frame, i32 off)
{
        i32 why   = ty->jit_why;
        u64 slots = ty->jit_why_slots;
        u32 guard = ty->jit_guard;

        ty->jit_why       = JIT_WHY_UNKNOWN;
        ty->jit_why_slots = 0;
        ty->jit_guard     = 0;

        if (!Started) {
                return;
        }

        Value const *f = &frame->f;
        Expr const *e = FunExpr(f);
        u64 now = NowNs() - StartWall;
        u64 ips[MAX_FRAMES];
        u64 mask;
        int nips = Walk(ty, 0, ips, &mask);
        u64 hash = 0;
        isize at = -1;
        isize shot = -1;

        if (nips > 0) {
                ips[0] = (uptr)(code_of(f) + off);
        }

        for (int i = 0; i < nips && i < SHOT_FRAMES; ++i) {
                hash = Mix(hash, ips[i]);
        }

        TySpinLockLock(&JitLock);

        for (usize i = 0; i < vN(Deopts); ++i) {
                DeoptSite *d = v_(Deopts, i);
                if (
                        (d->expr == e)
                     && (d->off == off)
                     && (d->code == code_of(f))
                     && (d->why == why)
                     && ((d->guard == guard) || (strcmp(GuardText(d->guard), GuardText(guard)) == 0))
                ) {
                        at = (isize)i;
                        break;
                }
        }

        if (at < 0) {
                xvP(
                        Deopts,
                        ((DeoptSite) {
                                .expr  = e,
                                .code  = code_of(f),
                                .off   = off,
                                .why   = why,
                                .guard = guard,
                                .first = now
                        })
                );
                at = (isize)vN(Deopts) - 1;
        }

        DeoptSite *site = v_(Deopts, at);

        site->n   += 1;
        site->last = now;

        DeoptNotes(ty, frame, site, why, slots);

        if (site->nshots < DEOPT_SHOTS) {
                DeoptShot *s = &site->shots[site->nshots];
                shot = site->nshots++;
                s->t       = now;
                s->hash    = hash;
                s->count   = 1;
                s->nframes = (u32)min(nips, SHOT_FRAMES);
                s->vars    = NULL;
                memcpy(s->ips, ips, s->nframes * sizeof ips[0]);
        }

        TySpinLockUnlock(&JitLock);

        if (shot < 0) {
                return;
        }

        char *vars = ShotVars(ty, frame);

        TySpinLockLock(&JitLock);

        site = v_(Deopts, at);

        for (isize k = 0; k < shot; ++k) {
                DeoptShot *s = &site->shots[k];
                if (
                        (s->hash == hash)
                     && (s->vars != NULL)
                     && (vars != NULL)
                     && (strcmp(s->vars, vars) == 0)
                     && (shot == (isize)site->nshots - 1)
                ) {
                        s->count += 1;
                        site->nshots -= 1;
                        free(vars);
                        vars = NULL;
                        break;
                }
        }

        if (vars != NULL) {
                site->shots[shot].vars = vars;
        }

        TySpinLockUnlock(&JitLock);
}

void
prof_jit_despecialize(Value const *f, u32 deopts)
{
        if (!Started) {
                return;
        }

        TySpinLockLock(&JitLock);
        xvP(Despecs, ((Despec) { .expr = FunExpr(f), .at = NowNs() - StartWall, .deopts = deopts }));
        TySpinLockUnlock(&JitLock);
}

static void
LoadExeSymbols(void)
{
        static atomic_bool once;

        if (atomic_exchange(&once, true)) {
                return;
        }

        Syms = prof_os_exe_symbols(&NSyms);

        if (NSyms > 0) {
                ExeLo = Syms[0].lo;
                ExeHi = Syms[NSyms - 1].hi;
        }
}

char const *
prof_symbolize(uptr addr)
{
        if (Syms == NULL) {
                LoadExeSymbols();
        }

        if (addr >= ExeLo && addr < ExeHi) {
                usize lo = 0;
                usize hi = NSyms;
                while (lo < hi) {
                        usize mid = lo + (hi - lo) / 2;
                        if (Syms[mid].lo < addr) {
                                lo = mid + 1;
                        } else {
                                hi = mid;
                        }
                }
                return (lo < NSyms && Syms[lo].lo == addr) ? Syms[lo].name : NULL;
        }

        Dl_info dl;

        if (dladdr((void *)addr, &dl) != 0 && dl.dli_sname != NULL && (uptr)dl.dli_saddr == addr) {
                return dl.dli_sname;
        }

        return NULL;
}

char const *
prof_jit_ip(Ty *ty, void const *ra)
{
        if (ty->st == NULL || vN(ty->st->frames) == 0) {
                return NULL;
        }

        return JitIP(vvL(ty->st->frames), (uptr)ra - 1, true);
}

static void
RingInit(Ring *r)
{
        r->buf = mmap(
                NULL,
                RING_WORDS * sizeof (u64),
                PROT_READ | PROT_WRITE,
                MAP_PRIVATE | MAP_ANON,
                -1,
                0
        );
        r->mask = RING_WORDS - 1;
        atomic_init(&r->head, 0);
        atomic_init(&r->tail, 0);
}

void
prof_thread_start(Ty *ty)
{
        if (MyProf != NULL) {
                return;
        }

        u32 slot = atomic_fetch_add(&NThreads, 1);

        if (slot >= MAX_THREADS) {
                return;
        }

        ProfThread *pt = calloc(1, sizeof *pt);

        pt->ty = ty;
        pt->tid = prof_os_tid();
        pt->self = pthread_self();
        pt->slot = slot;
        pt->state = &ProfState;

        pthread_mutex_lock(&ThreadsLock);

        if (Started) {
                RingInit(&pt->ring[0]);
                RingInit(&pt->ring[1]);
        }

        pthread_getname_np(pthread_self(), pt->name, sizeof pt->name);

        atomic_store(&pt->live, true);
        Threads[slot] = pt;
        MyProf = pt;

        if (ProfMode) {
                ProfAllocLeft = (AllocEvery > 0) ? (i64)AllocEvery / 2 + (i64)(random() % AllocEvery) : INT64_MAX;
                ProfOpsLeft   = (Mode == PK_OPS) ? (i64)OpsEvery - 1 : INT64_MAX;
        }

        if (atomic_load(&Running)) {
                prof_os_arm(pt, Mode, (Mode == PK_EVENT) ? EventPeriod : Period);
        }

        pthread_mutex_unlock(&ThreadsLock);

        TY_PROBE_IF(thread__start, (long)ty->id, (long)pt->tid);
}

void
prof_thread_stop(Ty *ty)
{
        ProfThread *pt = MyProf;

        TY_PROBE_IF(thread__stop, (long)ty->id);

        if (pt == NULL || pt->ty != ty) {
                return;
        }

        pthread_getname_np(pthread_self(), pt->name, sizeof pt->name);

        pthread_mutex_lock(&ThreadsLock);
        prof_os_disarm(pt);
        atomic_store(&pt->live, false);
        pthread_mutex_unlock(&ThreadsLock);
        MyProf = NULL;
}

static u32
Insert(u8 kind, u8 state, u32 sym, u32 thread, u64 mask, u64 const *frames, u16 n, u64 weight, u64 t)
{
        u64 h = Mix(Mix(Mix(kind | ((u64)state << 8) | ((u64)thread << 16), sym), mask), n);

        for (u16 i = 0; i < n; ++i) {
                h = Mix(h, frames[i]);
        }

        if ((vN(Stacks) + 1) * 2 >= TableCap) {
                u32 cap = (TableCap == 0) ? 4096 : TableCap * 2;
                u32 *table = malloc(cap * sizeof *table);
                memset(table, 0xFF, cap * sizeof *table);
                for (u32 i = 0; i < vN(Stacks); ++i) {
                        u32 j = v_(Stacks, i)->hash & (cap - 1);
                        while (table[j] != UINT32_MAX) {
                                j = (j + 1) & (cap - 1);
                        }
                        table[j] = i;
                }
                free(Table);
                Table = table;
                TableCap = cap;
        }

        u32 j = h & (TableCap - 1);
        u32 id;

        for (;;) {
                id = Table[j];
                if (id == UINT32_MAX) {
                        break;
                }
                Stack *s = v_(Stacks, id);
                if (
                        (s->hash == h)
                     && (s->kind == kind)
                     && (s->state == state)
                     && (s->sym == sym)
                     && (s->thread == thread)
                     && (s->mask == mask)
                     && (s->n == n)
                     && (memcmp(v_(Keys, s->off), frames, n * sizeof *frames) == 0)
                ) {
                        s->count += 1;
                        s->weight += weight;
                        goto Tick;
                }
                j = (j + 1) & (TableCap - 1);
        }

        id = vN(Stacks);
        Table[j] = id;

        xvP(Stacks, ((Stack) {
                .off    = vN(Keys),
                .n      = n,
                .kind   = kind,
                .state  = state,
                .sym    = sym,
                .thread = thread,
                .mask   = mask,
                .hash   = h,
                .count  = 1,
                .weight = weight
        }));

        xvPn(Keys, frames, n);

Tick:
        if (kind > PK_OPS) {
                return id;
        }

        if (Timeline.n == Timeline.cap) {
                Timeline.cap = (Timeline.cap == 0) ? 65536 : Timeline.cap * 2;
                Timeline.t = realloc(Timeline.t, Timeline.cap * sizeof *Timeline.t);
                Timeline.s = realloc(Timeline.s, Timeline.cap * sizeof *Timeline.s);
        }

        Timeline.t[Timeline.n] = t;
        Timeline.s[Timeline.n] = id;
        Timeline.n += 1;

        return id;
}

static void
DrainRing(Ring *r)
{
        u64 tail = atomic_load_explicit(&r->tail, memory_order_relaxed);
        u64 head = atomic_load_explicit(&r->head, memory_order_acquire);
        u64 frames[MAX_FRAMES];

        while (tail < head) {
                u64 hdr    = r->buf[tail & r->mask];
                u16 n      = hdr & 0xFFFF;
                u8  kind   = (hdr >> 16) & 0xFF;
                u8  state  = (hdr >> 24) & 0xFF;
                u32 thread = hdr >> 32;
                u64 weight = r->buf[(tail + 1) & r->mask];
                u64 t      = r->buf[(tail + 2) & r->mask];
                u64 rip    = r->buf[(tail + 3) & r->mask];
                u64 mask   = r->buf[(tail + 4) & r->mask];

                for (u16 i = 0; i < n && i < MAX_FRAMES; ++i) {
                        frames[i] = r->buf[(tail + HDR_WORDS + i) & r->mask];
                }

                u32 sym = (kind == PK_THROW) ? (u32)rip
                        : (kind == PK_ALLOC) ? (u32)(rip & 0xFF)
                        : ResolveRip(rip);

                if (sym == SYM_JIT && (kind == PK_CPU || kind == PK_EVENT || kind == PK_WALL)) {
                        jit_code_hit(rip);
                }

                u32 id = Insert(kind, state, sym, thread, mask, frames, n, weight, t);

                if (kind == PK_ALLOC) {
                        u64 seq = rip >> 8;
                        while (vN(SeqStack) <= seq) {
                                xvP(SeqStack, UINT32_MAX);
                        }
                        *v_(SeqStack, seq) = id;
                }

                tail += HDR_WORDS + n;
        }

        atomic_store_explicit(&r->tail, tail, memory_order_release);
}

static void
DrainAll(void)
{
        pthread_mutex_lock(&DrainLock);

        u32 n = atomic_load(&NThreads);

        for (u32 i = 0; i < n && i < MAX_THREADS; ++i) {
                ProfThread *pt = Threads[i];
                if (pt != NULL) {
                        DrainRing(&pt->ring[0]);
                        DrainRing(&pt->ring[1]);
                }
        }

        pthread_mutex_unlock(&DrainLock);
}

static void *
DrainLoop(void *_)
{
        while (!atomic_load(&Stopping)) {
                struct timespec ts = { 0, 20 * 1000000 };
                nanosleep(&ts, NULL);
                DrainAll();
        }

        return NULL;
}

static void *
WallLoop(void *_)
{
        u64 next = NowNs();

        while (!atomic_load(&Stopping)) {
                next += Period;
                prof_os_sleep_until(next);

                if (!atomic_load(&Running)) {
                        continue;
                }

                u32 n = atomic_load(&NThreads);

                pthread_mutex_lock(&ThreadsLock);

                for (u32 i = 0; i < n && i < MAX_THREADS; ++i) {
                        ProfThread *pt = Threads[i];

                        if (pt == NULL || !atomic_load(&pt->live)) {
                                continue;
                        }

                        if (pt->ty->locked || !TySpinLockTryLock(pt->ty->lock)) {
                                prof_os_kick(pt, Period);
                                continue;
                        }

                        if (!pt->ty->locked && atomic_load(&pt->live)) {
                                int s = *pt->state;
                                u64 t0 = NowNs();
                                Record(pt, &pt->ring[1], PK_WALL, (s == PS_RUN) ? PS_BLOCKED : s, Period, 0, 0, t0);
                                atomic_fetch_add_explicit(&HandlerNs, NowNs() - t0, memory_order_relaxed);
                        }

                        TySpinLockUnlock(pt->ty->lock);
                }

                pthread_mutex_unlock(&ThreadsLock);
        }

        return NULL;
}

static void
OnInterrupt(int _)
{
        static u64 last;
        u64 now = NowNs();

        if (last > 0 && now - last < 3000000000ULL) {
                _exit(130);
        }

        last = now;
        atomic_store(&ProfWantReport, true);
}

static void
StartRun(Ty *ty)
{
        static bool once;

        if (ProfileSampleInterval > 0) {
                Hz = 1000000000ULL / ProfileSampleInterval;
        }

        Hz = (Hz == 0) ? 1 : Hz;
        Period = 1000000000ULL / Hz;

        if (!once) {
                once = true;
                TySpinLockInit(&JitLock);
                LoadExeSymbols();
                xvP(SymNames, "(none)");
                xvP(SymNames, "[jit]");
                prof_os_init(OnSample, Sample);
        }

        StartWall = NowNs();
        StartUnix = time(NULL);
        getrusage(RUSAGE_SELF, &StartUsage);

        prof_thread_start(ty);

        pthread_mutex_lock(&ThreadsLock);

        Started = true;
        atomic_store(&Stopping, false);
        VmPoll.prof = ProfMode;

        u32 n = atomic_load(&NThreads);

        for (u32 i = 0; i < n && i < MAX_THREADS; ++i) {
                ProfThread *pt = Threads[i];
                if (pt == NULL || !atomic_load(&pt->live)) {
                        continue;
                }
                if (pt->ring[0].buf == NULL) {
                        RingInit(&pt->ring[0]);
                        RingInit(&pt->ring[1]);
                }
                prof_os_arm(pt, Mode, (Mode == PK_EVENT) ? EventPeriod : Period);
        }

        atomic_store(&Running, true);

        pthread_mutex_unlock(&ThreadsLock);

        HaveDrainThread = pthread_create(&DrainThread, NULL, DrainLoop, NULL) == 0;

        if (Mode == PK_WALL) {
                HaveWallThread = pthread_create(&WallThread, NULL, WallLoop, NULL) == 0;
        }
}

void
prof_start(Ty *ty)
{
        if (Started) {
                return;
        }

        char const *parent = getenv("TY_PROF_ACTIVE");

        FollowChildren = FollowChildren || (getenv("TY_PROF_FOLLOW") != NULL);

        if (parent != NULL && !FollowChildren) {
                return;
        }

        if (parent != NULL) {
                static char path[64];
                ty_snprintf(path, sizeof path, "ty-prof.%d.data", (int)getpid());
                DataPath = path;
                Quiet = true;
        }

        setenv("TY_PROF_ACTIVE", "1", 1);

        if (FollowChildren) {
                setenv("TY_PROF_FOLLOW", "1", 1);
        }

        if (ProfileOut == NULL) {
                ProfileOut = stdout;
        }

        signal(SIGINT, OnInterrupt);

        StartRun(ty);
}

static void
StopSampling(void)
{
        atomic_store(&Running, false);

        u32 n = atomic_load(&NThreads);

        for (u32 i = 0; i < n && i < MAX_THREADS; ++i) {
                if (Threads[i] != NULL) {
                        prof_os_disarm(Threads[i]);
                }
        }

        atomic_store(&Stopping, true);

        if (HaveWallThread) {
                pthread_join(WallThread, NULL);
                HaveWallThread = false;
        }

        if (HaveDrainThread) {
                pthread_join(DrainThread, NULL);
                HaveDrainThread = false;
        }

        StopWall = NowNs();

        DrainAll();
}

/* ------------------------------------------------------------------------ */

typedef struct {
        Expr const *fexpr;
        Module const *mod;
        char *name;
        char const *path;
        u32 line0;
        u32 line1;
        u64 self;
        u64 total;
        u64 cself;
        u64 ctotal;
        u64 jit_self;
        u64 jit_total;
        u64 interp_self;
        u64 native_self;
        u64 gc_total;
        u64 alloc_self;
        u64 alloc_total;
        u64 throws;
        u64 calls;
        bool lib;
        u32 stamp;
        int compiles;
        bool tier2;
        usize native_size;
        u64 compile_ns;
        char const *decline;
        i32 decline_line;
        u64 deopts;
        i32 deopt_line;
        u64 deopt_top;
} Func;

typedef struct {
        Module const *mod;
        u32 line;
        u32 func;
        u64 self;
        u64 total;
        u64 cself;
        u64 jit_self;
        u64 native_self;
        u64 alloc;
        u64 alloc_by[GC_ANY + 1];
        u64 throws;
        u64 cat[CAT_COUNT];
        u64 ucat[CAT_COUNT];
        u64 ualloc;
        u64 ualloc_by[GC_ANY + 1];
        u64 slow;
        u64 retained;
        u64 retained_objs;
        u64 retained_by[GC_ANY + 1];
        char *slow_desc;
        int slow_classes;
        u32 stamp;
        Expr const *expr;
} Line;

typedef struct {
        u64 ip;
        u32 func;
        u32 line;
} Site;

typedef struct {
        u32 from;
        u32 to;
        u64 w;
} Edge;

static struct {
        Ty *ty;
        vec(Func) funcs;
        vec(Line) lines;
        vec(Site) sites;
        vec(Edge) edges;
        u32 *site_tab;
        u32 site_cap;
        u32 *line_tab;
        u32 line_cap;
        u32 *edge_tab;
        u32 edge_cap;
        u64 total;
        u64 count;
        u64 cat[CAT_COUNT];
        u64 ccat[CAT_COUNT];
        u64 alloc_total;
        u64 alloc_by[GC_ANY + 1];
        u64 retained;
        u64 retained_by[GC_ANY + 1];
        bool retained_exact;
        u64 throws;
        u64 *sym_self;
        u64 *thread_total;
        int time_kind;
        u32 stamp;
        char cwd[4096];
} M;

static char const *
DisplayPath(char const *path)
{
        usize cl = strlen(M.cwd);
        char const *home = dirs_get(DIR_HOME);
        usize hl = (home != NULL) ? strlen(home) : 0;

        if (cl > 0 && strncmp(path, M.cwd, cl) == 0 && path[cl] == '/') {
                return path + cl + 1;
        }

        if (hl > 1 && strncmp(path, home, hl) == 0 && path[hl] == '/') {
                char *p = malloc(strlen(path) - hl + 2);
                p[0] = '~';
                strcpy(p + 1, path + hl);
                return p;
        }

        return path;
}

static u32
FuncOf(Expr const *fexpr, Expr const *expr)
{
        Module const *mod = (fexpr != NULL) ? fexpr->mod : (expr != NULL) ? expr->mod : NULL;
        void const *key = (fexpr != NULL) ? (void const *)fexpr : (void const *)mod;

        for (usize i = 0; i < vN(M.funcs); ++i) {
                Func const *f = v_(M.funcs, i);
                void const *k = (f->fexpr != NULL) ? (void const *)f->fexpr : (void const *)f->mod;
                if (k == key && (f->fexpr != NULL) == (fexpr != NULL)) {
                        return i;
                }
        }

        Func f = {0};
        f.fexpr = fexpr;
        f.mod = mod;
        f.decline_line = -1;
        f.deopt_line = -1;

        f.path = DisplayPath((mod != NULL && mod->path != NULL) ? mod->path : "<unknown>");

        if (fexpr != NULL) {
                char const *qn = QualifiedName(fexpr);
                if (strcmp(qn, "(error)") == 0) {
                        char buf[256];
                        ty_snprintf(
                                buf,
                                sizeof buf,
                                "(%s:%s:%u)",
                                (fexpr->fn->name != NULL) ? fexpr->fn->name : "anon",
                                (mod != NULL && mod->name != NULL) ? mod->name : "?",
                                LocLine(fexpr->start) + 1
                        );
                        qn = buf;
                }
                f.name = strdup(qn);
                f.line0 = LocLine(fexpr->start);
                f.line1 = LocLine(fexpr->end);
                if (mod != NULL && mod->name != NULL) {
                        usize ml = strlen(mod->name);
                        if (strncmp(f.name, mod->name, ml) == 0 && f.name[ml] == '.') {
                                memmove(f.name, f.name + ml + 1, strlen(f.name + ml + 1) + 1);
                        }
                }
        } else if (mod != NULL) {
                char buf[512];
                ty_snprintf(buf, sizeof buf, "<%s>", (mod->name != NULL) ? mod->name : "module");
                f.name = strdup(buf);
                f.line0 = 0;
                f.line1 = UINT32_MAX;
        } else {
                f.name = strdup("<unknown>");
        }

        xvP(M.funcs, f);

        return vN(M.funcs) - 1;
}

static u32
LineOf(Module const *mod, u32 line, u32 func, Expr const *expr)
{
        if ((vN(M.lines) + 1) * 2 >= M.line_cap) {
                u32 cap = (M.line_cap == 0) ? 1024 : M.line_cap * 2;
                u32 *tab = malloc(cap * sizeof *tab);
                memset(tab, 0xFF, cap * sizeof *tab);
                for (u32 i = 0; i < vN(M.lines); ++i) {
                        Line const *l = v_(M.lines, i);
                        u32 j = Mix((uptr)l->mod, l->line) & (cap - 1);
                        while (tab[j] != UINT32_MAX) {
                                j = (j + 1) & (cap - 1);
                        }
                        tab[j] = i;
                }
                free(M.line_tab);
                M.line_tab = tab;
                M.line_cap = cap;
        }

        u32 j = Mix((uptr)mod, line) & (M.line_cap - 1);

        while (M.line_tab[j] != UINT32_MAX) {
                Line const *l = v_(M.lines, M.line_tab[j]);
                if (l->mod == mod && l->line == line) {
                        return M.line_tab[j];
                }
                j = (j + 1) & (M.line_cap - 1);
        }

        M.line_tab[j] = vN(M.lines);

        xvP(M.lines, ((Line) { .mod = mod, .line = line, .func = func, .expr = expr }));

        return vN(M.lines) - 1;
}

static Site const *
SiteOf(u64 ip)
{
        if ((vN(M.sites) + 1) * 2 >= M.site_cap) {
                u32 cap = (M.site_cap == 0) ? 1024 : M.site_cap * 2;
                u32 *tab = malloc(cap * sizeof *tab);
                memset(tab, 0xFF, cap * sizeof *tab);
                for (u32 i = 0; i < vN(M.sites); ++i) {
                        u32 j = Mix(0, v_(M.sites, i)->ip) & (cap - 1);
                        while (tab[j] != UINT32_MAX) {
                                j = (j + 1) & (cap - 1);
                        }
                        tab[j] = i;
                }
                free(M.site_tab);
                M.site_tab = tab;
                M.site_cap = cap;
        }

        u32 j = Mix(0, ip) & (M.site_cap - 1);

        while (M.site_tab[j] != UINT32_MAX) {
                Site const *s = v_(M.sites, M.site_tab[j]);
                if (s->ip == ip) {
                        return s;
                }
                j = (j + 1) & (M.site_cap - 1);
        }

        char const *at = (char const *)ip - 1;
        Expr const *expr = compiler_find_expr(M.ty, at);
        Expr const *fexpr = compiler_find_func(M.ty, at);
        u32 func = FuncOf(fexpr, expr);
        Module const *mod = (expr != NULL) ? expr->mod : v_(M.funcs, func)->mod;
        u32 line = (expr != NULL) ? LocLine(expr->start) : (fexpr != NULL) ? LocLine(fexpr->start) : 0;

        if (
                (fexpr != NULL)
             && (expr != NULL)
             && (expr->mod == fexpr->mod)
             && (line < LocLine(fexpr->start) || line > LocLine(fexpr->end))
        ) {
                expr = fexpr;
                line = LocLine(fexpr->start);
        }

        M.site_tab[j] = vN(M.sites);

        xvP(M.sites, ((Site) {
                .ip   = ip,
                .func = func,
                .line = LineOf(mod, line, func, expr)
        }));

        return vvL(M.sites);
}

static void
AddEdge(u32 from, u32 to, u64 w)
{
        if ((vN(M.edges) + 1) * 2 >= M.edge_cap) {
                u32 cap = (M.edge_cap == 0) ? 1024 : M.edge_cap * 2;
                u32 *tab = malloc(cap * sizeof *tab);
                memset(tab, 0xFF, cap * sizeof *tab);
                for (u32 i = 0; i < vN(M.edges); ++i) {
                        Edge const *e = v_(M.edges, i);
                        u32 k = Mix(e->from, e->to) & (cap - 1);
                        while (tab[k] != UINT32_MAX) {
                                k = (k + 1) & (cap - 1);
                        }
                        tab[k] = i;
                }
                free(M.edge_tab);
                M.edge_tab = tab;
                M.edge_cap = cap;
        }

        u32 k = Mix(from, to) & (M.edge_cap - 1);

        while (M.edge_tab[k] != UINT32_MAX) {
                Edge *e = v_(M.edges, M.edge_tab[k]);
                if (e->from == from && e->to == to) {
                        e->w += w;
                        return;
                }
                k = (k + 1) & (M.edge_cap - 1);
        }

        M.edge_tab[k] = vN(M.edges);
        xvP(M.edges, ((Edge) { .from = from, .to = to, .w = w }));
}

static char const *
SymName(u32 sym)
{
        return (sym < vN(SymNames)) ? v__(SymNames, sym) : "?";
}

static bool
StartsWith(char const *s, char const *p)
{
        return strncmp(s, p, strlen(p)) == 0;
}

static bool
SymMatch(char const *name, char const *pat)
{
        usize n = strlen(pat);

        if (pat[n - 1] == '*') {
                return strncmp(name, pat, n - 1) == 0;
        }

        if (strncmp(name, pat, n) != 0) {
                return false;
        }

        return name[n] == '\0' || name[n] == '.';
}

static int
SymCategory(u32 sym)
{
        if (sym == SYM_JIT) {
                return CAT_JIT;
        }

        if (sym >= SymCatN) {
                u32 n = vN(SymNames) + 64;
                SymCat = realloc(SymCat, n);
                memset(SymCat + SymCatN, 0xFF, n - SymCatN);
                SymCatN = n;
        }

        if (SymCat[sym] != 0xFF) {
                return SymCat[sym];
        }

        char const *name = SymName(sym);
        int cat = CAT_NATIVE;

        for (usize i = 0; i < countof(SymClasses); ++i) {
                if (SymMatch(name, SymClasses[i].pat)) {
                        cat = SymClasses[i].cat;
                        break;
                }
        }

        SymCat[sym] = cat;

        return cat;
}

static int
CategoryOf(Stack const *s)
{
        switch (s->state) {
        case PS_GC:
        case PS_GC_WAIT:
                return CAT_GC;
        case PS_BLOCKED:
                return CAT_BLOCKED;
        case PS_JIT_COMPILE:
                return CAT_JIT_COMPILE;
        case PS_COMPILE:
                return CAT_COMPILE;
        }

        if (s->n == 0) {
                return CAT_COMPILE;
        }

        if (s->kind == PK_OPS) {
                return CAT_INTERP;
        }

        if (s->sym == SYM_NONE) {
                return (s->mask & 1) ? CAT_JIT : CAT_INTERP;
        }

        return SymCategory(s->sym);
}

static bool
IsTimeKind(int kind)
{
        return kind == PK_CPU || kind == PK_WALL || kind == PK_EVENT || kind == PK_OPS;
}

static void
AttachJit(void)
{
        TySpinLockLock(&JitLock);

        for (usize i = 0; i < vN(Declines); ++i) {
                JitDecline const *d = v_(Declines, i);
                for (usize j = 0; j < vN(M.funcs); ++j) {
                        Func *f = v_(M.funcs, j);
                        if (f->fexpr != NULL && f->fexpr == d->expr) {
                                f->decline = d->why;
                                if (d->off >= 0) {
                                        Expr const *e = compiler_find_expr(M.ty, d->code + d->off);
                                        f->decline_line = (e != NULL) ? (i32)LocLine(e->start) : -1;
                                }
                        }
                }
        }

        for (usize i = 0; i < vN(Deopts); ++i) {
                DeoptSite const *d = v_(Deopts, i);
                for (usize j = 0; j < vN(M.funcs); ++j) {
                        Func *f = v_(M.funcs, j);
                        if (f->fexpr != NULL && f->fexpr == d->expr) {
                                f->deopts += d->n;
                                if (d->n > f->deopt_top) {
                                        Expr const *e = compiler_find_expr(M.ty, d->code + d->off);
                                        f->deopt_top = d->n;
                                        f->deopt_line = (e != NULL) ? (i32)LocLine(e->start) : -1;
                                }
                        }
                }
        }

        TySpinLockUnlock(&JitLock);

        usize n;
        JitCompileRecord const *log = jit_compile_records(&n);

        for (usize i = 0; i < n; ++i) {
                for (usize j = 0; j < vN(M.funcs); ++j) {
                        Func *f = v_(M.funcs, j);
                        if (f->fexpr != NULL && f->fexpr == log[i].expr) {
                                f->compiles += 1;
                                f->native_size = log[i].native_size;
                                f->compile_ns += log[i].compile_time_ns;
                                f->tier2 = f->tier2 || !log[i].compact;
                        }
                }
        }
}

static void
OnSlowSite(void *ctx, char const *ip, char const *kind, u64 count, i32 const *classes, u64 const *counts, int n)
{
        Expr const *e = compiler_find_expr(M.ty, ip - 1);

        if (e == NULL || e->mod == NULL) {
                return;
        }

        Expr const *fe = compiler_find_func(M.ty, ip - 1);
        u32 func = FuncOf(fe, e);
        u32 li = LineOf(e->mod, LocLine(e->start), func, e);
        Line *l = v_(M.lines, li);

        l->slow += count;

        if (l->slow_desc != NULL && count * 2 < l->slow) {
                return;
        }

        u64 total = 0;

        for (int i = 0; i < n; ++i) {
                total += counts[i];
        }

        byte_vector b = {0};
        dump(&b, "%s missed the fast path %llu times", kind, (unsigned long long)count);

        for (int i = 0; i < n && i < 4; ++i) {
                int best = i;
                for (int j = i + 1; j < n; ++j) {
                        if (counts[j] > counts[best]) {
                                best = j;
                        }
                }
                dump(
                        &b,
                        "%s%s %.0f%%",
                        (i == 0) ? " (" : ", ",
                        class_name(M.ty, classes[best]),
                        (total > 0) ? 100.0 * counts[best] / total : 0.0
                );
                if (best != i) {
                        i32 tc = ((i32 *)classes)[i];
                        u64 tn = ((u64 *)counts)[i];
                        ((i32 *)classes)[i] = classes[best];
                        ((u64 *)counts)[i] = counts[best];
                        ((i32 *)classes)[best] = tc;
                        ((u64 *)counts)[best] = tn;
                }
        }

        if (n > 0) {
                xvP(b, ')');
        }

        xvP(b, '\0');

        free(l->slow_desc);
        l->slow_desc = strdup(vv(b));
        l->slow_classes = n;
        xvF(b);
}

static char UserRoot[4096];

static bool
IsUserPath(char const *path)
{
        usize n = strlen(UserRoot);
        usize c = strlen(M.cwd);

        if (path == NULL) {
                return false;
        }

        return (n > 0 && strncmp(path, UserRoot, n) == 0 && path[n] == '/')
            || (c > 0 && strncmp(path, M.cwd, c) == 0 && path[c] == '/');
}

static bool
IsUserLine(Line const *l)
{
        return l->mod != NULL && IsUserPath(l->mod->path);
}

static int
UserFrame(u32 const *lstack, u16 n)
{
        for (u16 k = 0; k < n; ++k) {
                if (IsUserLine(v_(M.lines, lstack[k]))) {
                        return k;
                }
        }

        return 0;
}

static u64
ObjSize(struct alloc const *a);

static void
AttachCalls(void);

static void
AttachRetained(void)
{
        pthread_mutex_lock(&LiveLock);

        M.retained_exact = (GcEpoch > 0);

        for (u64 i = 0; i < LiveCap; ++i) {
                LiveObj const *o = &Live[i];

                if (o->a == NULL || o->a == LIVE_TOMB) {
                        continue;
                }

                if (GcEpoch > 0 && o->epoch >= GcEpoch) {
                        continue;
                }

                if (o->seq >= vN(SeqStack) || v__(SeqStack, o->seq) == UINT32_MAX) {
                        continue;
                }

                Stack const *s = v_(Stacks, v__(SeqStack, o->seq));

                if (s->n == 0) {
                        continue;
                }

                u64 deep = ObjSize(o->a);
                u64 shallow = (o->a->size > 0) ? o->a->size : 1;
                u64 est = (shallow >= AllocEvery || deep > 64 * shallow)
                        ? deep
                        : (u64)((double)AllocEvery * deep / shallow);
                u64 objs = (shallow >= AllocEvery) ? 1 : AllocEvery / shallow;
                u32 type = (o->a->type <= GC_ANY) ? o->a->type : GC_ANY;
                Site const *site = SiteOf(*v_(Keys, s->off));
                Line *l = v_(M.lines, site->line);

                l->retained += est;
                l->retained_objs += objs;
                l->retained_by[type] += est;
                M.retained += est;
                M.retained_by[type] += est;
        }

        pthread_mutex_unlock(&LiveLock);

        u64 heap = 0;
        u32 nt = atomic_load(&NThreads);

        for (u32 i = 0; i < nt && i < MAX_THREADS; ++i) {
                if (Threads[i] != NULL && atomic_load(&Threads[i]->live)) {
                        heap += Threads[i]->ty->memory_used;
                }
        }

        if (heap > 0 && M.retained > heap) {
                double k = (double)heap / M.retained;
                for (usize i = 0; i < vN(M.lines); ++i) {
                        Line *l = v_(M.lines, i);
                        l->retained = (u64)(l->retained * k);
                }
                M.retained = heap;
        }
}

static void
BuildModel(Ty *ty)
{
        M.ty = ty;

        if (getcwd(M.cwd, sizeof M.cwd) == NULL) {
                M.cwd[0] = '\0';
        }

        M.time_kind = Mode;
        M.sym_self = calloc(vN(SymNames) + 1, sizeof *M.sym_self);

        UserRoot[0] = '\0';

        if (ProfTarget != NULL && realpath(ProfTarget, UserRoot) != NULL) {
                char *slash = strrchr(UserRoot, '/');
                if (slash != NULL) {
                        *slash = '\0';
                }
        } else {
                UserRoot[0] = '\0';
        }
        M.thread_total = calloc(MAX_THREADS, sizeof *M.thread_total);

        u32 *fstack = malloc(MAX_FRAMES * sizeof *fstack);
        u32 *lstack = malloc(MAX_FRAMES * sizeof *lstack);

        for (usize i = 0; i < vN(Stacks); ++i) {
                Stack const *s = v_(Stacks, i);
                u64 const *frames = v_(Keys, s->off);

                for (u16 k = 0; k < s->n; ++k) {
                        Site const *site = SiteOf(frames[k]);
                        fstack[k] = site->func;
                        lstack[k] = site->line;
                }

                M.stamp += 1;

                if (IsTimeKind(s->kind)) {
                        int cat = CategoryOf(s);

                        M.total += s->weight;
                        M.count += s->count;
                        M.cat[cat] += s->weight;
                        M.ccat[cat] += s->count;
                        M.thread_total[s->thread] += s->weight;

                        if (cat != CAT_JIT && cat != CAT_INTERP && cat != CAT_COMPILE && cat != CAT_JIT_COMPILE && cat != CAT_GC) {
                                M.sym_self[s->sym] += s->weight;
                        }

                        for (u16 k = 0; k < s->n; ++k) {
                                Func *f = v_(M.funcs, fstack[k]);
                                Line *l = v_(M.lines, lstack[k]);

                                if (k == 0) {
                                        f->self += s->weight;
                                        f->cself += s->count;
                                        l->self += s->weight;
                                        l->cself += s->count;
                                        if (cat == CAT_JIT) {
                                                f->jit_self += s->weight;
                                                l->jit_self += s->weight;
                                        } else if (cat == CAT_INTERP) {
                                                f->interp_self += s->weight;
                                        } else if (cat != CAT_GC && cat != CAT_BLOCKED) {
                                                f->native_self += s->weight;
                                                l->native_self += s->weight;
                                        }
                                        l->cat[cat] += s->weight;
                                }

                                if (f->stamp != M.stamp) {
                                        f->stamp = M.stamp;
                                        f->total += s->weight;
                                        f->ctotal += s->count;
                                        if (cat == CAT_GC) {
                                                f->gc_total += s->weight;
                                        }
                                        if (k < 64 && (s->mask >> k) & 1) {
                                                f->jit_total += s->weight;
                                        }
                                }

                                if (l->stamp != M.stamp) {
                                        l->stamp = M.stamp;
                                        l->total += s->weight;
                                }

                                if (k + 1 < s->n && fstack[k + 1] != fstack[k]) {
                                        AddEdge(fstack[k + 1], fstack[k], s->weight);
                                }
                        }

                        if (s->n > 0) {
                                v_(M.lines, lstack[UserFrame(lstack, s->n)])->ucat[cat] += s->weight;
                        }

                } else if (s->kind == PK_ALLOC) {
                        u32 type = (s->sym <= GC_ANY) ? s->sym : GC_ANY;

                        M.alloc_total += s->weight;
                        M.alloc_by[type] += s->weight;

                        if (s->n > 0) {
                                Line *ul = v_(M.lines, lstack[UserFrame(lstack, s->n)]);
                                ul->ualloc += s->weight;
                                ul->ualloc_by[type] += s->weight;
                        }

                        for (u16 k = 0; k < s->n; ++k) {
                                Func *f = v_(M.funcs, fstack[k]);
                                Line *l = v_(M.lines, lstack[k]);
                                if (k == 0) {
                                        f->alloc_self += s->weight;
                                        l->alloc += s->weight;
                                        l->alloc_by[type] += s->weight;
                                }
                                if (f->stamp != M.stamp) {
                                        f->stamp = M.stamp;
                                        f->alloc_total += s->weight;
                                }
                        }
                } else if (s->kind == PK_THROW) {
                        M.throws += s->weight;
                        if (s->n > 0) {
                                v_(M.funcs, fstack[0])->throws += s->weight;
                                v_(M.lines, lstack[0])->throws += s->weight;
                        }
                }
        }

        free(fstack);
        free(lstack);

        if (!NoJIT) {
                jit_slow_sites(OnSlowSite, NULL);
        }

        AttachRetained();

        AttachCalls();

        AttachJit();
}

/* ------------------------------------------------------------------------ */

static FILE *Out;

#define C(n) PTERM(n)

static double
Pct(u64 w)
{
        return (M.total == 0) ? 0.0 : 100.0 * (double)w / (double)M.total;
}

static double
Margin(u64 w)
{
        if (M.total == 0 || M.count == 0 || M.time_kind == PK_OPS) {
                return 0.0;
        }

        double p = (double)w / (double)M.total;

        return 100.0 * 1.96 * sqrt(p * (1.0 - p) / (double)M.count);
}

static void
FmtQty(char *buf, usize n, u64 w)
{
        switch (M.time_kind) {
        case PK_CPU:
        case PK_WALL:
                if (w >= 1000000000ULL) {
                        ty_snprintf(buf, n, "%.2fs", w / 1e9);
                } else if (w >= 1000000ULL) {
                        ty_snprintf(buf, n, "%.1fms", w / 1e6);
                } else {
                        ty_snprintf(buf, n, "%.0fus", w / 1e3);
                }
                break;

        default:
                if (w >= 1000000000ULL) {
                        ty_snprintf(buf, n, "%.2fG", w / 1e9);
                } else if (w >= 1000000ULL) {
                        ty_snprintf(buf, n, "%.1fM", w / 1e6);
                } else if (w >= 1000ULL) {
                        ty_snprintf(buf, n, "%.1fK", w / 1e3);
                } else {
                        ty_snprintf(buf, n, "%llu", (unsigned long long)w);
                }
                break;
        }
}

static void
FmtBytes(char *buf, usize n, u64 b)
{
        if (b >= (1ULL << 30)) {
                ty_snprintf(buf, n, "%.2f GiB", b / (double)(1ULL << 30));
        } else if (b >= (1ULL << 20)) {
                ty_snprintf(buf, n, "%.1f MiB", b / (double)(1ULL << 20));
        } else if (b >= (1ULL << 10)) {
                ty_snprintf(buf, n, "%.1f KiB", b / (double)(1ULL << 10));
        } else {
                ty_snprintf(buf, n, "%llu B", (unsigned long long)b);
        }
}

inline static int
ilerp(int lo, int hi, float a, float x, float b)
{
        if (x < a || x > b) {
                return -1;
        }

        float p = (x - a) / (b - a);

        return lo + p * (hi - lo);
}

void
color_sequence(float p, char *out)
{
        int r;
        int g;
        int b;

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

static char const *
Heat(double frac)
{
        static char bufs[8][32];
        static int k;

        if (!ColorProfile) {
                return "";
        }

        if (!(frac > 0.0)) {
                frac = 0.0;
        } else if (frac > 1.0) {
                frac = 1.0;
        }

        char *b = bufs[k++ & 7];
        color_sequence(sqrt(frac), b);

        return b;
}

static void
Bar(double pct, int width)
{
        static char const *blocks[] = { "", "▏", "▎", "▍", "▌", "▋", "▊", "▉" };
        double cells = pct / 100.0 * width;
        int full = (int)cells;
        int frac = (int)((cells - full) * 8);

        fputs(Heat(pct / 100.0), Out);

        for (int i = 0; i < full && i < width; ++i) {
                fputs("█", Out);
        }

        int used = full;

        if (full < width && frac > 0) {
                fputs(blocks[frac], Out);
                used += 1;
        }

        fputs(C(0), Out);

        for (int i = used; i < width; ++i) {
                fputc(' ', Out);
        }
}

static void
FmtCount(char *buf, usize n, u64 c)
{
        if (c >= 10000000000ULL) {
                ty_snprintf(buf, n, "%.1fG", c / 1e9);
        } else if (c >= 10000000ULL) {
                ty_snprintf(buf, n, "%.1fM", c / 1e6);
        } else if (c >= 100000ULL) {
                ty_snprintf(buf, n, "%.0fK", c / 1e3);
        } else {
                ty_snprintf(buf, n, "%llu", (unsigned long long)c);
        }
}

static void
FmtNs(char *buf, usize n, u64 ns)
{
        if (ns >= 10000000000ULL) {
                ty_snprintf(buf, n, "%.1fs", ns / 1e9);
        } else if (ns >= 1000000000ULL) {
                ty_snprintf(buf, n, "%.2fs", ns / 1e9);
        } else if (ns >= 1000000ULL) {
                ty_snprintf(buf, n, "%.1fms", ns / 1e6);
        } else {
                ty_snprintf(buf, n, "%.0fµs", ns / 1e3);
        }
}

static char const *
SourceLine(Module const *mod, u32 line, int *len)
{
        *len = 0;

        if (mod == NULL || mod->source == NULL) {
                return NULL;
        }

        char const *p = mod->source;

        for (u32 i = 0; i < line; ++i) {
                p = strchr(p, '\n');
                if (p == NULL) {
                        return NULL;
                }
                p += 1;
        }

        char const *end = strchr(p, '\n');
        *len = (end != NULL) ? (int)(end - p) : (int)strlen(p);

        return p;
}

static void
Snippet(char *buf, usize n, Module const *mod, u32 line)
{
        int len;
        char const *s = SourceLine(mod, line, &len);

        buf[0] = '\0';

        if (s == NULL) {
                return;
        }

        while (len > 0 && (*s == ' ' || *s == '\t')) {
                s += 1;
                len -= 1;
        }

        if ((usize)len >= n) {
                len = n - 1;
        }

        memcpy(buf, s, len);
        buf[len] = '\0';
}

static TokenVector const *
HaveTokens(Ty *ty, Module const *mod)
{
        if (mod == NULL || mod->source == NULL) {
                return NULL;
        }

        TokenVector const *ts = ModuleTokens(ty, (Module *)mod);

        bool ok = (vN(*ts) > 0)
               && (LocPtr(v_(*ts, 0)->start) == mod->source + v_(*ts, 0)->start.byte);

        return ok ? ts : NULL;
}

static void
PutSource(Module const *mod, u32 line, int max)
{
        Ty *ty = M.ty;
        int len;
        char const *s = SourceLine(mod, line, &len);

        if (s == NULL || max <= 1) {
                return;
        }

        while (len > 0 && (*s == ' ' || *s == '\t')) {
                s += 1;
                len -= 1;
        }

        while (len > 0 && (s[len - 1] == ' ' || s[len - 1] == '\r')) {
                len -= 1;
        }

        bool cut = term_width(s, len) > max;

        SCRATCH_SAVE();

        byte_vector b = {0};

        TokenVector const *ts = ColorProfile ? HaveTokens(ty, mod) : NULL;

        if (ts != NULL) {
                syntax_highlight(
                        ty,
                        &b,
                        mod->source,
                        ts,
                        s - mod->source,
                        s + len - mod->source,
                        NULL,
                        NULL
                );
        } else {
                sxdf(&b, "%.*s", len, s);
        }

        isize n = cut ? term_fit_cols(vv(b), vN(b), max - 1) : (isize)strlen(vv(b));

        fwrite(vv(b), 1, n, Out);
        fputs(C(0), Out);

        if (cut) {
                fprintf(Out, "%s…%s", C(90), C(0));
        }

        SCRATCH_RESTORE();
}

static int
ByFuncSelf(void const *a_, void const *b_)
{
        Func const *a = *(Func const **)a_;
        Func const *b = *(Func const **)b_;
        return (a->self < b->self) - (a->self > b->self);
}

static int
ByFuncTotal(void const *a_, void const *b_)
{
        Func const *a = *(Func const **)a_;
        Func const *b = *(Func const **)b_;
        return (a->total < b->total) - (a->total > b->total);
}

static int
ByLineSelf(void const *a_, void const *b_)
{
        Line const *a = *(Line const **)a_;
        Line const *b = *(Line const **)b_;
        return (a->self < b->self) - (a->self > b->self);
}

static int
ByLineAlloc(void const *a_, void const *b_)
{
        Line const *a = *(Line const **)a_;
        Line const *b = *(Line const **)b_;
        return (a->alloc < b->alloc) - (a->alloc > b->alloc);
}

static int
ByLineRetained(void const *a_, void const *b_)
{
        Line const *a = *(Line const **)a_;
        Line const *b = *(Line const **)b_;
        return (a->retained < b->retained) - (a->retained > b->retained);
}

static char const *
JitLabel(Func const *f)
{
        if (NoJIT) {
                return "off";
        }

        if (f->fexpr == NULL) {
                return "never";
        }

        if (f->decline != NULL) {
                return "declined";
        }

        if (f->compiles > 0) {
                return f->tier2 ? "tier2" : "tier1";
        }

        if (f->jit_total > 0) {
                return "compiled";
        }

        return "interp";
}

static char const *
JitColor(Func const *f)
{
        if (f->decline != NULL) {
                return C(91);
        }

        if (f->compiles > 0) {
                return C(32);
        }

        return C(90);
}

static Line *
FindLine(Module const *mod, u32 line)
{
        if (M.line_cap == 0) {
                return NULL;
        }

        u32 j = Mix((uptr)mod, line) & (M.line_cap - 1);

        while (M.line_tab[j] != UINT32_MAX) {
                Line *l = v_(M.lines, M.line_tab[j]);
                if (l->mod == mod && l->line == line) {
                        return l;
                }
                j = (j + 1) & (M.line_cap - 1);
        }

        return NULL;
}

static Line const *
TopLineFor(int cat, Line const *skip)
{
        Line const *best = NULL;

        for (usize i = 0; i < vN(M.lines); ++i) {
                Line const *l = v_(M.lines, i);
                if (l == skip || l->ucat[cat] == 0) {
                        continue;
                }
                if (best == NULL || l->ucat[cat] > best->ucat[cat]) {
                        best = l;
                }
        }

        return best;
}

static Func **
SortedFuncs(int (*cmp)(void const *, void const *))
{
        Func **fs = malloc((vN(M.funcs) + 1) * sizeof *fs);

        for (usize i = 0; i < vN(M.funcs); ++i) {
                fs[i] = v_(M.funcs, i);
        }

        qsort(fs, vN(M.funcs), sizeof *fs, cmp);

        return fs;
}

static Line **
SortedLines(int (*cmp)(void const *, void const *))
{
        Line **ls = malloc((vN(M.lines) + 1) * sizeof *ls);

        for (usize i = 0; i < vN(M.lines); ++i) {
                ls[i] = v_(M.lines, i);
        }

        qsort(ls, vN(M.lines), sizeof *ls, cmp);

        return ls;
}

static void
Heading(char const *title, char const *note)
{
        fprintf(Out, "\n%s%s%s", C(1), title, C(0));

        if (note != NULL) {
                fprintf(Out, "  %s%s%s", C(90), note, C(0));
        }

        fputc('\n', Out);
}

static char const *
Unit(void)
{
        switch (M.time_kind) {
        case PK_CPU:   return "CPU time";
        case PK_WALL:  return "Wall time";
        case PK_EVENT: return EventName;
        case PK_OPS:   return "Bytecode ops";
        }
        return "Samples";
}

static void
PutLoc(Func const *f, u32 line, int width)
{
        char loc[512];
        ty_snprintf(loc, sizeof loc, "%s:%u", f->path, line + 1);
        fprintf(Out, "%s%-*s%s", C(36), width, loc, C(0));
}

static double
RunCpuSeconds(void)
{
        struct rusage ru;
        getrusage(RUSAGE_SELF, &ru);

        return (ru.ru_utime.tv_sec - StartUsage.ru_utime.tv_sec)
             + (ru.ru_stime.tv_sec - StartUsage.ru_stime.tv_sec)
             + (ru.ru_utime.tv_usec - StartUsage.ru_utime.tv_usec) / 1e6
             + (ru.ru_stime.tv_usec - StartUsage.ru_stime.tv_usec) / 1e6;
}

static void
SummaryHeader(void)
{
        struct rusage ru;
        getrusage(RUSAGE_SELF, &ru);

        double cpu = RunCpuSeconds();
        double wall = (StopWall - StartWall) / 1e9;
        double overhead = (cpu > 0) ? 100.0 * (HandlerNs / 1e9) / cpu : 0.0;
        u32 nt = atomic_load(&NThreads);
        char n[32];

        FmtCount(n, sizeof n, M.count);

        fprintf(Out, "%s%sprofile%s %s%s%s", C(1), C(96), C(0), C(1), (ProfTarget != NULL) ? ProfTarget : "", C(0));

        if (Attached) {
                fprintf(Out, " %s(pid %d)%s", C(33), (int)getpid(), C(0));
        }

        fprintf(Out, "\n%s", C(90));

        switch (Mode) {
        case PK_CPU:   fprintf(Out, "CPU, %llu Hz", (unsigned long long)Hz);                  break;
        case PK_WALL:  fprintf(Out, "Wall clock, %llu Hz", (unsigned long long)Hz);           break;
        case PK_EVENT: fprintf(Out, "%s, every %llu", EventName, (unsigned long long)EventPeriod); break;
        case PK_OPS:   fprintf(Out, "Every %llu bytecode ops", (unsigned long long)OpsEvery);  break;
        }

        fprintf(
                Out,
                " · %s samples · %.2fs wall · %.2fs CPU · %.0f MiB max RSS",
                n,
                wall,
                cpu,
                MaxRssBytes(&ru) / 1048576.0
        );

        if (nt > 1) {
                fprintf(Out, " · %u threads", nt);
        }

        fprintf(Out, "%s\n", C(0));

        if (M.count > 0 && M.count < 200 && M.time_kind != PK_OPS) {
                fprintf(
                        Out,
                        "%sOnly %llu samples: shares are within ±%.0f%%. Use a higher -F or a longer run.%s\n",
                        C(33),
                        (unsigned long long)M.count,
                        Margin(M.total / 2),
                        C(0)
                );
        }

        if (Dropped + Busy > M.count / 100 && Dropped + Busy > 0) {
                fprintf(Out, "%s%llu samples dropped.%s\n", C(33), (unsigned long long)(Dropped + Busy), C(0));
        }

        if (Mode != PK_OPS && overhead >= 5.0) {
                fprintf(Out, "%sSampling overhead %.1f%% of CPU time.%s\n", C(33), overhead, C(0));
        }
}

static void
SummaryCategories(void)
{
        int order[CAT_COUNT];
        int n = 0;

        for (int i = 0; i < CAT_COUNT; ++i) {
                if (Pct(M.cat[i]) >= 1.0) {
                        order[n++] = i;
                }
        }

        for (int i = 0; i < n; ++i) {
                for (int j = i + 1; j < n; ++j) {
                        if (M.cat[order[j]] > M.cat[order[i]]) {
                                int t = order[i];
                                order[i] = order[j];
                                order[j] = t;
                        }
                }
        }

        if (n == 0) {
                return;
        }

        Heading(Unit(), NULL);

        int w = 0;

        for (int i = 0; i < n; ++i) {
                int len = term_width(CatNames[order[i]], -1);
                w = (len > w) ? len : w;
        }

        for (int i = 0; i < n; ++i) {
                int c = order[i];
                double p = Pct(M.cat[c]);
                char q[32];
                int pad = w - term_width(CatNames[c], -1);

                FmtQty(q, sizeof q, M.cat[c]);

                fprintf(Out, "  %s%*s  %s%5.1f%% %8s%s  ", CatNames[c], pad, "", Heat(p / 100), p, q, C(0));
                Bar(p, 20);

                Line const *l = (p >= 5.0 && c != CAT_COMPILE && c != CAT_JIT_COMPILE) ? TopLineFor(c, NULL) : NULL;

                if (l != NULL && Pct(l->ucat[c]) >= 2.0) {
                        Func const *f = v_(M.funcs, l->func);
                        fprintf(Out, " %s%5.1f%%%s ", Heat(Pct(l->ucat[c]) / 100), Pct(l->ucat[c]), C(0));
                        PutLoc(f, l->line, 0);
                }

                fputc('\n', Out);
        }
}

static void
SummaryFunctions(void)
{
        Func **fs = SortedFuncs(ByFuncSelf);
        int n = 0;
        int w = 8;
        u64 max_calls = 0;

        while (n < vN(M.funcs) && n < TopN && Pct(fs[n]->self) >= MinPct) {
                int len = term_width(fs[n]->name, -1);
                w = (len > w) ? len : w;
                max_calls = (fs[n]->calls > max_calls) ? fs[n]->calls : max_calls;
                n += 1;
        }

        w = (w > 40) ? 40 : w;

        if (n == 0) {
                free(fs);
                return;
        }

        Heading("Functions", NULL);
        fprintf(Out, "%s  %-*s   self  total    calls  JIT%s\n", C(90), w, "", C(0));

        for (int i = 0; i < n; ++i) {
                Func const *f = fs[i];
                char cs[32] = "";

                if (f->calls > 0) {
                        FmtCount(cs, sizeof cs, f->calls);
                }

                fprintf(Out, "  %s%-*.*s%s", C(1), w, w, f->name, C(0));
                fprintf(Out, " %s%5.1f%%%s", Heat(Pct(f->self) / 100), Pct(f->self), C(0));
                fprintf(Out, " %s%5.1f%%%s", Heat(Pct(f->total) / 100), Pct(f->total), C(0));
                fprintf(
                        Out,
                        " %s%8s%s",
                        (max_calls > 0) ? Heat((double)f->calls / max_calls) : "",
                        cs,
                        C(0)
                );
                fprintf(Out, "  %s%-8s%s ", JitColor(f), JitLabel(f), C(0));
                PutLoc(f, f->line0, 0);
                fputc('\n', Out);
        }

        free(fs);
}

typedef struct {
        u32 func;
        bool alloc;
        Line *const *hot;
        int nhot;
} Gutter;

static void
DrawGutter(void *ctx, byte_vector *out, int line)
{
        Gutter const *g = ctx;
        Func const *f = v_(M.funcs, g->func);
        Line const *l = FindLine(f->mod, line);
        char a[32];

        if (l != NULL && l->self > 0) {
                dump(out, "  %s%5.1f%%%s", Heat(Pct(l->self) / 100), Pct(l->self), C(0));
        } else {
                dump(out, "        ");
        }

        if (!g->alloc) {
                return;
        }

        if (l != NULL && l->alloc > 0 && M.alloc_total > 0) {
                FmtBytes(a, sizeof a, l->alloc);
                dump(out, " %s%9s%s", Heat((double)l->alloc / M.alloc_total), a, C(0));
        } else {
                dump(out, " %9s", "");
        }
}

static bool
MarkedLine(void *ctx, int line)
{
        Gutter const *g = ctx;

        for (int i = 0; i < g->nhot; ++i) {
                if ((int)g->hot[i]->line == line && g->hot[i]->func == g->func) {
                        return true;
                }
        }

        return false;
}

static int
ByU32(void const *a_, void const *b_)
{
        u32 a = *(u32 const *)a_;
        u32 b = *(u32 const *)b_;
        return (a > b) - (a < b);
}

static void
SummaryHotLines(void)
{
        Ty *ty = M.ty;
        Line **ls = SortedLines(ByLineSelf);
        Line *hot[16];
        int nhot = 0;

        for (usize i = 0; i < vN(M.lines) && nhot < HotLines && nhot < (int)countof(hot); ++i) {
                Line *l = ls[i];
                if (Pct(l->self) < HotMinPct) {
                        break;
                }
                if (l->mod != NULL && l->mod->source != NULL) {
                        hot[nhot++] = l;
                }
        }

        free(ls);

        if (nhot == 0) {
                return;
        }

        Heading("Hot lines", NULL);

        typedef struct {
                int hot;
                u32 lines[16];
                u32 a[16];
                u32 b[16];
                int n;
                int nr;
                bool alloc;
        } Block;

        Block blocks[16];
        int nb = 0;
        bool done[16] = {0};
        byte_vector buf = {0};

        for (int i = 0; i < nhot; ++i) {
                if (done[i]) {
                        continue;
                }

                Block *bl = &blocks[nb++];
                Func const *f = v_(M.funcs, hot[i]->func);

                bl->hot   = i;
                bl->n     = 0;
                bl->nr    = 0;
                bl->alloc = false;

                for (int j = i; j < nhot; ++j) {
                        if (hot[j]->func == hot[i]->func && hot[j]->mod == hot[i]->mod) {
                                done[j] = true;
                                bl->lines[bl->n++] = hot[j]->line;
                        }
                }

                qsort(bl->lines, bl->n, sizeof bl->lines[0], ByU32);

                u32 lo = (f->fexpr != NULL) ? f->line0 : 0;
                u32 hi = (f->fexpr != NULL) ? f->line1 : UINT32_MAX;

                if (bl->lines[0] < lo) {
                        lo = bl->lines[0];
                }

                if (bl->lines[bl->n - 1] > hi) {
                        hi = bl->lines[bl->n - 1];
                }

                for (int k = 0; k < bl->n; ++k) {
                        u32 a = (bl->lines[k] > lo + 1) ? bl->lines[k] - 2 : lo;
                        u32 b = bl->lines[k] + 2;

                        while (k + 1 < bl->n && bl->lines[k + 1] <= b + 3) {
                                k += 1;
                                b = bl->lines[k] + 2;
                        }

                        if (b > hi) {
                                b = hi;
                        }

                        bl->a[bl->nr] = a;
                        bl->b[bl->nr] = b;
                        bl->nr += 1;

                        for (u32 ln = a; ln <= b; ++ln) {
                                Line const *l = FindLine(hot[i]->mod, ln);
                                if (l != NULL && l->alloc > 0 && M.alloc_total > 0) {
                                        bl->alloc = true;
                                }
                        }
                }
        }

        int order[16];
        int no = 0;

        for (int pass = 0; pass < 2; ++pass) {
                for (int i = 0; i < nb; ++i) {
                        if (blocks[i].alloc == (pass == 1)) {
                                order[no++] = i;
                        }
                }
        }

        for (int i = 0; i < nb; ++i) {
                Block const *bl = &blocks[order[i]];
                bool alloc = bl->alloc;
                Line const *h = hot[bl->hot];
                Func const *f = v_(M.funcs, h->func);
                int strip = INT_MAX;

                for (int r = 0; r < bl->nr; ++r) {
                        int in = ModuleSourceIndent(h->mod, bl->a[r], bl->b[r]);
                        strip = (in < strip) ? in : strip;
                }

                Gutter g = {
                        .func  = h->func,
                        .alloc = alloc,
                        .hot   = hot,
                        .nhot  = nhot
                };

                SourceGutter sg = {
                        .width  = alloc ? 18 : 8,
                        .ctx    = &g,
                        .draw   = DrawGutter,
                        .marked = MarkedLine,
                        .shade  = ColorProfile ? C(48;2;46;50;60) : NULL,
                        .strip  = strip
                };

                v0(buf);

                fputc('\n', Out);

                dump(
                        &buf,
                        "%s    self%s%s  %s%s  %s%s%s\n",
                        C(90),
                        alloc ? "     alloc" : "",
                        C(0),
                        f->name,
                        C(0),
                        C(90),
                        f->path,
                        C(0)
                );

                for (int r = 0; r < bl->nr; ++r) {
                        if (r > 0) {
                                dump(&buf, "%*s%s⋮%s\n", sg.width + 6, "", C(90), C(0));
                        }

                        WriteModuleSourceLines(ty, &buf, Cols, h->mod, bl->a[r], bl->b[r], &sg);
                }

                fwrite(vv(buf), 1, vN(buf), Out);
        }

        xvF(buf);
}

static void
SummaryAllocs(void)
{
        if (M.alloc_total == 0) {
                return;
        }

        Line **ls = SortedLines(ByLineAlloc);
        int n = 0;

        while (n < vN(M.lines) && n < 3 && ls[n]->alloc > 0 && 100.0 * ls[n]->alloc / M.alloc_total >= 10.0) {
                n += 1;
        }

        if (n == 0) {
                free(ls);
                return;
        }

        char total[32];
        FmtBytes(total, sizeof total, M.alloc_total);

        char note[64];
        ty_snprintf(note, sizeof note, "%s sampled", total);

        Heading("Allocation", note);

        for (int i = 0; i < n; ++i) {
                Line const *l = ls[i];
                Func const *f = v_(M.funcs, l->func);
                double p = (double)l->alloc / M.alloc_total;
                u32 type = 0;
                char b[32];

                for (u32 t = 0; t <= GC_ANY; ++t) {
                        if (l->alloc_by[t] > l->alloc_by[type]) {
                                type = t;
                        }
                }

                FmtBytes(b, sizeof b, l->alloc);

                fprintf(Out, "  %s%5.1f%% %10s%s  %-7s ", Heat(p), 100 * p, b, C(0), GcTypeNames[type]);
                PutLoc(f, l->line, 24);
                fputc(' ', Out);
                PutSource(l->mod, l->line, Cols - 54);
                fputc('\n', Out);
        }

        free(ls);
}

static void
SummaryRetained(void)
{
        if (M.retained < (64ULL << 20) || !M.retained_exact) {
                return;
        }

        Line **ls = SortedLines(ByLineRetained);
        char total[32];
        char note[96];

        FmtBytes(total, sizeof total, M.retained);
        ty_snprintf(note, sizeof note, "%s live after the last GC", total);

        Heading("Retained heap", note);

        for (int i = 0; i < 3 && i < vN(M.lines); ++i) {
                Line const *l = ls[i];
                double p = (double)l->retained / M.retained;
                char b[32];

                if (l->retained == 0 || p < 0.1) {
                        break;
                }

                FmtBytes(b, sizeof b, l->retained);

                fprintf(Out, "  %s%5.1f%% %10s%s  ", Heat(p), 100 * p, b, C(0));
                PutLoc(v_(M.funcs, l->func), l->line, 24);
                fputc(' ', Out);
                PutSource(l->mod, l->line, Cols - 46);
                fputc('\n', Out);
        }

        free(ls);
}

static int
ByModSelf(void const *a_, void const *b_)
{
        ModLoad const *a = a_;
        ModLoad const *b = b_;
        u64 x = (a->t2 - a->t0) - a->child_total;
        u64 y = (b->t2 - b->t0) - b->child_total;
        return (x < y) - (x > y);
}

static void
SummaryNotes(void)
{
        u64 begin = StartWall;
        bool any = false;

        for (usize i = 0; i < vN(Mods); ++i) {
                begin = (v_(Mods, i)->t0 < begin) ? v_(Mods, i)->t0 : begin;
        }

        u64 wall = (StopWall > begin) ? StopWall - begin : 1;

        #define NOTE(label) do {                                                 \
                if (!any) {                                                      \
                        Heading("Also", NULL);                                   \
                        any = true;                                              \
                }                                                                \
                fprintf(Out, "  %s%-11s%s", C(1), (label), C(0));                \
        } while (0)

        if (GcStats.n > 0 && GcStats.total * 50 >= wall) {
                char t[32];
                char m[32];
                double p = (double)GcStats.total / wall;
                FmtNs(t, sizeof t, GcStats.total);
                FmtNs(m, sizeof m, GcStats.max);
                NOTE("GC");
                fprintf(
                        Out,
                        "%llu collections, %s%s%s paused (%s%.1f%%%s of the run), longest %s\n",
                        (unsigned long long)GcStats.n,
                        Heat(p),
                        t,
                        C(0),
                        Heat(p),
                        100 * p,
                        C(0),
                        m
                );
        }

        u64 imports = 0;
        usize nmods = 0;

        for (usize i = 0; i < vN(Mods); ++i) {
                ModLoad const *m = v_(Mods, i);
                if (m->t2 != 0 && m->parent < 0) {
                        imports += m->t2 - m->t0;
                }
                nmods += (m->t2 != 0);
        }

        if (nmods > 0 && imports * 10 >= wall && imports >= 20000000) {
                ModLoad *ms = malloc(vN(Mods) * sizeof *ms);
                char t[32];
                double p = (double)imports / wall;

                memcpy(ms, vv(Mods), vN(Mods) * sizeof *ms);
                qsort(ms, vN(Mods), sizeof *ms, ByModSelf);
                FmtNs(t, sizeof t, imports);

                NOTE("Imports");
                fprintf(Out, "%zu modules, %s%s%s (%s%.0f%%%s of the run):", nmods, Heat(p), t, C(0), Heat(p), 100 * p, C(0));

                for (usize i = 0, k = 0; i < vN(Mods) && k < 3; ++i) {
                        u64 self = (ms[i].t2 - ms[i].t0) - ms[i].child_total;
                        if (ms[i].t2 == 0 || self * 10 < imports) {
                                continue;
                        }
                        FmtNs(t, sizeof t, self);
                        fprintf(Out, "%s %s %s%s%s", (k > 0) ? "," : "", ms[i].name, Heat((double)self / wall), t, C(0));
                        k += 1;
                }

                fputc('\n', Out);
                free(ms);
        }

        for (usize i = 0; i < vN(M.funcs); ++i) {
                Func const *f = v_(M.funcs, i);

                if (f->decline == NULL || Pct(f->total) < 1.0) {
                        continue;
                }

                NOTE("JIT");
                fprintf(Out, "%s%s%s not compiled (%s), %s%.1f%%%s of time", C(1), f->name, C(0), f->decline, Heat(Pct(f->total) / 100), Pct(f->total), C(0));

                if (f->decline_line >= 0) {
                        fputc(' ', Out);
                        PutLoc(f, f->decline_line, 0);
                }

                fputc('\n', Out);
        }

        for (usize i = 0; i < vN(M.funcs); ++i) {
                Func const *f = v_(M.funcs, i);
                char d[32];

                if (f->deopts < 100 || Pct(f->total) < 1.0) {
                        continue;
                }

                FmtCount(d, sizeof d, f->deopts);
                NOTE("JIT");
                fprintf(Out, "%s%s%s deoptimized %s times", C(1), f->name, C(0), d);

                if (f->deopt_line >= 0) {
                        fputc(' ', Out);
                        PutLoc(f, f->deopt_line, 0);
                }

                fputc('\n', Out);
        }

        if (M.throws >= 1000) {
                Line const *top = NULL;
                char t[32];

                for (usize i = 0; i < vN(M.lines); ++i) {
                        Line const *l = v_(M.lines, i);
                        if (l->throws > 0 && (top == NULL || l->throws > top->throws)) {
                                top = l;
                        }
                }

                FmtCount(t, sizeof t, M.throws);
                NOTE("Exceptions");
                fprintf(Out, "%s thrown", t);

                if (top != NULL) {
                        fprintf(Out, ", %.0f%% at ", 100.0 * top->throws / M.throws);
                        PutLoc(v_(M.funcs, top->func), top->line, 0);
                }

                fputc('\n', Out);
        }

        #undef NOTE
}

static void
SummaryFooter(void)
{
        if (DataPath == NULL || DataSize == 0) {
                return;
        }

        char size[32];
        FmtBytes(size, sizeof size, DataSize);

        fprintf(
                Out,
                "\n%sRecorded %s%s%s (%s). Run %sty --prof-report%s to explore it.%s\n",
                C(90),
                C(0),
                DataPath,
                C(90),
                size,
                C(0),
                C(90),
                C(0)
        );
}

static void
Summary(void)
{
        int rows;

        Out = ProfileOut;

        if (!get_terminal_size(fileno(Out), &rows, &Cols) || Cols < 60) {
                Cols = (AttachCols >= 60) ? AttachCols : 100;
        }

        bool color = ColorOutput;
        ColorOutput = ColorProfile;

        SummaryHeader();

        if (M.total == 0) {
                fprintf(Out, "\nNo samples were collected. Use a higher -F, a longer run, or --count.\n");
        } else {
                SummaryCategories();
                SummaryFunctions();
                SummaryHotLines();
        }

        SummaryAllocs();
        SummaryRetained();
        SummaryNotes();
        SummaryFooter();

        ColorOutput = color;

        fflush(Out);
}

/* ------------------------------------------------------------------------ */

static void
JsonStr(FILE *f, char const *s)
{
        fputc('"', f);

        for (; s != NULL && *s != '\0'; ++s) {
                u8 c = *s;
                switch (c) {
                case '"':  fputs("\\\"", f); break;
                case '\\': fputs("\\\\", f); break;
                case '\n': fputs("\\n", f);  break;
                case '\t': fputs("\\t", f);  break;
                case '\r': fputs("\\r", f);  break;
                case '<':  fputs("\\u003c", f); break;
                default:
                        if (c < 0x20) {
                                fprintf(f, "\\u%04x", c);
                        } else {
                                fputc(c, f);
                        }
                }
        }

        fputc('"', f);
}

static char const *
DeoptWhy(i32 why)
{
        switch (why) {
        case JIT_WHY_LOOP_ENTRY: return "loop entry";
        case JIT_WHY_LOOP_TYPE:  return "loop variable type";
        case JIT_WHY_NUMERIC:    return "numeric speculation";
        case JIT_WHY_POLL:       return "interrupt";
        case JIT_WHY_TRAP:       return "trap";
        }
        return "unknown";
}

static void
JsonFuncName(FILE *f, Expr const *fe)
{
        char name[256];

        if (fe != NULL && fe->fn->name != NULL && fe->fn->class != NULL) {
                ty_snprintf(name, sizeof name, "%s.%s", fe->fn->class->name, fe->fn->name);
        } else {
                ty_snprintf(name, sizeof name, "%s", (fe != NULL && fe->fn->name != NULL) ? fe->fn->name : "<anonymous>");
        }

        JsonStr(f, name);
}

static void
ExportDeopts(FILE *f)
{
        TySpinLockLock(&JitLock);

        fputs(",\"jit_deopts\":[", f);

        for (usize i = 0; i < vN(Deopts); ++i) {
                DeoptSite const *d = v_(Deopts, i);
                Expr const *e = compiler_find_expr(M.ty, d->code + d->off);

                fprintf(f, "%s{\"func\":", (i > 0) ? "," : "");
                JsonFuncName(f, d->expr);
                fputs(",\"file\":", f);
                JsonStr(f, (e != NULL && e->mod != NULL && e->mod->path != NULL) ? DisplayPath(e->mod->path) : "");
                fprintf(f, ",\"line\":%d,\"why\":", (e != NULL) ? (int)LocLine(e->start) + 1 : 0);
                JsonStr(f, DeoptWhy(d->why));
                fputs(",\"guard\":", f);
                JsonStr(f, GuardText(d->guard));
                fputs(",\"shots\":[", f);

                for (u32 k = 0; k < d->nshots; ++k) {
                        DeoptShot const *s = &d->shots[k];
                        fprintf(
                                f,
                                "%s{\"t\":%llu,\"count\":%llu,\"stack\":[",
                                (k > 0) ? "," : "",
                                (unsigned long long)s->t,
                                (unsigned long long)s->count
                        );
                        for (u32 j = 0; j < s->nframes; ++j) {
                                char const *ip = (char const *)(uptr)s->ips[j];
                                Expr const *se = compiler_find_expr(M.ty, ip);
                                Expr const *sf = compiler_find_func(M.ty, ip);
                                fputs((j > 0) ? ",[" : "[", f);
                                JsonFuncName(f, sf);
                                fputc(',', f);
                                JsonStr(
                                        f,
                                        (se != NULL && se->mod != NULL && se->mod->path != NULL)
                                        ? DisplayPath(se->mod->path)
                                        : ""
                                );
                                fprintf(f, ",%d]", (se != NULL) ? (int)LocLine(se->start) + 1 : 0);
                        }
                        fprintf(f, "],\"vars\":%s}", (s->vars != NULL) ? s->vars : "[]");
                }

                fputc(']', f);
                fprintf(
                        f,
                        ",\"n\":%llu,\"first\":%llu,\"last\":%llu,\"notes\":[",
                        (unsigned long long)d->n,
                        (unsigned long long)d->first,
                        (unsigned long long)d->last
                );

                bool first = true;

                for (int k = 0; k < DEOPT_NOTES; ++k) {
                        if (d->notes[k].n == 0) {
                                continue;
                        }
                        fputs(first ? "[" : ",[", f);
                        JsonStr(f, d->notes[k].text);
                        fprintf(f, ",%llu]", (unsigned long long)d->notes[k].n);
                        first = false;
                }

                fputs("]}", f);
        }

        fputs("],\"jit_despecialized\":[", f);

        for (usize i = 0; i < vN(Despecs); ++i) {
                Despec const *d = v_(Despecs, i);
                fprintf(f, "%s{\"func\":", (i > 0) ? "," : "");
                JsonFuncName(f, d->expr);
                fprintf(f, ",\"at\":%llu,\"deopts\":%u}", (unsigned long long)d->at, d->deopts);
        }

        fputc(']', f);

        TySpinLockUnlock(&JitLock);
}

static void
JsonLineText(FILE *f, Module const *mod, u32 line)
{
        char buf[512];
        Snippet(buf, sizeof buf, mod, line);
        JsonStr(f, buf);
}

static char const *
LeafExtra(Stack const *s)
{
        static char buf[512];

        switch (CategoryOf(s)) {
        case CAT_GC:
                return "[GC]";
        case CAT_BLOCKED:
                if (s->sym >= SYM_FIRST) {
                        ty_snprintf(buf, sizeof buf, "[blocked] %s", SymName(s->sym));
                        return buf;
                }
                return "[blocked]";
        case CAT_COMPILE:
                return "[compile]";
        case CAT_JIT_COMPILE:
                return "[JIT compile]";
        case CAT_NATIVE:
        case CAT_JIT_RT:
                ty_snprintf(buf, sizeof buf, "[native] %s", SymName(s->sym));
                return buf;
        }

        return NULL;
}

static void
ExportJson(FILE *f)
{
        struct rusage ru;
        getrusage(RUSAGE_SELF, &ru);

        fprintf(f, "{\"ty-prof\":2,\"time\":%lld,\"argv\":[", (long long)StartUnix);

        for (int i = 0; i < TyArgc; ++i) {
                fprintf(f, "%s", (i > 0) ? "," : "");
                JsonStr(f, TyArgv[i]);
        }

        fprintf(f, "],\"cwd\":");
        JsonStr(f, M.cwd);
        fprintf(
                f,
                ",\"pid\":%d,\"attached\":%s,\"cpu_ns\":%llu,\"max_rss\":%llu,\"retained_exact\":%s",
                (int)getpid(),
                Attached ? "true" : "false",
                (unsigned long long)(RunCpuSeconds() * 1e9),
                (unsigned long long)MaxRssBytes(&ru),
                M.retained_exact ? "true" : "false"
        );

        fprintf(f, ",\"category_order\":[");
        for (int c = 0; c < CAT_COUNT; ++c) {
                fprintf(f, "%s{\"name\":", (c > 0) ? "," : "");
                JsonStr(f, CatNames[c]);
                fprintf(f, ",\"glyph\":\"%c\",\"total\":%llu,\"samples\":%llu}", CatGlyph[c], (unsigned long long)M.cat[c], (unsigned long long)M.ccat[c]);
        }

        fprintf(f, "],\"threads\":[");
        {
                u32 nt = atomic_load(&NThreads);
                bool first = true;
                for (u32 i = 0; i < nt && i < MAX_THREADS; ++i) {
                        if (Threads[i] == NULL) {
                                continue;
                        }
                        fprintf(f, "%s{\"id\":%u,\"name\":", first ? "" : ",", i);
                        JsonStr(f, Threads[i]->name);
                        fprintf(f, ",\"total\":%llu}", (unsigned long long)M.thread_total[i]);
                        first = false;
                }
        }

        fprintf(f, "],\"natives\":[");
        {
                bool first = true;
                for (u32 i = SYM_FIRST; i < vN(SymNames); ++i) {
                        if (M.sym_self[i] == 0) {
                                continue;
                        }
                        fprintf(f, "%s{\"name\":", first ? "" : ",");
                        JsonStr(f, SymName(i));
                        fprintf(f, ",\"self\":%llu}", (unsigned long long)M.sym_self[i]);
                        first = false;
                }
        }

        fprintf(f, "],\"target\":");
        JsonStr(f, (ProfTarget != NULL) ? ProfTarget : "");
        fprintf(f, ",\"target_file\":");
        {
                char real[4096];
                char const *t = (ProfTarget != NULL && realpath(ProfTarget, real) != NULL) ? real : "";
                usize cl = strlen(M.cwd);
                if (cl > 0 && strncmp(t, M.cwd, cl) == 0 && t[cl] == '/') {
                        t += cl + 1;
                }
                JsonStr(f, t);
        }
        fprintf(
                f,
                ",\"mode\":\"%s\",\"unit\":\"%s\",\"event\":",
                KindNames[Mode],
                (Mode == PK_CPU || Mode == PK_WALL) ? "ns" : (Mode == PK_OPS) ? "ops" : "events"
        );
        JsonStr(f, (Mode == PK_EVENT) ? EventName : "");
        fprintf(
                f,
                ",\"hz\":%llu,\"period\":%llu,\"samples\":%llu,\"total\":%llu,\"wall_ns\":%llu,\"overhead_ns\":%llu,\"dropped\":%llu,"
                "\"alloc_total\":%llu,\"alloc_every\":%llu,\"retained\":%llu,\"throws\":%llu,\"jit\":%s,",
                (unsigned long long)Hz,
                (unsigned long long)((Mode == PK_EVENT) ? EventPeriod : (Mode == PK_OPS) ? OpsEvery : Period),
                (unsigned long long)M.count,
                (unsigned long long)M.total,
                (unsigned long long)(StopWall - StartWall),
                (unsigned long long)HandlerNs,
                (unsigned long long)(Dropped + Busy),
                (unsigned long long)M.alloc_total,
                (unsigned long long)AllocEvery,
                (unsigned long long)M.retained,
                (unsigned long long)M.throws,
                NoJIT ? "false" : "true"
        );

        fprintf(f, "\"categories\":{");
        for (int c = 0; c < CAT_COUNT; ++c) {
                fprintf(f, "%s", (c > 0) ? "," : "");
                JsonStr(f, CatNames[c]);
                fprintf(f, ":%llu", (unsigned long long)M.cat[c]);
        }

        fprintf(f, "},\"functions\":[");
        for (usize i = 0; i < vN(M.funcs); ++i) {
                Func const *fn = v_(M.funcs, i);
                fprintf(f, "%s{\"name\":", (i > 0) ? "," : "");
                JsonStr(f, fn->name);
                fprintf(f, ",\"file\":");
                JsonStr(f, fn->path);
                fprintf(
                        f,
                        ",\"line\":%u,\"self\":%llu,\"total\":%llu,\"self_samples\":%llu,\"total_samples\":%llu,"
                        "\"jit_self\":%llu,\"interp_self\":%llu,\"native_self\":%llu,\"gc_total\":%llu,"
                        "\"alloc_self\":%llu,\"alloc_total\":%llu,\"throws\":%llu,\"calls\":%llu,\"jit\":\"%s\",\"deopts\":%llu,"
                        "\"end\":%u,\"compiles\":%d,\"native_size\":%zu,\"compile_ns\":%llu,\"deopt_line\":%d,\"decline_line\":%d,\"decline\":",
                        fn->line0 + 1,
                        (unsigned long long)fn->self,
                        (unsigned long long)fn->total,
                        (unsigned long long)fn->cself,
                        (unsigned long long)fn->ctotal,
                        (unsigned long long)fn->jit_self,
                        (unsigned long long)fn->interp_self,
                        (unsigned long long)fn->native_self,
                        (unsigned long long)fn->gc_total,
                        (unsigned long long)fn->alloc_self,
                        (unsigned long long)fn->alloc_total,
                        (unsigned long long)fn->throws,
                        (unsigned long long)fn->calls,
                        JitLabel(fn),
                        (unsigned long long)fn->deopts,
                        (fn->line1 == UINT32_MAX) ? 0 : fn->line1 + 1,
                        fn->compiles,
                        fn->native_size,
                        (unsigned long long)fn->compile_ns,
                        fn->deopt_line + 1,
                        fn->decline_line + 1
                );
                if (fn->decline != NULL) {
                        JsonStr(f, fn->decline);
                } else {
                        fputs("null", f);
                }
                fputc('}', f);
        }

        fprintf(f, "],\"lines\":[");
        bool first = true;
        for (usize i = 0; i < vN(M.lines); ++i) {
                Line const *l = v_(M.lines, i);
                if (l->self == 0 && l->total == 0 && l->alloc == 0 && l->throws == 0 && l->slow == 0 && l->retained == 0) {
                        continue;
                }
                fprintf(
                        f,
                        "%s{\"func\":%u,\"line\":%u,\"self\":%llu,\"total\":%llu,\"jit_self\":%llu,\"native_self\":%llu,"
                        "\"alloc\":%llu,\"retained\":%llu,\"throws\":%llu,\"text\":",
                        first ? "" : ",",
                        l->func,
                        l->line + 1,
                        (unsigned long long)l->self,
                        (unsigned long long)l->total,
                        (unsigned long long)l->jit_self,
                        (unsigned long long)l->native_self,
                        (unsigned long long)l->alloc,
                        (unsigned long long)l->retained,
                        (unsigned long long)l->throws
                );
                JsonLineText(f, l->mod, l->line);
                fprintf(f, ",\"file\":");
                JsonStr(f, v_(M.funcs, l->func)->path);
                if (l->slow_desc != NULL) {
                        fprintf(f, ",\"jit_slow\":");
                        JsonStr(f, l->slow_desc);
                        fprintf(f, ",\"jit_slow_hits\":%llu", (unsigned long long)l->slow);
                }
                if (l->retained > 0) {
                        fprintf(f, ",\"retained_objs\":%llu", (unsigned long long)l->retained_objs);
                }
                fprintf(f, ",\"cat\":[");
                for (int c = 0; c < CAT_COUNT; ++c) {
                        fprintf(f, "%s%llu", (c > 0) ? "," : "", (unsigned long long)l->cat[c]);
                }
                fputc(']', f);
                if (l->alloc > 0) {
                        bool any = false;
                        fprintf(f, ",\"alloc_by\":{");
                        for (u32 t = 0; t <= GC_ANY; ++t) {
                                if (l->alloc_by[t] > 0) {
                                        fprintf(f, "%s\"%s\":%llu", any ? "," : "", GcTypeNames[t], (unsigned long long)l->alloc_by[t]);
                                        any = true;
                                }
                        }
                        fputc('}', f);
                }
                fputc('}', f);
                first = false;
        }

        fprintf(f, "],\"edges\":[");
        for (usize i = 0; i < vN(M.edges); ++i) {
                Edge const *e = v_(M.edges, i);
                fprintf(f, "%s[%u,%u,%llu]", (i > 0) ? "," : "", e->from, e->to, (unsigned long long)e->w);
        }

        fprintf(f, "],\"stacks\":[");
        first = true;
        for (usize i = 0; i < vN(Stacks); ++i) {
                Stack const *s = v_(Stacks, i);
                u64 const *frames = v_(Keys, s->off);
                char const *extra = IsTimeKind(s->kind) ? LeafExtra(s) : NULL;
                fprintf(
                        f,
                        "%s{\"kind\":\"%s\",\"cat\":%d,\"state\":%d,\"thread\":%u,\"weight\":%llu,\"count\":%llu,\"frames\":[",
                        first ? "" : ",",
                        KindNames[s->kind],
                        IsTimeKind(s->kind) ? CategoryOf(s) : -1,
                        s->state,
                        s->thread,
                        (unsigned long long)s->weight,
                        (unsigned long long)s->count
                );
                for (int k = (int)s->n - 1; k >= 0; --k) {
                        Site const *site = SiteOf(frames[k]);
                        fprintf(f, "[%u,%u]%s", site->func, v_(M.lines, site->line)->line + 1, (k > 0) ? "," : "");
                }
                fprintf(f, "],\"leaf\":");
                if (extra != NULL) {
                        JsonStr(f, extra);
                } else if (s->kind == PK_ALLOC) {
                        JsonStr(f, GcTypeNames[(s->sym <= GC_ANY) ? s->sym : GC_ANY]);
                } else {
                        fputs("null", f);
                }
                fputc('}', f);
                first = false;
        }

        fprintf(f, "],\"timeline\":[");
        if (Timeline.n > 0) {
                enum { BUCKETS = 200 };
                u64 t0 = Timeline.t[0];
                u64 t1 = Timeline.t[0];
                for (usize i = 0; i < Timeline.n; ++i) {
                        t0 = (Timeline.t[i] < t0) ? Timeline.t[i] : t0;
                        t1 = (Timeline.t[i] > t1) ? Timeline.t[i] : t1;
                }
                u32 (*cnt)[CAT_COUNT] = calloc(BUCKETS, sizeof *cnt);
                for (usize i = 0; i < Timeline.n; ++i) {
                        u64 b = (t1 > t0) ? (Timeline.t[i] - t0) * (BUCKETS - 1) / (t1 - t0) : 0;
                        cnt[b][CategoryOf(v_(Stacks, Timeline.s[i]))] += 1;
                }
                for (int b = 0; b < BUCKETS; ++b) {
                        fprintf(f, "%s[", (b > 0) ? "," : "");
                        for (int c = 0; c < CAT_COUNT; ++c) {
                                fprintf(f, "%u%s", cnt[b][c], (c + 1 < CAT_COUNT) ? "," : "");
                        }
                        fputc(']', f);
                }
                free(cnt);
                fprintf(f, "],\"timeline_ns\":%llu", (unsigned long long)(t1 - t0));
        } else {
                fprintf(f, "],\"timeline_ns\":0");
        }

        fprintf(
                f,
                ",\"gc\":{\"count\":%llu,\"pause_ns\":%llu,\"max_ns\":%llu,\"freed\":%llu,\"peak\":%llu}",
                (unsigned long long)GcStats.n,
                (unsigned long long)GcStats.total,
                (unsigned long long)GcStats.max,
                (unsigned long long)GcStats.freed,
                (unsigned long long)GcStats.peak
        );

        fprintf(f, ",\"heap\":[");
        for (usize i = 0; i < vN(HeapTimeT); ++i) {
                fprintf(f, "%s[%llu,%llu]", (i > 0) ? "," : "", (unsigned long long)v__(HeapTimeT, i), (unsigned long long)v__(HeapTimeB, i));
        }
        fputc(']', f);

        fprintf(f, ",\"modules\":[");
        for (usize i = 0; i < vN(Mods); ++i) {
                ModLoad const *m = v_(Mods, i);
                fprintf(f, "%s{\"name\":", (i > 0) ? "," : "");
                JsonStr(f, m->name);
                fprintf(
                        f,
                        ",\"lines\":%u,\"parent\":%d,\"compile_ns\":%llu,\"total_ns\":%llu,\"child_ns\":%llu}",
                        m->lines,
                        m->parent,
                        (unsigned long long)((m->t1 > m->t0) ? m->t1 - m->t0 - m->child_compile : 0),
                        (unsigned long long)((m->t2 > m->t0) ? m->t2 - m->t0 : 0),
                        (unsigned long long)m->child_total
                );
        }
        fputc(']', f);

        fprintf(f, ",\"sources\":{");
        first = true;
        for (usize i = 0; i < vN(M.funcs); ++i) {
                Func const *fn = v_(M.funcs, i);
                if (fn->fexpr == NULL || fn->mod == NULL || fn->total == 0 || Pct(fn->total) < 0.5) {
                        continue;
                }
                fprintf(f, "%s\"%zu\":[", first ? "" : ",", i);
                first = false;
                u32 hi = (fn->line1 - fn->line0 > 400) ? fn->line0 + 400 : fn->line1;
                for (u32 ln = fn->line0; ln <= hi; ++ln) {
                        int len;
                        char const *s = SourceLine(fn->mod, ln, &len);
                        char buf[1024];
                        len = (len >= (int)sizeof buf) ? (int)sizeof buf - 1 : len;
                        if (s != NULL) {
                                memcpy(buf, s, len);
                        }
                        buf[(s != NULL) ? len : 0] = '\0';
                        fprintf(f, "%s", (ln > fn->line0) ? "," : "");
                        JsonStr(f, buf);
                }
                fputc(']', f);
        }

        fprintf(f, "},\"files\":{");
        {
                vec(Module const *) seen = {0};
                bool firstf = true;
                for (usize i = 0; i < vN(M.lines); ++i) {
                        Line const *l = v_(M.lines, i);
                        Module const *mod = l->mod;
                        bool dup = false;
                        if (mod == NULL || mod->source == NULL || (l->total == 0 && l->alloc == 0 && l->retained == 0)) {
                                continue;
                        }
                        for (usize k = 0; k < vN(seen); ++k) {
                                dup = dup || (v__(seen, k) == mod);
                        }
                        if (dup) {
                                continue;
                        }
                        xvP(seen, mod);
                        fprintf(f, "%s", firstf ? "" : ",");
                        JsonStr(f, v_(M.funcs, l->func)->path);
                        fputc(':', f);
                        JsonStr(f, mod->source);
                        firstf = false;
                }
                xvF(seen);
        }
        fputc('}', f);

        if (!NoJIT) {
                fprintf(f, ",\"jit_stats\":");
                jit_stats_json(M.ty, f);
        }

        ExportDeopts(f);

        fprintf(f, "}\n");
}

static bool
RecordTo(char const *path)
{
        struct stat st;
        char old[4096];

        if (
                (stat(path, &st) == 0)
             && S_ISREG(st.st_mode)
             && (st.st_size > 0)
             && (ty_snprintf(old, sizeof old, "%s.old", path) < (int)sizeof old)
        ) {
                rename(path, old);
        }

        FILE *f = fopen(path, "w");

        if (f == NULL) {
                fprintf(stderr, "ty: cannot write %s: %s\n", path, strerror(errno));
                return false;
        }

        ExportJson(f);
        DataSize = ftell(f);
        fclose(f);

        return true;
}

static void
RecordData(void)
{
        if (DataPath != NULL && !RecordTo(DataPath)) {
                DataPath = NULL;
        }
}

static void
ResetModel(void)
{
        for (usize i = 0; i < vN(M.funcs); ++i) {
                free(v_(M.funcs, i)->name);
        }

        free(M.site_tab);
        free(M.line_tab);
        free(M.edge_tab);
        free(M.sym_self);
        free(M.thread_total);
        xvF(M.funcs);
        xvF(M.lines);
        xvF(M.sites);
        xvF(M.edges);

        memset(&M, 0, sizeof M);
}

void
prof_report(Ty *ty)
{
        if (!Started || Reported) {
                return;
        }

        Reported = true;

        StopSampling();

        if (ProfTarget == NULL) {
                ProfTarget = getenv("TY_PROF_TARGET");
        }

        BuildModel(ty);
        RecordData();

        if (!Quiet) {
                Summary();
        }
}

void
prof_poll(Ty *ty)
{
        if (!atomic_exchange(&ProfWantReport, false) || !Started || Reported) {
                return;
        }

        DrainAll();
        StopWall = NowNs();

        pthread_mutex_lock(&DrainLock);
        BuildModel(ty);
        Summary();
        ResetModel();
        pthread_mutex_unlock(&DrainLock);
}

typedef struct jv Jv;

struct jv {
        char type;
        double num;
        char *str;
        Jv **items;
        char **keys;
        usize n;
};

static Jv JNull = { .type = 'n' };

static void
JSkip(char const **p)
{
        while (**p == ' ' || **p == '\n' || **p == '\t' || **p == '\r') {
                *p += 1;
        }
}

static Jv *JParse(char const **p);

static char *
JString(char const **p)
{
        byte_vector b = {0};

        *p += 1;

        while (**p != '\0' && **p != '"') {
                if (**p == '\\') {
                        *p += 1;
                        switch (**p) {
                        case 'n': xvP(b, '\n'); break;
                        case 't': xvP(b, '\t'); break;
                        case 'r': xvP(b, '\r'); break;
                        case 'u':
                                {
                                        unsigned c = 0;
                                        sscanf(*p + 1, "%4x", &c);
                                        xvP(b, (c < 0x80) ? (char)c : '?');
                                        *p += 4;
                                }
                                break;
                        default:  xvP(b, **p); break;
                        }
                } else {
                        xvP(b, **p);
                }
                *p += 1;
        }

        if (**p == '"') {
                *p += 1;
        }

        xvP(b, '\0');

        return vv(b);
}

static Jv *
JParse(char const **p)
{
        Jv *v = calloc(1, sizeof *v);

        JSkip(p);

        switch (**p) {
        case '{':
        case '[':
                {
                        bool obj = (**p == '{');
                        usize cap = 0;
                        v->type = obj ? 'o' : 'a';
                        *p += 1;
                        for (;;) {
                                JSkip(p);
                                if (**p == '}' || **p == ']') {
                                        *p += 1;
                                        break;
                                }
                                if (**p == ',') {
                                        *p += 1;
                                        continue;
                                }
                                if (**p == '\0') {
                                        break;
                                }
                                if (v->n == cap) {
                                        cap = (cap == 0) ? 8 : cap * 2;
                                        v->items = realloc(v->items, cap * sizeof *v->items);
                                        v->keys = realloc(v->keys, cap * sizeof *v->keys);
                                }
                                v->keys[v->n] = NULL;
                                if (obj) {
                                        v->keys[v->n] = JString(p);
                                        JSkip(p);
                                        if (**p == ':') {
                                                *p += 1;
                                        }
                                }
                                v->items[v->n++] = JParse(p);
                        }
                }
                break;

        case '"':
                v->type = 's';
                v->str = JString(p);
                break;

        case 't':
                v->type = 'b';
                v->num = 1;
                *p += 4;
                break;

        case 'f':
                v->type = 'b';
                *p += 5;
                break;

        case 'n':
                v->type = 'n';
                *p += 4;
                break;

        default:
                {
                        char *end;
                        v->type = 'd';
                        v->num = strtod(*p, &end);
                        *p = (end > *p) ? end : *p + 1;
                }
                break;
        }

        return v;
}

static Jv const *
JGet(Jv const *o, char const *key)
{
        if (o == NULL || o->type != 'o') {
                return &JNull;
        }

        for (usize i = 0; i < o->n; ++i) {
                if (strcmp(o->keys[i], key) == 0) {
                        return o->items[i];
                }
        }

        return &JNull;
}

static double
JNum(Jv const *o, char const *key)
{
        return JGet(o, key)->num;
}

static char const *
JStr(Jv const *o, char const *key)
{
        Jv const *v = JGet(o, key);
        return (v->type == 's') ? v->str : "";
}

static Jv *
JLoad(char const *path)
{
        FILE *f = fopen(path, "r");

        if (f == NULL) {
                fprintf(stderr, "ty: cannot read %s: %s\n", path, strerror(errno));
                exit(1);
        }

        byte_vector b = {0};
        char buf[65536];
        usize n;

        while ((n = fread(buf, 1, sizeof buf, f)) > 0) {
                xvPn(b, buf, n);
        }

        fclose(f);
        xvP(b, '\0');

        char const *p = vv(b);
        Jv *v = JParse(&p);

        if (v->type != 'o' || JGet(v, "ty-prof")->type != 'd') {
                fprintf(stderr, "ty: %s is not a ty profile\n", path);
                exit(1);
        }

        return v;
}

typedef struct {
        char const *name;
        char const *file;
        char const *text;
        int line;
        double a_self;
        double b_self;
        double a_total;
        double b_total;
        double a_cnt;
        double b_cnt;
        double z;
} DiffRow;

static char const *DiffTargetA;
static char const *DiffTargetB;

static bool
SameFile(char const *a, char const *b)
{
        if (strcmp(a, b) == 0) {
                return true;
        }

        return (strcmp(a, DiffTargetA) == 0 || strcmp(a, DiffTargetB) == 0)
            && (strcmp(b, DiffTargetA) == 0 || strcmp(b, DiffTargetB) == 0);
}

static double
ZScore(double c1, double n1, double c2, double n2)
{
        if (n1 <= 0 || n2 <= 0) {
                return 0.0;
        }

        double p1 = c1 / n1;
        double p2 = c2 / n2;
        double p = (c1 + c2) / (n1 + n2);
        double se = sqrt(p * (1.0 - p) * (1.0 / n1 + 1.0 / n2));

        return (se > 0) ? (p2 - p1) / se : 0.0;
}

static int
ByDiffImpact(void const *a_, void const *b_)
{
        DiffRow const *a = a_;
        DiffRow const *b = b_;
        double x = fabs(a->b_self - a->a_self);
        double y = fabs(b->b_self - b->a_self);
        return (x < y) - (x > y);
}

static void
QtyOf(char *buf, usize n, double w, char const *unit)
{
        if (strcmp(unit, "ns") == 0) {
                if (fabs(w) >= 1e9) {
                        ty_snprintf(buf, n, "%.2fs", w / 1e9);
                } else {
                        ty_snprintf(buf, n, "%.1fms", w / 1e6);
                }
        } else {
                ty_snprintf(buf, n, "%.3g", w);
        }
}

static void
DiffSection(FILE *out, char const *title, DiffRow *rows, usize n, double ta, double tb, double na, double nb, char const *unit)
{
        qsort(rows, n, sizeof *rows, ByDiffImpact);

        fprintf(out, "\n%s%s%s%s\n", C(1), C(95), title, C(0));
        fprintf(out, "%s     before      after     change   share%%  before→after z(share)%s\n", C(90), C(0));

        int shown = 0;

        for (usize i = 0; i < n && shown < TopN; ++i) {
                DiffRow const *r = &rows[i];
                double d = r->b_self - r->a_self;

                if (fabs(d) < 0.002 * (ta > tb ? ta : tb)) {
                        continue;
                }

                char a[32];
                char b[32];
                char c[32];
                QtyOf(a, sizeof a, r->a_self, unit);
                QtyOf(b, sizeof b, r->b_self, unit);
                QtyOf(c + 1, sizeof c - 1, fabs(d), unit);
                c[0] = (d < 0) ? '-' : '+';

                bool sig = fabs(r->z) >= 3.0;
                char const *col = !sig ? C(90) : (d < 0) ? C(92) : C(91);

                fprintf(
                        out,
                        "  %10s %10s %s%10s%s  %5.1f→%-5.1f  %s%5.1f%s%s  ",
                        a,
                        b,
                        col,
                        c,
                        C(0),
                        (ta > 0) ? 100.0 * r->a_self / ta : 0.0,
                        (tb > 0) ? 100.0 * r->b_self / tb : 0.0,
                        col,
                        r->z,
                        sig ? "*" : " ",
                        C(0)
                );

                if (r->text != NULL) {
                        fprintf(out, "%s%s:%d%s  ", C(94), r->file, r->line, C(0));
                        fprintf(out, "%.*s", (int)strspn(r->text, " \t") > 0 ? 60 : 60, r->text + strspn(r->text, " \t"));
                } else {
                        fprintf(out, "%s%s%s %s%s:%d%s", C(1), r->name, C(0), C(90), r->file, r->line, C(0));
                }

                fputc('\n', out);
                shown += 1;
        }
}

static void
Diff(char const *pa, char const *pb)
{
        Jv *A = JLoad(pa);
        Jv *B = JLoad(pb);
        FILE *out = (ProfileOut != NULL) ? ProfileOut : stdout;
        char const *unit = JStr(B, "unit");
        double ta = JNum(A, "total");
        double tb = JNum(B, "total");
        double na = JNum(A, "samples");
        double nb = JNum(B, "samples");
        char qa[32];
        char qb[32];

        Out = out;

        if (na == 0 || nb == 0) {
                fprintf(stderr, "ty: %s has no samples\n", (na == 0) ? pa : pb);
                exit(1);
        }

        QtyOf(qa, sizeof qa, ta, unit);
        QtyOf(qb, sizeof qb, tb, unit);

        fprintf(out, "%s%sprofile diff%s  %s → %s\n", C(1), C(96), C(0), pa, pb);

        if (strcmp(JStr(A, "mode"), JStr(B, "mode")) != 0 || strcmp(JStr(A, "unit"), unit) != 0) {
                fprintf(out, "%swarning: profiles use different modes (%s vs %s); comparing shares only%s\n", C(93), JStr(A, "mode"), JStr(B, "mode"), C(0));
        }

        double change = (ta > 0) ? 100.0 * (tb - ta) / ta : 0.0;

        fprintf(
                out,
                "total %s: %s → %s  %s%+.1f%%%s %s(%0.f vs %0.f samples; one run each, so compare against run-to-run noise)%s\n",
                strcmp(unit, "ns") == 0 ? "time" : unit,
                qa,
                qb,
                (change < 0) ? C(92) : C(91),
                change,
                C(0),
                C(90),
                na,
                nb,
                C(0)
        );

        DiffTargetA = JStr(A, "target_file");
        DiffTargetB = JStr(B, "target_file");

        Jv const *ca = JGet(A, "categories");
        Jv const *cb = JGet(B, "categories");

        fprintf(out, "\n%s%sBy category%s\n", C(1), C(95), C(0));

        for (usize i = 0; i < cb->n; ++i) {
                double a = JNum(ca, cb->keys[i]);
                double b = cb->items[i]->num;
                if (a == 0 && b == 0) {
                        continue;
                }
                char x[32];
                char y[32];
                QtyOf(x, sizeof x, a, unit);
                QtyOf(y, sizeof y, b, unit);
                fprintf(
                        out,
                        "  %10s → %-10s %s%+7.1f%%%s  %s\n",
                        x,
                        y,
                        (b < a) ? C(92) : C(91),
                        (a > 0) ? 100.0 * (b - a) / a : 100.0,
                        C(0),
                        cb->keys[i]
                );
        }

        Jv const *fa = JGet(A, "functions");
        Jv const *fb = JGet(B, "functions");
        vec(DiffRow) rows = {0};

        for (int side = 0; side < 2; ++side) {
                Jv const *src = side ? fb : fa;
                for (usize i = 0; i < src->n; ++i) {
                        Jv const *f = src->items[i];
                        char const *name = JStr(f, "name");
                        char const *file = JStr(f, "file");
                        DiffRow *row = NULL;
                        for (usize k = 0; k < vN(rows); ++k) {
                                DiffRow *r = v_(rows, k);
                                if (strcmp(r->name, name) == 0 && SameFile(r->file, file)) {
                                        row = r;
                                        break;
                                }
                        }
                        if (row == NULL) {
                                xvP(rows, ((DiffRow) { .name = name, .file = file, .line = (int)JNum(f, "line") }));
                                row = vvL(rows);
                        }
                        if (side) {
                                row->b_self += JNum(f, "self");
                                row->b_total += JNum(f, "total");
                                row->b_cnt += JNum(f, "self_samples");
                        } else {
                                row->a_self += JNum(f, "self");
                                row->a_total += JNum(f, "total");
                                row->a_cnt += JNum(f, "self_samples");
                        }
                }
        }

        for (usize k = 0; k < vN(rows); ++k) {
                DiffRow *r = v_(rows, k);
                r->z = ZScore(r->a_cnt, na, r->b_cnt, nb);
        }

        DiffSection(out, "Functions (self time; * = significant at |z|>=3)", vv(rows), vN(rows), ta, tb, na, nb, unit);

        vec(DiffRow) lrows = {0};

        for (int side = 0; side < 2; ++side) {
                Jv const *P = side ? B : A;
                Jv const *fs = JGet(P, "functions");
                Jv const *ls = JGet(P, "lines");
                for (usize i = 0; i < ls->n; ++i) {
                        Jv const *l = ls->items[i];
                        int fi = (int)JNum(l, "func");
                        Jv const *f = (fi >= 0 && (usize)fi < fs->n) ? fs->items[fi] : &JNull;
                        char const *file = JStr(f, "file");
                        char const *text = JStr(l, "text");
                        DiffRow *row = NULL;
                        for (usize k = 0; k < vN(lrows); ++k) {
                                DiffRow *r = v_(lrows, k);
                                if (SameFile(r->file, file) && strcmp(r->text, text) == 0 && (side == 0 || r->b_self == 0)) {
                                        row = r;
                                        break;
                                }
                        }
                        if (row == NULL) {
                                xvP(lrows, ((DiffRow) {
                                        .name = JStr(f, "name"),
                                        .file = file,
                                        .text = text,
                                        .line = (int)JNum(l, "line")
                                }));
                                row = vvL(lrows);
                        }
                        if (side) {
                                row->b_self += JNum(l, "self");
                                row->line = (int)JNum(l, "line");
                        } else {
                                row->a_self += JNum(l, "self");
                        }
                }
        }

        for (usize k = 0; k < vN(lrows); ++k) {
                DiffRow *r = v_(lrows, k);
                r->z = ZScore(
                        (ta > 0) ? r->a_self * na / ta : 0,
                        na,
                        (tb > 0) ? r->b_self * nb / tb : 0,
                        nb
                );
        }

        DiffSection(out, "Lines (self time, matched by source text)", vv(lrows), vN(lrows), ta, tb, na, nb, unit);

        double aa = JNum(A, "alloc_total");
        double ab = JNum(B, "alloc_total");

        if (aa > 0 || ab > 0) {
                char x[32];
                char y[32];
                FmtBytes(x, sizeof x, (u64)aa);
                FmtBytes(y, sizeof y, (u64)ab);
                fprintf(out, "\nallocated: %s → %s (%+.1f%%)\n", x, y, (aa > 0) ? 100.0 * (ab - aa) / aa : 0.0);
        }

        fputc('\n', out);
}

int
prof_diff_main(int argc, char **argv)
{
        char const *paths[2];
        int n = 0;

        for (int i = 1; i < argc; ++i) {
                if (ColorOption(argv[i]) || prof_option(argv[i])) {
                        continue;
                }
                if (argv[i][0] == '-' || n == 2) {
                        n = -1;
                        break;
                }
                paths[n++] = argv[i];
        }

        if (n != 2) {
                fprintf(stderr, "usage: ty --prof-diff OLD NEW [--prof-top=N]\n");
                return 1;
        }

        ProfileOut   = stdout;
        ColorProfile = ColorFor(stdout);
        Diff(paths[0], paths[1]);

        return 0;
}

void
prof_first_call(int *info)
{
        pthread_mutex_lock(&InfoLock);

        if ((InfoN + 1) * 2 >= InfoCap) {
                u64 cap = (InfoCap == 0) ? 1024 : InfoCap * 2;
                int **tab = calloc(cap, sizeof *tab);
                for (u64 i = 0; i < InfoCap; ++i) {
                        if (Infos[i] != NULL) {
                                u64 j = Mix(0, (uptr)Infos[i]) & (cap - 1);
                                while (tab[j] != NULL) {
                                        j = (j + 1) & (cap - 1);
                                }
                                tab[j] = Infos[i];
                        }
                }
                free(Infos);
                Infos = tab;
                InfoCap = cap;
        }

        u64 j = Mix(0, (uptr)info) & (InfoCap - 1);

        while (Infos[j] != NULL && Infos[j] != info) {
                j = (j + 1) & (InfoCap - 1);
        }

        if (Infos[j] == NULL) {
                Infos[j] = info;
                InfoN += 1;
        }

        pthread_mutex_unlock(&InfoLock);
}

static void
AttachCalls(void)
{
        pthread_mutex_lock(&InfoLock);

        for (u64 i = 0; i < InfoCap; ++i) {
                if (Infos[i] == NULL) {
                        continue;
                }

                Value f = { .type = VALUE_FUNCTION, .info = Infos[i] };
                Expr const *e = from_eval(&f) ? NULL : expr_of(&f);
                u64 n;

                memcpy(&n, (char const *)Infos[i] + FUN_CALLS, sizeof n);

                if (e == NULL || n == 0) {
                        continue;
                }

                for (usize k = 0; k < vN(M.funcs); ++k) {
                        Func *fn = v_(M.funcs, k);
                        if (fn->fexpr == e) {
                                fn->calls += n;
                                break;
                        }
                }
        }

        pthread_mutex_unlock(&InfoLock);
}


static void
LiveGrow(void)
{
        u64 cap = (LiveCap == 0) ? 4096 : LiveCap * 2;
        LiveObj *tab = calloc(cap, sizeof *tab);
        u64 used = 0;

        for (u64 i = 0; i < LiveCap; ++i) {
                if (Live[i].a != NULL && Live[i].a != LIVE_TOMB) {
                        u64 j = Mix(0, (uptr)Live[i].a) & (cap - 1);
                        while (tab[j].a != NULL) {
                                j = (j + 1) & (cap - 1);
                        }
                        tab[j] = Live[i];
                        used += 1;
                }
        }

        free(Live);
        Live = tab;
        LiveCap = cap;
        LiveUsed = used;
}

void
prof_alloc_bind(struct alloc *a)
{
        u64 seq = ProfPending;

        ProfPending = 0;

        if (!Started || Reported) {
                return;
        }

        pthread_mutex_lock(&LiveLock);

        if ((LiveUsed + 1) * 2 >= LiveCap) {
                LiveGrow();
        }

        u64 j = Mix(0, (uptr)a) & (LiveCap - 1);

        while (Live[j].a != NULL && Live[j].a != LIVE_TOMB) {
                j = (j + 1) & (LiveCap - 1);
        }

        LiveUsed += (Live[j].a == NULL);
        Live[j] = (LiveObj) { .a = a, .seq = seq, .epoch = GcEpoch };

        atomic_fetch_add_explicit(&ProfLiveN, 1, memory_order_relaxed);

        pthread_mutex_unlock(&LiveLock);
}

void
prof_free(struct alloc *a)
{
        pthread_mutex_lock(&LiveLock);

        if (LiveCap > 0) {
                u64 j = Mix(0, (uptr)a) & (LiveCap - 1);
                while (Live[j].a != NULL) {
                        if (Live[j].a == a) {
                                Live[j].a = LIVE_TOMB;
                                atomic_fetch_sub_explicit(&ProfLiveN, 1, memory_order_relaxed);
                                break;
                        }
                        j = (j + 1) & (LiveCap - 1);
                }
        }

        pthread_mutex_unlock(&LiveLock);
}

static u64
ObjSize(struct alloc const *a)
{
        u64 n = a->size;

        switch (a->type) {
        case GC_ARRAY:
                n += ((Array const *)a->data)->capacity * sizeof (Value);
                break;
        case GC_BLOB:
                n += ((Blob const *)a->data)->capacity;
                break;
        }

        return n;
}

int
prof_module_begin(char const *name, char const *path, char const *source)
{
        u32 lines = 1;

        for (char const *c = source; c != NULL && *c != '\0'; ++c) {
                lines += (*c == '\n');
        }

        xvP(Mods, ((ModLoad) {
                .name   = strdup(name),
                .path   = strdup((path != NULL) ? path : ""),
                .lines  = lines,
                .parent = ModTop,
                .t0     = NowNs()
        }));

        ModTop = vN(Mods) - 1;

        return ModTop;
}

void
prof_module_compiled(int id)
{
        if (id >= 0 && id < (int)vN(Mods)) {
                v_(Mods, id)->t1 = NowNs();
        }
}

void
prof_module_done(int id)
{
        if (id < 0 || id >= (int)vN(Mods)) {
                return;
        }

        ModLoad *m = v_(Mods, id);

        m->t2 = NowNs();
        ModTop = m->parent;

        if (m->parent >= 0) {
                ModLoad *p = v_(Mods, m->parent);
                if (p->t1 == 0) {
                        p->child_compile += m->t2 - m->t0;
                }
                p->child_total += m->t2 - m->t0;
        }
}

void
prof_gc_done(u64 before, u64 after, u64 ns)
{
        GcEpoch += 1;

        if (Started && !Reported) {
                xvP(HeapTimeT, NowNs() - StartWall);
                xvP(HeapTimeB, after);
        }

        GcStats.n += 1;
        GcStats.total += ns;
        GcStats.max = (ns > GcStats.max) ? ns : GcStats.max;
        GcStats.freed += (before > after) ? before - after : 0;
        GcStats.peak = (before > GcStats.peak) ? before : GcStats.peak;
}

static char AttachReq[128];
static char AttachPrefix[512];

static void
OnAttachPoke(void)
{
        struct stat st;

        if (
                !atomic_load(&Running)
             && (stat(AttachReq, &st) != 0 || st.st_uid != getuid())
        ) {
                return;
        }

        vm_attach_request();
}

void
prof_attach_init(Ty *ty)
{
        char const *off = getenv("TY_ATTACH");

        if (off != NULL && strcmp(off, "0") == 0) {
                return;
        }

        ty_snprintf(AttachReq, sizeof AttachReq, "/tmp/ty-prof-attach-%d.req", (int)getpid());
        prof_os_attach_listen(OnAttachPoke);
        prof_thread_start(ty);
}

static void
ReadAttachRequest(void)
{
        char const *path = AttachReq;
        char line[1024];

        ty_snprintf(AttachPrefix, sizeof AttachPrefix, "/tmp/ty-prof-%d-%llu", (int)getpid(), (unsigned long long)(NowNs() / 1000000));

        Mode = PK_CPU;
        ProfileSampleInterval = 0;
        Hz = 999;
        AttachColor = false;
        AttachCols = 0;
        ty_snprintf(AttachRecord, sizeof AttachRecord, "ty-prof.data");

        FILE *f = fopen(path, "r");

        if (f == NULL) {
                return;
        }

        while (fgets(line, sizeof line, f) != NULL) {
                line[strcspn(line, "\n")] = '\0';
                if (strncmp(line, "mode=wall", 9) == 0) {
                        Mode = PK_WALL;
                } else if (strncmp(line, "event=", 6) == 0) {
                        SetEvent(line + 6);
                } else if (strncmp(line, "hz=", 3) == 0 && atoll(line + 3) > 0) {
                        ProfileSampleInterval = 1000000000ULL / (u64)atoll(line + 3);
                } else if (strncmp(line, "prefix=", 7) == 0) {
                        ty_snprintf(AttachPrefix, sizeof AttachPrefix, "%s", line + 7);
                } else if (strncmp(line, "record=", 7) == 0) {
                        ty_snprintf(AttachRecord, sizeof AttachRecord, "%s", line + 7);
                } else if (strncmp(line, "color=", 6) == 0) {
                        AttachColor = atoi(line + 6) != 0;
                } else if (strncmp(line, "cols=", 5) == 0) {
                        AttachCols = atoi(line + 5);
                }
        }

        fclose(f);
        unlink(path);
}

static void
ResetRun(void)
{
        ResetModel();

        vN(Keys) = 0;
        vN(Stacks) = 0;
        free(Table);
        Table = NULL;
        TableCap = 0;
        Timeline.n = 0;
        vN(SeqStack) = 0;
        vN(HeapTimeT) = 0;
        vN(HeapTimeB) = 0;
        memset(&GcStats, 0, sizeof GcStats);

        atomic_store(&HandlerNs, 0);
        atomic_store(&Dropped, 0);
        atomic_store(&Busy, 0);
}

static void
WriteAs(char const *ext, void (*fn)(FILE *))
{
        char path[640];
        ty_snprintf(path, sizeof path, "%s%s", AttachPrefix, ext);

        FILE *f = fopen(path, "w");

        if (f != NULL) {
                fn(f);
                fclose(f);
        }
}

static void
AttachWrite(void)
{
        char path[640];

        ty_snprintf(path, sizeof path, "%s.data", AttachPrefix);

        FILE *f = fopen(path, "w");

        if (f != NULL) {
                ExportJson(f);
                DataSize = ftell(f);
                fclose(f);
                DataPath = AttachRecord;
        } else {
                DataPath = NULL;
        }

        ty_snprintf(path, sizeof path, "%s.txt", AttachPrefix);

        if ((f = fopen(path, "w")) != NULL) {
                FILE *saved = ProfileOut;
                bool color = ColorProfile;
                ProfileOut = f;
                ColorProfile = AttachColor;
                Summary();
                ProfileOut = saved;
                ColorProfile = color;
                fclose(f);
        }
}

static void
Done(FILE *f)
{
        fprintf(f, "%d\n", (int)getpid());
}

void
prof_attach_toggle(Ty *ty)
{
        if (!atomic_load(&Running)) {
                ReadAttachRequest();
                ResetRun();
                Attached = true;
                StartRun(ty);
                return;
        }

        StopSampling();

        pthread_mutex_lock(&DrainLock);
        BuildModel(ty);
        AttachWrite();
        WriteAs(".done", Done);
        pthread_mutex_unlock(&DrainLock);

        ResetRun();
        Started = false;
        VmPoll.prof = 0;
}

void
prof_attach_exit(Ty *ty)
{
        if (Attached && atomic_load(&Running)) {
                prof_attach_toggle(ty);
        }
}

static bool
FileExists(char const *path)
{
        struct stat st;
        return stat(path, &st) == 0;
}

static _Atomic bool AttachStopEarly;

static void
OnAttachInterrupt(int _)
{
        atomic_store(&AttachStopEarly, true);
}

int
prof_attach_main(int argc, char **argv)
{
        pid_t pid = 0;
        double secs = 10.0;
        int npos = 0;

        ProfileOut = stdout;

        for (int i = 1; i < argc; ++i) {
                char const *a = argv[i];
                if (ColorOption(a)) {
                        continue;
                }
                if (prof_option(a)) {
                        continue;
                }
                if (a[0] == '-' || npos == 2) {
                        fprintf(stderr, "ty --prof-attach: unexpected argument %s\n", a);
                        return 2;
                }
                if (npos++ == 0) {
                        pid = (pid_t)atol(a);
                } else {
                        secs = atof(a);
                }
        }

        if (pid <= 0 || secs <= 0 || Mode == PK_OPS) {
                fprintf(
                        stderr,
                        "usage: ty --prof-attach PID [SECONDS] [--prof=cpu[:HZ]|wall[:HZ]|EVENT]\n"
                        "                             [--prof-out=FILE] [--prof-summary=FILE]\n"
                );
                return 2;
        }

        char req[128];
        char prefix[256];
        ty_snprintf(req, sizeof req, "/tmp/ty-prof-attach-%d.req", (int)pid);
        ty_snprintf(prefix, sizeof prefix, "/tmp/ty-prof-%d-attach-%d", (int)pid, (int)getpid());

        FILE *f = fopen(req, "w");
        if (f == NULL) {
                fprintf(stderr, "ty: cannot write %s: %s\n", req, strerror(errno));
                return 1;
        }
        fprintf(f, "prefix=%s\n", prefix);
        if (Mode == PK_WALL) {
                fprintf(f, "mode=wall\n");
        }
        if (Mode == PK_EVENT) {
                fprintf(f, "event=%s\n", EventSpec);
        }
        if (ProfileSampleInterval > 0) {
                fprintf(f, "hz=%llu\n", (unsigned long long)(1000000000ULL / ProfileSampleInterval));
        }
        {
                int rows;
                int cols;
                if (get_terminal_size(fileno(ProfileOut), &rows, &cols)) {
                        fprintf(f, "cols=%d\n", cols);
                }
        }
        fprintf(f, "color=%d\n", ColorFor(ProfileOut));
        fprintf(f, "record=%s\n", DataPath);
        fclose(f);

        if (prof_os_attach_poke(pid) != 0) {
                fprintf(stderr, "ty: cannot signal %d: %s\n", (int)pid, strerror(errno));
                unlink(req);
                return 1;
        }

        signal(SIGINT, OnAttachInterrupt);
        fprintf(stderr, "ty: sampling pid %d for %.1fs (Ctrl-C to stop early)...\n", (int)pid, secs);

        u64 until = NowNs() + (u64)(secs * 1e9);
        while (NowNs() < until && !atomic_load(&AttachStopEarly)) {
                struct timespec ts = { 0, 50 * 1000000 };
                nanosleep(&ts, NULL);
                if (kill(pid, 0) != 0) {
                        break;
                }
        }

        prof_os_attach_poke(pid);

        char done[300];
        ty_snprintf(done, sizeof done, "%s.done", prefix);

        u64 deadline = NowNs() + 60000000000ULL;
        while (!FileExists(done) && NowNs() < deadline) {
                struct timespec ts = { 0, 50 * 1000000 };
                nanosleep(&ts, NULL);
                if (kill(pid, 0) != 0 && !FileExists(done)) {
                        struct timespec grace = { 0, 300 * 1000000 };
                        nanosleep(&grace, NULL);
                        break;
                }
        }

        if (!FileExists(done)) {
                fprintf(
                        stderr,
                        "ty: no report from %d. It reads the request the next time it runs Ty code; "
                        "a process blocked in a long system call answers once it wakes up.\n",
                        (int)pid
                );
                unlink(req);
                return 1;
        }

        char from[320];
        char buf[65536];
        usize n;

        ty_snprintf(from, sizeof from, "%s.data", prefix);

        FILE *in = fopen(from, "r");
        struct stat st;
        char old[4096];

        if (
                (in != NULL)
             && (stat(DataPath, &st) == 0)
             && S_ISREG(st.st_mode)
             && (st.st_size > 0)
             && (ty_snprintf(old, sizeof old, "%s.old", DataPath) < (int)sizeof old)
        ) {
                rename(DataPath, old);
        }

        FILE *dst = (in != NULL) ? fopen(DataPath, "w") : NULL;

        while (in != NULL && dst != NULL && (n = fread(buf, 1, sizeof buf, in)) > 0) {
                fwrite(buf, 1, n, dst);
        }

        if (in != NULL && dst == NULL) {
                fprintf(stderr, "ty: cannot write %s: %s\n", DataPath, strerror(errno));
        }

        if (in != NULL) {
                fclose(in);
        }

        if (dst != NULL) {
                fclose(dst);
        }

        unlink(from);

        ty_snprintf(from, sizeof from, "%s.txt", prefix);

        in = fopen(from, "r");

        while (!Quiet && in != NULL && (n = fread(buf, 1, sizeof buf, in)) > 0) {
                fwrite(buf, 1, n, ProfileOut);
        }

        if (in != NULL) {
                fclose(in);
        }

        unlink(from);
        unlink(done);

        return 0;
}

void
prof_set_target(char const *path)
{
        ProfTarget = path;
}

#else

void prof_first_call(int *info) {}
void prof_throw(Ty *ty, char const *ip) {}
void prof_jit_decline(Value const *f, char const *why, i32 off) {}
void prof_jit_deopt(Ty *ty, Frame const *frame, i32 off) {}
void prof_jit_despecialize(Value const *f, u32 deopts) {}
char const *prof_symbolize(uptr addr) { return NULL; }
char const *prof_jit_ip(Ty *ty, void const *ra) { return NULL; }
int prof_module_begin(char const *name, char const *path, char const *source) { return -1; }
void prof_module_compiled(int id) {}
void prof_module_done(int id) {}

#endif

/* vim: set sts=8 sw=8 expandtab: */
