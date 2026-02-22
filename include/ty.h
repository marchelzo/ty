#ifndef TY_H_INCLUDED
#define TY_H_INCLUDED

#include <assert.h>
#include <inttypes.h>
#include <setjmp.h>
#include <stdalign.h>
#include <stdbool.h>
#include <stddef.h>
#include <stdlib.h>
#include <string.h>

#include <pcre2.h>
#include <ffi.h>
#include "libco.h"

#include "panic.h"
#include "polyfill_stdatomic.h"
#include "tthread.h"
#include "vec.h"
#include "log.h"
#include "xd.h"

#define TY_MAX_CALL_DEPTH (1UL << 9)
#define TY_TMP_BUF_COUNT 3

#if defined(TY_RELEASE)
 #define CO_STACK_SIZE (1UL << 22)
#else
 #define CO_STACK_SIZE (1UL << 24)
#endif

typedef vec(struct alloc *) AllocList;
typedef vec(char *)         CallStack;
typedef vec(void *)         ContextVector;
typedef vec(cothread_t)     CoThreadVector;
typedef vec(Constraint)     ConstraintVector;
typedef vec(Frame)          FrameStack;
typedef vec(Value)          GCRootSet;
typedef vec(Value *)        GCWorkStack;
typedef vec(Refinement)     RefinementVector;
typedef vec(Scope *)        ScopeVector;
typedef vec(usize)          SPStack;
typedef vec(struct sigfn)   SigfnStack;
typedef vec(Target)         TargetStack;
typedef vec(struct token)   TokenVector;
typedef vec(struct try *)   TryStack;
typedef vec(Type *)         TypeVector;
typedef vec(Value)          ValueVector;
typedef ValueVector         ValueStack;
typedef vec(Class *)        ClassVector;
typedef vec(Symbol *)       symbol_vector;
typedef vec(TySavePoint *)  TySavePointVector;

enum { INTERN_TABLE_SIZE = 256 };

typedef struct {
        i64 id;
        char const *name;
        u64 hash;
        void *data;
} InternEntry;

typedef vec(InternEntry) InternBucket;

typedef struct {
        InternBucket set[INTERN_TABLE_SIZE];
        vec(u32) index;
} InternSet;

typedef struct location {
        u32 line;
        u32 col;
        u32 byte;
        u32 tok;
        char const *s;
} Location;

typedef struct {
        u64 key;
        i32 ref;
} CacheEntry;

typedef vec(CacheEntry) DispatchCache;

struct itable {
        i32Vector   ids;
        ValueVector values;
};

struct alloc {
        union {
                struct {
                        u8 type;
                        atomic_bool mark;
                        atomic_uint_least16_t hard;
                        u32 size;
                };
                void const * restrict padding;
        };
        char data[];
};

typedef struct arena Arena;

struct arena {
        char *base;
        char *beg;
        char *end;
        Arena *next;
        bool gc;
        bool immortal;
};

typedef struct array {
        Value *items;
        usize count;
        usize capacity;
} Array;

typedef struct blob {
        unsigned char *items;
        usize count;
        usize capacity;
} Blob;

typedef struct regex {
        pcre2_code *pcre2;
        char const *pattern;
        bool gc;
        bool detailed;
        u32 ncap;
} Regex;

typedef struct {
        char *name;
        char *proto;
        char *doc;
        i32 class;
} FunUserInfo;

struct refinement {
        Symbol *var;
        Type *t0;
        bool active;
        bool mut;
};

typedef struct object TyObject;

typedef struct dict Dict;
typedef struct dict_item DictItem;

typedef struct generator Generator;
typedef struct thread Thread;
typedef struct channel Channel;
typedef struct chanval ChanVal;

typedef struct compiler_state CompileState;

enum { CTX_EXPR, CTX_TYPE };
enum { FT_NONE, FT_FUNC, FT_GEN, FT_PATTERN };

enum {
        MT_NONE,
        MT_DFL    = (1 << 0),
        MT_GET    = (1 << 1),
        MT_SET    = (1 << 2),
        MT_2OP    = (1 << 3),
        MT_STATIC = (1 << 4)
};

enum {
        VALUE_ZERO             ,
        VALUE_FUNCTION = 1     ,
        VALUE_BOUND_FUNCTION   ,
        VALUE_METHOD           ,
        VALUE_BUILTIN_FUNCTION ,
        VALUE_BUILTIN_METHOD   ,
        VALUE_FOREIGN_FUNCTION ,
        VALUE_NATIVE_FUNCTION  ,
        VALUE_CLASS            ,
        VALUE_GENERATOR        ,
        VALUE_TAG              ,
        VALUE_ARRAY            ,
        VALUE_DICT             ,
        VALUE_OBJECT           ,
        VALUE_OPERATOR         ,
        VALUE_TYPE             ,
        VALUE_REGEX            , // CALLABLE here and above
        VALUE_INTEGER          ,
        VALUE_REAL             ,
        VALUE_BOOLEAN          ,
        VALUE_NIL              ,
        VALUE_STRING           ,
        VALUE_BLOB             ,
        VALUE_SENTINEL         ,
        VALUE_INDEX            ,
        VALUE_NONE             ,
        VALUE_UNINITIALIZED    ,
        VALUE_NAMESPACE        ,
        VALUE_MODULE           ,
        VALUE_PTR              ,
        VALUE_REF              ,
        VALUE_THREAD           ,
        VALUE_TUPLE            ,
        VALUE_TRACE            ,
        VALUE_BREAK            ,
        VALUE_TOMBSTONE        ,
        VALUE_FUN_META         ,
        VALUE_ANY              ,
        VALUE_TAGGED           = (1 << 7),


        // Aliases for working around macro expansion issues
        // arising from NONE et al. being object-like macros
        VALUE__NONE   = VALUE_NONE,
        VALUE__NIL    = VALUE_NIL,
        VALUE__ANY    = VALUE_ANY
};

typedef Value BuiltinFunction(Ty *, int, Value *);
typedef Value BuiltinMethod(Ty *, Value *, int, Value *);

enum {
        FUN_INFO_HEADER_SIZE,
        FUN_INFO_CODE_SIZE,
        FUN_INFO_CAPTURES,
        FUN_INFO_BOUND,
        FUN_INFO_PARAM_COUNT,
        FUN_INFO_GATHER_IDXS,
        FUN_INFO_CLASS,
        FUN_INFO_FLAGS
};

enum {
        FF_HIDDEN    = (1 << 0),
        FF_FROM_EVAL = (1 << 1),
        FF_DECORATED = (1 << 2),
        FF_HAS_META  = (1 << 3),
        FF_OVERLOAD  = (1 << 4)
};

enum {
        FUN_HEADER_SIZE = 0,
        FUN_CODE_SIZE   = FUN_HEADER_SIZE + sizeof (i32),
        FUN_CAPTURES    = FUN_CODE_SIZE   + sizeof (i32),
        FUN_BOUND       = FUN_CAPTURES    + sizeof (i32),
        FUN_PARAM_COUNT = FUN_BOUND       + sizeof (i32),
        FUN_REST_IDX    = FUN_PARAM_COUNT + sizeof (i32),
        FUN_KWARGS_IDX  = FUN_REST_IDX    + sizeof (i16),
        FUN_CLASS       = FUN_KWARGS_IDX  + sizeof (i16),
        FUN_FLAGS       = FUN_CLASS       + sizeof (i32),
        FUN_METH        = FUN_FLAGS       + sizeof (i16),
        FUN_PROTO       = FUN_METH        + sizeof (i32),
        FUN_DOC         = FUN_PROTO       + sizeof (uptr),
        FUN_META        = FUN_DOC         + sizeof (uptr),
        FUN_NAME        = FUN_META        + sizeof (uptr),
        FUN_EXPR        = FUN_NAME        + sizeof (uptr),
#if defined(TY_ENABLE_JIT)
        FUN_JIT         = FUN_EXPR        + sizeof (uptr),
        FUN_PARAM_NAMES = FUN_JIT         + sizeof (uptr)
#else
        FUN_PARAM_NAMES = FUN_EXPR        + sizeof (uptr)
#endif
};

#define TY_ERROR_TYPES           \
        X(NONE,     NotAn,    0) \
        X(PARSE,    Parse,    1) \
        X(COMPILE,  Compile,  2) \
        X(TYPE,     Type,     3) \
        X(RUNTIME,  Runtime,  4)


#define X(f, n, i) TY_ERROR_##f = ((1 << i) >> 1),
enum { TY_ERROR_TYPES };
#undef X

#define X(f, n, i) #n "Error" ,
static char const *TY_ERROR_NAMES[] = {
        TY_ERROR_TYPES
};
#undef X

enum {
        TY_F_DYING          = (1 << 0),
        TY_F_IN_GC          = (1 << 1),
        TY_F_TDB            = (1 << 2),
        TY_F_IN_EVAL        = (1 << 3),
        TY_F_IGNORING_TYPES = (1 << 4),
        TY_F_FOREIGN        = (1 << 5),
};

#define TY_IS(x)    (ty->flags & TY_F_ ## x)
#define TY_START(x) (ty->flags |= TY_F_ ## x)
#define TY_STOP(x)  (ty->flags &= ~TY_F_ ## x)

struct value {
        u8 type;
        u16 tags;
        u32 src;
        union {
                short tag;
                double real;
                bool boolean;
                Array *array;
                Dict *dict;
                Blob *blob;
                Thread *thread;
                Symbol *sym;
                Module *mod;
                struct {
                        union {
                                Value *ref;
                                void *ptr;
                        };
                        void *gcptr;
                        void *extra;
                };
                struct {
                        imax z;
                        char const *constant;
                };
                struct {
                        i32 class;
                        TyObject *object;
                        Type **t0;
                };
                struct {
                        i32 uop;
                        i32 bop;
                };
                struct {
                        union {
                                struct {
                                        Value *this;
                                        union {
                                                Value *method;
                                                BuiltinMethod *builtin_method;
                                        };
                                };
                                struct {
                                        BuiltinFunction *builtin_function;
                                        char const *module;
                                };
                        };
                        i32 name;
                };
                struct {
                        u8 const *str;
                        u32 bytes;
                        bool ro;
                        u8 *str0;
                };
                struct {
                        imax i;
                        ptrdiff_t off;
                        int nt;
                };
                struct {
                        i32 count;
                        Value *items;
                        i32 *ids;
                };
                Regex const *regex;
                struct {
                        union {
                                struct {
                                        void (*ff)();
                                        ffi_cif *ffi;
                                };
                                struct {
                                        i32 *info;
                                        Value **env;
                                };
                        };
                        FunUserInfo *xinfo;
                };
                Expr *namespace;
                Generator *gen;
        };
};

struct object {
        bool          init;
        u32           nslot;
        Class         *class;
        struct itable *dynamic;
        Value         slots[];
};

struct class {
        int i;

        int ti;
        bool is_trait;

        bool final;
        bool really_final;

        Class *super;

        u16Vector offsets_r;
        u16Vector offsets_w;

        struct itable methods;
        struct itable getters;
        struct itable setters;
        struct itable fields;

        struct itable s_methods;
        struct itable s_getters;
        struct itable s_setters;
        struct itable s_fields;

        vec(bool) impls;
        ClassVector traits;

        Value finalizer;
        Value init;

        char const *name;
        char const *doc;

        Stmt *def;

        Type *type;
        Type *object_type;
};

struct frame {
        Value f;
        usize fp;
        char const *ip;
};

typedef struct cothread_state {
        int exec_depth;
        int rc;
        FrameStack frames;
        CallStack calls;
        SPStack sps;
        TargetStack targets;
        TryStack try_stack;
        ValueVector to_drop;
} co_state;

struct generator {
        int fp;
        ValueVector frame;
        char *ip;
        cothread_t co;
        co_state st;
        GCRootSet gc_roots;
        Value f;
};

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

struct thread {
        TyThread t;
        TyMutex mutex;
        TyCondVar cond;

        Value v;
        u64 i;
        bool alive;
        bool joined;
        bool detached;
};

struct chanval {
        vec(void *) as;
        Value v;
};

struct channel {
        bool open;
        TyMutex m;
        TyCondVar c;
        vec(ChanVal) q;
};

typedef atomic_intmax_t TyAtomicInt;

struct dict_item {
        Value k;
        Value v;
        u64   h;
        DictItem *prev;
        DictItem *next;
};

struct dict {
        DictItem *items;
        usize     size;
        usize     count;
        usize     tombs;
        DictItem *last;
        Value     dflt;
};

typedef struct target {
        struct {
                Value *t;
                void *gc;
        };
} Target;

typedef struct {
        int i;
        void *beg;
} ScratchSave;

enum { TRY_NONE, TRY_TRY, TRY_THROW, TRY_CATCH, TRY_FINALLY };
enum { TY_SAVE_INTERNAL, TY_SAVE_USER };

struct try {
        jmp_buf jb;

        u32 sp;
        u32 gc;
        u32 cs;
        u32 ts;
        u32 ds;
        u32 ctxs;
        u32 nsp;
        u16 vs;
        u16 ed;

        bool executing;
        bool need_trace;

        u8 state;

        u32 flags;

        ScratchSave ss;

        char *catch;
        char *finally;
        char *end;

        ValueVector defer;
};

struct ty_save {
        u8 type;
        byte_vector msg;
};

typedef struct {
        intrusive_vec(void *);
        vec(ValueVector) locals;
        Value exc;
} ThrowCtx;

typedef struct ty0 {
        Ty *ty;
        CompileState *compiler;
        InternSet u_ops;
        InternSet b_ops;
        InternSet members;
        InternSet strings;
        bool initialized;
        bool ready;
} TY;

typedef struct thread_group ThreadGroup;

typedef struct {
        char *ip;
        char op;
        Expr *cond;
} DebugBreakpoint;

typedef struct param Param;
typedef struct type Type;

struct param {
        char const *name;
        Type *type;
        Type *dflt;
        bool required;
        bool rest;
        bool kws;
        bool pack;
};

typedef vec(Param) ParamVector;

#define TY_TDB_STATES   \
        X(OFF)          \
        X(STARTING)     \
        X(ACTIVE)       \
        X(STOPPED)      \
        X(STEPPING)     \
        X(DEAD)

#define X(s) TDB_STATE_ ## s ,
enum {
        TY_TDB_STATES
        TDB_MAX_STATE
};
#undef X

#define X(s) #s ,
static char const *TDB_STATE_NAMES[] = {
        TY_TDB_STATES
};
#undef X

typedef struct {
        atomic_uint_least8_t state;

        Ty *ty;
        Ty *host;

        Value thread;
        Value hook;

        DebugBreakpoint next;
        DebugBreakpoint alt;
        vec(DebugBreakpoint) breaks;

        byte_vector context_buffer;
} TyTDB;

typedef struct ty {
        char *ip;

        ValueStack stack;

        co_state st;
        cothread_t co_top;

        ValueVector tls;

        vec(DispatchCache) _2op_cache;

        int GC_OFF_COUNT;

        GCRootSet   gc_roots;
        GCWorkStack marking;

        isize memory_used;
        isize memory_limit;

        AllocList allocs;
        ThreadGroup *group;
        TyThreadState *state;
        TySpinLock *lock;
        bool locked;

        CoThreadVector cothreads;

        vec(ThrowCtx *) throw_stack;

        i32 eval_depth;
        u32 flags;
        u64 id;

        u64 prng[4];

        struct {
                pcre2_match_context *ctx;
                pcre2_jit_stack *stack;
                pcre2_match_data *match;
        } pcre2;

        Arena arena;

        struct { void *p; usize n; } tmp[TY_TMP_BUF_COUNT];

        struct {
                int i;
                vec(Arena) arenas;
        } scratch;

        vec(void *) visiting;

        Value exc;
        byte_vector err;

        char *code;

        TyTDB *tdb;
        TY *ty;
} Ty;

typedef struct {
        int a;
        int b;
        int call;
        int _cause;
        int _class_;
        int contains;
        int count;
        int _ctx;
        int _def_;
        int _drop_;
        int _enter_;
        int fmt;
        int _free_;
        int _fqn_;
        int groups;
        int _hash_;
        int init;
        int _init_subclass_;
        int _iter_;
        int json;
        int len;
        int _len_;
        int match;
        int _meta_;
        int missing;
        int method_missing;
        int _name_;
        int negate;
        int _next_;
        int ptr;
        int question;
        int _repr_;
        int slice;
        int str;
        int _str_;
        int subscript;
        int unapply;
        int _what;

        int _fields_;
        int _methods_;
        int _getters_;
        int _setters_;
        int _static_fields_;
        int _static_methods_;
        int _static_getters_;
        int _static_setters_;
        int _super_;

        int _readln;
        int env;
        int exe;
        int exit_hooks;
        int pp;
        int pretty;
        int q;
        int TEST;
        int tests;
        int tdb_hook;
} InternedNames;

enum {
        TY_COLOR_AUTO,
        TY_COLOR_ALWAYS,
        TY_COLOR_NEVER,
        TY_COLOR_MODE_COUNT
};

#define MemoryUsed  (ty->memory_used)
#define MemoryLimit (ty->memory_limit)

#define TY_IS_READY       (xD.ready)
#define TY_IS_INITIALIZED (xD.initialized)

#define EVAL_DEPTH (ty->eval_depth)

extern Ty vvv;
extern TY xD;

extern InternedNames NAMES;

extern int  ColorMode;
extern bool ColorStdout;
extern bool ColorStderr;
extern bool ColorProfile;
extern char const *COLOR_MODE_NAMES[TY_COLOR_MODE_COUNT];

extern bool RunningTests;
extern bool CheckTypes;
extern bool CheckConstraints;
extern bool DetailedExceptions;
extern bool CompileOnly;
extern bool AllowErrors;
extern bool InteractiveSession;

extern u64 TypeCheckCounter;
extern u64 TypeAllocCounter;
extern u64 TypeCheckTime;

#if !defined(TY_RELEASE)
extern volatile bool GC_EVERY_ALLOC;
#endif

#if defined(TY_TRACE_GC)
extern _Thread_local u64 ThisReached;
extern _Thread_local u64 TotalReached;
#define MARK(v) do {                        \
        atomic_store_explicit(              \
                &(ALLOC_OF(v))->mark,       \
                true,                       \
                memory_order_relaxed        \
        );                                  \
        ThisReached += ALLOC_OF(v)->size;  \
        TotalReached += ALLOC_OF(v)->size; \
} while (0)
#define ADD_REACHED(n) do {          \
        ThisReached += (n);          \
        TotalReached += (n);         \
} while (0)
#define RESET_REACHED() do {         \
        ThisReached = 0;             \
} while (0)
#define RESET_TOTAL_REACHED() do {    \
        TotalReached = 0;             \
} while (0)
#define LOG_REACHED(...) XxLOG(__VA_ARGS__)
#else
#define MARK(v) do {                     \
        atomic_store_explicit(           \
                &(ALLOC_OF(v))->mark,    \
                true,                    \
                memory_order_relaxed     \
        );                               \
} while (0)
#define ADD_REACHED(n)
#define RESET_REACHED()
#define RESET_TOTAL_REACHED()
#define LOG_REACHED(...)
#endif
#define MARKED(v) atomic_load_explicit(  \
        &(ALLOC_OF(v))->mark,            \
        memory_order_relaxed             \
)

#if defined(TY_GC_STATS)
extern usize TotalBytesAllocated;
#endif

#define dont_printf(...) 0

#if 0
#define GC_STOP() do { XXX("GC_STOP(): " __FILE__ ":%d: %d", __LINE__, ty->GC_OFF_COUNT + 1); ty->GC_OFF_COUNT += 1; } while (0)
#define GC_RESUME() do { XXX("GC_RESUME(): " __FILE__ ":%d: %d", __LINE__, ty->GC_OFF_COUNT - 1); ty->GC_OFF_COUNT -= 1; } while (0)
#else
#define GC_STOP()   (ty->GC_OFF_COUNT += 1)
#define GC_RESUME() (ty->GC_OFF_COUNT -= 1)
#endif

#define ALLOC_OF(p) ((struct alloc *)(((char *)(p)) - offsetof(struct alloc, data)))


#define NOGC(v)   atomic_fetch_add_explicit(&(ALLOC_OF(v))->hard, 1, memory_order_relaxed)
#define OKGC(v)   atomic_fetch_sub_explicit(&(ALLOC_OF(v))->hard, 1, memory_order_relaxed)

#define POISON(v)   atomic_store_explicit(&(ALLOC_OF(v))->hard, 0xDEAD, memory_order_seq_cst)
#define POISONED(v) (atomic_load_explicit(&(ALLOC_OF(v))->hard, memory_order_seq_cst) == 0xDEAD)

#define ErrorBuffer (ty->err)

#if 1
#define TY_THROW_ERROR() (vm_throw_ty(ty))
#define TY_CATCH_ERROR() (TyClearError(ty), !VM_TRY())
#define TY_CATCH()       (vm_catch(ty))
#define TY_CATCH_END()   (vm_finally(ty))
#else
#define TY_THROW_ERROR() (XXX("%30s:%-7d: THROW",   __FILE__, __LINE__ + 1), vm_throw_ty(ty))
#define TY_CATCH_ERROR() (XXX("%30s:%-7d: TRY",     __FILE__, __LINE__ + 1), TyClearError(ty), !VM_TRY())
#define TY_CATCH()       (XXX("%30s:%-7d: CATCH",   __FILE__, __LINE__ + 1), vm_catch(ty))
#define TY_CATCH_END()   (XXX("%30s:%-7d: END_TRY", __FILE__, __LINE__ + 1), vm_finally(ty))
#endif
#define TY_RETHROW()     (vm_rethrow(ty))

#ifdef _WIN32
#  define UNLIKELY(x)  (x)
#  define LIKELY(x)    (x)
#  define EXPECT(x, y) (x)
#  ifndef TY_RELEASE
#    define UNREACHABLE(msg) assert(! "" msg)
#  else
#    define UNREACHABLE(msg) __assume(0)
#  endif
#else
#  define UNLIKELY(x)  __builtin_expect((x), 0)
#  define LIKELY(x)    __builtin_expect((x), 1)
#  define EXPECT(x, y) __builtin_expect((x), (y))
#  ifndef TY_RELEASE
#    define UNREACHABLE(msg) assert(! "" msg)
#  else
#    define UNREACHABLE(msg) __builtin_unreachable()
#  endif
#endif

#define TODO(msg) UNREACHABLE("TODO: " msg)

#ifndef TY_RELEASE
#define ASSERT(expr, ...) do {                              \
        if (!(expr)) {                                      \
                fprintf(                                    \
                        stderr,                             \
                        "%s:%d: %s: assertion '%s' failed"  \
                        __VA_OPT__(": ")                    \
                        __VA_ARGS__                         \
                        "\n",                               \
                        __FILE__,                           \
                        __LINE__,                           \
                        __func__,                           \
                        #expr                               \
                );                                          \
                *(volatile char *)0 = 0;                    \
        }                                                   \
} while (0)
#else
#define ASSERT(...) ;
#endif

#define TY_INSTRUCTIONS           \
        X(NOP),                   \
        X(LOAD_LOCAL),            \
        X(LOAD_REF),              \
        X(LOAD_CAPTURED),         \
        X(LOAD_GLOBAL),           \
        X(LOAD_THREAD_LOCAL),     \
        X(CHECK_INIT),            \
        X(CAPTURE),               \
        X(DECORATE),              \
        X(INTO_METHOD),           \
        X(BIND_CAPTURED),         \
        X(TARGET_LOCAL),          \
        X(TARGET_REF),            \
        X(TARGET_CAPTURED),       \
        X(TARGET_GLOBAL),         \
        X(TARGET_THREAD_LOCAL),   \
        X(TARGET_MEMBER),         \
        X(TARGET_DYN_MEMBER),     \
        X(TARGET_SELF_MEMBER),    \
        X(TARGET_SELF_STATIC),    \
        X(TARGET_STATIC_MEMBER),  \
        X(TARGET_SUBSCRIPT),      \
        X(INC),                   \
        X(DEC),                   \
        X(ASSIGN),                \
        X(MAYBE_ASSIGN),          \
        X(ASSIGN_LOCAL),          \
        X(ASSIGN_GLOBAL),         \
        X(ASSIGN_SUBSCRIPT),      \
        X(ARRAY_REST),            \
        X(TUPLE_REST),            \
        X(RECORD_REST),           \
        X(INT8),                  \
        X(INTEGER),               \
        X(REAL),                  \
        X(TRUE),                  \
        X(FALSE),                 \
        X(STRING),                \
        X(REGEX),                 \
        X(ARRAY),                 \
        X(ARRAY0),                \
        X(DICT),                  \
        X(DEFAULT_DICT),          \
        X(TUPLE),                 \
        X(GATHER_TUPLE),          \
        X(NIL),                   \
        X(SELF),                  \
        X(TAG),                   \
        X(CLASS),                 \
        X(TO_STRING),             \
        X(CONCAT_STRINGS),        \
        X(RANGE),                 \
        X(INCRANGE),              \
        X(CLASS_OF),              \
        X(MEMBER_ACCESS),         \
        X(TRY_MEMBER_ACCESS),     \
        X(SELF_MEMBER_ACCESS),    \
        X(SELF_STATIC_ACCESS),    \
        X(STATIC_MEMBER_ACCESS),  \
        X(GET_MEMBER),            \
        X(TRY_GET_MEMBER),        \
        X(TRY_MEMBER),            \
        X(TRY_UNAPPLY),           \
        X(UNAPPLY),               \
        X(SUBSCRIPT),             \
        X(SLICE),                 \
        X(TAIL_CALL),             \
        X(CALL),                  \
        X(CALL_GLOBAL),           \
        X(CALL_METHOD),           \
        X(TRY_CALL_METHOD),       \
        X(CALL_SELF_METHOD),      \
        X(CALL_STATIC_METHOD),    \
        X(CALL_SELF_STATIC),      \
        X(BIND_CLASS),            \
        X(GET_NEXT),              \
        X(PUSH_INDEX),            \
        X(READ_INDEX),            \
        X(LOOP_ITER),             \
        X(LOOP_CHECK),            \
        X(SPREAD_CHECK),          \
        X(POP),                   \
        X(POP2),                  \
        X(UNPOP),                 \
        X(DROP2),                 \
        X(DUP),                   \
        X(DUP2_SWAP),             \
        X(ARRAY_COMPR),           \
        X(DICT_COMPR),            \
        X(THROW_IF_NIL),          \
        X(PRE_INC),               \
        X(POST_INC),              \
        X(PRE_DEC),               \
        X(POST_DEC),              \
        X(FUNCTION),              \
        X(JUMP),                  \
        X(JUMP_IF),               \
        X(JUMP_IF_NIL),           \
        X(JUMP_IF_NOT),           \
        X(JUMP_IF_NONE),          \
        X(JUMP_IF_TYPE),          \
        X(JUMP_IF_INIT),          \
        X(JLE),                   \
        X(JLT),                   \
        X(JGE),                   \
        X(JGT),                   \
        X(JEQ),                   \
        X(JNE),                   \
        X(JNI),                   \
        X(JII),                   \
        X(JUMP_AND),              \
        X(JUMP_OR),               \
        X(JUMP_WTF),              \
        X(SKIP_CHECK),            \
        X(RETURN),                \
        X(RETURN_PRESERVE_CTX),   \
        X(EXEC_CODE),             \
        X(HALT),                  \
        X(MULTI_RETURN),          \
        X(RETURN_IF_NOT_NONE),    \
        X(SENTINEL),              \
        X(FIX_TO),                \
        X(FIXED_TO),              \
        X(REVERSE),               \
        X(SWAP),                  \
        X(NONE),                  \
        X(NONE_IF_NIL),           \
        X(NONE_IF_NOT),           \
        X(CLEAR_RC),              \
        X(GET_EXTRA),             \
        X(PUSH_NTH),              \
        X(PUSH_ARRAY_ELEM),       \
        X(PUSH_TUPLE_ELEM),       \
        X(PUSH_TUPLE_MEMBER),     \
        X(MULTI_ASSIGN),          \
        X(MAYBE_MULTI),           \
        X(JUMP_IF_SENTINEL),      \
        X(CLEAR_EXTRA),           \
        X(FIX_EXTRA),             \
        X(VALUE),                 \
        X(EVAL),                  \
        X(SAVE_STACK_POS),        \
        X(RESTORE_STACK_POS),     \
        X(POP_STACK_POS),         \
        X(POP_STACK_POS_POP),     \
        X(POP_STACK_POS_POP2),    \
        X(DROP_STACK_POS),        \
        X(YIELD),                 \
        X(YIELD_NONE),            \
        X(YIELD_SOME),            \
        X(MAKE_GENERATOR),        \
        X(THROW),                 \
        X(RETHROW),               \
        X(TRY),                   \
        X(CATCH),                 \
        X(END_TRY),               \
        X(FINALLY),               \
        X(PUSH_DEFER_GROUP),      \
        X(DEFER),                 \
        X(CLEANUP),               \
        X(DROP),                  \
        X(PUSH_DROP),             \
        X(PUSH_DROP_GROUP),       \
        X(DISCARD_DROP_GROUP),    \
        X(TAG_PUSH),              \
        X(DEFINE_TAG),            \
        X(DEFINE_CLASS),          \
        X(INIT_STATIC_FIELD),     \
        X(TRY_INDEX),             \
        X(TRY_INDEX_TUPLE),       \
        X(INDEX_TUPLE),           \
        X(TRY_TUPLE_MEMBER),      \
        X(TRY_TAG_POP),           \
        X(TRY_REGEX),             \
        X(ASSIGN_REGEX_MATCHES),  \
        X(TRY_ASSIGN_NON_NIL),    \
        X(TRY_RANGE),             \
        X(TRY_INCRANGE),          \
        X(MATCH_TAG),             \
        X(MATCH_STRING),          \
        X(BAD_MATCH),             \
        X(BAD_CALL),              \
        X(BAD_DISPATCH),          \
        X(BAD_ASSIGN),            \
        X(PUSH_UNTAGGED),         \
        X(UNTAG_OR_DIE),          \
        X(STEAL_TAG),             \
        X(TRY_STEAL_TAG),         \
        X(ENSURE_LEN),            \
        X(ENSURE_LEN_TUPLE),      \
        X(ENSURE_EQUALS_VAR),     \
        X(ENSURE_DICT),           \
        X(ENSURE_CONTAINS),       \
        X(ENSURE_SAME_KEYS),      \
        X(RENDER_TEMPLATE),       \
        X(BINARY_OP),             \
        X(UNARY_OP),              \
        X(TRAP),                  \
        X(TRAP_TY),               \
        X(DEBUG),                 \
        X(ADD),                   \
        X(SUB),                   \
        X(MUL),                   \
        X(DIV),                   \
        X(BIT_AND),               \
        X(BIT_OR),                \
        X(BIT_XOR),               \
        X(SHL),                   \
        X(SHR),                   \
        X(MOD),                   \
        X(EQ),                    \
        X(NEQ),                   \
        X(LT),                    \
        X(GT),                    \
        X(LEQ),                   \
        X(GEQ),                   \
        X(CMP),                   \
        X(CHECK_MATCH),           \
        X(TYPE),                  \
        X(ASSIGN_TYPE),           \
        X(MUT_ADD),               \
        X(MUT_MUL),               \
        X(MUT_DIV),               \
        X(MUT_MOD),               \
        X(MUT_SUB),               \
        X(MUT_AND),               \
        X(MUT_OR),                \
        X(MUT_XOR),               \
        X(MUT_SHL),               \
        X(MUT_SHR),               \
        X(NEG),                   \
        X(NOT),                   \
        X(QUESTION),              \
        X(COUNT),                 \
        X(TRACE),                 \
        X(ENTER),                 \
        X(OPERATOR),              \
        X(PATCH_ENV),             \
        X(GET_TAG),               \
        X(BIND_INSTANCE),         \
        X(BIND_GETTER),           \
        X(BIND_SETTER),           \
        X(BIND_STATIC),           \
        X(NAMESPACE)


#define X(i) INSTR_ ## i
enum {
        TY_INSTRUCTIONS
};
#undef X

#define INTEGER(k)               ((Value){ .type = VALUE_INTEGER,          .z              = (k),                                  .tags = 0 })
#define REAL(f)                  ((Value){ .type = VALUE_REAL,             .real           = (f),                                  .tags = 0 })
#define BOOLEAN(b)               ((Value){ .type = VALUE_BOOLEAN,          .boolean        = (b),                                  .tags = 0 })
#define ARRAY(a)                 ((Value){ .type = VALUE_ARRAY,            .array          = (a),                                  .tags = 0 })
#define TUPLE(vs, ns, n, gc)     ((Value){ .type = VALUE_TUPLE,            .items          = (vs), .count = (n),  .ids = (ns),     .tags = 0 })
#define BLOB(b)                  ((Value){ .type = VALUE_BLOB,             .blob           = (b),                                  .tags = 0 })
#define DICT(d)                  ((Value){ .type = VALUE_DICT,             .dict           = (d),                                  .tags = 0 })
#define REGEX(r)                 ((Value){ .type = VALUE_REGEX,            .regex          = (r),                                  .tags = 0 })
#define FUNCTION()               ((Value){ .type = VALUE_FUNCTION,                                                                 .tags = 0 })
#define PTR(p)                   ((Value){ .type = VALUE_PTR,              .ptr            = (p),  .gcptr = NULL,                  .tags = 0 })
#define TPTR(t, p)               ((Value){ .type = VALUE_PTR,              .ptr            = (p),  .gcptr = NULL,  .extra = (t),   .tags = 0 })
#define GCPTR(p, gcp)            ((Value){ .type = VALUE_PTR,              .ptr            = (p),  .gcptr = (gcp),                 .tags = 0 })
#define TGCPTR(p, t, gcp)        ((Value){ .type = VALUE_PTR,              .ptr            = (p),  .gcptr = (gcp), .extra = (t),   .tags = 0 })
#define EPTR(p, gcp, ep)         ((Value){ .type = VALUE_PTR,              .ptr            = (p),  .gcptr = (gcp), .extra = (ep),  .tags = 0 })
#define TRACE(t)                 ((Value){ .type = VALUE_TRACE,            .ptr            = (t),                                  .tags = 0 })
#define BLOB(b)                  ((Value){ .type = VALUE_BLOB,             .blob           = (b),                                  .tags = 0 })
#define REF(p)                   ((Value){ .type = VALUE_REF,              .ptr            = (p),                                  .tags = 0 })
#define UNINITIALIZED(p)         ((Value){ .type = VALUE_UNINITIALIZED,    .ptr            = (p),                                  .tags = 0 })
#define TAG(t)                   ((Value){ .type = VALUE_TAG,              .tag            = (t),                                  .tags = 0 })
#define CLASS(c)                 ((Value){ .type = VALUE_CLASS,            .class          = (c),  .object = NULL,                 .tags = 0 })
#define TYPE(t)                  ((Value){ .type = VALUE_TYPE,             .ptr            = (t),                                  .tags = 0 })
#define OBJECT(o, c)             ((Value){ .type = VALUE_OBJECT,           .object         = (o),  .class  = (c),                  .tags = 0 })
#define OPERATOR(u, b)           ((Value){ .type = VALUE_OPERATOR,         .uop            = (u),  .bop    = (b),                  .tags = 0 })
#define NAMESPACE(ns)            ((Value){ .type = VALUE_NAMESPACE,        .namespace      = (ns),                                 .tags = 0 })
#define MODULE(m)                ((Value){ .type = VALUE_MODULE,           .mod            = (m),                                  .tags = 0 })
#define METHOD(n, m, t)          ((Value){ .type = VALUE_METHOD,           .method         = (m),  .this   = (t),  .name = (n),    .tags = 0 })
#define GENERATOR(g)             ((Value){ .type = VALUE_GENERATOR,        .gen            = (g),                                  .tags = 0 })
#define THREAD(t)                ((Value){ .type = VALUE_THREAD,           .thread         = (t),                                  .tags = 0 })
#define BUILTIN_METHOD(n, m, t)  ((Value){ .type = VALUE_BUILTIN_METHOD,   .builtin_method = (m),  .this   = (t),  .name = (n),    .tags = 0 })
#define FOREIGN_FUN(p, i, x)     ((Value){ .type = VALUE_FOREIGN_FUNCTION, .ffi            = (i),  .ff     = (p),  .xinfo = (x),   .tags = 0 })
#define NIL                      ((Value){ .type = VALUE_NIL,                                                                      .tags = 0 })
#define INDEX(ix, o, n)          ((Value){ .type = VALUE_INDEX,            .i              = (ix), .off   = (o), .nt = (n),        .tags = 0 })
#define SENTINEL                 ((Value){ .type = VALUE_SENTINEL,         .i              = 0,    .off   = 0,                     .tags = 0 })
#define NONE                     ((Value){ .type = VALUE_NONE,             .i              = 0,    .off   = 0,                     .tags = 0 })
#define BREAK                    ((Value){ .type = VALUE_BREAK,            .i              = 0,    .off   = 0,                     .tags = 0 })

#define CALLABLE(v) ((v).type <= VALUE_REGEX)
#define ARITY(f)    ((f).type == VALUE_FUNCTION ? (((i16 *)((f).info + 5))[0] == -1 ? (f).info[4] : 100) : 1)

#define PAIR(a, b)            PAIR_(ty, (a), (b))
#define TRIPLE(a, b, c)       TRIPLE_(ty, (a), (b), (c))
#define QUADRUPLE(a, b, c, d) QUADRUPLE_(ty, (a), (b), (c), (d))

#define TAGGED(t, ...) tagged(ty, (t), __VA_ARGS__, NONE)
#define TAGGED_RECORD(t, ...) tagged(ty, (t), vTn(__VA_ARGS__), NONE)

#define v_eq(a, b) value_test_equality(ty, (a), (b))

#define TY_UNARY_OPERATORS   \
        X(COMPL,      "~"),  \
        X(COUNT,      "#"),  \
        X(DEC,       "--"),  \
        X(INC,       "++"),  \
        X(NEG,        "-"),  \
        X(NOT,        "!"),  \
        X(QUESTION,   "?"),  \
        X(UOP_MAX,    "z")

#define TY_BINARY_OPERATORS  \
        X(ADD,       "+"),   \
        X(SUB,       "-"),   \
        X(MUL,       "*"),   \
        X(DIV,       "/"),   \
        X(MOD,       "%"),   \
        X(DIVMOD,   "/%"),   \
        X(BIT_AND,   "&"),   \
        X(BIT_OR,    "|"),   \
        X(BIT_XOR,   "^"),   \
        X(BIT_SHL,  "<<"),   \
        X(BIT_SHR,  ">>"),   \
        X(MUT_ADD,  "+="),   \
        X(MUT_SUB,  "-="),   \
        X(MUT_MUL,  "*="),   \
        X(MUT_DIV,  "/="),   \
        X(MUT_MOD,  "%="),   \
        X(MUT_AND,  "&="),   \
        X(MUT_OR,   "|="),   \
        X(MUT_XOR,  "^="),   \
        X(MUT_SHL, "<<="),   \
        X(MUT_SHR, ">>="),   \
        X(AND,      "&&"),   \
        X(OR,       "||"),   \
        X(EQL,      "=="),   \
        X(NEQ,      "!="),   \
        X(CMP,     "<=>"),   \
        X(GT,        ">"),   \
        X(LT,        "<"),   \
        X(GEQ,      ">="),   \
        X(LEQ,      "<="),   \
        X(IN,       "in"),   \
        X(NOT_IN,  "!in"),   \
        X(BOP_MAX,  "zz")

#define X(op, id) OP_ ## op
enum {
        TY_BINARY_OPERATORS
};
#undef X

#define X(op, id) OP_ ## op
enum {
        TY_UNARY_OPERATORS
};
#undef X

#define FMT_MORE "\n                 "
#define FMT_CS   "%s%s%s"

#define FMT_MAGENTA2(s) TERM(95), (s), TERM(0)

#define VSC(v, ...) value_show_color(ty, (v), __VA_ARGS__ + 0)

#define SHOW_4(v, f1, f2, f3) (value_show_color(ty, (v), TY_SHOW_##f1 | TY_SHOW_##f2 | TY_SHOW_##f3))
#define SHOW_3(v, f1, f2)     (value_show_color(ty, (v), TY_SHOW_##f1 | TY_SHOW_##f2))
#define SHOW_2(v, f1)         (value_show_color(ty, (v), TY_SHOW_##f1))
#define SHOW_1(v)             (value_show_color(ty, (v), 0))
#define SHOW(...) VA_SELECT(SHOW, __VA_ARGS__)

#define M_ID(m)   intern(&xD.members, (m))->id
#define M_NAME(i) intern_entry(&xD.members, (i))->name

#define S_ID(s)     intern(&xD.strings, (s))->id
#define S_STRING(i) intern_entry(&xD.strings, (i))->name

#define PMASK3 ((uptr)7)
#define pT(p) (((uptr)(p)) &  PMASK3)
#define pP(p) (((uptr)(p)) & ~PMASK3)


inline static void *
mrealloc(void *p, usize n)
{
        p = ty_realloc(p, n);

        if (UNLIKELY(p == NULL)) {
                panic("Out of memory!");
        }

        return p;
}

inline static void *
alloc0(usize n)
{
        void *p = ty_calloc(1, n);

        if (UNLIKELY(p == NULL)) {
                panic("Out of memory!");
        }

        return p;
}

void *
Allocate(Ty *ty, usize n);

inline static void *
Allocate0(Ty *ty, usize n)
{
        return memset(Allocate(ty, n), 0, n);
}

static u64
jb_hash(jmp_buf const *jb)
{
        u64 hash = 2166136261UL;
        u8 const *p = (u8 const *)jb;

        for (usize i = 0; i < sizeof (*jb); ++i) {
                hash = (hash ^ p[i]) * 16777619UL;
        }

        return hash;
}

inline static void
ExpandScratch(Ty *ty)
{
#define S(x)  (ty->scratch . x)
#define SS(i) (&S(arenas.items)[i])
#define SSS   SS(S(i) - 1)
        if (S(i) == S(arenas.count)) {
                ptrdiff_t cap;

                if (S(i) == 0) {
                        cap = 1LL << 12;
                } else {
                        cap = 2 * (vvL(S(arenas))->end - vvL(S(arenas))->base);
                }

                char *new_ = mrealloc(NULL, cap);

                xvP(
                        S(arenas),
                        ((Arena) {
                                .base = new_,
                                .beg  = new_,
                                .end  = new_ + cap
                        })
                );
        }

        S(i) += 1;
}

inline static void *
AllocateScratch(Ty *ty, usize n)
{
        for (;;) {
                ptrdiff_t avail = SSS->end - SSS->beg;
                ptrdiff_t padding = -(iptr)SSS->beg & ((alignof (void *)) - 1);

                if (n > avail - padding) {
                        ExpandScratch(ty);
                } else {
                        char *new = SSS->beg + padding;
                        SSS->beg += padding + n;
                        return new;
                }
        }
}

inline static void *
AllocateScratch0(Ty *ty, usize n)
{
        return memset(AllocateScratch(ty, n), 0, n);
}

inline static ScratchSave
SaveScratch(Ty *ty)
{
        return (ScratchSave) {
                .i = S(i),
                .beg = SSS->beg
        };
}

inline static void
RestoreScratch(Ty *ty, ScratchSave save)
{
        while (S(i) > save.i) {
                SSS->beg = SSS->base;
                S(i) -= 1;
        }

        SSS->beg = save.beg;
}

inline static void
ResetScratch(Ty *ty)
{
        RestoreScratch(
                ty,
                ((ScratchSave) {
                        .i = 1,
                        .beg = SS(0)->base
                })
        );
#undef S
#undef SS
}

#define SCRATCH_SAVE()    ScratchSave _scratch_save = SaveScratch(ty);
#define SCRATCH_RESTORE() RestoreScratch(ty, _scratch_save);
#define SCRATCH_RESET()   ResetScratch(ty);
#define WITH_SCRATCH for (                              \
        struct {                                        \
                ScratchSave save;                       \
                bool cond;                              \
        } _ss_ctx = { SaveScratch(ty), 1 };             \
        (                                               \
                _ss_ctx.cond                            \
             || (RestoreScratch(ty, _ss_ctx.save), 0)   \
        );                                              \
        _ss_ctx.cond = 0                                \
)

inline static void *
TyEnsureTmpBuffer(Ty *ty, u32 i, usize n)
{
        void **p = &ty->tmp[i].p;
        usize *cap = &ty->tmp[i].n;

        if (*cap < n) {
                *p = mrealloc(*p, n);
                *cap = n;
        }

        return *p;
}

inline static char *
TyTmpCString(Ty *ty, u32 i, Value val)
{
        usize n;
        void const *str;

        switch (val.type) {
        case VALUE_STRING:
                n = sN(val);
                str = ss(val);
                break;

        case VALUE_BLOB:
                n = vN(*val.blob);
                str = vv(*val.blob);
                break;

        case VALUE_PTR:
                n = strlen((char const *)val.ptr);
                str = val.ptr;
                break;

        default:
                UNREACHABLE();
        }

        char *c_str = TyEnsureTmpBuffer(ty, i, n + 1);

        memcpy(c_str, str, n);
        c_str[n] = '\0';

        return c_str;
}

inline static char *
TyNewCString(Ty *ty, Value val, bool nul_before)
{
        usize n;
        void const *str;

        switch (val.type) {
        case VALUE_STRING:
                n = sN(val);
                str = ss(val);
                break;

        case VALUE_BLOB:
                n = vN(*val.blob);
                str = vv(*val.blob);
                break;

        default:
                UNREACHABLE();
        }

        return memcpy(alloc0(n + 1 + nul_before) + nul_before, str, n);
}

#define TY_BUF_i(i, n) (                                                          \
        sizeof (                                                                  \
                struct {                                                          \
                        _Static_assert(                                           \
                                (i) < TY_TMP_BUF_COUNT,                           \
                                "we don't maintain that many temporary buffers!"  \
                        );                                                        \
                }                                                                 \
        ),                                                                        \
        TyEnsureTmpBuffer(ty, (i), (n))                                           \
)
#define TY_BUF_A(n) TY_BUF_i(0, (n))
#define TY_BUF_B(n) TY_BUF_i(1, (n))
#define TY_BUF_C(n) TY_BUF_i(2, (n))
#define TY_BUF(n)   TY_BUF_A(n)

#define KB_1   1024U
#define KB_8   (8   * KB_1)
#define KB_256 (256 * KB_1)
#define KB_512 (512 * KB_1)

#define MB_1 (KB_1 * KB_1)
#define MB_2 (2 * MB_1)
#define MB_4 (2 * MB_2)

#define TY_TMP_N MB_2
#define TY_TMP_A() TY_BUF_A(TY_TMP_N)
#define TY_TMP_B() TY_BUF_B(TY_TMP_N)
#define TY_TMP_C() TY_BUF_C(TY_TMP_N)
#define TY_TMP()   TY_BUF(TY_TMP_N)

#define TY_TMP_C_STR_i(i, n) (                                                    \
        sizeof (                                                                  \
                struct {                                                          \
                        _Static_assert(                                           \
                                (i) < TY_TMP_BUF_COUNT,                           \
                                "we don't maintain that many temporary buffers!"  \
                        );                                                        \
                }                                                                 \
        ),                                                                        \
        TyTmpCString(ty, (i), (n))                                                \
)
#define TY_TMP_C_STR_A(s) TY_TMP_C_STR_i(0, (s))
#define TY_TMP_C_STR_B(s) TY_TMP_C_STR_i(1, (s))
#define TY_TMP_C_STR_C(s) TY_TMP_C_STR_i(2, (s))
#define TY_TMP_C_STR TY_TMP_C_STR_A

#define TY_C_STR(s) TyNewCString(ty, (s), false)
#define TY_0_C_STR(s) TyNewCString(ty, (s), true)

noreturn void
CompileError(Ty *ty, u32 type, char const *fmt, ...);

noreturn void
vm_panic(Ty *ty, char const *fmt, ...);

noreturn void
vm_error(Ty *ty, char const *fmt, ...);

#define I_AM_TDB       (ty == TDB_TY)
#define TDB            (ty->tdb)
#define TDB_TY         ((TDB == NULL) ? NULL : (Ty *)(TDB->ty))
#define TDB_STATE      ((TDB == NULL) ? TDB_STATE_OFF : TDB->state)
#define TDB_STATE_NAME (TDB_STATE_NAMES[TDB_STATE])
#define TDB_MUTEX      (TDB->thread.thread->mutex)
#define TDB_CONDVAR    (TDB->thread.thread->cond)
#define DEBUGGING      (!TDB_IS(OFF))

#if 0
#define TDB_IS(x) (                                                  \
        fprintf(                                                     \
                stderr,                                              \
                "[%s] %16s:%-6d TDB_IS(%s) --> %d (state: %s)\n",    \
                I_AM_TDB ? "TDB" : "Ty",                             \
                __FILE__,                                            \
                __LINE__,                                            \
                #x,                                                  \
                TDB_STATE == (TDB_STATE_ ## x),                      \
                TDB_STATE_NAME                                       \
        ),                                                           \
        (TDB_STATE == (TDB_STATE_ ## x))                             \
)

#define TDB_IS_NOW(x) (                                              \
        fprintf(                                                     \
                stderr,                                              \
                "[%s] %16s:%-6d TDB_WAS(%s) --> TDB_IS_NOW(%s)\n",   \
                I_AM_TDB ? "TDB" : "Ty",                             \
                __FILE__,                                            \
                __LINE__,                                            \
                TDB_STATE_NAME,                                      \
                #x                                                   \
        ),                                                           \
        (TDB->state = TDB_STATE_ ## x)                               \
)
#else
#define TDB_IS(x)     (TDB_STATE == (TDB_STATE_ ## x))
#define TDB_IS_NOW(x) (TDB->state = TDB_STATE_ ## x)
#endif

#define TDB_SET_STATE(x) (TDB->state = (x))

void
tdb_start(Ty *ty);

char const *GetInstructionName(unsigned char inst);

void
tdb_set_break(Ty *ty, char *ip);

DebugBreakpoint *
tdb_get_break(Ty *ty, char const *ip);

void
tdb_list(Ty *ty);

void
tdb_go(Ty *ty);

bool
tdb_step_over(Ty *ty);

bool
tdb_step_expr(Ty *ty);

bool
tdb_step_into(Ty *ty);

bool
tdb_step_line(Ty *ty);

Value
tdb_locals(Ty *ty);

void
tdb_backtrace(Ty *ty);

inline static bool
TyHasError(Ty *ty)
{
        return vN(ty->err) > 0;
}

inline static void
TyClearError(Ty *ty)
{
        v0(ty->err);
}

char const *
TyError(Ty *ty);

Ty *
get_my_ty(void);

Value
this_executable(Ty *ty);

void
TyFunctionsCleanup(void);

void
TyValueCleanup(void);

inline static u64
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

inline static u64
TyRealTime()
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

inline static u64
xrotl(u64 x, int k)
{
        return (x << k) | (x >> (64 - k));
}

inline static u64
xoshiro256ss(Ty *ty)
{
        u64 const result = xrotl(ty->prng[1] * 5, 7) * 9;
        u64 const t = ty->prng[1] << 17;

        ty->prng[2] ^= ty->prng[0];
        ty->prng[3] ^= ty->prng[1];
        ty->prng[1] ^= ty->prng[2];
        ty->prng[0] ^= ty->prng[3];

        ty->prng[2] ^= t;
        ty->prng[3] = xrotl(ty->prng[3], 45);

        return result;
}

inline static double
TyRandom(Ty *ty)
{
        return xoshiro256ss(ty) / (double)UINT64_MAX;
}

inline static isize
TyStrLen(Value const *str)
{
        return rune_count(ss(*str), sN(*str));
}

#define afmt(...) ((afmt)(ty, __VA_ARGS__))
#define adump(...) ((adump)(ty, __VA_ARGS__))
#define sxdf(...) ((sxdf)(ty, __VA_ARGS__))
#define sfmt(...) ((sfmt)(ty, __VA_ARGS__))

#define XPRINT_CTX(fmt, ...) do { \
        Expr const *expr   = compiler_find_expr(ty, ty->ip - 1);   \
        Expr const *ret    = vN(ty->st.calls)  ? compiler_find_expr(ty, v_L(ty->st.calls)) : NULL; \
        Expr const *parent = (vN(ty->st.frames) > 1) ? compiler_find_expr(ty, (vZ(ty->st.frames) - 2)->ip) : NULL; \
        LOGX( \
                "(%d:%s) [sp=%3zu fr=%2zu call=%2zu] %s[%12.12s]%s [%s:%d:%d]: %s: " fmt, \
                (int)ty->id,                             \
                (co_active() != ty->co_top) ? ">" : " ", \
                vN(ty->stack),                               \
                vN(ty->st.frames),                              \
                vN(ty->st.calls),                               \
                TERM(91;1), (vN(ty->st.frames) > 0) ? name_of(&vvL(ty->st.frames)->f) : "   --  ", TERM(0), \
                expr ? GetExpressionModule(expr) : "?",  \
                (expr ? expr->start.line : 0) + 1,       \
                (expr ? expr->start.col : 0) + 1,        \
                GetInstructionName(ty->ip[-1])               \
                __VA_OPT__(,) __VA_ARGS__ \
        ); \
} while (0)
#if 0
        if (ret != NULL) { \
                LOGX("    returning to [%s:%d:%d]: %s", \
                        GetExpressionModule(ret), \
                        (ret->start.line) + 1, \
                        (ret->start.col) + 1, \
                        GetInstructionName(*v_L(ty->st.calls)) \
                ); \
        } else if (vN(ty->st.calls) > 0) { \
                LOGX("    returning to [unknown]: %s", \
                        GetInstructionName(*v_L(ty->st.calls)) \
                ); \
        } \
        if (parent != NULL || vN(ty->st.frames) > 1) { \
                LOGX("    parent %s[%s:%12.12s]%s:%d:%d: %s", \
                        TERM(94), \
                        parent ? GetExpressionModule(parent) : "?", \
                        name_of(&(vZ(ty->st.frames) - 2)->f), \
                        TERM(0), \
                        parent ? (parent->start.line) + 1 : 0, \
                        parent ? (parent->start.col) + 1 : 0, \
                        parent ? GetInstructionName(*(vZ(ty->st.frames) - 2)->ip) : "?" \
                ); \
        } \
} while (0)
#endif
#if 0
#define PRINT_CTX(fmt, ...) XPRINT_CTX(fmt, __VA_ARGS__)
#else
#define PRINT_CTX(fmt, ...) ((void)0)
#endif

#endif

/* vim: set sts=8 sw=8 expandtab: */
