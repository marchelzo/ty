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
#include "libco.h"

#include "panic.h"
#include "polyfill_stdatomic.h"
#include "tthread.h"
#include "vec.h"
#include "log.h"

#define TY_TMP_BUF_COUNT 2

#define CAT(a, b) a ## b

#define VA_COUNT_INNER(_1, _2, _3, _4, _5, _6, _7, _8, COUNT, ...) COUNT
#define VA_COUNT(...) VA_COUNT_INNER(__VA_ARGS__, 8, 7, 6, 5, 4, 3, 2, 1, 0)

#define VA_SELECT_INNER(f, i) CAT(f ## _, i)
#define VA_SELECT(f, ...) VA_SELECT_INNER(f, VA_COUNT(__VA_ARGS__))(__VA_ARGS__)

typedef struct ty0        TY;
typedef struct ty         Ty;
typedef struct ty_save    TySavePoint;
typedef struct value      Value;
typedef struct expression Expr;
typedef struct statement  Stmt;
typedef struct module     Module;
typedef struct symbol     Symbol;
typedef struct scope      Scope;
typedef struct frame      Frame;
typedef struct target     Target;
typedef struct type       Type;
typedef struct constraint Constraint;
typedef struct refinement Refinement;
typedef struct type_env   TypeEnv;
typedef struct frame      Frame;
typedef struct table      ValueTable;

typedef uint8_t   u8;
typedef uint16_t  u16;
typedef uint32_t  u32;
typedef uint64_t  u64;
typedef size_t    usize;
typedef uintmax_t umax;
typedef uintptr_t uptr;

typedef int8_t   i8;
typedef int16_t  i16;
typedef int32_t  i32;
typedef int64_t  i64;
typedef int64_t  isize;
typedef intmax_t imax;
typedef intptr_t iptr;

typedef vec(struct alloc *) AllocList;
typedef vec(char *)         CallStack;
typedef vec(void *)         ContextVector;
typedef vec(cothread_t)     CoThreadVector;
typedef vec(char const *)   ConstStringVector;
typedef vec(Constraint)     ConstraintVector;
typedef vec(Frame)          FrameStack;
typedef vec(Value)          GCRootSet;
typedef vec(Value *)        GCWorkStack;
typedef vec(jmp_buf *)      JmpBufVector;
typedef vec(Refinement)     RefinementVector;
typedef vec(Scope *)        ScopeVector;
typedef vec(usize)          SPStack;
typedef vec(struct sigfn)   SigfnStack;
typedef vec(char *)         StringVector;
typedef vec(Target)         TargetStack;
typedef vec(struct token)   TokenVector;
typedef vec(struct try *)   TryStack;
typedef vec(Type *)         TypeVector;
typedef vec(u32)            U32Vector;
typedef vec(Value)          ValueVector;
typedef ValueVector         ValueStack;
typedef vec(char)           byte_vector;
typedef vec(bool)           BoolVector;
typedef vec(int)            int_vector;
typedef vec(i32)            i32Vector;
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

typedef struct dict Dict;

typedef struct generator Generator;
typedef struct thread Thread;
typedef struct channel Channel;
typedef struct chanval ChanVal;

typedef struct compiler_state CompileState;

enum { FT_NONE, FT_FUNC, FT_GEN };
enum { MT_NONE, MT_INSTANCE, MT_GET, MT_SET, MT_STATIC, MT_2OP };

enum {
        VALUE_ZERO             ,
        VALUE_FUNCTION = 1     ,
        VALUE_METHOD           ,
        VALUE_BUILTIN_FUNCTION ,
        VALUE_BUILTIN_METHOD   ,
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
        VALUE_PTR              ,
        VALUE_REF              ,
        VALUE_THREAD           ,
        VALUE_TUPLE            ,
        VALUE_BREAK            ,
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
        FUN_PROTO       = FUN_FLAGS       + sizeof (i32),
        FUN_DOC         = FUN_PROTO       + sizeof (uptr),
        FUN_META        = FUN_DOC         + sizeof (uptr),
        FUN_NAME        = FUN_META        + sizeof (uptr),
        FUN_EXPR        = FUN_NAME        + sizeof (uptr),
        FUN_PARAM_NAMES = FUN_EXPR        + sizeof (uptr)
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
                struct {
                        union {
                                Value *ref;
                                void *ptr;
                        };
                        void *gcptr;
                        void *extra;
                };
                struct {
                        imax integer;
                        char const *constant;
                };
                struct {
                        i32 class;
                        struct itable *object;
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
                        int off;
                        int nt;
                };
                struct {
                        i32 count;
                        Value *items;
                        i32 *ids;
                };
                Regex const *regex;
                struct {
                        i32 *info;
                        Value **env;
                        FunUserInfo *xinfo;
                };
                Expr *namespace;
                Generator *gen;
        };
};

struct frame {
        usize fp;
        Value f;
        char const *ip;
};

typedef struct cothread_state {
        int exec_depth;
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

struct thread {
        TyThread t;
        TyMutex mutex;
        TyCondVar cond;

        Value v;
        u64 i;
        bool alive;
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

struct dict {
        u64   *hashes;
        Value *keys;
        Value *values;
        usize size;
        usize count;
        Value dflt;
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

        int GC_OFF_COUNT;
        int rc;

        GCRootSet   gc_roots;
        GCWorkStack marking;

        isize memory_used;
        isize memory_limit;

        AllocList allocs;
        ThreadGroup *my_group;

        CoThreadVector cothreads;

        vec(void *) throw_stack;

        i32 eval_depth;
        u32 flags;

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

        byte_vector err;
        JmpBufVector jbs;

        char *code;

        TyTDB *tdb;
        TY *ty;

        TypeEnv *tenv;
} Ty;

typedef struct {
        int call;
        int _class_;
        int contains;
        int count;
        int _def_;
        int _drop_;
        int _enter_;
        int fmt;
        int _free_;
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
        int slice;
        int str;
        int subscript;
        int _what;

        int _fields_;
        int _methods_;
        int _getters_;
        int _setters_;
        int _static_fields_;
        int _static_methods_;
        int _static_getters_;
        int _static_setters_;

        int _readln;
        int env;
        int exe;
        int exit_hooks;
        int pp;
        int pretty;
        int q;
        int tdb_hook;
} InternedNames;

#define MemoryUsed  (ty->memory_used)
#define MemoryLimit (ty->memory_limit)

#define MyGroup (ty->my_group)

#define TY_IS_READY       (ty->ty->ready)
#define TY_IS_INITIALIZED (ty->ty->initialized)

#define EVAL_DEPTH (ty->eval_depth)

extern Ty *ty;
extern TY xD;

extern InternedNames NAMES;

extern bool ColorStdout;
extern bool ColorStderr;
extern bool ColorProfile;

extern bool CheckTypes;
extern bool CheckConstraints;
extern bool DetailedExceptions;
extern bool CompileOnly;
extern bool AllowErrors;
extern bool InteractiveSession;

extern u64 TypeCheckCounter;
extern u64 TypeAllocCounter;
extern u64 TypeCheckTime;

#if defined(TY_GC_STATS)
extern usize TotalBytesAllocated;
#endif

#define dont_printf(...) 0

#if 0
#define GC_STOP() do { GCLOG("GC_STOP(): " __FILE__ ":%d: %d", __LINE__, ty->GC_OFF_COUNT + 1); ty->GC_OFF_COUNT += 1; } while (0)
#define GC_RESUME() do { GCLOG("GC_RESUME(): " __FILE__ ":%d: %d", __LINE__, ty->GC_OFF_COUNT - 1); ty->GC_OFF_COUNT -= 1; } while (0)
#else
#define GC_STOP()   (ty->GC_OFF_COUNT += 1)
#define GC_RESUME() (ty->GC_OFF_COUNT -= 1)
#endif

#define ALLOC_OF(p) ((struct alloc *)(((char *)(p)) - offsetof(struct alloc, data)))

#define MARKED(v) atomic_load_explicit(&(ALLOC_OF(v))->mark, memory_order_relaxed)
#define MARK(v)   atomic_store_explicit(&(ALLOC_OF(v))->mark, true, memory_order_relaxed)

#define NOGC(v)   atomic_fetch_add_explicit(&(ALLOC_OF(v))->hard, 1, memory_order_relaxed)
#define OKGC(v)   atomic_fetch_sub_explicit(&(ALLOC_OF(v))->hard, 1, memory_order_relaxed)

#define POISON(v)   atomic_store_explicit(&(ALLOC_OF(v))->hard, 0xDEAD, memory_order_seq_cst)
#define POISONED(v) (atomic_load_explicit(&(ALLOC_OF(v))->hard, memory_order_seq_cst) == 0xDEAD)

#define ErrorBuffer (ty->err)

//#define TY_CATCH_ERROR()  (TyClearError(ty), (setjmp(*NewTySavePoint(ty)) != 0))
//#define TY_THROW_ERROR()  (longjmp(**vvX(ty->jbs), 1))
//#define TY_CATCH_END()    (vvX(ty->jbs))

#define TY_CATCH_ERROR() (TyClearError(ty), !VM_TRY())
#define TY_THROW_ERROR() (vm_throw_ty(ty))
#define TY_CATCH_END()   (vm_finally(ty))
#define TY_CATCH()       (vm_catch(ty))
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

#ifndef TY_RELEASE
#define ASSERT(expr, ...) do {                              \
        if (!(expr)) {                                      \
                fprintf(                                    \
                        stderr,                             \
                        "%s:%d: %s: assertion '%s' failed"  \
                        __VA_OPT__(": ")                    \
                        __VA_ARGS__                         \
                        "\n"                                \
                        __FILE__,                           \
                        __LINE__,                           \
                        __func__,                           \
                        #expr                               \
                );                                          \
                abort();                                    \
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
        X(TARGET_LOCAL),          \
        X(TARGET_REF),            \
        X(TARGET_CAPTURED),       \
        X(TARGET_GLOBAL),         \
        X(TARGET_THREAD_LOCAL),   \
        X(TARGET_MEMBER),         \
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
        X(MEMBER_ACCESS),         \
        X(TRY_MEMBER_ACCESS),     \
        X(SELF_MEMBER_ACCESS),    \
        X(SELF_STATIC_ACCESS),    \
        X(STATIC_MEMBER_ACCESS),  \
        X(GET_MEMBER),            \
        X(TRY_GET_MEMBER),        \
        X(SUBSCRIPT),             \
        X(SLICE),                 \
        X(TAIL_CALL),             \
        X(CALL),                  \
        X(CALL_METHOD),           \
        X(TRY_CALL_METHOD),       \
        X(CALL_SELF_METHOD),      \
        X(CALL_STATIC_METHOD),    \
        X(CALL_SELF_STATIC),      \
        X(GET_NEXT),              \
        X(PUSH_INDEX),            \
        X(READ_INDEX),            \
        X(LOOP_ITER),             \
        X(LOOP_CHECK),            \
        X(SPREAD_CHECK),          \
        X(POP),                   \
        X(UNPOP),                 \
        X(DROP2),                 \
        X(DUP),                   \
        X(DUP2),                  \
        X(LEN),                   \
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
        X(DROP_STACK_POS),        \
        X(NEXT),                  \
        X(YIELD),                 \
        X(YIELD_NONE),            \
        X(YIELD_SOME),            \
        X(MAKE_GENERATOR),        \
        X(THROW),                 \
        X(RETHROW),               \
        X(TRY),                   \
        X(CATCH),                 \
        X(END_TRY),               \
        X(RESUME_TRY),            \
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
        X(TRY_TUPLE_MEMBER),      \
        X(TRY_TAG_POP),           \
        X(TRY_REGEX),             \
        X(ASSIGN_REGEX_MATCHES),  \
        X(TRY_ASSIGN_NON_NIL),    \
        X(BAD_MATCH),             \
        X(BAD_CALL),              \
        X(BAD_DISPATCH),          \
        X(BAD_ASSIGN),            \
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

#define INTEGER(k)               ((Value){ .type = VALUE_INTEGER,        .integer        = (k),                                  .tags = 0 })
#define REAL(f)                  ((Value){ .type = VALUE_REAL,           .real           = (f),                                  .tags = 0 })
#define BOOLEAN(b)               ((Value){ .type = VALUE_BOOLEAN,        .boolean        = (b),                                  .tags = 0 })
#define ARRAY(a)                 ((Value){ .type = VALUE_ARRAY,          .array          = (a),                                  .tags = 0 })
#define TUPLE(vs, ns, n, gc)     ((Value){ .type = VALUE_TUPLE,          .items          = (vs), .count = (n),  .ids = (ns),     .tags = 0 })
#define BLOB(b)                  ((Value){ .type = VALUE_BLOB,           .blob           = (b),                                  .tags = 0 })
#define DICT(d)                  ((Value){ .type = VALUE_DICT,           .dict           = (d),                                  .tags = 0 })
#define REGEX(r)                 ((Value){ .type = VALUE_REGEX,          .regex          = (r),                                  .tags = 0 })
#define FUNCTION()               ((Value){ .type = VALUE_FUNCTION,                                                               .tags = 0 })
#define PTR(p)                   ((Value){ .type = VALUE_PTR,            .ptr            = (p),  .gcptr = NULL,                  .tags = 0 })
#define TPTR(t, p)               ((Value){ .type = VALUE_PTR,            .ptr            = (p),  .gcptr = NULL,  .extra = (t),   .tags = 0 })
#define GCPTR(p, gcp)            ((Value){ .type = VALUE_PTR,            .ptr            = (p),  .gcptr = (gcp),                 .tags = 0 })
#define TGCPTR(p, t, gcp)        ((Value){ .type = VALUE_PTR,            .ptr            = (p),  .gcptr = (gcp), .extra = (t),   .tags = 0 })
#define EPTR(p, gcp, ep)         ((Value){ .type = VALUE_PTR,            .ptr            = (p),  .gcptr = (gcp), .extra = (ep),  .tags = 0 })
#define BLOB(b)                  ((Value){ .type = VALUE_BLOB,           .blob           = (b),                                  .tags = 0 })
#define REF(p)                   ((Value){ .type = VALUE_REF,            .ptr            = (p),                                  .tags = 0 })
#define UNINITIALIZED(p)         ((Value){ .type = VALUE_UNINITIALIZED,  .ptr            = (p),                                  .tags = 0 })
#define TAG(t)                   ((Value){ .type = VALUE_TAG,            .tag            = (t),                                  .tags = 0 })
#define CLASS(c)                 ((Value){ .type = VALUE_CLASS,          .class          = (c),  .object = NULL,                 .tags = 0 })
#define TYPE(t)                  ((Value){ .type = VALUE_TYPE,           .ptr            = (t),                                  .tags = 0 })
#define OBJECT(o, c)             ((Value){ .type = VALUE_OBJECT,         .object         = (o),  .class  = (c),                  .tags = 0 })
#define OPERATOR(u, b)           ((Value){ .type = VALUE_OPERATOR,       .uop            = (u),  .bop    = (b),                  .tags = 0 })
#define NAMESPACE(ns)            ((Value){ .type = VALUE_NAMESPACE,      .namespace      = (ns),                                 .tags = 0 })
#define METHOD(n, m, t)          ((Value){ .type = VALUE_METHOD,         .method         = (m),  .this   = (t),  .name = (n),    .tags = 0 })
#define GENERATOR(g)             ((Value){ .type = VALUE_GENERATOR,      .gen            = (g),                                  .tags = 0 })
#define THREAD(t)                ((Value){ .type = VALUE_THREAD,         .thread         = (t),                                  .tags = 0 })
#define BUILTIN_METHOD(n, m, t)  ((Value){ .type = VALUE_BUILTIN_METHOD, .builtin_method = (m),  .this   = (t),  .name = (n),    .tags = 0 })
#define NIL                      ((Value){ .type = VALUE_NIL,                                                                    .tags = 0 })
#define INDEX(ix, o, n)          ((Value){ .type = VALUE_INDEX,          .i              = (ix), .off   = (o), .nt = (n),        .tags = 0 })
#define SENTINEL                 ((Value){ .type = VALUE_SENTINEL,       .i              = 0,    .off   = 0,                     .tags = 0 })
#define NONE                     ((Value){ .type = VALUE_NONE,           .i              = 0,    .off   = 0,                     .tags = 0 })
#define BREAK                    ((Value){ .type = VALUE_BREAK,          .i              = 0,    .off   = 0,                     .tags = 0 })

#define CALLABLE(v) ((v).type <= VALUE_REGEX)
#define ARITY(f)    ((f).type == VALUE_FUNCTION ? (((i16 *)((f).info + 5))[0] == -1 ? (f).info[4] : 100) : 1)

#define m0(x) memset(&(x), 0, sizeof (x))

#define zP(...)    vm_error(ty, __VA_ARGS__)
#define zPx(...)   vm_panic(ty, __VA_ARGS__)
#define zPxx(...)   vm_panic_ex(ty, __VA_ARGS__)

#define mRE(...)   resize(__VA_ARGS__)
#define mREu(...)  resize_unchecked(__VA_ARGS__)
#define mA(...)    gc_alloc(ty, __VA_ARGS__)
#define mA0(...)   gc_alloc0(ty, __VA_ARGS__)
#define mAo(...)   gc_alloc_object(ty, __VA_ARGS__)
#define mAo0(...)  gc_alloc_object0(ty, __VA_ARGS__)
#define mF(p)      gc_free(ty, p)

#define uAo(...)   gc_alloc_object_unchecked(ty, __VA_ARGS__)

#define amA(n)  Allocate(ty, (n))
#define amA0(n) Allocate0(ty, (n))
#define amX(n)  DestroyArena(ty, (n))
#define amF(n)  ReleaseArena(ty, (n))

#define aclone(x) memcpy(amA(sizeof *(x)), (x), sizeof *(x))

#define smA(n) AllocateScratch(ty, (n))
#define smA0(n) AllocateScratch0(ty, (n))

#define xmA(n) mrealloc(NULL, (n))

#define vSs(s, n)  STRING_CLONE(ty, (s), (n))
#define vSzs(s, n) STRING_C_CLONE(ty, (s), (n))
#define vSsz(s)    STRING_CLONE_C(ty, (s))
#define vSzz(s)    STRING_C_CLONE_C(ty, (s))

#define xSs(s, n) STRING_NOGC((s), (n))
#define xSz(s)    STRING_NOGC_C(s)

#define vA()       value_array_new(ty)
#define vAn(n)     value_array_new_sized(ty, n)
#define vAp(a, x)  value_array_push(ty, a, x)

#define vT(n)     value_tuple(ty, n)
#define vTn(...)  value_named_tuple(ty, __VA_ARGS__, NULL)

#define vvPn(a, b, c)     vec_push_n((a), (b), (c))
#define vvPv(v, u)        vec_push_n((v), (u).items, (u).count)
#define vvP(a, b)         vec_push((a), (b))
#define vvI(v, x, i)      vec_insert((v), (x), (i))
#define vvIn(v, xs, n, i) vec_insert_n((v), (xs), (n), (i))
#define vvF(a)            mF((a).items)
#define vv0(v)            vec_empty(v)
#define vvR(a, b)         vec_reserve((a), (b))

#define vvX  vec_pop
#define vvL  vec_last
#define vvXi vec_pop_ith

#define vN(v)     ((v).count)
#define v0(v)     ((v).count = 0)
#define v00(v)    (((v).count = 0), ((v).items = NULL), ((v).capacity = 0))
#define v_(v, i)  (&(v).items[(i)])
#define v_0(v)    ((v).items[0])
#define v_L(v)    ((v).items[(v).count - 1])
#define v__(v, i) ((v).items[(i)])
#define vv(v)     ((v).items)
#define vZ(v)     ((v).items + (v).count)
#define vPx(v, x) ((v).items[(v).count++] = (x))
#define vC(v)     ((v).capacity)

#define vM(v, i, j, n) memmove((v).items + (i), (v).items + (j), (n) sizeof *(v).items)

#define vfor_4(i, x, v, go) for (isize i = 0; i < vN(v); ++i) { typeof (vv(v)) x = v_((v), i); go; }
#define vfor_3(   x, v, go) vfor_4(_i_##x, x,  (v), (go))
#define vfor_2(      v, go) vfor_4(_vfi,   it, (v), (go))

#define vfor(...) VA_SELECT(vfor, __VA_ARGS__)

#define avP(a, b)        VPush((a), (b))
#define avPn(a, b, c)    VPushN(a, b, c)
#define avI(v, x, i)     VInsert(v, x, i)
#define avIn(a, b, c, d) VInsertN(a, b, c, d)
#define avPv(a, b)       VPushN((a), ((b).items), ((b).count))
#define avPvn(a, b, n)   VPushN((a), ((b).items), (n))
#define avR(v, n)        VReserve((v), (n))

#define avC(v) (                                       \
        (v).items = memcpy(                            \
                amA((v).capacity * sizeof *(v).items), \
                (v).items,                             \
                ((v).count * sizeof *(v).items)        \
        )                                              \
)

#define uvP(v, x)         vec_push_unchecked((v), (x))
#define uvPn(v, xs, n)    vec_push_n_unchecked((v), (xs), (n))
#define uvPv(v, u)        vec_push_n_unchecked((v), ((u).items), ((u).count))
#define uvI(v, x, i)      vec_insert_unchecked((v), (x), (i))
#define uvIn(v, xs, n, i) vec_insert_n_unchecked((v), (xs), (n), (i))
#define uvR(v, n)         vec_reserve_unchecked((v), (n))

#define xvP(a, b)        vec_nogc_push((a), (b))
#define xvPn(a, b, c)    vec_nogc_push_n((a), (b), (c))
#define xvPv(a, b)       vec_nogc_push_n((a), ((b).items), ((b).count))
#define xvI(a, b, c)     vec_nogc_insert((a), (b), (c))
#define xvIn(a, b, c, d) vec_nogc_insert_n(a, (b), (c), (d))
#define xvR(a, b)        vec_nogc_reserve((a), (b))
#define xvF(v)           free((v).items)

#define svPn(a, b, c)    vec_push_n_scratch((a), (b), (c))
#define svPv(a, b)       vec_push_n_scratch((a), ((b).items), ((b).count))
#define svP(a, b)        vec_push_scratch((a), (b))
#define svI(a, b, c)     vec_insert_scratch((a), (b), (c))
#define svIn(a, b, c, d) vec_insert_n_scratch(a, (b), (c), (d))
#define svR(v, n)        vec_reserve_scratch((v), (n))

#define gP(x) (xvP(RootSet, *(x)))
#define gX()  (vvX(RootSet))

#define lGv(b) ReleaseLock(ty, b)
#define lTk()  TakeLock(ty)

#define vmP(x)   vm_push(ty, x)
#define vmX()    vm_pop(ty)
#define vmE(x)   vm_throw(ty, x)
#define vmC(...) vm_call(ty, __VA_ARGS__)

#define PAIR(a, b)            PAIR_(ty, (a), (b))
#define TRIPLE(a, b, c)       TRIPLE_(ty, (a), (b), (c))
#define QUADRUPLE(a, b, c, d) QUADRUPLE_(ty, (a), (b), (c), (d))

#define TAGGED(t, ...) tagged(ty, (t), __VA_ARGS__, NONE)
#define TAGGED_RECORD(t, ...) tagged(ty, (t), vTn(__VA_ARGS__), NONE)

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

enum {
        TY_COLOR_AUTO,
        TY_COLOR_ALWAYS,
        TY_COLOR_NEVER
};

#define FMT_MORE "\n                 "
#define FMT_CS   "%s%s%s"

#define FMT_MAGENTA2(s) TERM(95), (s), TERM(0)

#define VSC(v) value_show_color(ty, v)

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
        p = realloc(p, n);

        if (UNLIKELY(p == NULL)) {
                panic("Out of memory!");
        }

        return p;
}

inline static void *
alloc0(usize n)
{
        void *p = calloc(1, n);

        if (UNLIKELY(p == NULL)) {
                panic("Out of memory!");
        }

        return p;
}

#define mresize(ptr, n) ((ptr) = mrealloc((ptr), (n)))

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

inline static jmp_buf *
NewTySavePoint(Ty *ty)
{
        usize n = vN(ty->jbs);

        if (n == vC(ty->jbs)) {
                do xvP(ty->jbs, mrealloc(NULL, sizeof (jmp_buf)));
                while (vN(ty->jbs) < vC(ty->jbs));
        }

        vN(ty->jbs) = n + 1;

        return *vvL(ty->jbs);
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
                n = val.bytes;
                str = val.str;
                break;

        case VALUE_BLOB:
                n = vN(*val.blob);
                str = vv(*val.blob);
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
                n = val.bytes;
                str = val.str;
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
#define TY_TMP() TY_BUF(TY_TMP_N)

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

inline static char const *
TyError(Ty *ty)
{
        return (vN(ty->err) > 0) ? vv(ty->err) : "(no error)";
}

Ty *
get_my_ty(void);

Value
this_executable(Ty *ty);

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

#endif

/* vim: set sts=8 sw=8 expandtab: */
