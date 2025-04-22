#ifndef TY_H_INCLUDED
#define TY_H_INCLUDED

#include <stdlib.h>
#include <stddef.h>
#include <setjmp.h>
#include <stdbool.h>
#include <inttypes.h>
#include <stdalign.h>
#include <assert.h>

#include <pcre2.h>

#include "libco.h"
#include "vec.h"
#include "intern.h"
#include "panic.h"
#include "tthread.h"

typedef struct ty0        TY;
typedef struct ty         Ty;
typedef struct value      Value;
typedef struct expression Expr;
typedef struct statement  Stmt;
typedef struct symbol     Symbol;
typedef struct scope      Scope;
typedef struct frame      Frame;
typedef struct target     Target;
typedef struct type       Type;
typedef struct constraint Constraint;
typedef struct type_env   TypeEnv;

typedef size_t   usize;
typedef uint64_t u64;
typedef uint32_t u32;

typedef vec(int)            int_vector;
typedef vec(char)           byte_vector;
typedef vec(char *)         CallStack;
typedef vec(Value)          ValueVector;
typedef vec(Value const *)  GCRootSet;
typedef ValueVector         ValueStack;
typedef vec(char *)         StringVector;
typedef vec(char const *)   ConstStringVector;
typedef vec(struct try *)   TryStack;
typedef vec(struct sigfn)   SigfnStack;
typedef vec(size_t)         SPStack;
typedef vec(Frame)          FrameStack;
typedef vec(Target)         TargetStack;
typedef vec(struct alloc *) AllocList;
typedef vec(Symbol *)       symbol_vector;
typedef vec(Type *)         TypeVector;
typedef vec(Constraint)     ConstraintVector;
typedef vec(u32)            U32Vector;
typedef vec(jmp_buf *)      JmpBufVector;

typedef struct array {
        Value *items;
        size_t count;
        size_t capacity;
} Array;

typedef struct blob {
        unsigned char *items;
        size_t count;
        size_t capacity;
} Blob;

typedef struct regex {
        pcre2_code *pcre2;
        char const *pattern;
        bool gc;
        bool detailed;
        uint32_t ncap;
} Regex;

typedef struct {
        char *name;
        char *proto;
        char *doc;
} FunUserInfo;

typedef struct dict Dict;

typedef struct generator Generator;
typedef struct thread Thread;
typedef struct channel Channel;
typedef struct chanval ChanVal;

enum {
        VALUE_FUNCTION = 1     ,
        VALUE_METHOD           ,
        VALUE_BUILTIN_FUNCTION ,
        VALUE_BUILTIN_METHOD   ,
        VALUE_CLASS            ,
        VALUE_GENERATOR        ,
        VALUE_TAG              ,
        VALUE_ARRAY            ,
        VALUE_DICT             ,
        VALUE_OPERATOR         ,
        VALUE_TYPE             ,
        VALUE_REGEX            , // CALLABLE here and above
        VALUE_INTEGER          ,
        VALUE_REAL             ,
        VALUE_BOOLEAN          ,
        VALUE_NIL              ,
        VALUE_OBJECT           ,
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
        VALUE_TAGGED           = 1 << 7
};

typedef Value BuiltinFunction(Ty *, int, Value *);
typedef Value BuiltinMethod(Ty *, Value *, int, Value *);

enum {
        FUN_INFO_HEADER_SIZE,
        FUN_INFO_CODE_SIZE,
        FUN_INFO_CAPTURES,
        FUN_INFO_BOUND,
        FUN_INFO_PARAM_COUNT,
        FUN_INFO__PAD1,
        FUN_INFO_CLASS
};

enum {
        FUN_HEADER_SIZE = 0,
        FUN_CODE_SIZE   = FUN_HEADER_SIZE + sizeof (int),
        FUN_CAPTURES    = FUN_CODE_SIZE   + sizeof (int),
        FUN_BOUND       = FUN_CAPTURES    + sizeof (int),
        FUN_PARAM_COUNT = FUN_BOUND       + sizeof (int),
        FUN_REST_IDX    = FUN_PARAM_COUNT + sizeof (int),
        FUN_KWARGS_IDX  = FUN_REST_IDX    + sizeof (int16_t),
        FUN_CLASS       = FUN_REST_IDX    + sizeof (int),
        FUN_FROM_EVAL   = FUN_CLASS       + sizeof (int),
        FUN_HIDDEN      = FUN_FROM_EVAL   + 1,
        FUN_PROTO       = FUN_HIDDEN      + 1,
        FUN_DOC         = FUN_PROTO       + sizeof (uintptr_t),
        FUN_NAME        = FUN_DOC         + sizeof (uintptr_t),
        FUN_EXPR        = FUN_NAME        + sizeof (uintptr_t),
        FUN_PARAM_NAMES = FUN_EXPR        + sizeof (uintptr_t)
};

struct value {
        uint8_t type;
        uint16_t tags;
        uint32_t src;
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
                        void *ptr;
                        void *gcptr;
                        void *extra;
                };
                struct {
                        intmax_t integer;
                        char const *constant;
                };
                struct {
                        int class;
                        struct itable *object;
                        Type **t0;
                };
                struct {
                        int uop;
                        int bop;
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
                        int name;
                };
                struct {
                        char const *string;
                        uint32_t bytes;
                        char *gcstr;
                };
                struct {
                        intmax_t i;
                        int off;
                        int nt;
                };
                struct {
                        int count;
                        Value *items;
                        int *ids;
                };
                Regex const *regex;
                struct {
                        int *info;
                        Value **env;
                        FunUserInfo *xinfo;
                };
                Expr *namespace;
                Generator *gen;
        };
};

struct frame {
        size_t fp;
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
        uint64_t i;
        bool alive;
};

struct chanval {
        vec(void *) as;
        struct value v;
};

struct channel {
        bool open;
        TyMutex m;
        TyCondVar c;
        vec(ChanVal) q;
};

struct dict {
        unsigned long *hashes;
        struct value *keys;
        struct value *values;
        size_t size;
        size_t count;
        struct value dflt;
};


typedef struct target {
        struct {
                Value *t;
                void *gc;
        };
} Target;

struct frame;
typedef struct frame Frame;

typedef struct table ValueTable;

enum { TRY_TRY, TRY_THROW, TRY_CATCH, TRY_FINALLY };

struct try {
        jmp_buf jb;
        bool executing;
        uint8_t state;
        int sp;
        int gc;
        int cs;
        int ts;
        int ds;
        int ctxs;
        int nsp;
        int exec_depth;
        char *catch;
        char *finally;
        char *end;
        ValueVector defer;
};

typedef struct ThrowCtx {
        int ctxs;
        char const *ip;
} ThrowCtx;

typedef struct ty0 {
        InternSet u_ops;
        InternSet b_ops;
        InternSet members;
} TY;

typedef struct thread_group ThreadGroup;

typedef struct arena Arena;
struct arena {
        char *base;
        char *beg;
        char *end;
        Arena *next;
        bool gc;
};

typedef struct {
        int i;
        void *beg;
} ScratchSave;

typedef struct {
        char *ip;
        char op;
        Expr *cond;
} DebugBreakpoint;

typedef struct param Param;
typedef struct type Type;

struct param {
        Symbol *var;
        Type *type;
        bool required;
        bool rest;
        bool kws;
};

typedef vec(Param) ParamVector;

typedef struct {
        enum {
                TDB_STATE_OFF,
                TDB_STATE_ACTIVE,
                TDB_STATE_STOPPED,
                TDB_STATE_STEPPING
        } state;

        Ty *ty;
        Ty *host;

        Value thread;
        Value hook;

        DebugBreakpoint next;
        DebugBreakpoint alt;
        vec(DebugBreakpoint) breaks;

        byte_vector context_buffer;
} TDB;

typedef struct ty {
        char *ip;

        ValueStack stack;

        co_state st;
        cothread_t co_top;

        int GC_OFF_COUNT;
        int rc;

        size_t memory_used;
        size_t memory_limit;

        AllocList allocs;
        ThreadGroup *my_group;

        TryStack try_stack;
        ValueStack drop_stack;
        vec(ThrowCtx) throw_stack;

        uint64_t prng[4];

        struct {
                pcre2_match_context *ctx;
                pcre2_jit_stack *stack;
                pcre2_match_data *match;
        } pcre2;

        Arena arena;

        struct {
                int i;
                vec(Arena) arenas;
        } scratch;

        char *code;
        jmp_buf jb;
        byte_vector err;

        Scope *tscope;
        TypeEnv *tenv;
        vec(ConstraintVector) tcons;

        TY *ty;
        TDB *tdb;
} Ty;

typedef struct {
        int call;
        int contains;
        int count;
        int _drop_;
        int fmt;
        int _free_;
        int init;
        int _iter_;
        int json;
        int len;
        int _len_;
        int match;
        int missing;
        int method_missing;
        int _name_;
        int _next_;
        int ptr;
        int question;
        int slice;
        int str;
        int subscript;

        int exit_hooks;
        int tdb_hook;
} InternedNames;

#define MemoryUsed  (ty->memory_used)
#define MemoryLimit (ty->memory_limit)

#define MyGroup (ty->my_group)

extern Ty *ty;
extern TY xD;

extern InternedNames NAMES;

extern bool ColorStdout;
extern bool ColorStderr;
extern bool ColorProfile;

extern bool CompileOnly;

#define dont_printf(...) do { } while (0)

#if 0
#define GC_STOP() do { GCLOG("GC_STOP(): " __FILE__ ":%d: %d", __LINE__, ty->GC_OFF_COUNT + 1); ty->GC_OFF_COUNT += 1; } while (0)
#define GC_RESUME() do { GCLOG("GC_RESUME(): " __FILE__ ":%d: %d", __LINE__, ty->GC_OFF_COUNT - 1); ty->GC_OFF_COUNT -= 1; } while (0)
#else
#define GC_STOP()   (ty->GC_OFF_COUNT += 1)
#define GC_RESUME() (ty->GC_OFF_COUNT -= 1)
#endif

#define ErrorBuffer (ty->err)

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

#define TY_INSTRUCTIONS           \
        X(NOP),                   \
        X(LOAD_LOCAL),            \
        X(LOAD_REF),              \
        X(LOAD_CAPTURED),         \
        X(LOAD_GLOBAL),           \
        X(CHECK_INIT),            \
        X(CAPTURE),               \
        X(DECORATE),              \
        X(TARGET_LOCAL),          \
        X(TARGET_REF),            \
        X(TARGET_CAPTURED),       \
        X(TARGET_GLOBAL),         \
        X(TARGET_MEMBER),         \
        X(TARGET_SUBSCRIPT),      \
        X(ASSIGN),                \
        X(MAYBE_ASSIGN),          \
        X(ASSIGN_LOCAL),          \
        X(ASSIGN_GLOBAL),         \
        X(ARRAY_REST),            \
        X(TUPLE_REST),            \
        X(RECORD_REST),           \
        X(INTEGER),               \
        X(REAL),                  \
        X(BOOLEAN),               \
        X(STRING),                \
        X(REGEX),                 \
        X(ARRAY),                 \
        X(DICT),                  \
        X(TUPLE),                 \
        X(DICT_DEFAULT),          \
        X(NIL),                   \
        X(SELF),                  \
        X(TAG),                   \
        X(CLASS),                 \
        X(TO_STRING),             \
        X(FMT1),                  \
        X(FMT2),                  \
        X(CONCAT_STRINGS),        \
        X(RANGE),                 \
        X(INCRANGE),              \
        X(MEMBER_ACCESS),         \
        X(TRY_MEMBER_ACCESS),     \
        X(GET_MEMBER),            \
        X(TRY_GET_MEMBER),        \
        X(SUBSCRIPT),             \
        X(SLICE),                 \
        X(TAIL_CALL),             \
        X(CALL),                  \
        X(CALL_METHOD),           \
        X(TRY_CALL_METHOD),       \
        X(GET_NEXT),              \
        X(PUSH_INDEX),            \
        X(READ_INDEX),            \
        X(LOOP_ITER),             \
        X(LOOP_CHECK),            \
        X(POP),                   \
        X(UNPOP),                 \
        X(DUP),                   \
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
        X(JLE),                   \
        X(JLT),                   \
        X(JGE),                   \
        X(JGT),                   \
        X(JEQ),                   \
        X(JNE),                   \
        X(JUMP_AND),              \
        X(JUMP_OR),               \
        X(JUMP_WTF),              \
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
        X(PUSH_ALL),              \
        X(VALUE),                 \
        X(EVAL),                  \
        X(SAVE_STACK_POS),        \
        X(RESTORE_STACK_POS),     \
        X(POP_STACK_POS),         \
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
#define ARITY(f)    ((f).type == VALUE_FUNCTION ? (((int16_t *)((f).info + 5))[0] == -1 ? (f).info[4] : 100) : 1)

#define zP(...)   vm_panic(ty, __VA_ARGS__)
#define mRE(...)  resize(__VA_ARGS__)
#define mREu(...) resize_unchecked(__VA_ARGS__)
#define mA(...)   gc_alloc(ty, __VA_ARGS__)
#define mAo(...)  gc_alloc_object(ty, __VA_ARGS__)
#define mAo0(...) gc_alloc_object0(ty, __VA_ARGS__)
#define mF(p)     gc_free(ty, p)

#define amA(n)  Allocate(ty, (n))
#define amA0(n) Allocate0(ty, (n))
#define amX(n)  DestroyArena(ty, (n))
#define amF(n)  ReleaseArena(ty, (n))

#define smA(n) AllocateScratch(ty, (n))

#define amN(c)  NewArena(ty, (c))
#define amNg(c) NewArenaGC(ty, (c))

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
#define v__(v, i) ((v).items[(i)])
#define vZ(v)     ((v).items + (v).count)
#define vPx(v, x) ((v).items[(v).count++] = (x))
#define vC(v)     ((v).capacity)

#define vM(v, i, j, n) memmove((v).items + (i), (v).items + (j), (n) sizeof *(v).items)

#define avP(a, b)        VPush((a), (b))
#define avPn(a, b, c)    VPushN(a, b, c)
#define avI(v, x, i)     VInsert(v, x, i)
#define avIn(a, b, c, d) VInsertN(a, b, c, d)
#define avPv(a, b)       VPushN((a), ((b).items), ((b).count))
#define avPvn(a, b, n)   VPushN((a), ((b).items), (n))

#define uvP(v, x)         vec_push_unchecked((v), (x))
#define uvPn(v, xs, n)    vec_push_n_unchecked((v), (xs), (n))
#define uvI(v, x, i)      vec_insert_unchecked((v), (x), (i))
#define uvIn(v, xs, n, i) vec_insert_n_unchecked((v), (xs), (n), (i))
#define uvR(v, n)         vec_reserve_unchecked((v), (n))

#define xvP(a, b)        vec_nogc_push((a), (b))
#define xvPn(a, b, c)    vec_nogc_push_n((a), (b), (c))
#define xvI(a, b, c)     vec_nogc_insert((a), (b), (c))
#define xvIn(a, b, c, d) vec_nogc_insert_n(a, (b), (c), (d))
#define xvR(a, b)        vec_nogc_reserve((a), (b))

#define svPn(a, b, c)    vec_push_n_scratch((a), (b), (c))
#define svP(a, b)        vec_push_scratch((a), (b))
#define svI(a, b, c)     vec_insert_scratch((a), (b), (c))
#define svIn(a, b, c, d) vec_insert_n_scratch(a, (b), (c), (d))

#define gP(x) gc_push(ty, x)
#define gX()  gc_pop(ty)

#define lGv(b) ReleaseLock(ty, b)
#define lTk()  TakeLock(ty)

#define vmP(x)   vm_push(ty, x)
#define vmX()    vm_pop(ty)
#define vmE(x)   vm_throw(ty, x)
#define vmC(...) vm_call(ty, __VA_ARGS__)

#define PAIR(a, b)            PAIR_(ty, (a), (b))
#define TRIPLE(a, b, c)       TRIPLE_(ty, (a), (b), (c))
#define QUADRUPLE(a, b, c, d) QUADRUPLE_(ty, (a), (b), (c), (d))

#define TY_UNARY_OPERATORS   \
        X(COMPL,      "~"),  \
        X(NEG,        "-"),  \
        X(NOT,        "!"),  \
        X(COUNT,      "#"),  \
        X(QUESTION,   "?"),  \
        X(DEC,       "--"),  \
        X(INC,       "++"),  \
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

#define pT(p) ((uintptr_t)p &  7)
#define pP(p) ((uintptr_t)p & ~7)

#define M_ID(m)   intern(&xD.members, (m))->id
#define M_NAME(i) intern_entry(&xD.members, (i))->name

#define PMASK3 ((uintptr_t)7)

inline static void *
mrealloc(void *p, size_t n)
{
        p = realloc(p, n);

        if (UNLIKELY(p == NULL)) {
                panic("Out of memory!");
        }

        return p;
}

inline static void *
alloc0(size_t n)
{
        void *p = calloc(1, n);

        if (UNLIKELY(p == NULL)) {
                panic("Out of memory!");
        }

        return p;
}

#define mresize(ptr, n) ((ptr) = mrealloc((ptr), (n)))

inline static void
ExpandScratch(Ty *ty)
{
#define S(x) (ty->scratch . x)
#define SS   (&S(arenas.items)[S(i) - 1])
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
AllocateScratch(Ty *ty, size_t n)
{
        for (;;) {
                ptrdiff_t avail = SS->end - SS->beg;
                ptrdiff_t padding = -(intptr_t)SS->beg & ((alignof (void *)) - 1);

                if (n > avail - padding) {
                        ExpandScratch(ty);
                } else {
                        char *new = SS->beg + padding;
                        SS->beg += padding + n;
                        return new;
                }
        }
}

inline static ScratchSave
SaveScratch(Ty *ty)
{
        return (ScratchSave) {
                .i = S(i),
                .beg = SS->beg
        };
}

inline static void
RestoreScratch(Ty *ty, ScratchSave save)
{
        while (S(i) > save.i) {
                SS->beg = SS->base;
                S(i) -= 1;
        }
}
#undef S
#undef SS

#define SCRATCH_SAVE()    ScratchSave _scratch_save = SaveScratch(ty);
#define SCRATCH_RESTORE() RestoreScratch(ty, _scratch_save);

#define TDB           (ty->tdb)
#define TDB_TY        ((Ty *)(ty->tdb)->ty)
#define TDB_STATE     ((TDB == NULL) ? TDB_STATE_OFF : TDB->state)
#define TDB_IS(x)     (TDB_STATE == (TDB_STATE_ ## x))
#define TDB_IS_NOW(x) (TDB->state = TDB_STATE_ ## x)
#define DEBUGGING     (!TDB_IS(OFF))

void
tdb_start(Ty *ty);

inline static void
tdb_set_trap(DebugBreakpoint *breakpoint, char *ip)
{
        breakpoint->ip = ip;
        breakpoint->op = *ip;
        *ip = (char)INSTR_TRAP_TY;
}

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

inline static char const *
TyError(Ty *ty)
{
        return ty->err.items;
}

Ty *
get_my_ty(void);

#endif

/* vim: set sts=8 sw=8 expandtab: */
