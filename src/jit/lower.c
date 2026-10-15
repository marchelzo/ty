#include "ty.h"
#include "vm.h"
#include "compiler.h"
#include "operators.h"
#include "inline.h"
#include "types2.h"
#include "jit/lir.h"
#include "jit_impl.h"

typedef struct bc_lir_node {
        u8          op;
        bool        branch;
        i32         next;
        i32         target;
        i32         sp;
        i32         fall_sp;
        i32         saved;
        i32         sentinel;
        i32         sentinel_sp;
        i32         owner;
        i32         outer;
        i32         catch_to;
        i32         finally_to;
        i32         end_to;
        i32         argc;
        i32         global;
        i32         nkw;
        i32         member;
        char const *kw_ip;
        LirLabel    label;
        LirLabel    deopt;
        LirLabel    resume;
        u32         resume_id;
        LirLabel    osr;
        u32         osr_id;
} BcLirNode;

typedef struct bc_slot {
        u8     kind;
        LirReg r;
        u64    bits;
        T2Type hint;
        i32    src;
        i32    off;
} BcSlot;

typedef struct bc_loop {
        i32      head;
        i32      end;
        i32      sp;
        LirLabel deopt;
        i32      slots[8];
        i32      nslots;
        u8      *live;
        i32      owned[8];
        u8       owned_bit[8];
        LirReg   owned_reg[8];
        i32      nowned;
        bool     stack;
        LirReg   sreg[2];
        i32      arrays[4];
        i32      akind[4];
        LirReg   areg[4][3];
        i32      narrays;
        bool     lazy;
        u8       written;
        u8       escaping;
        u8       deferred;
        i32      ivar;
        i32      isrc;
        u8       ishift;
} BcLoop;

typedef struct {
        LirLabel stub;
        LirLabel target;
        i32      to;
        i32      inner;
        bool     done;
} BcExit;

typedef struct {
        u8     kind;
        LirReg r;
        bool   keep;
} BcJoin;

typedef struct {
        i32 cont;
        i32 base;
        i32 lo;
        i32 hi;
        u32 gen;
} BcFact;

typedef struct bc_lir {
        Lir                  *L;
        Ty                   *ctx;
        Value const          *function;
        char const           *code;
        BcLirNode            *nodes;
        i32                   size;
        u32                   offset;
        i32                   at;
        bool                  ok;
        bool                  dynamic;
        bool                  has_try;
        bool                  compact;
        bool                  speculate;
        bool                  skip_next;
        i32                   skip_extra;

        LirReg                ty;
        LirReg                locals;
        LirReg                env;
        LirReg                fp;
        LirReg                ops;
        LirReg                base_index;
        LirLabel              deopt;

        i32                   sp;
        i32                   bound;
        i32                   max_sp;
        i32                   self_index;
        i32                   saved;
        i32                   sentinel;
        i32                   sentinel_sp;
        u32                   nresume;
        u32                   nosr;
        u32                   last_call;
        i32                  *tier;

        BcSlot               *vs;
        BcSlot               *known;
        u32                  *known_gen;
        u32                   gen;
        BcFact                facts[8];
        i32                   nfacts;
        i32                   tuple_off;
        i32                   tuple_sp;
        i32                   tuple_min;
        i32                  *local_class;
        T2Type               *local_type;
        LirReg              **held;
        TypeHintVector const *hints;

        BcLoop               *loops;
        i32                   nloops;
        LirReg               *lreg;
        i32                  *lowner;
        i32                  *hkind;
        BcJoin               *joins;
        bool                 *stubbed;
        bool                  falls;
        BcExit               *exits;
        i32                   nexits;
        i32                   cexits;
        LirReg               *spin;
        i32                  *active;
        i32                   nactive;
} BcLir;

#define new(c, T, n)   ((T *)AllocateScratch0((c)->ctx, (usize)(n) * sizeof (T)))
#define nones(c, T, n) ((T *)memset(new(c, T, n), 0xff, (usize)(n) * sizeof (T)))

static bool
method_fast(BcLir *c, BcLirNode const *node);

static i32
prepare_call(Ty *ty, Value *out, Value *fn, i32 argc);

static void
sync_call(Ty *ty, Value *out, Value *fn, i32 argc);

static void
native_call(BcLir *c, LirOpnd *enter_args);

static void
native_invoke(BcLir *c, LirReg frame, LirReg out);

static Frame *
method_enter(Ty *ty, Value *top, i32 op, i32 member, i32 argc, char *kw_ip);

static void
inline_call(
        BcLir *c,
        LirReg fn,
        Value const *callee,
        i32 out,
        i32 argc,
        LirReg self,
        LirLabel miss,
        LirLabel done
);

static bool
inline_method(BcLir *c, BcLirNode const *node, LirLabel *done);

static bool
builtin_call(
        BcLir *c,
        LirReg fn,
        Value const *callee,
        i32 out,
        i32 argc,
        LirLabel miss,
        LirLabel done
);

static bool
kernel_ok(LirCode const *code, i32 argc);

static bool
kernel_call(
        BcLir *c,
        LirReg fn,
        Value const *callee,
        i32 out,
        i32 argc,
        LirLabel miss,
        LirLabel done
);

static bool
inline_ctor(
        BcLir *c,
        LirReg fn,
        Value const *callee,
        i32 out,
        i32 argc,
        LirLabel *ready
);

static bool
try_plan(
        BcLir *c,
        Value const *callee,
        TyInlineKind kind,
        i32 argc,
        i32 base,
        LirReg self,
        Class *self_class,
        Class **arg_classes,
        i32 out,
        LirLabel done
);

static void
state(BcLir *c, BcLirNode const *node, char const *ip);

static bool
loop_lower(BcLir *c, BcLirNode const *node, char const *ip);

static LirReg const *
held_array(BcLir const *c, i32 i);

static LirReg const *
held_blob(BcLir const *c, i32 i);

static LirReg const *
held_any(BcLir const *c, i32 i);

static LirReg
loop_reg(BcLir const *c, i32 slot);

static bool
loop_pinned(BcLir const *c, i32 pos);

#include "lower/build.h"

static void
local_load(BcLir *c, i32 slot)
{
        copy(c, c->ops, vat(c->sp++), c->locals, vat(slot));
}

static void
local_store(BcLir *c, i32 slot)
{
        copy(c, c->locals, vat(slot), c->ops, vat(--c->sp));
}

static void
literal(BcLir *c, i32 type, u64 bits)
{
        put_scalar(c, c->sp++, type, lir_i(bits));
}

typedef struct {
        LirOp  iop;
        LirOp  fop;
        LirCC  icc;
        LirCC  fcc;
        void  *helper;
} BcBoxed;

static BcBoxed const BoxedOps[256] = {
        [INSTR_ADD] = { LIR_ADD,   LIR_FADD,   LIR_EQ, LIR_FEQ, jit_rt_add },
        [INSTR_SUB] = { LIR_SUB,   LIR_FSUB,   LIR_EQ, LIR_FEQ, jit_rt_sub },
        [INSTR_MUL] = { LIR_MUL,   LIR_FMUL,   LIR_EQ, LIR_FEQ, jit_rt_mul },
        [INSTR_EQ]  = { LIR_SETCC, LIR_FSETCC, LIR_EQ, LIR_FEQ, jit_rt_eq  },
        [INSTR_NEQ] = { LIR_SETCC, LIR_FSETCC, LIR_NE, LIR_FNE, jit_rt_ne  },
        [INSTR_LT]  = { LIR_SETCC, LIR_FSETCC, LIR_LT, LIR_FLT, jit_rt_lt  },
        [INSTR_GT]  = { LIR_SETCC, LIR_FSETCC, LIR_GT, LIR_FGT, jit_rt_gt  },
        [INSTR_LEQ] = { LIR_SETCC, LIR_FSETCC, LIR_LE, LIR_FLE, jit_rt_le  },
        [INSTR_GEQ] = { LIR_SETCC, LIR_FSETCC, LIR_GE, LIR_FGE, jit_rt_ge  }
};

_Static_assert(VOFF(z) == VOFF(real), "z and real must overlap");

static LirReg
combine(BcLir *c, LirOp op, LirCC cc, LirClass cls, LirReg a, LirReg b)
{
        if (op == LIR_SETCC || op == LIR_FSETCC) {
                return vop(c, op, LIR_I64, lir_cc(cc), lir_r(a), lir_r(b));
        }

        return vop(c, op, cls, lir_r(a), lir_r(b));
}

static void
promote_pair(BcLir *c, LirReg at, LirReg bt, LirLabel slow, LirReg *a, LirReg *b)
{
        i32      lhs  = c->sp - 2;
        i32      rhs  = c->sp - 1;
        LirOpnd  la   = mref(c->ops, vat(lhs) + VOFF(real));
        LirOpnd  lb   = mref(c->ops, vat(rhs) + VOFF(real));
        LirLabel lint = newlabel(c);
        LirLabel rint = newlabel(c);
        LirLabel done = newlabel(c);

        *a = lir_reg(c->L, LIR_F64);
        *b = lir_reg(c->L, LIR_F64);

        unless(c, at, VALUE_REAL, lint);
        set(c, LIR_LD_F64, *a, &la, 1);
        unless(c, bt, VALUE_REAL, rint);
        set(c, LIR_LD_F64, *b, &lb, 1);
        jump(c, done);

        bind(c, rint);
        unless(c, bt, VALUE_INTEGER, slow);
        vset(c, LIR_I2F, *b, lir_r(int_at(c, rhs)));
        jump(c, done);

        bind(c, lint);
        unless(c, at, VALUE_INTEGER, slow);
        unless(c, bt, VALUE_REAL, slow);
        vset(c, LIR_I2F, *a, lir_r(int_at(c, lhs)));
        set(c, LIR_LD_F64, *b, &lb, 1);

        bind(c, done);
}

static void
numeric(BcLir *c, u8 op)
{
        BcBoxed const *ar     = &BoxedOps[op];
        bool           cmp    = (ar->iop == LIR_SETCC);
        i32            lhs    = c->sp - 2;
        i32            rhs    = c->sp - 1;
        LirLabel       floats = newlabel(c);
        LirLabel       slow   = newlabel(c);
        LirLabel       end    = newlabel(c);
        LirReg         at     = tag_of(c, lhs);
        LirReg         bt     = tag_of(c, rhs);

        unless(c, at, VALUE_INTEGER, floats);
        unless(c, bt, VALUE_INTEGER, floats);

        LirReg a = int_at(c, lhs);
        LirReg b = int_at(c, rhs);
        LirReg d = combine(c, ar->iop, ar->icc, LIR_I64, a, b);

        if (cmp) {
                put_scalar(c, lhs, VALUE_BOOLEAN, lir_r(d));
        } else {
                stq(c, c->ops, vat(lhs) + VOFF(z), lir_r(d));
        }

        jump(c, end);
        bind(c, floats);

        if (c->compact || op == INSTR_EQ || op == INSTR_NEQ) {
                unless(c, at, VALUE_REAL, slow);
                unless(c, bt, VALUE_REAL, slow);
                a = real_at(c, lhs);
                b = real_at(c, rhs);
        } else {
                promote_pair(c, at, bt, slow, &a, &b);
        }

        d = combine(c, ar->fop, ar->fcc, LIR_F64, a, b);

        if (cmp) {
                put_scalar(c, lhs, VALUE_BOOLEAN, lir_r(d));
        } else {
                stq(c, c->ops, vat(lhs) + VOFF(type), lir_i(VALUE_REAL));
                stf(c, c->ops, vat(lhs) + VOFF(real), lir_r(d));
        }

        jump(c, end);
        bind(c, slow);

        LirReg out = slot_of(c, lhs);
        LirReg arg = slot_of(c, rhs);

        tycall(c, ar->helper, LT_VOID, preg(out), preg(out), preg(arg));

        bind(c, end);

        c->sp -= 1;
}

static void
stack_index(BcLir *c, LirReg p, LirReg dst)
{
        LirReg base  = ldq(c, c->ty, offsetof(Ty, stack.items));
        LirReg bits  = vop(c, LIR_BITCAST, LIR_I64, lir_r(p));
        LirReg bytes = vop(c, LIR_SUB, LIR_I64, lir_r(bits), lir_r(base));

        vset(c, LIR_SHR, dst, lir_r(bytes), lir_i(__builtin_ctz(sizeof (Value))));
}

static void
base_slot(BcLir *c)
{
        stack_index(c, c->ops, c->base_index);
}

static void
count_at(BcLir *c, i32 slot)
{
        LirReg count = c->base_index;

        if (count == LIR_NONE) {
                count = lir_reg(c->L, LIR_I64);
                stack_index(c, slot_of(c, slot), count);
        } else if (slot != 0) {
                count = vop(c, LIR_ADD, LIR_I64, lir_r(count), lir_i(slot));
        }

        stq(c, c->ty, offsetof(Ty, stack.count), lir_r(count));
}

static void
sync_sp(BcLir *c)
{
        count_at(c, c->sp);
}

static void
resync(BcLir *c, BcLirNode const *node)
{
        c->sp = node->fall_sp;
        sync_sp(c);
}

static void
poll(BcLir *c, LirReg top, LirOpnd info, LirLabel deopt)
{
        LirInst in = {
                .op    = LIR_POLL,
                .dst   = LIR_NONE,
                .args  = { lir_r(c->ty), lir_r(top), info, lir_l(deopt) },
                .nargs = 4,
                .flags = LIR_CALL_SITE,
                .tag   = c->offset
        };

        c->ok = c->ok && lir_emit(c->L, &in);
}

static JitDeopt DeoptAt[512];

__attribute__((constructor))
static void
deopt_table(void)
{
        for (i32 i = 0; i < countof(DeoptAt); ++i) {
                DeoptAt[i] = (JitDeopt) { .sp = i };
        }
}

static LirOpnd
deopt_info(BcLir *c)
{
        if (c->sp >= 0 && c->sp < countof(DeoptAt)) {
                return lir_i((uptr)&DeoptAt[c->sp]);
        }

        LirReg info = vop(
                c,
                LIR_ALLOCA,
                LIR_PTR,
                lir_i(sizeof (JitDeopt)),
                lir_i(alignof (JitDeopt))
        );

        stw(c, info, offsetof(JitDeopt, sp), lir_i(c->sp));
        stw(c, info, offsetof(JitDeopt, nsave), lir_i(0));

        return lir_r(info);
}

static void
safepoint(BcLir *c, LirLabel deopt)
{
        LirOpnd info = deopt_info(c);
        poll(c, slot_of(c, c->sp), info, deopt);
}

static void
tier_hot(i32 *count, i32 *info)
{
        Value f = { .type = VALUE_FUNCTION, .info = info };
        *count = INT32_MAX;
        jit_tier_up(&f);
}

static void
tier_check(BcLir *c, LirLabel deopt)
{
        LirLabel cold = newlabel(c);
        LirReg   p    = pval(c, c->tier);
        LirReg   n    = ldw(c, p, 0);
        LirReg   m    = vop(c, LIR_ADD, LIR_I64, lir_r(n), lir_i(-1));

        stw(c, p, 0, lir_r(m));
        jcc(c, LIR_GT, lir_r(m), lir_i(0), cold);

        ccallf(
                c,
                tier_hot,
                LT_VOID,
                LIR_READS_NO_LOCALS,
                preg(p),
                pimm(c->function->info)
        );

        if (deopt != LIR_NONE) {
                sync_sp(c);
                jump(c, deopt);
        }

        bind(c, cold);
}

typedef struct {
        i32 *at;
        u32  n;
} BcQueue;

typedef struct {
        bool known;
        bool stop;
        bool post;
        i8   need;
        i8   delta;
} BcEffect;

#define FX(n, d)  { .known = true, .need = (n), .delta = (d) }
#define FXP(n, d) { .known = true, .need = (n), .delta = (d), .post = true }
#define FXS(n)    { .known = true, .need = (n), .stop = true }

static BcEffect const Effects[256] = {
        [INSTR_NOP]                  = FX(0, 0),
        [INSTR_JUMP]                 = FX(0, 0),
        [INSTR_CATCH]                = FX(0, 0),
        [INSTR_POP_TRY]              = FX(0, 0),
        [INSTR_CHECK_INIT]           = FX(0, 0),
        [INSTR_JUMP_IF_INIT]         = FX(0, 0),
        [INSTR_SKIP_CHECK]           = FX(0, 0),
        [INSTR_TARGET_GLOBAL]        = FX(0, 0),
        [INSTR_TARGET_THREAD_LOCAL]  = FX(0, 0),
        [INSTR_TARGET_SELF_STATIC]   = FX(0, 0),
        [INSTR_TARGET_STATIC_MEMBER] = FX(0, 0),
        [INSTR_TARGET_SELF_MEMBER]   = FX(0, 0),
        [INSTR_TARGET_LOCAL]         = FX(0, 0),
        [INSTR_TARGET_CAPTURED]      = FX(0, 0),
        [INSTR_TARGET_REF]           = FX(0, 0),
        [INSTR_DROP]                 = FX(0, 0),
        [INSTR_DISCARD_DROP_GROUP]   = FX(0, 0),
        [INSTR_PUSH_DROP_GROUP]      = FX(0, 0),
        [INSTR_PUSH_DEFER_GROUP]     = FX(0, 0),
        [INSTR_CLEANUP]              = FX(0, 0),
        [INSTR_EXEC_CODE]            = FX(0, 0),
        [INSTR_DEBUG]                = FX(0, 0),
        [INSTR_REVERSE]              = FX(0, 0),
        [INSTR_CAPTURE]              = FX(0, 0),
        [INSTR_PATCH_ENV]            = FX(0, 0),

        [INSTR_MUT_ADD]              = FX(1, 0),
        [INSTR_MUT_SUB]              = FX(1, 0),
        [INSTR_MUT_MUL]              = FX(1, 0),
        [INSTR_MUT_DIV]              = FX(1, 0),
        [INSTR_MUT_MOD]              = FX(1, 0),
        [INSTR_MUT_AND]              = FX(1, 0),
        [INSTR_MUT_OR]               = FX(1, 0),
        [INSTR_MUT_XOR]              = FX(1, 0),
        [INSTR_MUT_SHL]              = FX(1, 0),
        [INSTR_MUT_SHR]              = FX(1, 0),
        [INSTR_ASSIGN]               = FX(1, 0),
        [INSTR_MAYBE_ASSIGN]         = FX(1, 0),
        [INSTR_DECORATE]             = FX(1, 0),
        [INSTR_INTO_METHOD]          = FX(1, 0),
        [INSTR_BIND_CLASS]           = FX(1, 0),
        [INSTR_BIND_INSTANCE]        = FX(1, 0),
        [INSTR_BIND_GETTER]          = FX(1, 0),
        [INSTR_BIND_SETTER]          = FX(1, 0),
        [INSTR_PUSH_DROP]            = FX(1, 0),
        [INSTR_ENTER]                = FX(1, 0),
        [INSTR_TRY_YIELD_FROM]       = FX(1, 0),
        [INSTR_UNARY_OP]             = FX(1, 0),
        [INSTR_QUESTION]             = FX(1, 0),
        [INSTR_TO_REGEX]             = FX(1, 0),
        [INSTR_COMPILE_REGEX]        = FX(1, 0),
        [INSTR_EVAL]                 = FX(1, 0),
        [INSTR_GET_TAG]              = FX(1, 0),
        [INSTR_NONE_IF_NIL]          = FX(1, 0),
        [INSTR_RETURN_IF_NOT_NONE]   = FX(1, 0),
        [INSTR_JUMP_IF_SENTINEL]     = FX(1, 0),
        [INSTR_JUMP_IF_NONE]         = FX(1, 0),
        [INSTR_JUMP_IF_TYPE]         = FX(1, 0),
        [INSTR_UNTAG_OR_DIE]         = FX(1, 0),
        [INSTR_STEAL_TAG]            = FX(1, 0),
        [INSTR_THROW_IF_NIL]         = FX(1, 0),
        [INSTR_MEMBER_ACCESS]        = FX(1, 0),
        [INSTR_TRY_MEMBER_ACCESS]    = FX(1, 0),
        [INSTR_NEG]                  = FX(1, 0),
        [INSTR_NOT]                  = FX(1, 0),
        [INSTR_INC]                  = FX(1, 0),
        [INSTR_DEC]                  = FX(1, 0),
        [INSTR_TO_STRING]            = FX(1, 0),
        [INSTR_COUNT]                = FX(1, 0),
        [INSTR_CLASS_OF]             = FX(1, 0),
        [INSTR_TAG_PUSH]             = FX(1, 0),
        [INSTR_YIELD]                = FX(1, 0),
        [INSTR_YIELD_SOME]           = FX(1, 0),
        [INSTR_ENSURE_LEN]           = FX(1, 0),
        [INSTR_ENSURE_LEN_TUPLE]     = FX(1, 0),
        [INSTR_ENSURE_DICT]          = FX(1, 0),
        [INSTR_TRY_ASSIGN_NON_NIL]   = FX(1, 0),
        [INSTR_TRY_TAG_POP]          = FX(1, 0),
        [INSTR_TRY_STEAL_TAG]        = FX(1, 0),
        [INSTR_ARRAY_REST]           = FX(1, 0),
        [INSTR_TUPLE_REST]           = FX(1, 0),
        [INSTR_RECORD_REST]          = FX(1, 0),
        [INSTR_UNAPPLY]              = FX(2, 0),

        [INSTR_LOAD_LOCAL]           = FX(0, 1),
        [INSTR_LOAD_GLOBAL]          = FX(0, 1),
        [INSTR_LOAD_CAPTURED]        = FX(0, 1),
        [INSTR_LOAD_REF]             = FX(0, 1),
        [INSTR_LOAD_THREAD_LOCAL]    = FX(0, 1),
        [INSTR_PRE_INC]              = FX(0, 1),
        [INSTR_POST_INC]             = FX(0, 1),
        [INSTR_PRE_DEC]              = FX(0, 1),
        [INSTR_POST_DEC]             = FX(0, 1),
        [INSTR_BIND_STATIC]          = FX(0, 1),
        [INSTR_SELF_STATIC_ACCESS]   = FX(0, 1),
        [INSTR_STATIC_MEMBER_ACCESS] = FX(0, 1),
        [INSTR_SELF_MEMBER_ACCESS]   = FX(0, 1),
        [INSTR_NAMESPACE]            = FX(0, 1),
        [INSTR_TRACE]                = FX(0, 1),
        [INSTR_OPERATOR]             = FX(0, 1),
        [INSTR_READ_INDEX]           = FX(0, 1),
        [INSTR_UNPOP]                = FX(0, 1),
        [INSTR_PUSH_INDEX]           = FX(0, 1),
        [INSTR_ARRAY0]               = FX(0, 1),
        [INSTR_STRING]               = FX(0, 1),
        [INSTR_SELF]                 = FX(0, 1),
        [INSTR_CLASS]                = FX(0, 1),
        [INSTR_TAG]                  = FX(0, 1),
        [INSTR_REGEX]                = FX(0, 1),
        [INSTR_TYPE]                 = FX(0, 1),
        [INSTR_VALUE]                = FX(0, 1),
        [INSTR_FUNCTION]             = FX(0, 1),
        [INSTR_GENERATOR]            = FX(0, 1),
        [INSTR_INT8]                 = FX(0, 1),
        [INSTR_INTEGER]              = FX(0, 1),
        [INSTR_REAL]                 = FX(0, 1),
        [INSTR_TRUE]                 = FX(0, 1),
        [INSTR_FALSE]                = FX(0, 1),
        [INSTR_NIL]                  = FX(0, 1),
        [INSTR_NONE]                 = FX(0, 1),
        [INSTR_YIELD_NONE]           = FX(0, 1),
        [INSTR_DUP]                  = FX(1, 1),
        [INSTR_PUSH_NTH]             = FX(1, 1),
        [INSTR_PUSH_ARRAY_ELEM]      = FX(1, 1),
        [INSTR_PUSH_TUPLE_ELEM]      = FX(1, 1),
        [INSTR_PUSH_TUPLE_MEMBER]    = FX(1, 1),
        [INSTR_PUSH_UNTAGGED]        = FX(1, 1),
        [INSTR_TRY_INDEX]            = FX(1, 1),
        [INSTR_INDEX_TUPLE]          = FX(1, 1),
        [INSTR_TRY_INDEX_TUPLE]      = FX(1, 1),
        [INSTR_TRY_MEMBER]           = FX(1, 1),
        [INSTR_TRY_TUPLE_MEMBER]     = FX(1, 1),
        [INSTR_TRY_REGEX]            = FX(1, 1),
        [INSTR_GET_NEXT]             = FX(2, 1),
        [INSTR_DUP2_SWAP]            = FX(2, 2),
        [INSTR_LOOP_ITER]            = FX(2, 2),

        [INSTR_POP]                  = FXP(1, -1),
        [INSTR_DEFER]                = FXP(1, -1),
        [INSTR_ASSIGN_LOCAL]         = FXP(1, -1),
        [INSTR_ASSIGN_GLOBAL]        = FXP(1, -1),
        [INSTR_ASSIGN_REGEX_MATCHES] = FXP(1, -1),
        [INSTR_JUMP_IF]              = FXP(1, -1),
        [INSTR_JUMP_IF_NOT]          = FXP(1, -1),
        [INSTR_JUMP_IF_NIL]          = FXP(1, -1),
        [INSTR_JUMP_AND]             = FX(1, -1),
        [INSTR_JUMP_OR]              = FX(1, -1),
        [INSTR_JUMP_WTF]             = FX(1, -1),
        [INSTR_NONE_IF_NOT]          = FX(1, -1),
        [INSTR_TARGET_MEMBER]        = FX(1, -1),
        [INSTR_INIT_STATIC_FIELD]    = FX(1, -1),
        [INSTR_TRY_UNAPPLY]          = FX(2, -1),
        [INSTR_ENSURE_EQUALS_VAR]    = FXP(2, -1),
        [INSTR_ENSURE_CONTAINS]      = FXP(2, -1),
        [INSTR_ENSURE_SAME_KEYS]     = FXP(2, -1),

        [INSTR_ADD]                  = FX(2, -1),
        [INSTR_SUB]                  = FX(2, -1),
        [INSTR_MUL]                  = FX(2, -1),
        [INSTR_DIV]                  = FX(2, -1),
        [INSTR_MOD]                  = FX(2, -1),
        [INSTR_EQ]                   = FX(2, -1),
        [INSTR_NEQ]                  = FX(2, -1),
        [INSTR_LT]                   = FX(2, -1),
        [INSTR_GT]                   = FX(2, -1),
        [INSTR_LEQ]                  = FX(2, -1),
        [INSTR_GEQ]                  = FX(2, -1),
        [INSTR_CMP]                  = FX(2, -1),
        [INSTR_BIT_AND]              = FX(2, -1),
        [INSTR_BIT_OR]               = FX(2, -1),
        [INSTR_BIT_XOR]              = FX(2, -1),
        [INSTR_SHL]                  = FX(2, -1),
        [INSTR_SHR]                  = FX(2, -1),
        [INSTR_RANGE]                = FX(2, -1),
        [INSTR_INCRANGE]             = FX(2, -1),
        [INSTR_BINARY_OP]            = FX(2, -1),
        [INSTR_CHECK_MATCH]          = FX(2, -1),
        [INSTR_SUBSCRIPT]            = FX(2, -1),
        [INSTR_SAFE_SUBSCRIPT]       = FX(2, -1),
        [INSTR_GET_MEMBER]           = FX(2, -1),
        [INSTR_TRY_GET_MEMBER]       = FX(2, -1),

        [INSTR_POP2]                 = FX(2, -2),
        [INSTR_TARGET_DYN_MEMBER]    = FX(2, -2),
        [INSTR_TARGET_SUBSCRIPT]     = FX(2, -2),
        [INSTR_JEQ]                  = FXP(2, -2),
        [INSTR_JNE]                  = FXP(2, -2),
        [INSTR_JLT]                  = FXP(2, -2),
        [INSTR_JGT]                  = FXP(2, -2),
        [INSTR_JLE]                  = FXP(2, -2),
        [INSTR_JGE]                  = FXP(2, -2),
        [INSTR_TRY_RANGE]            = FXP(3, -2),
        [INSTR_TRY_INCRANGE]         = FXP(3, -2),
        [INSTR_DROP2]                = FX(3, -2),
        [INSTR_SLICE]                = FX(4, -3),

        [INSTR_BAD_DISPATCH]         = FXS(0),
        [INSTR_TRAP]                 = FXS(0),
        [INSTR_TRAP_TY]              = FXS(0),
        [INSTR_BAD_CALL]             = FXS(1),
        [INSTR_BAD_ASSIGN]           = FXS(1),
        [INSTR_BAD_MATCH]            = FXS(1),
        [INSTR_THROW]                = FXS(1),
        [INSTR_RETURN]               = FXS(1),
        [INSTR_RETURN_PRESERVE_CTX]  = FXS(1)
};

#undef FX
#undef FXP
#undef FXS

inline static bool
decoded(BcLirNode const *node)
{
        return node->next != 0;
}

inline static bool
reached(BcLirNode const *node)
{
        return (node->next != 0) && (node->sp >= 0);
}

inline static bool
is_call(u8 op)
{
        switch (op) {
        case INSTR_CALL:
        case INSTR_CALL_GLOBAL:
        case INSTR_CALL_METHOD:
        case INSTR_TRY_CALL_METHOD:
        case INSTR_CALL_SELF_METHOD:
        case INSTR_CALL_STATIC_METHOD:
        case INSTR_CALL_SELF_STATIC:
                return true;

        default:
                return false;
        }
}

inline static bool
restores(u8 op)
{
        return (op == INSTR_RESTORE_STACK_POS)
            || (op == INSTR_POP_STACK_POS)
            || (op == INSTR_POP_STACK_POS_POP)
            || (op == INSTR_POP_STACK_POS_POP2);
}

static void
unwind_sentinel(BcLir *c)
{
        BcLirNode const *parent = &c->nodes[c->sentinel];
        c->sentinel    = parent->sentinel;
        c->sentinel_sp = parent->sentinel_sp;
}

static void
restore_sentinel(BcLir *c, BcLirNode const *node)
{
        c->sentinel    = node->sentinel;
        c->sentinel_sp = node->sentinel_sp;
}

static bool
same_saves(BcLir const *c, i32 a, i32 b)
{
        for (i32 n = 0; a >= 0 && b >= 0 && a != b && n < c->size; ++n) {
                a = c->nodes[a].saved;
                b = c->nodes[b].saved;
        }

        return a == b;
}

static bool
edge(BcLir *c, BcQueue *q, i32 offset, i32 sp)
{
        if (offset < 0 || offset >= c->size || !decoded(&c->nodes[offset])) {
                return false;
        }

        BcLirNode *node = &c->nodes[offset];

        if (node->sp < 0) {
                node->sp          = sp;
                node->saved       = c->saved;
                node->sentinel    = c->sentinel;
                node->sentinel_sp = c->sentinel_sp;
                q->at[q->n++]     = offset;
                return true;
        }

        bool resets = restores(node->op);
        bool twins  = resets
                   && (node->saved >= 0)
                   && (c->saved >= 0)
                   && (c->nodes[node->saved].sp == c->nodes[c->saved].sp)
                   && (c->nodes[node->saved].saved == c->nodes[c->saved].saved);

        if (node->saved != c->saved && !twins) {
                if (!same_saves(c, node->saved, c->saved)) {
                        return false;
                }
                c->dynamic = true;
        }

        c->dynamic = c->dynamic || (node->sp != sp && !resets);

        return true;
}

static bool
in_try(BcLir const *c, i32 offset)
{
        for (i32 t = 0; t <= offset && t < c->size; ++t) {
                BcLirNode const *node = &c->nodes[t];

                if (!decoded(node) || node->op != INSTR_TRY) {
                        continue;
                }

                i32 end = max(node->catch_to, max(node->finally_to, node->end_to));

                if (end < 0 || offset < end) {
                        return true;
                }
        }

        return false;
}

static bool
dynamic_op(u8 op)
{
        switch (op) {
        case INSTR_TRY_YIELD_FROM:
        case INSTR_SPREAD_CHECK:
        case INSTR_GET_NEXT:
        case INSTR_FIX_TO:
        case INSTR_FIX_EXTRA:
        case INSTR_EXEC_CODE:
                return true;

        default:
                return false;
        }
}

static bool
decode_call(BcLir *c, BcLirNode *node, char const *ip)
{
        char const *p = ip + 1;

        if (node->op == INSTR_CALL_GLOBAL || node->op == INSTR_CALL_STATIC_METHOD) {
                node->global = load_i32(p);
                p += sizeof (i32);
        }

        node->argc = load_i32(p);
        p += sizeof (i32);

        if (node->op != INSTR_CALL && node->op != INSTR_CALL_GLOBAL) {
                node->member = load_i32(p);
                p += sizeof (i32);
        }

        node->nkw   = load_i32(p);
        node->kw_ip = p + sizeof (i32);

        if (node->argc < -1 || node->nkw < 0) {
                return false;
        }

        c->dynamic = c->dynamic || (node->argc == -1);

        return true;
}

static void
decode_match(BcLir *c, BcLirNode *node, i32 off)
{
        i32 at = off + 1;

        if (node->op == INSTR_MATCH_TAG) {
                node->member = (u8)c->code[at++];
        }

        node->argc   = load_i32(c->code + at);
        at          += sizeof (i32);
        node->target = at + sizeof (i32) + load_i32(c->code + at);
        node->kw_ip  = c->code + at + sizeof (i32);
        node->branch = true;
}

static void
decode_try(BcLir *c, BcLirNode *node, i32 off)
{
        char const *ip      = c->code + off;
        i32         catch   = load_i32(ip + 1);
        i32         finally = load_i32(ip + 5);
        i32         end     = load_i32(ip + 9);

        node->catch_to   = off + 5 + catch;
        node->finally_to = (finally == -1) ? -1 : off + 9 + finally;
        node->end_to     = (end == -1) ? -1 : off + 13 + end;
        node->owner      = off;
        c->dynamic       = true;
        c->has_try       = true;
}

static bool
decode_operands(BcLir *c, Value const *f, BcLirNode *node, i32 off)
{
        char const *ip = c->code + off;

        switch (node->op) {
        case INSTR_TAIL_CALL:
                node->argc   = f->info[FUN_INFO_PARAM_COUNT];
                node->member = node->argc + (f->info[FUN_INFO_CLASS] != -1);
                node->target = 0;
                node->branch = true;
                return true;

        case INSTR_CALL:
        case INSTR_CALL_GLOBAL:
        case INSTR_CALL_METHOD:
        case INSTR_TRY_CALL_METHOD:
        case INSTR_CALL_SELF_METHOD:
        case INSTR_CALL_STATIC_METHOD:
        case INSTR_CALL_SELF_STATIC:
                return decode_call(c, node, ip);

        case INSTR_ENSURE_LEN:
        case INSTR_ENSURE_LEN_TUPLE:
        case INSTR_ENSURE_EQUALS_VAR:
        case INSTR_TRY_UNAPPLY:
        case INSTR_TRY_ASSIGN_NON_NIL:
        case INSTR_TRY_RANGE:
        case INSTR_TRY_INCRANGE:
        case INSTR_ENSURE_DICT:
        case INSTR_ENSURE_CONTAINS:
        case INSTR_ENSURE_SAME_KEYS:
        case INSTR_TRY_INDEX:
        case INSTR_INDEX_TUPLE:
        case INSTR_TRY_INDEX_TUPLE:
        case INSTR_TRY_MEMBER:
        case INSTR_TRY_TUPLE_MEMBER:
        case INSTR_TRY_TAG_POP:
        case INSTR_TRY_REGEX:
        case INSTR_TRY_STEAL_TAG:
        case INSTR_ARRAY_REST:
        case INSTR_TUPLE_REST:
        case INSTR_RECORD_REST:
        case INSTR_JNI:
        case INSTR_JII:
        case INSTR_JUMP_IF_TYPE:
        case INSTR_SPREAD_CHECK:
        case INSTR_LOOP_CHECK:
                if (node->op == INSTR_SPREAD_CHECK) {
                        node->member = (u8)ip[5];
                } else if (node->next - off >= 9) {
                        node->member = load_i32(ip + 5);
                }
                node->target = off + 5 + load_i32(ip + 1);
                node->branch = true;
                return true;

        case INSTR_MATCH_TAG:
        case INSTR_MATCH_STRING:
                decode_match(c, node, off);
                return true;

        case INSTR_JUMP:
        case INSTR_JEQ:
        case INSTR_JNE:
        case INSTR_JLT:
        case INSTR_JGT:
        case INSTR_JLE:
        case INSTR_JGE:
        case INSTR_JUMP_IF:
        case INSTR_JUMP_IF_NOT:
        case INSTR_JUMP_IF_NIL:
        case INSTR_JUMP_IF_NONE:
        case INSTR_TRY_YIELD_FROM:
        case INSTR_JUMP_WTF:
        case INSTR_NONE_IF_NOT:
        case INSTR_SKIP_CHECK:
        case INSTR_JUMP_IF_SENTINEL:
        case INSTR_JUMP_IF_INIT:
        case INSTR_JUMP_AND:
        case INSTR_JUMP_OR:
                node->target = node->next + load_i32(ip + 1);
                node->branch = true;
                return true;

        default:
                return true;
        }
}

static bool
decode(BcLir *c, Value const *f)
{
        i32 owner = -1;

        for (i32 off = 0; off < c->size;) {
                BcLirNode *node = &c->nodes[off];

                c->offset = off;

                *node = (BcLirNode) {
                        .op       = c->code[off],
                        .next     = StepInstruction(c->code + off) - c->code,
                        .sp       = -1,
                        .target   = -1,
                        .saved    = -1,
                        .owner    = owner,
                        .outer    = owner,
                        .label    = LIR_NONE,
                        .deopt    = LIR_NONE,
                        .resume   = LIR_NONE
                };

                if (node->op == INSTR_TRY) {
                        decode_try(c, node, off);
                        owner = off;
                } else if (node->op == INSTR_END_TRY) {
                        if (owner < 0) {
                                return false;
                        }
                        owner = c->nodes[owner].outer;
                }

                c->dynamic = c->dynamic || dynamic_op(node->op);

                if (
                        (node->next <= off)
                     || (node->next > c->size)
                     || !decode_operands(c, f, node, off)
                ) {
                        return false;
                }

                off = node->next;
        }

        return true;
}

static bool
arm_at(BcLir const *c, BcLirNode const *node, i32 i, i32 *target)
{
        char const *arm = node->kw_ip + 8 * i;

        *target = arm + 8 + load_i32(arm + 4) - c->code;

        return load_i32(arm) != -1;
}

static bool
match_edges(BcLir *c, BcQueue *q, BcLirNode const *node, i32 sp)
{
        for (i32 i = 0, t; i < node->argc; ++i) {
                if (arm_at(c, node, i, &t) && !edge(c, q, t, sp)) {
                        return false;
                }
        }

        return true;
}

static bool
finally_edges(BcLir *c, BcQueue *q, i32 owner)
{
        for (i32 off = 0; off < c->size; ++off) {
                BcLirNode const *f = &c->nodes[off];

                if (
                        decoded(f)
                     && (f->op == INSTR_FINALLY)
                     && (f->owner == owner)
                     && (f->sp >= 0)
                     && !edge(c, q, f->next, f->sp)
                ) {
                        return false;
                }
        }

        return true;
}

static bool
pop_saved(BcLir *c, i32 *sp, i32 extra)
{
        if (c->saved < 0) {
                return false;
        }

        *sp      = c->nodes[c->saved].sp + extra;
        c->saved = c->nodes[c->saved].saved;

        return true;
}

static i32
nmethods(char const *ip, u8 op, i32 sp)
{
        i32 first = (op == INSTR_DEFINE_TAG) ? 9 : 5;
        i32 last  = (op == INSTR_DEFINE_TAG) ? 25 : 29;
        i32 count = 0;

        for (i32 at = first; at < last; at += 4) {
                i32 n = load_i32(ip + at);
                if (n < 0 || n > sp - count) {
                        return -1;
                }
                count += n;
        }

        return count;
}

enum { FLOW_FAIL, FLOW_FALL, FLOW_STOP };

static int
flow_special(BcLir *c, BcQueue *q, i32 at, i32 *sp, i32 *taken)
{
        BcLirNode  *node = &c->nodes[at];
        char const *ip   = c->code + at;

        switch (node->op) {
        case INSTR_TRY:
                c->sentinel    = at;
                c->sentinel_sp = *sp;
                if (!edge(c, q, node->catch_to, *sp + 2)) {
                        return FLOW_FAIL;
                }
                restore_sentinel(c, node);
                return FLOW_FALL;

        case INSTR_SAVE_STACK_POS:
                c->saved = at;
                return FLOW_FALL;

        case INSTR_RESTORE_STACK_POS:
        case INSTR_POP_STACK_POS:
        case INSTR_POP_STACK_POS_POP:
        case INSTR_POP_STACK_POS_POP2:
        case INSTR_DROP_STACK_POS:
                if (c->saved < 0) {
                        return FLOW_FAIL;
                }
                if (node->op != INSTR_DROP_STACK_POS) {
                        *sp = c->nodes[c->saved].sp
                            - (node->op == INSTR_POP_STACK_POS_POP)
                            - 2 * (node->op == INSTR_POP_STACK_POS_POP2);
                        restore_sentinel(c, &c->nodes[c->saved]);
                }
                if (node->op != INSTR_RESTORE_STACK_POS) {
                        c->saved = c->nodes[c->saved].saved;
                }
                return FLOW_FALL;

        case INSTR_CLEAR_EXTRA:
                if (c->sentinel >= 0) {
                        *sp = c->sentinel_sp;
                        unwind_sentinel(c);
                } else if (node->owner >= 0) {
                        *sp = c->nodes[node->owner].sp;
                } else {
                        return FLOW_FAIL;
                }
                return FLOW_FALL;

        case INSTR_FINALLY:
        case INSTR_RETHROW: {
                if (node->owner < 0) {
                        return FLOW_FAIL;
                }
                BcLirNode const *t = &c->nodes[node->owner];
                if (
                        (node->op == INSTR_FINALLY && !edge(c, q, node->next, *sp))
                     || (t->finally_to < 0)
                     || !edge(c, q, t->finally_to, t->sp + 1)
                ) {
                        return FLOW_FAIL;
                }
                return FLOW_STOP;
        }

        case INSTR_END_TRY: {
                BcLirNode const *t = &c->nodes[node->owner];
                if (
                        (t->end_to >= 0 && !edge(c, q, t->end_to, *sp))
                     || !finally_edges(c, q, node->owner)
                ) {
                        return FLOW_FAIL;
                }
                return FLOW_STOP;
        }

        case INSTR_RENDER_TEMPLATE: {
                Expr const *expr  = peek(void const *, ip + 1);
                i32         count = vN(expr->template.holes);
                if (*sp < count) {
                        return FLOW_FAIL;
                }
                *sp += 1 - count;
                return FLOW_FALL;
        }

        case INSTR_SENTINEL:
                c->sentinel    = at;
                c->sentinel_sp = (*sp)++;
                return FLOW_FALL;

        case INSTR_FIX_TO: {
                i32 count = load_i32(ip + 1);
                if (count < 0 || c->sentinel < 0) {
                        return FLOW_FAIL;
                }
                *sp = c->sentinel_sp + 1 + count;
                return FLOW_FALL;
        }

        case INSTR_FIX_EXTRA:
                return (c->sentinel < 0) ? FLOW_FAIL : FLOW_FALL;

        case INSTR_JNI:
        case INSTR_JII:
                if (*sp < 1) {
                        return FLOW_FAIL;
                }
                *sp   -= (node->member < 0);
                *taken = *sp;
                return FLOW_FALL;

        case INSTR_MATCH_TAG:
        case INSTR_MATCH_STRING:
                if (
                        (*sp < 1)
                     || (node->argc < 0)
                     || !edge(c, q, node->target, *sp)
                     || !match_edges(c, q, node, *sp)
                ) {
                        return FLOW_FAIL;
                }
                return FLOW_STOP;

        case INSTR_LOOP_CHECK:
        case INSTR_SPREAD_CHECK:
                if (*sp < 4 || (node->op == INSTR_LOOP_CHECK && node->member < 0)) {
                        return FLOW_FAIL;
                }
                *taken = *sp - 4;
                *sp   += node->member - 1;
                return FLOW_FALL;

        case INSTR_ARRAY_COMPR:
        case INSTR_SET_COMPR:
                return pop_saved(c, sp, 0) ? FLOW_FALL : FLOW_FAIL;

        case INSTR_ARRAY:
        case INSTR_SET:
        case INSTR_DICT:
        case INSTR_DEFAULT_DICT:
        case INSTR_GATHER_TUPLE:
                return pop_saved(c, sp, 1) ? FLOW_FALL : FLOW_FAIL;

        case INSTR_DICT_COMPR: {
                i32 n = load_i32(ip + 5);
                if (n < 0 || *sp < 2 * n) {
                        return FLOW_FAIL;
                }
                *sp -= 2 * n;
                return FLOW_FALL;
        }

        case INSTR_TUPLE:
        case INSTR_XTUPLE:
        case INSTR_CONCAT_STRINGS: {
                i32 count = load_i32(ip + 1);
                if (count < 0 || *sp < count) {
                        return FLOW_FAIL;
                }
                *sp += 1 - count;
                return FLOW_FALL;
        }

        case INSTR_ASSIGN_SUBSCRIPT: {
                i32 count = (u8)ip[1];
                if (*sp < count + 2) {
                        return FLOW_FAIL;
                }
                *sp -= count + 1;
                return FLOW_FALL;
        }

        case INSTR_SWAP:
                if (c->sentinel_sp == *sp - 1) {
                        c->sentinel_sp -= 1;
                } else if (c->sentinel_sp == *sp - 2) {
                        c->sentinel_sp += 1;
                }
                return (*sp < 2) ? FLOW_FAIL : FLOW_FALL;

        case INSTR_CALL:
        case INSTR_CALL_GLOBAL:
        case INSTR_CALL_METHOD:
        case INSTR_TRY_CALL_METHOD:
        case INSTR_CALL_SELF_METHOD:
        case INSTR_CALL_STATIC_METHOD:
        case INSTR_CALL_SELF_STATIC: {
                if (node->argc == -1) {
                        return pop_saved(c, sp, 1) ? FLOW_FALL : FLOW_FAIL;
                }
                bool explicit = (node->op == INSTR_CALL)
                             || (node->op == INSTR_CALL_METHOD)
                             || (node->op == INSTR_TRY_CALL_METHOD);
                bool dynamic  = explicit
                             && (node->op != INSTR_CALL)
                             && (node->member == -1);
                if (*sp < node->argc + node->nkw + explicit + dynamic) {
                        return FLOW_FAIL;
                }
                *sp -= node->argc + node->nkw + dynamic;
                *sp += !explicit;
                return FLOW_FALL;
        }

        case INSTR_DEFINE_TAG:
        case INSTR_DEFINE_CLASS: {
                i32 count = nmethods(ip, node->op, *sp);
                if (count < 0) {
                        return FLOW_FAIL;
                }
                *sp -= count;
                return FLOW_FALL;
        }

        case INSTR_TAIL_CALL:
                if (*sp < node->argc) {
                        return FLOW_FAIL;
                }
                c->saved       = -1;
                c->sentinel    = -1;
                c->sentinel_sp = -1;
                return edge(c, q, 0, 0) ? FLOW_STOP : FLOW_FAIL;

        default:
                return FLOW_FAIL;
        }
}

static int
flow_step(BcLir *c, BcQueue *q, i32 at, i32 *sp, i32 *taken)
{
        BcEffect const *e = &Effects[c->nodes[at].op];

        if (!e->known) {
                return flow_special(c, q, at, sp, taken);
        }

        if (*sp < e->need) {
                return FLOW_FAIL;
        }

        if (e->stop) {
                return FLOW_STOP;
        }

        *sp += e->delta;

        if (e->post) {
                *taken = *sp;
        }

        return FLOW_FALL;
}

static bool
flow(BcLir *c, BcQueue *q)
{
        if (!edge(c, q, 0, 0)) {
                return false;
        }

        for (u32 i = 0; i < q->n; ++i) {
                i32        off  = q->at[i];
                BcLirNode *node = &c->nodes[off];
                i32        sp   = node->sp;
                i32        taken;

                c->offset = off;
                c->max_sp = max(c->max_sp, sp);
                c->saved  = node->saved;
                restore_sentinel(c, node);

                taken = sp;

                switch (flow_step(c, q, off, &sp, &taken)) {
                case FLOW_FAIL: return false;
                case FLOW_STOP: continue;
                }

                while (c->sentinel >= 0 && c->sentinel_sp >= sp) {
                        unwind_sentinel(c);
                }

                if (sp > INT32_MAX / sizeof (Value) - c->bound) {
                        return false;
                }

                node->fall_sp = sp;

                if (node->branch && !edge(c, q, node->target, taken)) {
                        return false;
                }

                if (node->op != INSTR_JUMP && !edge(c, q, node->next, sp)) {
                        return false;
                }
        }

        return true;
}

static bool
graph(BcLir *c, Value const *f)
{
        Ty *ty = c->ctx;

        c->code        = code_of(f);
        c->size        = code_size_of(f);
        c->saved       = -1;
        c->sentinel    = -1;
        c->sentinel_sp = -1;
        c->nodes       = smA0((c->size + 1) * sizeof *c->nodes);

        BcQueue q = { .at = smA((c->size + 1) * sizeof *q.at) };

        return decode(c, f) && flow(c, &q);
}

static LirReg
truthy(BcLir *c)
{
        i32      top    = c->sp - 1;
        LirReg   type   = tag_of(c, top);
        LirReg   r      = lir_reg(c->L, LIR_I64);
        LirLabel scalar = newlabel(c);
        LirLabel nil    = newlabel(c);
        LirLabel end    = newlabel(c);

        jcc(c, LIR_EQ, lir_r(type), lir_i(VALUE_INTEGER), scalar);
        jcc(c, LIR_EQ, lir_r(type), lir_i(VALUE_BOOLEAN), scalar);
        jcc(c, LIR_EQ, lir_r(type), lir_i(VALUE_NIL), nil);

        LirReg p     = slot_of(c, top);
        LirReg truth = tycall(c, jit_rt_truthy, LT_I32, preg(p));

        mov(c, r, truth);
        jump(c, end);

        bind(c, scalar);
        LirReg value = int_at(c, top);
        vset(c, LIR_SETCC, r, lir_cc(LIR_NE), lir_r(value), lir_i(0));
        jump(c, end);

        bind(c, nil);
        vset(c, LIR_LI, r, lir_i(0));

        bind(c, end);

        return r;
}

static void
compare_branch(BcLir *c, BcLirNode const *node, u8 op)
{
        BcBoxed const *ar     = &BoxedOps[op];
        i32            lhs    = c->sp - 2;
        i32            rhs    = c->sp - 1;
        bool           eq     = (op == INSTR_EQ) || (op == INSTR_NEQ);
        LirLabel       nil    = eq ? newlabel(c) : LIR_NONE;
        LirLabel       floats = newlabel(c);
        LirLabel       slow   = newlabel(c);
        LirLabel       done   = newlabel(c);
        LirReg         result = lir_reg(c->L, LIR_I64);
        LirReg         at     = tag_of(c, lhs);
        LirReg         bt     = tag_of(c, rhs);

        if (eq) {
                jcc(c, LIR_EQ, lir_r(at), lir_i(VALUE_NIL), nil);
                jcc(c, LIR_EQ, lir_r(bt), lir_i(VALUE_NIL), nil);
        }

        unless(c, at, VALUE_INTEGER, floats);
        unless(c, bt, VALUE_INTEGER, floats);

        LirReg a = int_at(c, lhs);
        LirReg b = int_at(c, rhs);

        vset(c, LIR_SETCC, result, lir_cc(ar->icc), lir_r(a), lir_r(b));
        jump(c, done);

        bind(c, floats);
        unless(c, at, VALUE_REAL, slow);
        unless(c, bt, VALUE_REAL, slow);
        a = real_at(c, lhs);
        b = real_at(c, rhs);
        vset(c, LIR_FSETCC, result, lir_cc(ar->fcc), lir_r(a), lir_r(b));
        jump(c, done);

        if (eq) {
                bind(c, nil);
                vset(c, LIR_SETCC, result, lir_cc(ar->icc), lir_r(at), lir_r(bt));
                jump(c, done);
        }

        bind(c, slow);

        LirReg out = slot_of(c, lhs);
        LirReg arg = slot_of(c, rhs);

        tycall(c, ar->helper, LT_VOID, preg(out), preg(out), preg(arg));
        vset(c, LIR_LD_I64, result, mref(c->ops, vat(lhs) + VOFF(z)));

        bind(c, done);

        c->sp = node->fall_sp;

        if (c->dynamic) {
                sync_sp(c);
        }

        jnz(c, result, dest(c, node));
}

static u8 const JumpCompare[256] = {
        [INSTR_JEQ] = INSTR_EQ,
        [INSTR_JNE] = INSTR_NEQ,
        [INSTR_JLT] = INSTR_LT,
        [INSTR_JGT] = INSTR_GT,
        [INSTR_JLE] = INSTR_LEQ,
        [INSTR_JGE] = INSTR_GEQ
};

inline static i64
tag_test(u8 op)
{
        switch (op) {
        case INSTR_JUMP_IF_NIL:      return VALUE_NIL;
        case INSTR_JUMP_IF_SENTINEL: return VALUE_SENTINEL;
        default:                     return VALUE_NONE;
        }
}

static void
control(BcLir *c, BcLirNode const *node)
{
        BcLirNode const *to     = &c->nodes[node->target];
        LirLabel         target = dest(c, node);

        if (node->deopt != LIR_NONE) {
                safepoint(c, node->deopt);
                if (c->tier != NULL && node->op == INSTR_JUMP && to->osr_id != 0) {
                        tier_check(c, node->deopt);
                }
        }

        if (JumpCompare[node->op] != 0) {
                compare_branch(c, node, JumpCompare[node->op]);
                return;
        }

        LirReg value;
        LirCC  cc   = LIR_EQ;
        i64    test = 0;

        switch (node->op) {
        case INSTR_JUMP:
                jump(c, target);
                return;

        case INSTR_JUMP_IF_TYPE:
                value = tag_of(c, c->sp - 1);
                jcc(c, LIR_EQ, lir_r(value), lir_i(node->member), target);
                return;

        case INSTR_JUMP_IF_NIL:
        case INSTR_JUMP_IF_SENTINEL:
        case INSTR_JUMP_IF_NONE:
                value = tag_of(c, c->sp - 1);
                test  = tag_test(node->op);
                break;

        default:
                value = truthy(c);
                if (node->op != INSTR_JUMP_IF_NOT && node->op != INSTR_JUMP_AND) {
                        cc = LIR_NE;
                }
                break;
        }

        if (c->dynamic && node->op != INSTR_JUMP_AND && node->op != INSTR_JUMP_OR) {
                resync(c, node);
        }

        jcc(c, cc, lir_r(value), lir_i(test), target);
}

static void
invoke_keywords(BcLir *c, BcLirNode const *node)
{
        LirReg top = slot_of(c, c->sp);

        switch (node->op) {
        case INSTR_CALL:
                tycall(
                        c,
                        jit_rt_call_kw,
                        LT_VOID,
                        preg(top),
                        imm32(node->argc),
                        imm32(node->nkw),
                        pimm(node->kw_ip)
                );
                break;

        case INSTR_CALL_METHOD:
                tycall(
                        c,
                        jit_rt_call_method_kw,
                        LT_VOID,
                        preg(top),
                        imm32(node->member),
                        imm32(node->argc),
                        imm32(node->nkw),
                        pimm(node->kw_ip)
                );
                break;

        default:
                tycall(
                        c,
                        jit_rt_call_global_kw,
                        LT_VOID,
                        preg(top),
                        imm32(node->global),
                        imm32(node->argc),
                        imm32(node->nkw),
                        pimm(node->kw_ip)
                );
                break;
        }
}

static void
rt_method(
        Ty *ty,
        Value *top,
        i32 op,
        i32 class,
        i32 member,
        i32 argc,
        i32 nkw,
        char *kw_ip
)
{
        ty->stack.count = top - ty->stack.items;

        switch (op) {
        case INSTR_CALL_SELF_METHOD:
                xvP(ty->stack, *vm_get_self(ty));
                break;

        case INSTR_CALL_SELF_STATIC: {
                Value self = *vm_get_self(ty);
                xvP(ty->stack, CLASS(ClassOf(&self)));
                break;
        }

        case INSTR_CALL_STATIC_METHOD:
                xvP(ty->stack, CLASS(class));
                break;
        }

        jit_call_method_at(
                ty,
                ty->stack.items + ty->stack.count,
                member,
                argc,
                nkw,
                kw_ip,
                op == INSTR_TRY_CALL_METHOD
        );
}

static void
invoke_method(BcLir *c, BcLirNode const *node)
{
        if (method_fast(c, node)) {
                return;
        }

        LirLabel inlined = LIR_NONE;

        inline_method(c, node, &inlined);

        LirReg top = slot_of(c, c->sp);

        if (
                (node->nkw == 0)
             && (node->argc >= 0)
             && (node->member >= 0)
             && (node->op == INSTR_CALL_METHOD || node->op == INSTR_CALL_SELF_METHOD)
        ) {
                bool   explicit = (node->op == INSTR_CALL_METHOD);
                LirReg out      = slot_of(c, c->sp - explicit - node->argc);
                LirReg frame    = tycall(
                        c,
                        method_enter,
                        LT_PTR,
                        preg(top),
                        imm32(node->op),
                        imm32(node->member),
                        imm32(node->argc),
                        pimm(node->kw_ip)
                );

                native_invoke(c, frame, out);

                if (inlined != LIR_NONE) {
                        bind(c, inlined);
                }

                return;
        }

        tycall(
                c,
                rt_method,
                LT_VOID,
                preg(top),
                imm32(node->op),
                imm32(node->global),
                imm32(node->member),
                imm32(node->argc),
                imm32(node->nkw),
                pimm(node->kw_ip)
        );
}

static void
spread_call(Ty *ty, Value *top, i32 global, i32 nkw, char *kw_ip)
{
        ty->stack.count = top - ty->stack.items;

        Value fn = (global >= 0) ? *vm_global(ty, global) : vXx(ty->stack);

        i32 argc = ty->stack.count - vXx(ty->st->sps) - nkw;

        gP(&fn);
        Value kwargs = BuildKwargsDict(ty, &kw_ip, nkw);
        DoCallEx(ty, &fn, argc, &kwargs, true);
        gX();
}

static bool
defers(BcLir const *c)
{
        for (i32 off = 0; off < c->size; ++off) {
                BcLirNode const *node = &c->nodes[off];

                if (!decoded(node)) {
                        continue;
                }

                switch (node->op) {
                case INSTR_PUSH_DROP_GROUP:
                case INSTR_PUSH_DEFER_GROUP:
                case INSTR_DEFER:
                        return true;
                }
        }

        return false;
}

static bool
tail_position(BcLir const *c, BcLirNode const *node)
{
        i32 n = node->next;

        for (i32 hops = 0; hops < 8 && n > 0 && n < c->size; ++hops) {
                if (c->nodes[n].op != INSTR_JUMP) {
                        break;
                }
                n = c->nodes[n].target;
        }

        if (n <= 0 || n >= c->size || c->nodes[n].op != INSTR_RETURN) {
                return false;
        }

        return !defers(c);
}

static void
restart(BcLir *c, i32 base, i32 argc, i32 unset)
{
        for (i32 i = 0; i < argc; ++i) {
                copy(c, c->locals, vat(i), c->ops, vat(base + i));
        }

        for (i32 i = unset; i < c->bound; ++i) {
                stq(c, c->locals, vat(i), lir_i(VALUE_NIL));
        }

        count_at(c, 0);
        jump(c, c->nodes[0].label);
}

static void
guard_self(BcLir *c, LirReg fn, Value const *callee, LirLabel miss)
{
        LirReg type = ldx(c, LIR_LD_U8, LIR_I64, fn, VOFF(type));
        unless(c, type, VALUE_FUNCTION, miss);

        LirReg info = ldp(c, fn, VOFF(info));
        LirReg want = pval(c, callee->info);
        jcc(c, LIR_NE, lir_r(info), lir_r(want), miss);
}

static bool
inlinable(BcLir const *c, Value const *callee, i32 argc)
{
        return !c->compact
            && jit_linkable_global(callee, argc)
            && (callee->info[FUN_INFO_BOUND] - argc <= 32);
}

static void
tail_self(BcLir *c, BcLirNode const *node, LirReg fn)
{
        Value const *f = c->function;

        if (
                c->dynamic
             || c->has_try
             || (c->base_index == LIR_NONE)
             || (c->self_index >= 0)
             || is_starred(f)
             || (node->argc > 16)
             || (c->bound > 48)
             || !jit_linkable_global(f, node->argc)
             || !tail_position(c, node)
        ) {
                return;
        }

        LirLabel miss  = newlabel(c);
        LirLabel deopt = newlabel(c);
        LirLabel go    = newlabel(c);

        guard_self(c, fn, f, miss);

        LirReg env = ldp(c, fn, VOFF(env));
        jcc(c, LIR_NE, lir_r(env), lir_r(c->env), miss);

        safepoint(c, deopt);
        jump(c, go);

        bind(c, deopt);
        sync_sp(c);
        flush_active(c);
        leave(c, JIT_PACK(JIT_DEOPT, c->at));

        bind(c, go);
        restart(c, c->sp - 1 - node->argc, node->argc, node->argc);

        bind(c, miss);
}

static LirLabel
invoke_global_fast(BcLir *c, BcLirNode const *node, LirReg fn, i32 first)
{
        Value const *callee = vm_global(c->ctx, node->global);
        LirLabel     done   = LIR_NONE;
        LirLabel     miss;

        if (inlinable(c, callee, node->argc)) {
                miss = newlabel(c);
                done = newlabel(c);
                guard_self(c, fn, callee, miss);
                try_plan(
                        c,
                        callee,
                        TY_INLINE_GLOBAL,
                        node->argc,
                        first,
                        LIR_NONE,
                        NULL,
                        NULL,
                        first,
                        done
                );
                inline_call(c, fn, callee, first, node->argc, LIR_NONE, miss, done);
                bind(c, miss);
        } else if (callee->type == VALUE_CLASS && node->argc <= 8) {
                inline_ctor(c, fn, callee, first, node->argc, &done);
        } else if (callee->type == VALUE_BUILTIN_FUNCTION) {
                miss = newlabel(c);
                done = newlabel(c);
                builtin_call(c, fn, callee, first, node->argc, miss, done);
                bind(c, miss);
        } else if (
                (callee->type == VALUE_JIT_FUNCTION)
             && kernel_ok(callee->jit_code, node->argc)
        ) {
                miss = newlabel(c);
                done = newlabel(c);
                kernel_call(c, fn, callee, first, node->argc, miss, done);
                bind(c, miss);
        }

        return done;
}

static LirLabel
invoke_local_fast(BcLir *c, BcLirNode const *node, LirReg fn, i32 first)
{
        i32      at    = node - c->nodes;
        bool     klass = (at >= 5) && ((u8)c->code[at - 5] == INSTR_CLASS);
        LirLabel done  = LIR_NONE;

        tail_self(c, node, fn);

        if (!klass && inlinable(c, c->function, node->argc)) {
                LirLabel miss = newlabel(c);
                done = newlabel(c);
                inline_call(c, fn, c->function, first, node->argc, LIR_NONE, miss, done);
                bind(c, miss);
        }

        if (
                klass
             && (c->nodes[at - 5].sp >= 0)
             && (c->nodes[at - 5].next == at)
             && (node->label == LIR_NONE)
             && (node->argc <= 8)
        ) {
                Value class = { .type = VALUE_CLASS };
                class.class = peek(typeof (class.class), c->code + at - 4);
                inline_ctor(c, fn, &class, first, node->argc, &done);
        }

        return done;
}

static LirReg
global_addr(BcLir *c, i32 global)
{
        LirReg where   = pval(c, &Globals.items);
        LirReg globals = ldp(c, where, 0);

        return addr(c, globals, vat(global));
}

static void
invoke(BcLir *c, BcLirNode const *node)
{
        bool global = (node->op == INSTR_CALL_GLOBAL);

        if (node->op != INSTR_CALL && !global) {
                invoke_method(c, node);
                return;
        }

        if (node->argc == -1) {
                LirReg top = slot_of(c, c->sp);
                tycall(
                        c,
                        spread_call,
                        LT_VOID,
                        preg(top),
                        imm32(global ? node->global : -1),
                        imm32(node->nkw),
                        pimm(node->kw_ip)
                );
                return;
        }

        if (node->nkw != 0) {
                invoke_keywords(c, node);
                return;
        }

        i32      first = c->sp - node->argc - !global;
        LirReg   fn;
        LirLabel done;

        if (global) {
                fn   = global_addr(c, node->global);
                done = invoke_global_fast(c, node, fn, first);
        } else {
                fn   = slot_of(c, c->sp - 1);
                done = invoke_local_fast(c, node, fn, first);
        }

        LirReg  out     = slot_of(c, first);
        LirOpnd enter[] = { lir_r(c->ty), lir_r(out), lir_r(fn), lir_i(node->argc) };

        sync_sp(c);

        if (node->resume_id == 0) {
                native_call(c, enter);
                if (done != LIR_NONE) {
                        bind(c, done);
                }
                return;
        }

        LirReg   status   = tycall(
                c,
                prepare_call,
                LT_I32,
                preg(out),
                preg(fn),
                imm32(node->argc)
        );
        LirLabel returned = newlabel(c);

        jz(c, status, returned);
        leave(c, JIT_PACK(JIT_CALL, node->resume_id));
        bind(c, returned);
}

static LirReg
reference(BcLir *c, i32 local, bool all)
{
        LirReg   p     = addr(c, c->locals, vat(local));
        LirLabel again = newlabel(c);
        LirLabel end   = newlabel(c);

        bind(c, again);

        LirReg type = ldx(c, LIR_LD_U8, LIR_I64, p, VOFF(type));
        unless(c, type, VALUE_REF, end);
        vset(c, LIR_LD_I64, p, mref(p, VOFF(ref)));

        if (all) {
                jump(c, again);
        }

        bind(c, end);

        return p;
}

static void
assign_value(Ty *ty, Value const *value)
{
        ty->stack.count = value - ty->stack.items + 1;
        DoAssignExec(ty);
}

static void
lower_target(BcLir *c, char const *ip, u8 op)
{
        i32    index = load_i32(ip + 1);
        LirReg p;

        switch (op) {
        case INSTR_TARGET_CAPTURED:
                p = captured(c, index);
                break;

        case INSTR_TARGET_REF:
                p = reference(c, index, false);
                break;

        default:
                p = addr(c, c->locals, vat(index));
                break;
        }

        tycall(c, vm_jit_push_target, LT_VOID, preg(p));
}

static void *const Mutators[256] = {
        [INSTR_MUT_ADD] = DoMutAdd,
        [INSTR_MUT_SUB] = DoMutSub,
        [INSTR_MUT_MUL] = DoMutMul,
        [INSTR_MUT_DIV] = DoMutDiv,
        [INSTR_MUT_MOD] = DoMutMod,
        [INSTR_MUT_AND] = DoMutAnd,
        [INSTR_MUT_OR]  = DoMutOr,
        [INSTR_MUT_XOR] = DoMutXor,
        [INSTR_MUT_SHL] = DoMutShl,
        [INSTR_MUT_SHR] = DoMutShr
};

static void
mutate(BcLir *c, u8 op)
{
        if (Mutators[op] == NULL) {
                c->ok = false;
                return;
        }

        sync_sp(c);
        tycall(c, Mutators[op], LT_VOID, bimm(true));
}

static void
capture(BcLir *c, char const *ip)
{
        i32    local = load_i32(ip + 1);
        i32    index = load_i32(ip + 5);
        LirReg p     = addr(c, c->locals, vat(local));

        tycall(c, jit_rt_capture, LT_VOID, preg(p), preg(c->env), imm32(index));
}

static void
function_literal(BcLir *c, char const *ip, u8 op)
{
        LirReg top    = slot_of(c, c->sp);
        void  *helper = (op == INSTR_FUNCTION) ? jit_rt_function : jit_rt_generator;

        tycall(c, helper, LT_VOID, preg(top), pimm(ip + 1));
}

static void
yield(BcLir *c, BcLirNode const *node)
{
        void *helper;
        i32   reason;

        switch (node->op) {
        case INSTR_YIELD:      helper = jit_rt_yield;      reason = JIT_YIELD;      break;
        case INSTR_YIELD_SOME: helper = jit_rt_yield_some; reason = JIT_YIELD_SOME; break;
        default:               helper = jit_rt_yield_none; reason = JIT_YIELD_NONE; break;
        }

        if (!c->has_try) {
                sync_sp(c);
                leave(c, JIT_PACK(reason, node->resume_id));
                return;
        }

        LirReg top = slot_of(c, c->sp);
        LirReg fp  = tycall(c, helper, LT_I32, preg(top));

        if (node->op == INSTR_YIELD_NONE) {
                LirLabel next = newlabel(c);
                jcc(c, LIR_GE, lir_r(fp), lir_i(0), next);
                leave(c, JIT_RETURN);
                bind(c, next);
        }
}

#include "lower/try.h"
#include "lower/call.h"
#include "lower/member.h"
#include "lower/fast.h"
#include "lower/inline.h"
#include "lower/vstack.h"
#include "lower/loop.h"
#include "lower/ops.h"
#include "lower/pattern.h"
#include "lower/vm.h"

static struct {
        u64 insts[256];
        u64 count[256];
        i32 op;
        u32 mark;
} OpStat = { .op = -1 };

static void
opstat_dump(void)
{
        for (int i = 0; i < 256; ++i) {
                if (OpStat.count[i] != 0) {
                        fprintf(
                                stderr,
                                "opstat %s %llu %llu\n",
                                GetInstructionName(i),
                                (unsigned long long)OpStat.count[i],
                                (unsigned long long)OpStat.insts[i]
                        );
                }
        }
}

__attribute__((constructor))
static void
opstat_init(void)
{
        if (getenv("TY_JIT_OPSTAT") != NULL) {
                atexit(opstat_dump);
        }
}

static void
opstat(BcLir const *c, u8 op, bool live)
{
        u32 n = vN(c->L->insts);

        if (OpStat.op >= 0) {
                OpStat.insts[OpStat.op] += n - OpStat.mark;
        }

        OpStat.op         = op;
        OpStat.count[op] += live;
        OpStat.mark       = n;
}

static void
mark_label(BcLir *c, i32 offset)
{
        if (offset < 0 || offset >= c->size) {
                return;
        }

        BcLirNode *node = &c->nodes[offset];

        if (node->sp >= 0 && node->label == LIR_NONE) {
                node->label = newlabel(c);
        }
}

static bool
is_yield(u8 op)
{
        return (op == INSTR_YIELD)
            || (op == INSTR_YIELD_SOME)
            || (op == INSTR_YIELD_NONE);
}

static void
plan_node(BcLir *c, i32 off)
{
        BcLirNode *node = &c->nodes[off];

        if (!c->has_try && is_yield(node->op)) {
                node->resume    = newlabel(c);
                node->resume_id = ++c->nresume;
                mark_label(c, node->next);
        }

        if (node->branch) {
                if (node->target <= off) {
                        node->deopt = newlabel(c);
                }
                mark_label(c, node->target);
        }

        if (node->op == INSTR_CALL && tail_position(c, node)) {
                mark_label(c, 0);
        }

        switch (node->op) {
        case INSTR_TRY:
                mark_label(c, node->catch_to);
                mark_label(c, node->finally_to);
                mark_label(c, node->end_to);
                break;

        case INSTR_FINALLY:
                mark_label(c, node->next);
                break;

        case INSTR_MATCH_TAG:
        case INSTR_MATCH_STRING:
                for (i32 i = 0, t; i < node->argc; ++i) {
                        if (arm_at(c, node, i, &t)) {
                                mark_label(c, t);
                        }
                }
                break;
        }
}

static void
plan_osr(BcLir *c)
{
        for (i32 off = 0; off < c->size; ++off) {
                BcLirNode const *node = &c->nodes[off];

                if (
                        !reached(node)
                     || !node->branch
                     || (node->target > off)
                     || (c->has_try && in_try(c, node->target))
                ) {
                        continue;
                }

                BcLirNode *head = &c->nodes[node->target];

                if (head->osr_id == 0 && head->label != LIR_NONE && head->sp >= 0) {
                        head->osr    = newlabel(c);
                        head->osr_id = ++c->nresume;
                        c->nosr     += 1;
                }
        }
}

static void
plan_nodes(BcLir *c)
{
        for (i32 off = 0; off < c->size; ++off) {
                if (reached(&c->nodes[off])) {
                        plan_node(c, off);
                }
        }

        if (!c->dynamic && getenv("TY_JIT_NO_OSR") == NULL) {
                plan_osr(c);
        }
}

static void
dispatch(BcLir *c, LirLabel normal)
{
        Ty       *ty      = c->ctx;
        LirLabel *targets = smA((c->nresume + 1) * sizeof *targets);

        targets[0] = normal;

        for (i32 off = 0; off < c->size; ++off) {
                BcLirNode const *node = &c->nodes[off];

                if (!decoded(node)) {
                        continue;
                }

                if (node->resume_id != 0) {
                        targets[node->resume_id] = node->resume;
                }

                if (node->osr_id != 0) {
                        targets[node->osr_id] = node->osr;
                }
        }

        LirInst in = {
                .op       = LIR_SWITCH,
                .dst      = LIR_NONE,
                .args     = { lir_r(c->L->params[1]), lir_l(normal) },
                .nargs    = 2,
                .targets  = targets,
                .ntargets = c->nresume + 1
        };

        c->ok = c->ok && lir_emit(c->L, &in);
}

static void
pin(BcLir *c)
{
        Lir *L = c->L;

        c->ok = c->ok
             && lir_pin_param(L, LIR_PIN_0, 0)
             && lir_pin_param(L, LIR_PIN_1, 2)
             && lir_pin_param(L, LIR_PIN_2, 3)
             && lir_pc_param(L, 4);

        L->ty_param    = 0;
        L->stable_pins = (1 << LIR_PIN_0) | (1 << LIR_PIN_2);
        L->stack_pins  = (1 << LIR_PIN_1) | (1 << LIR_PIN_3);

        c->ty     = lir_pinned(L, LIR_PIN_0);
        c->locals = lir_pinned(L, LIR_PIN_1);
        c->env    = lir_pinned(L, LIR_PIN_2);
        c->ops    = lir_pinned(L, LIR_PIN_3);
}

static void
frame_slot(BcLir *c)
{
        c->fp = lir_pinned(c->L, LIR_PIN_4);
        v_(c->L->regs, c->fp)->cls = LIR_I64;

        LirReg base = ldq(c, c->ty, offsetof(Ty, stack.items));
        LirReg bits = vop(c, LIR_BITCAST, LIR_I64, lir_r(c->locals));

        vset(c, LIR_SUB, c->fp, lir_r(bits), lir_r(base));
}

static void
prologue(BcLir *c)
{
        static JitDeopt const entry = {0};

        pin(c);

        if (c->dynamic) {
                frame_slot(c);
        }

        vset(c, LIR_LEA, c->ops, mref(c->locals, vat(c->bound)));

        c->base_index = LIR_NONE;

        if (!c->dynamic) {
                c->base_index = lir_reg(c->L, LIR_I64);
                base_slot(c);
        }

        c->deopt = newlabel(c);

        LirLabel normal = newlabel(c);

        if (c->nresume != 0) {
                dispatch(c, normal);
        }

        bind(c, normal);

        if (c->max_sp > 240) {
                tycall(c, reserve, LT_VOID, preg(c->ops), imm32(c->max_sp));
        }

        poll(c, c->ops, lir_i((uptr)&entry), c->deopt);

        if (c->compact && jit_tier() != 1) {
                c->tier  = alloc0(sizeof *c->tier);
                *c->tier = (jit_tier() == 3) ? 3 : JIT_TIER_BUDGET;
                tier_check(c, LIR_NONE);
        }
}

static void
push_from(BcLir *c, LirReg p)
{
        copy(c, c->ops, vat(c->sp++), p, 0);
}

static void
destructure_op(BcLir *c, u8 op, char const *ip)
{
        LirReg top = slot_of(c, c->sp);

        tycall(c, destructure, LT_VOID, preg(top), pimm(ip));

        if (op == INSTR_BAD_MATCH) {
                never_returns(c);
        }
}

static void
load_local(BcLir *c, i32 local)
{
        local_load(c, local);

        if (c->vs != NULL && c->local_type != NULL && local_ok(c, local)) {
                c->vs[c->sp - 1].hint = c->local_type[local];
        }
}

static bool
lower_op(BcLir *c, BcLirNode const *node, char const *ip)
{
        u8 op = node->op;

        switch (op) {
        case INSTR_TRY_YIELD_FROM:
        case INSTR_TAIL_CALL:
        case INSTR_DEFINE_TAG:
        case INSTR_DEFINE_CLASS:
        case INSTR_INIT_STATIC_FIELD:
        case INSTR_BAD_CALL:
        case INSTR_BAD_ASSIGN:
        case INSTR_BAD_DISPATCH:
                finish_op(c, node, ip);
                return false;

        case INSTR_EXEC_CODE:
        case INSTR_DEBUG:
        case INSTR_REVERSE:
        case INSTR_RENDER_TEMPLATE:
        case INSTR_NAMESPACE:
        case INSTR_TRACE:
        case INSTR_OPERATOR:
        case INSTR_READ_INDEX:
        case INSTR_UNARY_OP:
        case INSTR_QUESTION:
        case INSTR_TO_REGEX:
        case INSTR_COMPILE_REGEX:
        case INSTR_EVAL:
        case INSTR_GET_TAG:
        case INSTR_NONE_IF_NIL:
        case INSTR_RETURN_IF_NOT_NONE:
        case INSTR_BINARY_OP:
        case INSTR_SLICE:
        case INSTR_GET_NEXT:
        case INSTR_FIX_TO:
        case INSTR_FIX_EXTRA:
        case INSTR_TRAP:
        case INSTR_TRAP_TY:
        case INSTR_JUMP_WTF:
        case INSTR_NONE_IF_NOT:
        case INSTR_SKIP_CHECK:
                misc(c, node, ip);
                return false;

        case INSTR_JUMP_IF_INIT:
        case INSTR_TARGET_GLOBAL:
        case INSTR_TARGET_THREAD_LOCAL:
        case INSTR_TARGET_SELF_STATIC:
        case INSTR_TARGET_STATIC_MEMBER:
        case INSTR_TARGET_DYN_MEMBER:
        case INSTR_DROP:
        case INSTR_DISCARD_DROP_GROUP:
        case INSTR_PUSH_DROP_GROUP:
        case INSTR_PUSH_DEFER_GROUP:
        case INSTR_CLEANUP:
        case INSTR_LOAD_THREAD_LOCAL:
        case INSTR_PRE_INC:
        case INSTR_POST_INC:
        case INSTR_PRE_DEC:
        case INSTR_POST_DEC:
        case INSTR_BIND_STATIC:
        case INSTR_SELF_STATIC_ACCESS:
        case INSTR_STATIC_MEMBER_ACCESS:
        case INSTR_MAYBE_ASSIGN:
        case INSTR_DECORATE:
        case INSTR_INTO_METHOD:
        case INSTR_BIND_CLASS:
        case INSTR_BIND_INSTANCE:
        case INSTR_BIND_GETTER:
        case INSTR_BIND_SETTER:
        case INSTR_PUSH_DROP:
        case INSTR_ENTER:
        case INSTR_DEFER:
        case INSTR_ASSIGN_GLOBAL:
                state(c, node, ip);
                return false;

        case INSTR_ENSURE_LEN:
        case INSTR_ENSURE_LEN_TUPLE:
        case INSTR_ENSURE_EQUALS_VAR:
        case INSTR_TRY_UNAPPLY:
        case INSTR_TRY_ASSIGN_NON_NIL:
        case INSTR_TRY_RANGE:
        case INSTR_TRY_INCRANGE:
        case INSTR_ENSURE_DICT:
        case INSTR_ENSURE_CONTAINS:
        case INSTR_ENSURE_SAME_KEYS:
        case INSTR_TRY_INDEX:
        case INSTR_INDEX_TUPLE:
        case INSTR_TRY_INDEX_TUPLE:
        case INSTR_TRY_MEMBER:
        case INSTR_TRY_TUPLE_MEMBER:
        case INSTR_TRY_TAG_POP:
        case INSTR_TRY_REGEX:
        case INSTR_TRY_STEAL_TAG:
        case INSTR_ARRAY_REST:
        case INSTR_TUPLE_REST:
        case INSTR_RECORD_REST:
        case INSTR_JNI:
        case INSTR_JII:
        case INSTR_MATCH_TAG:
        case INSTR_MATCH_STRING:
                return lower_pattern(c, node, ip);

        case INSTR_UNAPPLY:
        case INSTR_PUSH_ARRAY_ELEM:
        case INSTR_PUSH_TUPLE_ELEM:
        case INSTR_PUSH_TUPLE_MEMBER:
        case INSTR_PUSH_UNTAGGED:
        case INSTR_UNTAG_OR_DIE:
        case INSTR_STEAL_TAG:
        case INSTR_THROW_IF_NIL:
        case INSTR_BAD_MATCH:
        case INSTR_ASSIGN_REGEX_MATCHES:
                destructure_op(c, op, ip);
                return false;

        case INSTR_ARRAY_COMPR:
        case INSTR_SET_COMPR:
        case INSTR_DICT_COMPR:
        case INSTR_PUSH_INDEX:
        case INSTR_LOOP_CHECK:
        case INSTR_SPREAD_CHECK:
        case INSTR_ASSIGN_SUBSCRIPT:
        case INSTR_ARRAY:
        case INSTR_ARRAY0:
        case INSTR_SET:
        case INSTR_DICT:
        case INSTR_DEFAULT_DICT:
        case INSTR_GATHER_TUPLE:
        case INSTR_TUPLE:
        case INSTR_XTUPLE:
        case INSTR_STRING:
        case INSTR_SELF:
        case INSTR_CLASS:
        case INSTR_TAG:
        case INSTR_REGEX:
        case INSTR_TYPE:
        case INSTR_VALUE:
        case INSTR_CONCAT_STRINGS:
        case INSTR_MEMBER_ACCESS:
        case INSTR_SELF_MEMBER_ACCESS:
        case INSTR_TRY_MEMBER_ACCESS:
        case INSTR_SUBSCRIPT:
        case INSTR_SAFE_SUBSCRIPT:
        case INSTR_GET_MEMBER:
        case INSTR_TRY_GET_MEMBER:
        case INSTR_TAG_PUSH:
        case INSTR_NEG:
        case INSTR_NOT:
        case INSTR_INC:
        case INSTR_DEC:
        case INSTR_TO_STRING:
        case INSTR_COUNT:
        case INSTR_CLASS_OF:
        case INSTR_DIV:
        case INSTR_CMP:
        case INSTR_CHECK_MATCH:
        case INSTR_MOD:
        case INSTR_BIT_AND:
        case INSTR_BIT_OR:
        case INSTR_BIT_XOR:
        case INSTR_SHL:
        case INSTR_SHR:
        case INSTR_RANGE:
        case INSTR_INCRANGE:
        case INSTR_SWAP:
        case INSTR_POP2:
        case INSTR_DUP2_SWAP:
                lower_misc(c, node, ip);
                return false;

        case INSTR_TRY:
        case INSTR_CATCH:
        case INSTR_RETHROW:
        case INSTR_FINALLY:
        case INSTR_POP_TRY:
        case INSTR_END_TRY:
                lower_tryop(c, node);
                return false;

        case INSTR_SAVE_STACK_POS:
        case INSTR_RESTORE_STACK_POS:
        case INSTR_POP_STACK_POS:
        case INSTR_POP_STACK_POS_POP:
        case INSTR_POP_STACK_POS_POP2:
        case INSTR_DROP_STACK_POS:
        case INSTR_CLEAR_EXTRA:
                saved_stack(c, op);
                return false;

        case INSTR_MUT_ADD:
        case INSTR_MUT_SUB:
        case INSTR_MUT_MUL:
        case INSTR_MUT_DIV:
        case INSTR_MUT_MOD:
        case INSTR_MUT_AND:
        case INSTR_MUT_OR:
        case INSTR_MUT_XOR:
        case INSTR_MUT_SHL:
        case INSTR_MUT_SHR:
                mutate(c, op);
                return false;

        case INSTR_ADD:
        case INSTR_SUB:
        case INSTR_MUL:
        case INSTR_EQ:
        case INSTR_NEQ:
        case INSTR_LT:
        case INSTR_GT:
        case INSTR_LEQ:
        case INSTR_GEQ:
                if (!inline_operator(c, op)) {
                        numeric(c, op);
                }
                return false;

        case INSTR_CALL:
        case INSTR_CALL_GLOBAL:
        case INSTR_CALL_METHOD:
        case INSTR_TRY_CALL_METHOD:
        case INSTR_CALL_SELF_METHOD:
        case INSTR_CALL_STATIC_METHOD:
        case INSTR_CALL_SELF_STATIC:
                invoke(c, node);
                return false;

        case INSTR_JUMP:
        case INSTR_JUMP_IF_TYPE:
        case INSTR_JEQ:
        case INSTR_JNE:
        case INSTR_JLT:
        case INSTR_JGT:
        case INSTR_JLE:
        case INSTR_JGE:
        case INSTR_JUMP_IF:
        case INSTR_JUMP_IF_NOT:
        case INSTR_JUMP_IF_NIL:
        case INSTR_JUMP_IF_SENTINEL:
        case INSTR_JUMP_IF_NONE:
        case INSTR_JUMP_AND:
        case INSTR_JUMP_OR:
                control(c, node);
                return false;

        case INSTR_YIELD:
        case INSTR_YIELD_SOME:
        case INSTR_YIELD_NONE:
                yield(c, node);
                return false;

        case INSTR_LOOP_ITER:
                if (fast_loop(c, node)) {
                        return true;
                }
                lower_misc(c, node, ip);
                return false;

        case INSTR_TARGET_SUBSCRIPT:
                if (fast_target_subscript(c, node)) {
                        return true;
                }
                lower_misc(c, node, ip);
                return false;

        case INSTR_TARGET_LOCAL:
                if (fast_target_local(c, node, ip)) {
                        return true;
                }
                lower_target(c, ip, op);
                return false;

        case INSTR_TARGET_MEMBER:
        case INSTR_TARGET_SELF_MEMBER:
                if (member_assign(c, node, ip)) {
                        return true;
                }
                lower_misc(c, node, ip);
                return false;

        case INSTR_TARGET_CAPTURED:
        case INSTR_TARGET_REF:
                lower_target(c, ip, op);
                return false;

        case INSTR_CAPTURE:
                capture(c, ip);
                return false;

        case INSTR_FUNCTION:
        case INSTR_GENERATOR:
                function_literal(c, ip, op);
                return false;

        case INSTR_LOAD_LOCAL:
                load_local(c, load_i32(ip + 1));
                return false;

        case INSTR_LOAD_GLOBAL:
                push_from(c, tycall(c, vm_global, LT_PTR, imm32(load_i32(ip + 1))));
                return false;

        case INSTR_LOAD_CAPTURED:
                push_from(c, captured(c, load_i32(ip + 1)));
                return false;

        case INSTR_LOAD_REF:
                push_from(c, reference(c, load_i32(ip + 1), true));
                return false;

        case INSTR_ASSIGN_LOCAL:
                local_store(c, load_i32(ip + 1));
                return false;

        case INSTR_ASSIGN: {
                LirReg p = slot_of(c, c->sp - 1);
                tycall(c, assign_value, LT_VOID, preg(p));
                return false;
        }

        case INSTR_PATCH_ENV: {
                LirReg p = slot_of(c, c->sp - 1);
                tycall(c, jit_rt_patch_env, LT_VOID, preg(p), imm32(load_i32(ip + 1)));
                return false;
        }

        case INSTR_THROW: {
                LirReg p = slot_of(c, c->sp - 1);
                tycall(c, jit_rt_throw, LT_VOID, preg(p));
                never_returns(c);
                return false;
        }

        case INSTR_PUSH_NTH: {
                i32 nth = load_i32(ip + 1);
                copy(c, c->ops, vat(c->sp), c->ops, vat(c->sp - 1 - nth));
                c->sp += 1;
                return false;
        }

        case INSTR_DUP:
                copy(c, c->ops, vat(c->sp), c->ops, vat(c->sp - 1));
                c->sp += 1;
                return false;

        case INSTR_DROP2:
                copy(c, c->ops, vat(c->sp - 3), c->ops, vat(c->sp - 1));
                c->sp -= 2;
                return false;

        case INSTR_UNPOP:
                c->sp += 1;
                return false;

        case INSTR_POP:
                c->sp -= 1;
                return false;

        case INSTR_SENTINEL: literal(c, VALUE_SENTINEL, 0);                return false;
        case INSTR_INT8:     literal(c, VALUE_INTEGER, (i8)ip[1]);         return false;
        case INSTR_INTEGER:  literal(c, VALUE_INTEGER, peek(u64, ip + 1)); return false;
        case INSTR_REAL:     literal(c, VALUE_REAL, peek(u64, ip + 1));    return false;
        case INSTR_TRUE:     literal(c, VALUE_BOOLEAN, 1);                 return false;
        case INSTR_FALSE:    literal(c, VALUE_BOOLEAN, 0);                 return false;
        case INSTR_NIL:      literal(c, VALUE_NIL, 0);                     return false;
        case INSTR_NONE:     literal(c, VALUE_NONE, 0);                    return false;

        case INSTR_RETURN:
        case INSTR_RETURN_PRESERVE_CTX:
                sync_sp(c);
                leave(c, JIT_RETURN);
                return false;

        case INSTR_CHECK_INIT:
        case INSTR_NOP:
        case INSTR_HALT:
                return false;

        default:
                c->ok = false;
                return false;
        }
}

static void
reset_slots(BcLir *c, BcLirNode const *node, i32 off)
{
        if (c->vs == NULL) {
                return;
        }

        for (i32 i = node->sp; i < c->max_sp + 8; ++i) {
                c->vs[i].kind = VS_MEM;
                c->vs[i].hint = T2_TYPE_INVALID;
        }

        if (c->hints != NULL && node->sp > 0) {
                T2Type hint = find_type_hint(c->hints, off);
                if (hint != T2_TYPE_INVALID) {
                        c->vs[node->sp - 1].hint = hint;
                }
        }
}

static void
enter_node(BcLir *c, BcLirNode const *node, char const *ip)
{
        i32 off = ip - c->code;

        c->sp = node->sp;

        loop_leave(c, off);

        BcJoin *join = (node->label != LIR_NONE) ? vs_join_at(c, off) : NULL;

        if (join != NULL) {
                if (c->falls) {
                        c->at = off;
                        vs_carry(c, join, node->sp - 1);
                }
                if (!join->keep) {
                        vs_flush_below(c, node->sp - 1);
                }
        } else if (node->label != LIR_NONE) {
                vs_flush_below(c, node->sp);
        }

        if (node->label != LIR_NONE) {
                loop_enter(c, off);
                vs_forget(c);
                bind(c, node->label);
        }

        reset_slots(c, node, off);

        if (join != NULL) {
                vs_joined(c, join, node->sp - 1);
        }

        if (c->dynamic) {
                dynamic_ops(c);
        }

        c->offset = StepInstruction(ip) - c->code;
        c->at     = off;

#ifdef TY_PROFILER
        sync_sp(c);
        tycall(c, jit_profiler_tick, LT_VOID, pimm(ip));
#endif
}

static bool
lower_node(BcLir *c, BcLirNode const *node, char const *ip)
{
        enter_node(c, node, ip);

        c->falls = falls(node->op);

        if (vs_lower(c, node, ip)) {
                bool skip    = c->skip_next;
                c->skip_next = false;
                return skip;
        }

        vs_flush_all(c);
        vs_forget(c);

        bool skip = lower_op(c, node, ip);

        if (
                c->dynamic
             && sync_after(node->op)
             && !(is_call(node->op) && node->argc == -1)
        ) {
                resync(c, node);
        }

        return skip;
}

static void
lower_all(BcLir *c)
{
        char const *end = c->code + c->size;

        for (char const *ip = c->code; c->ok && ip < end; ip = StepInstruction(ip)) {
                BcLirNode const *node = &c->nodes[ip - c->code];

                opstat(c, (u8)*ip, node->sp >= 0);

                if (node->sp >= 0 && lower_node(c, node, ip)) {
                        ip = StepInstruction(ip);
                }

                for (; c->skip_extra > 0; --c->skip_extra) {
                        ip = StepInstruction(ip);
                }
        }
}

static void
entry_point(BcLir *c, LirLabel label, u32 tag)
{
        c->ok = c->ok && lir_entry(c->L, label);
        vvL(c->L->insts)->tag = tag;

        if (c->base_index != LIR_NONE) {
                base_slot(c);
        }
}

static void
epilogue(BcLir *c)
{
        for (i32 off = 0; off < c->size; ++off) {
                BcLirNode const *node = &c->nodes[off];

                if (!decoded(node)) {
                        continue;
                }

                if (node->osr_id != 0) {
                        entry_point(c, node->osr, off);
                        loop_osr(c, off, node->sp);
                        jump(c, node->label);
                }

                if (node->resume_id != 0) {
                        entry_point(c, node->resume, node->next);
                        jump(c, c->nodes[node->next].label);
                }
        }

        exit_stubs(c);
        loop_stubs(c);

        bind(c, c->deopt);
        leave(c, JIT_PACK(JIT_DEOPT, 0));

        for (i32 off = 0; off < c->size; ++off) {
                BcLirNode const *node = &c->nodes[off];

                if (node->deopt != LIR_NONE && reached(node) && !(c->stubbed != NULL && c->stubbed[off])) {
                        bind(c, node->deopt);
                        flush_around(c, off);
                        leave(c, JIT_PACK(JIT_DEOPT, off));
                }
        }
}

static u32 *
osr_table(BcLir const *c, u32 *n)
{
        u32 *osr = (c->nosr != 0) ? xtA(u32, 2 * c->nosr) : NULL;

        *n = 0;

        for (i32 off = 0; osr != NULL && off < c->size; ++off) {
                BcLirNode const *node = &c->nodes[off];

                if (decoded(node) && node->osr_id != 0) {
                        osr[2 * *n]     = off;
                        osr[2 * *n + 1] = node->osr_id;
                        *n += 1;
                }
        }

        return osr;
}

static bool
is_compact(Value const *f)
{
        i16 flags = atomic_load((_Atomic i16 *)flags_of(f));

        switch (jit_tier()) {
        case 1:  return true;
        case 0:
        case 3:  return !(flags & FF_JIT_TIER2);
        default: return false;
        }
}

#define AUDIT(...) do {                                         \
        if (jit_audit_level() >= 2) {                           \
                fprintf(stderr, "jit-audit: " __VA_ARGS__);     \
        }                                                       \
} while (0)

static bool
admit(BcLir *c, Value const *f)
{
        if (!graph(c, f)) {
                AUDIT(
                        "lir cfg decline %s off=%u op=%s\n",
                        name_of(f),
                        c->offset,
                        GetInstructionName(c->code[c->offset])
                );
                return false;
        }

        if (c->dynamic && c->size > 4096) {
                AUDIT("lir decline %s reason=large dynamic stack\n", name_of(f));
                return false;
        }

        return true;
}

static LirCode *
publish(Ty *ty, Value const *f, BcLir const *c, LirCode *code, u64 begin)
{
#ifdef TY_PROFILER
        Expr const *expr    = !from_eval(f) ? expr_of(f) : NULL;
        char const *cls     = (expr != NULL && expr->class != NULL)
                            ? expr->class->name
                            : "";
        u64         elapsed = TyMonotonicTime() - begin;

        jit_log_compile((JitCompileRecord) {
                .name            = name_of(f),
                .class_name      = cls,
                .expr            = expr,
                .native_size     = code->size,
                .compile_time_ns = elapsed,
                .bc_code_size    = c->size
        });
#endif

        Expr const *source = !from_eval(f) ? expr_of(f) : NULL;

        jit_perf_map(code->body, code->size, name_of(f), source);

        code = lir_code_adopt(ty, code);
        set_jit_code_of(f, code);

        if (!from_eval(f)) {
                Value root = { .type = VALUE_PTR, .ptr = code, .gcptr = code };
                gc_immortalize(ty, &root);
        }

        return code;
}

static JitFn *
compile(Ty *ty, Value const *f, u64 begin)
{
        LirType  types[] = { LT_PTR, LT_I32, LT_PTR, LT_PTR, LT_PTR };
        LirSig   sig     = { .ret = LT_I32, .params = types, .nparams = 5, .nfixed = 5 };
        bool     method  = (f->info[FUN_INFO_CLASS] != -1);
        LirError err;
        BcLir    c       = {
                .L          = lir_new(name_of(f), &sig, LIR_MODE_ATTACHED, &err),
                .ctx        = ty,
                .function   = f,
                .ok         = true,
                .bound      = f->info[FUN_INFO_BOUND],
                .self_index = method ? f->info[FUN_INFO_PARAM_COUNT] : -1,
                .tuple_off  = -1,
                .compact    = is_compact(f)
        };

        if (c.L == NULL) {
                return NULL;
        }

        if (!admit(&c, f)) {
                lir_free(c.L);
                return NULL;
        }

        plan_nodes(&c);
        prologue(&c);

        c.ok = c.ok && vs_plan(&c, ty, f);
        c.ok = c.ok && loop_plan(&c);
        c.ok = c.ok && join_plan(&c);

        lower_all(&c);
        epilogue(&c);

        u32      ninsts = vN(c.L->insts);
        u32      nregs  = vN(c.L->regs);
        u32      nosr;
        u32     *osr    = osr_table(&c, &nosr);
        LirCode *code   = c.ok ? lir_finish_owned(ty, c.L, &err) : NULL;

        lir_free(c.L);

        if (code == NULL) {
                xmF(osr);
                xmF(c.tier);
                AUDIT("lir decline %s op=%u reason=%s\n", name_of(f), err.op, err.message);
                return NULL;
        }

        AUDIT(
                "lir %s native=%zu insts=%u regs=%u bc=%d "
                "dynamic=%d try=%d compile_us=%llu\n",
                name_of(f),
                code->size,
                ninsts,
                nregs,
                c.size,
                c.dynamic,
                c.has_try,
                (unsigned long long)((TyMonotonicTime() - begin) / 1000)
        );

        code->osr  = osr;
        code->nosr = nosr;
        code->tier = c.tier;

        return publish(ty, f, &c, code, begin)->body;
}

#undef AUDIT

JitFn *
jit_lower(Ty *ty, Value const *f)
{
        if (lir_target() == NULL) {
                return NULL;
        }

#ifdef TY_PROFILER
        u64 begin = TyMonotonicTime();
#else
        u64 begin = (jit_audit_level() >= 2) ? TyMonotonicTime() : 0;
#endif

        SCRATCH_SAVE();
        JitFn *fn = compile(ty, f, begin);
        SCRATCH_RESTORE();

        return fn;
}
