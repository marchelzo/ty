#include "impl.h"

#define VAL(f)   offsetof(Value, f)
#define FRAME(f) offsetof(LirEntryFrame, f)

#define call(t, fn, ret, flags, ...) invoke(                    \
        (t),                                                    \
        (void *)(fn),                                           \
        (ret),                                                  \
        (flags),                                                \
        (Arg[]) { __VA_ARGS__ },                                \
        countof(((Arg[]) { __VA_ARGS__ }))                      \
)

typedef struct {
        Lir              *L;
        LirRuntime const *rt;
        LirReg            ty;
        LirReg            out;
        LirReg            frame;
} Thunk;

typedef struct {
        LirType type;
        LirOpnd value;
} Arg;

inline static Arg
arg(LirType type, LirOpnd value)
{
        return (Arg) { .type = type, .value = value };
}

inline static Arg
preg(LirReg r)
{
        return arg(LT_PTR, lir_r(r));
}

inline static Arg
imm32(i64 n)
{
        return arg(LT_I32, lir_i(n));
}

static LirReg
emit_call(
        Thunk *t,
        void *fn,
        LirType ret,
        LirType const *types,
        LirOpnd *args,
        u32 n,
        u32 flags
)
{
        LirReg r = (ret == LT_VOID) ? LIR_NONE : lir_reg(t->L, lir_type_class(ret));

        lir_emit(t->L, &(LirInst) {
                .op         = LIR_CALL,
                .dst        = r,
                .args       = { lir_i((uptr)fn) },
                .nargs      = 1,
                .sig        = { .ret = ret, .params = types, .nparams = n, .nfixed = n },
                .flags      = flags,
                .call_args  = args,
                .ncall_args = n
        });

        return r;
}

static LirReg
invoke(Thunk *t, void *fn, LirType ret, u32 flags, Arg const *xs, u32 n)
{
        LirType types[LIR_MAX_OPERANDS];
        LirOpnd args[LIR_MAX_OPERANDS];

        for (u32 i = 0; i < n; ++i) {
                types[i] = xs[i].type;
                args[i]  = xs[i].value;
        }

        return emit_call(t, fn, ret, types, args, n, flags);
}

static LirReg
load(Thunk *t, LirOp op, LirClass cls, LirReg base, i32 disp)
{
        LirReg r = lir_reg(t->L, cls);
        lir_emit_to(t->L, op, r, (LirOpnd[]) { lir_m(base, LIR_NONE, 1, disp) }, 1);
        return r;
}

static void
store(Thunk *t, LirOp op, LirReg base, i32 disp, LirOpnd value)
{
        LirOpnd args[] = { lir_m(base, LIR_NONE, 1, disp), value };
        lir_emit_to(t->L, op, LIR_NONE, args, countof(args));
}

static void
unary(Thunk *t, LirOp op, LirReg d, LirReg a)
{
        lir_emit_to(t->L, op, d, (LirOpnd[]) { lir_r(a) }, 1);
}

static void
binary(Thunk *t, LirOp op, LirReg d, LirOpnd a, LirOpnd b)
{
        lir_emit_to(t->L, op, d, (LirOpnd[]) { a, b }, 2);
}

static void
move(Thunk *t, LirReg d, LirReg a)
{
        unary(t, LIR_MOV, d, a);
}

static void
branch(Thunk *t, LirCC cc, LirReg a, i64 b, LirLabel to)
{
        LirOpnd args[] = { lir_cc(cc), lir_r(a), lir_i(b), lir_l(to) };
        lir_emit_to(t->L, LIR_BR, LIR_NONE, args, countof(args));
}

static void
jump(Thunk *t, LirLabel to)
{
        lir_emit_to(t->L, LIR_JMP, LIR_NONE, (LirOpnd[]) { lir_l(to) }, 1);
}

static LirReg
pointer(Thunk *t, LirReg value, LirReg tag, u32 i)
{
        Lir     *L    = t->L;
        LirReg   r    = lir_reg(L, LIR_PTR);
        LirLabel fast = lir_label(L);
        LirLabel blob = lir_label(L);
        LirLabel done = lir_label(L);

        branch(t, LIR_EQ, tag, VALUE_PTR, fast);
        branch(t, LIR_EQ, tag, VALUE_BLOB, blob);
        LirReg slow = call(
                t,
                t->rt->ptr_from,
                LT_PTR,
                LIR_MAY_GC | LIR_MAY_THROW,
                preg(t->ty),
                preg(t->frame),
                imm32(i)
        );

        move(t, r, slow);
        jump(t, done);

        lir_bind(L, fast);
        move(t, r, load(t, LIR_LD_I64, LIR_PTR, value, VAL(ptr)));
        jump(t, done);

        lir_bind(L, blob);
        LirReg b = load(t, LIR_LD_I64, LIR_PTR, value, VAL(blob));
        move(t, r, load(t, LIR_LD_I64, LIR_PTR, b, offsetof(Blob, items)));

        lir_bind(L, done);

        return r;
}

static LirReg
floating(Thunk *t, LirReg value, LirReg tag, LirType type, LirLabel error)
{
        Lir     *L    = t->L;
        LirReg   r    = lir_reg(L, lir_type_class(type));
        LirLabel real = lir_label(L);
        LirLabel done = lir_label(L);

        branch(t, LIR_EQ, tag, VALUE_REAL, real);
        branch(t, LIR_NE, tag, VALUE_INTEGER, error);
        unary(t, LIR_I2F, r, load(t, LIR_LD_I64, LIR_I64, value, VAL(z)));
        jump(t, done);

        lir_bind(L, real);
        unary(
                t,
                (type == LT_F32) ? LIR_FTRUNC : LIR_MOV,
                r,
                load(t, LIR_LD_F64, LIR_F64, value, VAL(real))
        );

        lir_bind(L, done);

        return r;
}

static LirReg
argument(Thunk *t, LirType type, u32 i)
{
        Lir   *L     = t->L;
        LirReg args  = load(t, LIR_LD_I64, LIR_PTR, t->frame, FRAME(args));
        LirReg value = lir_reg(L, LIR_PTR);

        binary(t, LIR_ADD, value, lir_r(args), lir_i((u64)i * sizeof (Value)));

        if (type == LT_VAL) {
                return value;
        }

        if (type == LT_REF) {
                return call(
                        t,
                        t->rt->ref_from,
                        LT_REF,
                        LIR_MAY_GC | LIR_MAY_THROW,
                        preg(t->ty),
                        preg(value),
                        imm32(i)
                );
        }

        LirReg tag = load(t, LIR_LD_U8, LIR_I64, value, VAL(type));

        binary(t, LIR_AND, tag, lir_r(tag), lir_i(~VALUE_TAGGED & 255));

        if (type == LT_PTR) {
                return pointer(t, value, tag, i);
        }

        LirLabel error = lir_label(L);
        LirLabel done  = lir_label(L);
        LirReg   r;

        if (type == LT_F32 || type == LT_F64) {
                r = floating(t, value, tag, type, error);
        } else if (type == LT_BOOL) {
                branch(t, LIR_NE, tag, VALUE_BOOLEAN, error);
                r = load(t, LIR_LD_U8, LIR_I64, value, VAL(boolean));
        } else {
                branch(t, LIR_NE, tag, VALUE_INTEGER, error);
                r = load(t, LIR_LD_I64, LIR_I64, value, VAL(z));
        }

        jump(t, done);

        lir_bind(L, error);
        call(
                t,
                t->rt->arg_type_error,
                LT_VOID,
                LIR_MAY_THROW | LIR_NORETURN,
                preg(t->ty),
                imm32(i),
                imm32(type),
                preg(value)
        );

        lir_bind(L, done);

        return r;
}

static LirReg
widen(Thunk *t, LirReg f32)
{
        LirReg f64 = lir_reg(t->L, LIR_F64);
        unary(t, LIR_FEXT, f64, f32);
        return f64;
}

static void
box(Thunk *t, LirReg value, LirType type)
{
        if (type == LT_VAL) {
                for (u32 off = 0; off < sizeof (Value); off += 8) {
                        LirReg part = load(t, LIR_LD_I64, LIR_I64, value, off);
                        store(t, LIR_ST64, t->out, off, lir_r(part));
                }
                return;
        }

        for (u32 off = 0; off < sizeof (Value); off += 8) {
                store(t, LIR_ST64, t->out, off, lir_i(0));
        }

        if (type == LT_VOID) {
                store(t, LIR_ST8, t->out, VAL(type), lir_i(VALUE_NIL));
                return;
        }

        u8    tag = VALUE_INTEGER;
        LirOp op  = LIR_ST64;
        u32   off = VAL(z);

        switch (type) {
        case LT_F32:
                value = widen(t, value);
        case LT_F64:
                tag = VALUE_REAL;
                op  = LIR_ST_F64;
                off = VAL(real);
                break;

        case LT_BOOL:
                tag = VALUE_BOOLEAN;
                op  = LIR_ST8;
                off = VAL(boolean);
                break;

        case LT_REF:
                store(t, LIR_ST64, t->out, VAL(gcptr), lir_r(value));
        case LT_PTR:
                tag = VALUE_PTR;
                off = VAL(ptr);
                break;
        }

        store(t, op, t->out, off, lir_r(value));
        store(t, LIR_ST8, t->out, VAL(type), lir_i(tag));
}

static bool
takes(LirSig const *sig, LirType type)
{
        for (u32 i = 0; i < sig->nparams; ++i) {
                if (sig->params[i] == type) {
                        return true;
                }
        }

        return false;
}

static char const *
unsupported(LirRuntime const *rt, LirCode const *code)
{
        if (
                (rt == NULL)
             || (rt->arity_error == NULL)
             || (rt->arg_type_error == NULL)
             || (rt->reserve == NULL)
             || (rt->restore == NULL)
             || (code->release && (rt->unlock == NULL || rt->lock == NULL))
        ) {
                return "entry thunk requires a VM runtime";
        }

        if (
                (rt->ptr_from == NULL && takes(&code->sig, LT_PTR))
             || (rt->ref_from == NULL && takes(&code->sig, LT_REF))
        ) {
                return "entry conversion requires a VM runtime";
        }

        return NULL;
}

static void
arguments(Thunk *t, LirCode const *code, LirOpnd *args)
{
        for (u32 pass = 0; pass < 2; ++pass) {
                for (u32 i = 0; i < code->sig.nparams; ++i) {
                        LirType type = code->sig.params[i];
                        if ((type == LT_PTR) == (pass == 0)) {
                                args[i] = lir_r(argument(t, type, i));
                        }
                }
        }
}

static void
body(Ty *ty, Thunk *t, LirCode *code)
{
        Lir     *L       = t->L;
        LirOpnd *args    = stA(LirOpnd, code->sig.nparams + 1);
        bool     lean    = (code->nvslots == 0) && (code->mode == LIR_MODE_DETACHED);
        bool     vm      = (code->mode == LIR_MODE_ATTACHED);
        LirOpnd  frame[] = {
                lir_i(sizeof (LirEntryFrame)),
                lir_i(alignof (LirEntryFrame))
        };

        lir_emit_to(L, LIR_ALLOCA, t->frame, frame, countof(frame));
        store(t, LIR_ST64, t->frame, FRAME(out), lir_r(t->out));
        store(t, LIR_ST64, t->frame, FRAME(args), lir_r(L->params[2]));

        if (lean) {
                store(t, LIR_ST64, t->frame, FRAME(base), lir_i(0));
        } else {
                call(
                        t,
                        t->rt->reserve,
                        LT_VOID,
                        LIR_MAY_GC,
                        preg(t->ty),
                        preg(t->frame),
                        arg(LT_U32, lir_i(code->nvslots))
                );
        }

        arguments(t, code, args);

        if (code->release) {
                call(t, t->rt->unlock, LT_VOID, 0, preg(t->ty));
        }

        LirReg result = emit_call(
                t,
                code->body,
                code->sig.ret,
                code->sig.params,
                args,
                code->sig.nparams,
                vm ? LIR_MAY_GC | LIR_MAY_THROW : 0
        );

        if (code->release) {
                call(t, t->rt->lock, LT_VOID, 0, preg(t->ty));
        }

        if (!lean) {
                LirReg out = call(t, t->rt->restore, LT_PTR, 0, preg(t->ty), preg(t->frame));
                move(t, t->out, out);
        } else if (takes(&code->sig, LT_PTR)) {
                move(t, t->out, load(t, LIR_LD_I64, LIR_PTR, t->frame, FRAME(out)));
        }

        box(t, result, code->sig.ret);
}

Lir *
lir_build_entry(Ty *ty, LirCode *code, LirError *err)
{
        static LirType const params[] = { LT_PTR, LT_PTR, LT_PTR, LT_I32 };

        ty = lir_scratch(ty);

        LirRuntime const *rt  = lir_runtime();
        char const       *why = unsupported(rt, code);

        if (why != NULL) {
                lir_fail(err, LE_MODE, LIR_NOWHERE, "%s", why);
                return NULL;
        }

        LirSig sig = {
                .ret     = LT_VOID,
                .params  = params,
                .nparams = countof(params),
                .nfixed  = countof(params)
        };

        Lir *L = lir_new_in(&ty->scratch, code->name, &sig, LIR_MODE_ATTACHED, err);

        lir_pin_param(L, LIR_PIN_0, 0);
        lir_pin_param(L, LIR_PIN_1, 1);

        Thunk t = {
                .L     = L,
                .rt    = rt,
                .ty    = lir_pinned(L, LIR_PIN_0),
                .out   = lir_pinned(L, LIR_PIN_1),
                .frame = lir_reg(L, LIR_PTR)
        };

        LirReg   argc  = L->params[3];
        LirLabel arity = lir_label(L);

        branch(&t, LIR_NE, argc, code->sig.nparams, arity);

        body(ty, &t, code);

        lir_emit_to(L, LIR_RET, LIR_NONE, NULL, 0);

        lir_bind(L, arity);
        call(
                &t,
                rt->arity_error,
                LT_VOID,
                LIR_MAY_THROW | LIR_NORETURN,
                preg(t.ty),
                imm32(code->sig.nparams),
                arg(LT_I32, lir_r(argc))
        );

        if (!lir_validate(ty, L, err)) {
                lir_free(L);
                return NULL;
        }

        return L;
}
