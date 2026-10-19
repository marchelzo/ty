enum {
        CF_VM    = LIR_MAY_GC | LIR_MAY_THROW | LIR_CALL_SITE,
        CF_ENTER = CF_VM | LIR_WRITES_LOCALS,
        CF_PURE  = LIR_READS_NO_LOCALS
};

typedef struct {
        LirType type;
        LirOpnd opnd;
} BcArg;

#define LIST(T, ...) (T const []) { __VA_ARGS__ }, countof(((T const []) { __VA_ARGS__ }))
#define OPNDS(...)   LIST(LirOpnd, __VA_ARGS__)
#define ARGS(...)    LIST(BcArg, __VA_ARGS__)

#define VOFF(f)    ((i32)offsetof(Value, f))
#define peek(T, p) (*(T *)memcpy(&(T) {0}, (p), sizeof (T)))

inline static i32
vat(i32 slot)
{
        return slot * (i32)sizeof (Value);
}

inline static BcArg
imm(LirType type, i64 x)
{
        return (BcArg) { type, lir_i(x) };
}

inline static BcArg
imm32(i64 x)
{
        return imm(LT_I32, x);
}

inline static BcArg
imm64(i64 x)
{
        return imm(LT_I64, x);
}

inline static BcArg
bimm(bool b)
{
        return imm(LT_BOOL, b);
}

inline static BcArg
pimm(void const *p)
{
        return imm(LT_PTR, (uptr)p);
}

inline static BcArg
preg(LirReg r)
{
        return (BcArg) { LT_PTR, lir_r(r) };
}

inline static BcArg
reg32(LirReg r)
{
        return (BcArg) { LT_I32, lir_r(r) };
}

inline static BcArg
freg(LirReg r)
{
        return (BcArg) { LT_F64, lir_r(r) };
}

static LirReg
emitv(BcLir *c, LirOp op, LirClass cls, LirOpnd const *args, u32 n)
{
        LirReg r = lir_reg(c->L, cls);
        c->ok = c->ok && (r != LIR_NONE) && lir_emit_to(c->L, op, r, args, n);
        return r;
}

static void
set(BcLir *c, LirOp op, LirReg dst, LirOpnd const *args, u32 n)
{
        c->ok = c->ok && lir_emit_to(c->L, op, dst, args, n);
}

static void
effect(BcLir *c, LirOp op, LirOpnd const *args, u32 n)
{
        set(c, op, LIR_NONE, args, n);
}

#define vop(c, op, cls, ...) emitv((c), (op), (cls), OPNDS(__VA_ARGS__))
#define vset(c, op, d, ...)  set((c), (op), (d), OPNDS(__VA_ARGS__))
#define veff(c, op, ...)     effect((c), (op), OPNDS(__VA_ARGS__))

inline static LirOpnd
mref(LirReg base, i32 disp)
{
        return lir_m(base, LIR_NONE, 1, disp);
}

static LirReg
addr(BcLir *c, LirReg base, i32 disp)
{
        return vop(c, LIR_LEA, LIR_PTR, mref(base, disp));
}

static LirReg
ldx(BcLir *c, LirOp op, LirClass cls, LirReg base, i32 disp)
{
        return vop(c, op, cls, mref(base, disp));
}

static void
store(BcLir *c, LirOp op, LirReg base, i32 disp, LirOpnd value)
{
        veff(c, op, mref(base, disp), value);
}

static void
copy(BcLir *c, LirReg dst, i32 di, LirReg src, i32 si)
{
        veff(c, LIR_COPY32, mref(dst, di), mref(src, si));
}

static LirLabel
newlabel(BcLir *c)
{
        return lir_label(c->L);
}

static LirLabel
coldlabel(BcLir *c)
{
        LirLabel label = newlabel(c);
        lir_cold(c->L, label);
        return label;
}

static void
bind(BcLir *c, LirLabel label)
{
        c->ok = c->ok && lir_bind(c->L, label);
}

static void
jump(BcLir *c, LirLabel label)
{
        veff(c, LIR_JMP, lir_l(label));
}

static void
jcc(BcLir *c, LirCC cc, LirOpnd a, LirOpnd b, LirLabel target)
{
        veff(c, LIR_BR, lir_cc(cc), a, b, lir_l(target));
}

inline static void
unless(BcLir *c, LirReg r, i64 x, LirLabel miss)
{
        jcc(c, LIR_NE, lir_r(r), lir_i(x), miss);
}

inline static void
jz(BcLir *c, LirReg r, LirLabel to)
{
        jcc(c, LIR_EQ, lir_r(r), lir_i(0), to);
}

inline static void
jnz(BcLir *c, LirReg r, LirLabel to)
{
        unless(c, r, 0, to);
}

static LirLabel
exit_edge(BcLir *c, i32 to);

static void
flush_active(BcLir *c);

static void
flush_around(BcLir *c, i32 off);

static bool
lazy_pinned(BcLir const *c, i32 pos);

inline static i32
opslot(BcLir const *c, i32 off)
{
        return load_i32(c->code + off + 1);
}

static bool
in_range(BcLir const *c, i32 idx, i32 cont, u8 shift);

static LirReg const *
held_string(BcLir const *c, i32 i);

inline static LirLabel
dest(BcLir *c, BcLirNode const *node)
{
        return exit_edge(c, node->target);
}

inline static bool
local_ok(BcLir const *c, i32 slot)
{
        return (slot >= 0) && (slot < c->bound);
}

inline static BcLirNode const *
next_of(BcLir const *c, BcLirNode const *node)
{
        return &c->nodes[node->next];
}

static LirReg
call_target(
        BcLir *c,
        LirOpnd target,
        LirType ret,
        LirType const *types,
        LirOpnd *args,
        u32 n,
        u32 flags
)
{
        LirReg  r  = (ret == LT_VOID) ? LIR_NONE : lir_reg(c->L, lir_type_class(ret));
        LirInst in = {
                .op         = LIR_CALL,
                .dst        = r,
                .args       = { target },
                .nargs      = 1,
                .sig        = { .ret = ret, .params = types, .nparams = n, .nfixed = n },
                .flags      = flags,
                .tag        = c->offset,
                .call_args  = args,
                .ncall_args = n
        };

        c->last_call = vN(c->L->insts);
        c->ok        = c->ok && lir_emit(c->L, &in);

        return r;
}

static LirReg
call_with(BcLir *c, LirOpnd target, LirType ret, u32 flags, BcArg const *xs, u32 n)
{
        LirType types[n];
        LirOpnd args[n];

        for (u32 i = 0; i < n; ++i) {
                types[i] = xs[i].type;
                args[i]  = xs[i].opnd;
        }

        return call_target(c, target, ret, types, args, n, flags);
}

static u32
helper_flags(void const *helper)
{
        if (
                (helper == vm_global)
             || (helper == vm_get_self)
             || (helper == ClassOf)
             || (helper == jit_rt_truthy)
        ) {
                return LIR_READS_NO_LOCALS;
        }

        u32 flags = LIR_MAY_GC | LIR_MAY_THROW | LIR_CALL_SITE | LIR_WRITES_LOCALS;

        if (helper == jit_rt_throw || helper == vm_jit_end_try_rethrow) {
                flags |= LIR_NORETURN;
        }

        return flags;
}

#define fnptr(fn) ((void const *)(uptr)(fn))

#define ccallf(c, fn, ret, flags, ...) call_with(               \
        (c),                                                    \
        lir_i((uptr)(fn)),                                      \
        (ret),                                                  \
        (flags),                                                \
        ARGS(__VA_ARGS__)                                       \
)

#define ccall(c, fn, ret, ...)                                  \
        ccallf((c), (fn), (ret), helper_flags(fnptr(fn)), __VA_ARGS__)

#define tycall(c, fn, ret, ...)                                 \
        ccall((c), (fn), (ret), preg((c)->ty) __VA_OPT__(,) __VA_ARGS__)

#define jcall(c, code, ...)                                     \
        call_with((c), lir_r(code), LT_I32, CF_ENTER, ARGS(__VA_ARGS__))

static void
never_returns(BcLir *c)
{
        v_(c->L->insts, c->last_call)->flags |= LIR_NORETURN;
}

static void
leave(BcLir *c, i64 status)
{
        veff(c, LIR_RET, lir_i(status));
}

static void
bail(BcLir *c, i32 off)
{
        leave(c, JIT_PACK(JIT_DEOPT, off));
}

inline static LirReg
binop(BcLir *c, LirOp op, LirClass cls, LirOpnd a, LirOpnd b)
{
        return vop(c, op, cls, a, b);
}

inline static LirReg
binr(BcLir *c, LirOp op, LirClass cls, LirReg a, LirReg b)
{
        return binop(c, op, cls, lir_r(a), lir_r(b));
}

inline static LirReg
setcc(BcLir *c, LirOp op, LirCC cc, LirReg a, LirReg b)
{
        return vop(c, op, LIR_I64, lir_cc(cc), lir_r(a), lir_r(b));
}

inline static LirReg
unop(BcLir *c, LirOp op, LirClass cls, LirOpnd a)
{
        return vop(c, op, cls, a);
}

inline static LirReg
plus(BcLir *c, LirReg r, i64 n)
{
        return binop(c, LIR_ADD, LIR_I64, lir_r(r), lir_i(n));
}

inline static LirReg
ival(BcLir *c, i64 n)
{
        return unop(c, LIR_LI, LIR_I64, lir_i(n));
}

inline static LirReg
fval(BcLir *c, double x)
{
        return unop(c, LIR_FLI, LIR_F64, lir_f(x));
}

inline static LirReg
pval(BcLir *c, void const *p)
{
        return unop(c, LIR_LI, LIR_PTR, lir_i((uptr)p));
}

inline static LirReg
konst(BcLir *c, Value const *v)
{
        return unop(c, LIR_MOV, LIR_PTR, lir_const(c->L, v));
}

inline static void
mov(BcLir *c, LirReg d, LirReg s)
{
        vset(c, LIR_MOV, d, lir_r(s));
}

inline static LirReg
lea(BcLir *c, LirReg base, LirReg index, i32 disp)
{
        return unop(c, LIR_LEA, LIR_PTR, lir_m(base, index, 1, disp));
}

inline static LirReg
elem(BcLir *c, LirReg items, LirReg i, i32 disp)
{
        return lea(c, items, binop(c, LIR_SHL, LIR_I64, lir_r(i), lir_i(5)), disp);
}

inline static LirReg
ldp(BcLir *c, LirReg base, i32 disp)
{
        return ldx(c, LIR_LD_I64, LIR_PTR, base, disp);
}

inline static LirReg
ldq(BcLir *c, LirReg base, i32 disp)
{
        return ldx(c, LIR_LD_I64, LIR_I64, base, disp);
}

inline static LirReg
ldw(BcLir *c, LirReg base, i32 disp)
{
        return ldx(c, LIR_LD_I32, LIR_I64, base, disp);
}

inline static LirReg
ldf(BcLir *c, LirReg base, i32 disp)
{
        return ldx(c, LIR_LD_F64, LIR_F64, base, disp);
}

inline static LirReg
tagat(BcLir *c, LirReg base, i32 disp)
{
        return ldx(c, LIR_LD_U8, LIR_I64, base, disp + VOFF(type));
}

inline static void
stq(BcLir *c, LirReg base, i32 disp, LirOpnd v)
{
        store(c, LIR_ST64, base, disp, v);
}

inline static void
xinc(BcLir *c, void const *counter)
{
        LirReg p = pval(c, counter);
        stq(c, p, 0, lir_r(binop(c, LIR_ADD, LIR_I64, lir_r(ldq(c, p, 0)), lir_i(1))));
}

inline static void
stw(BcLir *c, LirReg base, i32 disp, LirOpnd v)
{
        store(c, LIR_ST32, base, disp, v);
}

static void
GuardNote(BcLir *c, char const *fmt, ...)
{
        char buf[512];
        va_list ap;

        va_start(ap, fmt);
        vsnprintf(buf, sizeof buf, fmt, ap);
        va_end(ap);

        c->guard = jit_guard(buf);
}

#define guard_note(c, ...) (JIT_DETAIL ? GuardNote((c), __VA_ARGS__) : (void)0)

inline static void
deopt_why(BcLir *c, i32 why, u64 slots)
{
        if (JIT_DETAIL) {
                stw(c, c->ty, offsetof(Ty, jit_why), lir_i(why));
                stq(c, c->ty, offsetof(Ty, jit_why_slots), lir_i(slots));
                stw(c, c->ty, offsetof(Ty, jit_guard), lir_i(c->guard));
                c->guard = 0;
        }
}

inline static void
miss_site(BcLir *c)
{
        if (JitStatsOn) {
                effect(c, LIR_SITE, (LirOpnd[]) { lir_i(c->at + 1) }, 1);
        }
}

inline static void
count_fast(BcLir *c, int kind)
{
        if (JitStatsOn) {
                u64 *n = jit_site_fast(c->code + c->at + 1, kind);
                if (n != NULL) {
                        LirReg base = pval(c, jit_site_fast_base());
                        i32    disp = (i32)((n - jit_site_fast_base()) * sizeof *n);
                        stq(c, base, disp, lir_r(binop(c, LIR_ADD, LIR_I64, lir_r(ldq(c, base, disp)), lir_i(1))));
                }
        }
}

inline static void
stb(BcLir *c, LirReg base, i32 disp, LirOpnd v)
{
        store(c, LIR_ST8, base, disp, v);
}

inline static void
stf(BcLir *c, LirReg base, i32 disp, LirOpnd v)
{
        store(c, LIR_ST_F64, base, disp, v);
}

inline static LirReg
bump(BcLir *c, LirReg base, i32 disp, i64 n)
{
        LirReg r = plus(c, ldq(c, base, disp), n);
        stq(c, base, disp, lir_r(r));
        return r;
}

inline static void
bumpw(BcLir *c, LirReg base, i32 disp, i64 n)
{
        stw(c, base, disp, lir_r(plus(c, ldw(c, base, disp), n)));
}

inline static LirReg
expect(BcLir *c, LirReg base, i32 disp, i32 type, LirLabel miss)
{
        LirReg tag = tagat(c, base, disp);
        unless(c, tag, type, miss);
        return tag;
}

inline static void
same_ptr(BcLir *c, LirReg r, void const *p, LirLabel miss)
{
        jcc(c, LIR_NE, lir_r(r), lir_r(pval(c, p)), miss);
}

inline static void
guard_epoch(BcLir *c, LirLabel miss)
{
        unless(c, ldw(c, pval(c, &ClassMethodEpoch), 0), 0, miss);
}

inline static void
guard_class(BcLir *c, LirReg value, i32 class, LirLabel miss)
{
        expect(c, value, 0, VALUE_OBJECT, miss);
        unless(c, ldw(c, value, VOFF(class)), class, miss);
}

inline static LirReg
tag_of(BcLir *c, i32 slot)
{
        return tagat(c, c->ops, vat(slot));
}

inline static LirReg
slot_of(BcLir *c, i32 slot)
{
        return addr(c, c->ops, vat(slot));
}

inline static LirReg
int_at(BcLir *c, i32 slot)
{
        return ldq(c, c->ops, vat(slot) + VOFF(z));
}

inline static LirReg
real_at(BcLir *c, i32 slot)
{
        return ldf(c, c->ops, vat(slot) + VOFF(real));
}

static LirReg
captured(BcLir *c, i32 index)
{
        return ldp(c, c->env, index * sizeof (Value *));
}

[[gnu::always_inline]]
inline static u16
offset_of(Class const *class, i32 member, bool writing, u16 kind)
{
        u16Vector const *offsets = writing ? &class->offsets_w : &class->offsets_r;

        if (member < 0 || member >= vN(*offsets)) {
                return OFF_NOT_FOUND;
        }

        u16 off = v__(*offsets, member);

        if (off == OFF_NOT_FOUND || (off >> OFF_SHIFT) != kind) {
                return OFF_NOT_FOUND;
        }

        return off;
}

static void
put_scalar(BcLir *c, i32 slot, i32 type, LirOpnd payload)
{
        i32 at = vat(slot);

        for (u32 i = 0; i < sizeof (Value); i += 8) {
                stq(c, c->ops, at + i, lir_i(0));
        }

        stb(c, c->ops, at + VOFF(type), lir_i(type));
        stq(c, c->ops, at + VOFF(z), payload);
}

static void
put_real(BcLir *c, LirReg base, i32 at, LirReg x)
{
        stq(c, base, at, lir_i(VALUE_REAL));
        stf(c, base, at + VOFF(real), lir_r(x));
}

static LirReg
as_real(BcLir *c, LirReg tag, LirReg base, i32 disp, bool strict, LirLabel slow)
{
        LirLabel integer = newlabel(c);
        LirLabel ready   = newlabel(c);
        LirReg   x       = lir_reg(c->L, LIR_F64);

        jcc(c, LIR_NE, lir_r(tag), lir_i(VALUE_REAL), strict ? slow : integer);
        vset(c, LIR_LD_F64, x, mref(base, disp + VOFF(real)));
        jump(c, ready);

        bind(c, integer);
        if (!strict) {
                unless(c, tag, VALUE_INTEGER, slow);
                vset(c, LIR_I2F, x, lir_r(ldq(c, base, disp + VOFF(z))));
        }

        bind(c, ready);

        return x;
}

static void
nonzero_real(BcLir *c, LirReg base, i32 disp, LirLabel slow)
{
        LirReg bits = ldq(c, base, disp + VOFF(real));
        LirReg mag  = binop(c, LIR_SHL, LIR_I64, lir_r(bits), lir_i(1));

        jz(c, mag, slow);
}

static void
no_overflow_div(BcLir *c, LirReg d, LirLabel slow)
{
        jz(c, d, slow);
        jcc(c, LIR_EQ, lir_r(d), lir_i(-1), slow);
}
