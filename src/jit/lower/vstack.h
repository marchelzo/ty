enum {
        VS_MEM,
        VS_INT,
        VS_REAL,
        VS_BOOL,
        VS_CINT,
        VS_CREAL,
        VS_CBOOL,
        VS_LOCAL,
        VS_CNIL
};

enum {
        VALUE_SHIFT = __builtin_ctz(sizeof (Value))
};

enum {
        UNTYPED,
        INTS,
        REALS,
        MIXED
};

enum {
        ARITH = 1,
        COMPARE
};

typedef struct {
        LirReg base;
        i32    at;
} Spot;

typedef struct {
        u8    how;
        LirOp iop;
        LirOp fop;
        LirCC icc;
        LirCC fcc;
} Numeric;

static Numeric const Numerics[] = {
        [INSTR_ADD] = { ARITH,   LIR_ADD,  LIR_FADD },
        [INSTR_SUB] = { ARITH,   LIR_SUB,  LIR_FSUB },
        [INSTR_MUL] = { ARITH,   LIR_MUL,  LIR_FMUL },
        [INSTR_DIV] = { ARITH,   LIR_SDIV, LIR_FDIV },
        [INSTR_EQ]  = { COMPARE, .icc = LIR_EQ, .fcc = LIR_FEQ },
        [INSTR_NEQ] = { COMPARE, .icc = LIR_NE, .fcc = LIR_FNE },
        [INSTR_LT]  = { COMPARE, .icc = LIR_LT, .fcc = LIR_FLT },
        [INSTR_GT]  = { COMPARE, .icc = LIR_GT, .fcc = LIR_FGT },
        [INSTR_LEQ] = { COMPARE, .icc = LIR_LE, .fcc = LIR_FLE },
        [INSTR_GEQ] = { COMPARE, .icc = LIR_GE, .fcc = LIR_FGE },
        [INSTR_JEQ] = { COMPARE, .icc = LIR_EQ, .fcc = LIR_FEQ },
        [INSTR_JNE] = { COMPARE, .icc = LIR_NE, .fcc = LIR_FNE },
        [INSTR_JLT] = { COMPARE, .icc = LIR_LT, .fcc = LIR_FLT },
        [INSTR_JGT] = { COMPARE, .icc = LIR_GT, .fcc = LIR_FGT },
        [INSTR_JLE] = { COMPARE, .icc = LIR_LE, .fcc = LIR_FLE },
        [INSTR_JGE] = { COMPARE, .icc = LIR_GE, .fcc = LIR_FGE }
};

#define each_arm(c, n, to)                                              \
        for (i32 _i = 0, _id, to; _i < narms(n); ++_i)                  \
        if ((to = arm((c), (n), _i, &_id)), (_id != -1))

inline static i32
numtag(bool real)
{
        return real ? VALUE_REAL : VALUE_INTEGER;
}

inline static u8
numkind(bool real)
{
        return real ? VS_REAL : VS_INT;
}

inline static LirClass
numcls(bool real)
{
        return real ? LIR_F64 : LIR_I64;
}

inline static bool
local_op(u8 op)
{
        return (op == INSTR_LOAD_LOCAL)
            || (op == INSTR_ASSIGN_LOCAL)
            || (op == INSTR_TARGET_LOCAL);
}

inline static bool
matches(BcLirNode const *n)
{
        return (n->op == INSTR_MATCH_TAG) || (n->op == INSTR_MATCH_STRING);
}

inline static i32
narms(BcLirNode const *n)
{
        return matches(n) ? n->argc : 0;
}

static i32
arm(BcLir const *c, BcLirNode const *n, i32 i, i32 *id)
{
        char const *p = n->kw_ip + 8 * i;

        *id = load_i32(p);

        return (i32)(p + 8 - c->code) + load_i32(p + 4);
}

static i32
vtag(u8 kind)
{
        switch (kind) {
        case VS_INT:
        case VS_CINT:  return VALUE_INTEGER;
        case VS_REAL:
        case VS_CREAL: return VALUE_REAL;
        case VS_CNIL:  return VALUE_NIL;
        default:       return VALUE_BOOLEAN;
        }
}

inline static bool
intish(u8 kind)
{
        return (kind == VS_INT) || (kind == VS_CINT);
}

inline static bool
realish(u8 kind)
{
        return (kind == VS_REAL) || (kind == VS_CREAL);
}

inline static bool
isconst(u8 kind)
{
        return (kind == VS_CINT)
            || (kind == VS_CREAL)
            || (kind == VS_CBOOL)
            || (kind == VS_CNIL);
}

inline static bool
boxed(u8 kind)
{
        return (kind == VS_MEM) || (kind == VS_LOCAL);
}

inline static bool
same_local(BcSlot const *s, i32 slot)
{
        return (s->kind == VS_LOCAL) && ((i32)s->bits == slot);
}

static int
pairing(u8 a, u8 b)
{
        if (intish(a) && intish(b)) {
                return INTS;
        }

        if (realish(a) && realish(b)) {
                return REALS;
        }

        if ((intish(a) || realish(a)) && (intish(b) || realish(b))) {
                return MIXED;
        }

        return UNTYPED;
}

static Numeric
numeric_op(u8 op)
{
        return (op < countof(Numerics)) ? Numerics[op] : (Numeric) {0};
}

static LirOp
mutop(u8 op, bool real)
{
        switch (op) {
        case INSTR_MUT_ADD: return real ? LIR_FADD : LIR_ADD;
        case INSTR_MUT_SUB: return real ? LIR_FSUB : LIR_SUB;
        default:            return real ? LIR_FMUL : LIR_MUL;
        }
}

inline static Spot
lspot(BcLir const *c, i32 slot)
{
        return (Spot) { c->locals, vat(slot) };
}

inline static Spot
sspot(BcLir const *c, i32 i)
{
        return (Spot) { c->ops, vat(i) };
}

static Spot
spot(BcLir const *c, i32 i)
{
        BcSlot const *s = &c->vs[i];
        return (s->kind == VS_LOCAL) ? lspot(c, (i32)s->bits) : sspot(c, i);
}

static LirReg
ldtag(BcLir *c, Spot s)
{
        return tagat(c, s.base, s.at);
}

static void
typecheck(BcLir *c, Spot s, i32 tag, LirLabel fail)
{
        expect(c, s.base, s.at, tag, fail);
}

static LirReg
unbox(BcLir *c, Spot s, bool real)
{
        return real ? ldf(c, s.base, s.at + VOFF(real)) : ldq(c, s.base, s.at + VOFF(z));
}

static void
unbox_to(BcLir *c, LirReg r, Spot s, bool real)
{
        vset(c, real ? LIR_LD_F64 : LIR_LD_I64, r, mref(s.base, s.at + VOFF(z)));
}

static void
put(BcLir *c, Spot s, LirReg r, bool real)
{
        store(c, real ? LIR_ST_F64 : LIR_ST64, s.base, s.at + VOFF(z), lir_r(r));
}

static void
box(BcLir *c, BcSlot const *s, Spot to)
{
        if (s->kind == VS_LOCAL) {
                copy(c, to.base, to.at, c->locals, vat((i32)s->bits));
                return;
        }

        LirOpnd x  = isconst(s->kind) ? lir_i((i64)s->bits) : lir_r(s->r);
        LirOp   op = (s->kind == VS_REAL) ? LIR_ST_F64 : LIR_ST64;

        stq(c, to.base, to.at, lir_i(vtag(s->kind)));
        store(c, op, to.base, to.at + VOFF(z), x);
}

static bool
vs_pinned(BcLir const *c, i32 i)
{
        BcSlot const *s = &c->vs[i];

        return loop_pinned(c, i)
            && (s->kind == VS_INT)
            && (s->r == c->spin[i]);
}

static void
vs_flush(BcLir *c, i32 i)
{
        if (c->vs[i].kind != VS_MEM && !vs_pinned(c, i)) {
                box(c, &c->vs[i], sspot(c, i));
                c->vs[i].kind = VS_MEM;
        }
}

static void
vs_flush_below(BcLir *c, i32 n)
{
        if (c->vs == NULL) {
                return;
        }

        for (i32 i = 0; i < n; ++i) {
                vs_flush(c, i);
        }
}

static void
vs_flush_all(BcLir *c)
{
        vs_flush_below(c, c->sp);
}

static void
vs_spill(BcLir *c, i32 i)
{
        if (c->vs[i].kind != VS_MEM) {
                box(c, &c->vs[i], sspot(c, i));
        }
}

static void
vs_push(BcLir *c, u8 kind, LirReg r, u64 bits)
{
        c->vs[c->sp++] = (BcSlot) { .kind = kind, .r = r, .bits = bits };
}

static void
vs_pop(BcLir *c, i32 n)
{
        while (n --> 0) {
                c->vs[--c->sp].kind = VS_MEM;
        }
}

static LirReg
numreg(BcLir *c, BcSlot const *s)
{
        switch (s->kind) {
        case VS_CINT:  return ival(c, (i64)s->bits);
        case VS_CREAL: return fval(c, peek(double, &s->bits));
        default:       return s->r;
        }
}

static LirReg
vreg(BcLir *c, i32 i)
{
        return numreg(c, &c->vs[i]);
}

static LirOpnd
iopnd(BcLir const *c, i32 i)
{
        BcSlot const *s = &c->vs[i];
        return (s->kind == VS_CINT) ? lir_i((i64)s->bits) : lir_r(s->r);
}

static void
vs_deopt(BcLir *c)
{
        for (i32 i = 0; i < c->sp; ++i) {
                vs_spill(c, i);
        }

        sync_sp(c);
        bail(c, c->at);
}

static LirLabel
vs_guard(BcLir *c)
{
        return newlabel(c);
}

static void
vs_seal(BcLir *c, LirLabel failed)
{
        LirLabel ok = newlabel(c);

        jump(c, ok);
        bind(c, failed);
        vs_deopt(c);
        bind(c, ok);
}

static void
assume(BcLir *c, Spot s, i32 tag)
{
        LirLabel failed = vs_guard(c);

        typecheck(c, s, tag, failed);
        vs_seal(c, failed);
}

static i32
lclass(BcLir const *c, i32 slot)
{
        return (c->local_class != NULL && local_ok(c, slot)) ? c->local_class[slot] : -1;
}

static i32
exact_class(T2Type type)
{
        T2Universe *u = t2_global_universe();

        if (type == T2_TYPE_INVALID) {
                return -1;
        }

        if (type == t2_primitive(u, T2_TYPE_INT)) {
                return CLASS_INT;
        }

        if (type == t2_primitive(u, T2_TYPE_FLOAT)) {
                return CLASS_FLOAT;
        }

        return -1;
}

static BcSlot const *
vs_known(BcLir const *c, i32 slot)
{
        bool fresh = (c->known != NULL)
                  && local_ok(c, slot)
                  && (c->known_gen[slot] == c->gen);

        return fresh ? &c->known[slot] : NULL;
}

static void
vs_remember(BcLir *c, i32 slot, BcSlot const *v)
{
        if (c->known == NULL || !local_ok(c, slot)) {
                return;
        }

        if (v == NULL || boxed(v->kind)) {
                c->known_gen[slot] = 0;
                return;
        }

        c->known[slot]     = *v;
        c->known_gen[slot] = c->gen;
}

static void
vs_forget(BcLir *c)
{
        c->gen += 1;
}

static void
vs_release(BcLir *c, i32 slot)
{
        for (i32 i = 0; i < c->sp; ++i) {
                if (same_local(&c->vs[i], slot)) {
                        vs_flush(c, i);
                }
        }
}

static LirReg
subidx(BcLir *c, i32 i, LirLabel slow)
{
        if (intish(c->vs[i].kind)) {
                return vreg(c, i);
        }

        Spot s = spot(c, i);

        typecheck(c, s, VALUE_INTEGER, slow);

        return unbox(c, s, false);
}

static LirReg
cell(BcLir *c, i32 i, LirReg idx, LirLabel slow)
{
        Spot s = spot(c, i);

        typecheck(c, s, VALUE_ARRAY, slow);

        i32    at    = s.at + VOFF(array);
        LirReg array = ldp(c, s.base, at);
        LirReg count = ldq(c, array, offsetof(Array, count));

        jcc(c, LIR_UGE, lir_r(idx), lir_r(count), slow);

        LirReg items  = ldp(c, array, offsetof(Array, items));
        LirReg scaled = vop(c, LIR_SHL, LIR_I64, lir_r(idx), lir_i(VALUE_SHIFT));

        return lea(c, items, scaled, 0);
}

static bool
indexable(BcSlot cont, BcSlot idx)
{
        return boxed(cont.kind) && (boxed(idx.kind) || intish(idx.kind));
}

static i32
hinted_class(BcLir const *c, BcLirNode const *node)
{
        if (!c->speculate || c->hints == NULL || node->next >= c->size) {
                return -1;
        }

        return exact_class(find_type_hint(c->hints, node->next));
}

static void
typed_subscript(BcLir *c, bool real)
{
        LirLabel failed = vs_guard(c);
        LirReg   i      = subidx(c, c->sp - 1, failed);
        Spot     e      = { cell(c, c->sp - 2, i, failed), 0 };

        typecheck(c, e, numtag(real), failed);

        LirReg r = unbox(c, e, real);

        vs_seal(c, failed);
        vs_pop(c, 2);
        vs_push(c, numkind(real), r, 0);
}

static bool
vs_subscript(BcLir *c, BcLirNode const *node)
{
        BcSlot cont = c->vs[c->sp - 2];
        BcSlot idx  = c->vs[c->sp - 1];

        if (!indexable(cont, idx) || (cont.kind == VS_MEM && idx.kind == VS_MEM)) {
                return false;
        }

        i32 class = hinted_class(c, node);

        if (class >= 0) {
                typed_subscript(c, class == CLASS_FLOAT);
                return true;
        }

        LirLabel slow = newlabel(c);
        LirLabel done = newlabel(c);
        LirReg   i    = subidx(c, c->sp - 1, slow);
        LirReg   p    = cell(c, c->sp - 2, i, slow);

        copy(c, c->ops, vat(c->sp - 2), p, 0);
        jump(c, done);

        bind(c, slow);
        vs_spill(c, c->sp - 2);
        vs_spill(c, c->sp - 1);

        LirReg left = slot_of(c, c->sp - 2);

        tycall(c, jit_rt_subscript, LT_VOID, preg(left));
        bind(c, done);

        vs_pop(c, 1);
        c->vs[c->sp - 1].kind = VS_MEM;

        return true;
}

static bool
vs_assign_subscript(BcLir *c, char const *ip)
{
        if ((u8)ip[1] != 1) {
                return false;
        }

        BcSlot value = c->vs[c->sp - 3];
        BcSlot cont  = c->vs[c->sp - 2];
        BcSlot idx   = c->vs[c->sp - 1];

        if (
                !indexable(cont, idx)
             || (cont.kind == VS_MEM && idx.kind == VS_MEM && value.kind == VS_MEM)
        ) {
                return false;
        }

        LirLabel slow = newlabel(c);
        LirLabel done = newlabel(c);
        LirReg   i    = subidx(c, c->sp - 1, slow);
        LirReg   p    = cell(c, c->sp - 2, i, slow);

        if (value.kind == VS_MEM) {
                copy(c, p, 0, c->ops, vat(c->sp - 3));
        } else {
                box(c, &value, (Spot) { p, 0 });
        }

        jump(c, done);

        bind(c, slow);

        for (i32 k = 3; k > 0; --k) {
                vs_spill(c, c->sp - k);
        }

        LirReg top = slot_of(c, c->sp);

        tycall(c, jit_rt_assign_subscript, LT_VOID, preg(top), imm32(1));
        bind(c, done);

        vs_pop(c, 2);

        return true;
}

static bool
chains(u8 op)
{
        switch (op) {
        case INSTR_INC:
        case INSTR_DEC:
        case INSTR_NEG:
        case INSTR_INT8:
        case INSTR_INTEGER:
        case INSTR_REAL:
        case INSTR_DUP:
        case INSTR_LOAD_LOCAL:
        case INSTR_ASSIGN_LOCAL:
        case INSTR_TARGET_LOCAL:
        case INSTR_SUBSCRIPT:
        case INSTR_ASSIGN_SUBSCRIPT:
                return true;

        default:
                return numeric_op(op).how != 0;
        }
}

static bool
numeric_next(BcLir const *c, BcLirNode const *node)
{
        if (node->next >= c->size) {
                return false;
        }

        BcLirNode const *next = next_of(c, node);

        return (next->label == LIR_NONE) && chains(next->op);
}

static bool
vs_plan(BcLir *c, Ty *ty, Value const *f)
{
        Expr const *expr = expr_of(f);

        c->vs        = new(c, BcSlot, c->max_sp + 8);
        c->hints     = (expr != NULL && !from_eval(f)) ? &expr->type_hints : NULL;
        c->speculate = !c->dynamic
                    && !c->has_try
                    && (c->nresume == c->nosr)
                    && !(flags_of(f)[0] & FF_JIT_NOSPEC)
                    && (getenv("TY_JIT_NO_SPECULATE") == NULL);

        if (c->bound == 0) {
                return true;
        }

        c->local_class = nones(c, i32, c->bound);
        c->local_type  = new(c, T2Type, c->bound);
        c->known       = new(c, BcSlot, c->bound);
        c->known_gen   = new(c, u32, c->bound);
        c->gen         = 1;

        if (expr == NULL || expr->scope == NULL) {
                return true;
        }

        c->hints = &expr->type_hints;

        i32 n = min(c->bound, vN(expr->scope->owned));

        for (i32 slot = 0; slot < n; ++slot) {
                Symbol *sym = v__(expr->scope->owned, slot);

                if (SymbolIsCaptured(sym)) {
                        continue;
                }

                c->local_type[slot] = sym->type;

                if (slot != c->self_index) {
                        c->local_class[slot] = exact_class(sym->type);
                }
        }

        return true;
}

static LirReg
tagreg(BcLir *c, i32 i)
{
        u8 kind = c->vs[i].kind;
        return boxed(kind) ? ldtag(c, spot(c, i)) : ival(c, vtag(kind));
}

static bool
nilcmp(BcLir const *c, u8 op, i32 *other)
{
        if (op != INSTR_EQ && op != INSTR_NEQ && op != INSTR_JEQ && op != INSTR_JNE) {
                return false;
        }

        if (c->vs[c->sp - 1].kind == VS_CNIL) {
                *other = c->sp - 2;
                return true;
        }

        if (c->vs[c->sp - 2].kind == VS_CNIL) {
                *other = c->sp - 1;
                return true;
        }

        return false;
}

static void
promote(BcLir *c)
{
        for (i32 i = c->sp - 2; i < c->sp; ++i) {
                if (intish(c->vs[i].kind)) {
                        c->vs[i].r    = vop(c, LIR_I2F, LIR_F64, lir_r(vreg(c, i)));
                        c->vs[i].kind = VS_REAL;
                        c->vs[i].bits = 0;
                }
        }
}

static void
operands(BcLir *c, bool real, bool div, LirOpnd *x, LirOpnd *y)
{
        if (real) {
                *x = lir_r(vreg(c, c->sp - 2));
                *y = lir_r(vreg(c, c->sp - 1));
                return;
        }

        *x = lir_r(vreg(c, c->sp - 2));
        *y = iopnd(c, c->sp - 1);

        if (div && y->kind == LO_IMM) {
                *y = lir_r(vreg(c, c->sp - 1));
        }
}

static bool
checked_divisor(BcLir *c, bool real)
{
        BcSlot const *b = &c->vs[c->sp - 1];

        if (!real && b->kind == VS_CINT && (i64)b->bits != 0 && (i64)b->bits != -1) {
                return true;
        }

        if (!c->speculate) {
                return false;
        }

        LirLabel failed = vs_guard(c);
        LirReg   d      = vreg(c, c->sp - 1);

        if (real) {
                LirReg raw = vop(c, LIR_BITCAST, LIR_I64, lir_r(d));
                LirReg mag = vop(c, LIR_SHL, LIR_I64, lir_r(raw), lir_i(1));
                jz(c, mag, failed);
        } else {
                jz(c, d, failed);
                jcc(c, LIR_EQ, lir_r(d), lir_i(-1), failed);
        }

        vs_seal(c, failed);

        c->vs[c->sp - 1] = (BcSlot) { .kind = numkind(real), .r = d };

        return true;
}

static bool
vs_binary(BcLir *c, u8 op)
{
        i32 other;

        if (nilcmp(c, op, &other)) {
                LirOpnd cc = lir_cc((op == INSTR_EQ) ? LIR_EQ : LIR_NE);
                LirReg  t  = tagreg(c, other);
                LirReg  d  = vop(c, LIR_SETCC, LIR_I64, cc, lir_r(t), lir_i(VALUE_NIL));

                vs_pop(c, 2);
                vs_push(c, VS_BOOL, d, 0);

                return true;
        }

        Numeric n    = numeric_op(op);
        int     pair = pairing(c->vs[c->sp - 2].kind, c->vs[c->sp - 1].kind);

        if (pair == MIXED && (op == INSTR_EQ || op == INSTR_NEQ)) {
                vs_pop(c, 2);
                vs_push(c, VS_CBOOL, LIR_NONE, op == INSTR_NEQ);
                return true;
        }

        if (pair == MIXED) {
                promote(c);
                pair = REALS;
        }

        if (pair == UNTYPED || n.how == 0) {
                return false;
        }

        bool real = (pair == REALS);

        if (op == INSTR_DIV && !checked_divisor(c, real)) {
                return false;
        }

        LirOpnd x;
        LirOpnd y;
        LirReg  d;
        u8      kind;

        operands(c, real, op == INSTR_DIV, &x, &y);

        if (n.how == COMPARE) {
                LirCC cc = real ? n.fcc : n.icc;
                d    = vop(c, real ? LIR_FSETCC : LIR_SETCC, LIR_I64, lir_cc(cc), x, y);
                kind = VS_BOOL;
        } else {
                d    = vop(c, real ? n.fop : n.iop, numcls(real), x, y);
                kind = numkind(real);
        }

        vs_pop(c, 2);
        vs_push(c, kind, d, 0);

        return true;
}

static bool
truth_jump(BcLir *c, bool when, LirLabel target)
{
        BcSlot top = c->vs[c->sp - 1];

        if (top.kind != VS_BOOL && top.kind != VS_CBOOL) {
                return false;
        }

        vs_flush_below(c, c->sp - 1);
        vs_pop(c, 1);

        if (top.kind == VS_BOOL) {
                jcc(c, when ? LIR_NE : LIR_EQ, lir_r(top.r), lir_i(0), target);
        } else if ((top.bits != 0) == when) {
                jump(c, target);
        }

        return true;
}

static void
nil_jump(BcLir *c, i32 i, i32 n, LirCC cc, LirLabel target)
{
        LirReg t = tagreg(c, i);

        vs_flush_below(c, c->sp - n);
        vs_pop(c, n);
        jcc(c, cc, lir_r(t), lir_i(VALUE_NIL), target);
}

static bool
vs_jump(BcLir *c, BcLirNode const *node)
{
        LirLabel target = dest(c, node);
        u8       op     = node->op;
        i32      other;

        if (node->deopt != LIR_NONE || target == LIR_NONE) {
                return false;
        }

        if (op == INSTR_JUMP_IF || op == INSTR_JUMP_IF_NOT) {
                return truth_jump(c, op == INSTR_JUMP_IF, target);
        }

        if (nilcmp(c, op, &other)) {
                nil_jump(c, other, 2, (op == INSTR_JEQ) ? LIR_EQ : LIR_NE, target);
                return true;
        }

        if (op == INSTR_JUMP_IF_NIL) {
                nil_jump(c, c->sp - 1, 1, LIR_EQ, target);
                return true;
        }

        Numeric n = numeric_op(op);

        if (n.how != COMPARE) {
                return false;
        }

        int pair = pairing(c->vs[c->sp - 2].kind, c->vs[c->sp - 1].kind);

        if (pair == MIXED && (op == INSTR_JEQ || op == INSTR_JNE)) {
                vs_flush_below(c, c->sp - 2);
                vs_pop(c, 2);

                if (op == INSTR_JNE) {
                        jump(c, target);
                }

                return true;
        }

        if (pair == MIXED) {
                promote(c);
                pair = REALS;
        }

        if (pair == UNTYPED) {
                return false;
        }

        bool    real = (pair == REALS);
        LirOpnd x;
        LirOpnd y;

        vs_flush_below(c, c->sp - 2);
        operands(c, real, false, &x, &y);
        vs_pop(c, 2);

        if (real) {
                veff(c, LIR_FBR, lir_cc(n.fcc), x, y, lir_l(target));
        } else {
                jcc(c, n.icc, x, y, target);
        }

        return true;
}

static bool
vs_mutate(BcLir *c, BcLirNode const *node, char const *ip)
{
        if (!c->speculate || node->next >= c->size) {
                return false;
        }

        BcLirNode const *next = next_of(c, node);

        if (
                (next->label != LIR_NONE)
             || (
                        (next->op != INSTR_MUT_ADD)
                     && (next->op != INSTR_MUT_SUB)
                     && (next->op != INSTR_MUT_MUL)
                )
        ) {
                return false;
        }

        i32  slot  = load_i32(ip + 1);
        i32  class = lclass(c, slot);
        u8   rhs   = c->vs[c->sp - 1].kind;
        bool ints  = (class == CLASS_INT) && intish(rhs);
        bool reals = (class == CLASS_FLOAT) && realish(rhs);

        if (!ints && !reals) {
                return false;
        }

        bool          real  = reals;
        Spot          s     = lspot(c, slot);
        BcSlot const *known = vs_known(c, slot);

        if (known != NULL && (real ? !realish(known->kind) : !intish(known->kind))) {
                known = NULL;
        }

        if (known == NULL) {
                assume(c, s, numtag(real));
        }

        c->offset    = next->next;
        c->skip_next = true;

        vs_release(c, slot);

        LirReg  cur = (known != NULL) ? numreg(c, known) : unbox(c, s, real);
        LirOpnd y   = real ? lir_r(vreg(c, c->sp - 1)) : iopnd(c, c->sp - 1);
        LirReg  r   = vop(c, mutop(next->op, real), numcls(real), lir_r(cur), y);

        put(c, s, r, real);

        c->vs[c->sp - 1] = (BcSlot) { .kind = numkind(real), .r = r };
        vs_remember(c, slot, &c->vs[c->sp - 1]);

        return true;
}

static bool
vs_load_local(BcLir *c, BcLirNode const *node, i32 slot)
{
        BcSlot const *known = vs_known(c, slot);
        i32           class = lclass(c, slot);

        if (known != NULL) {
                c->vs[c->sp++] = *known;
                return true;
        }

        if (!c->speculate || class < 0 || !numeric_next(c, node)) {
                if (!local_ok(c, slot)) {
                        return false;
                }

                vs_push(c, VS_LOCAL, LIR_NONE, (u64)slot);

                if (c->local_type != NULL) {
                        c->vs[c->sp - 1].hint = c->local_type[slot];
                }

                return true;
        }

        bool real = (class == CLASS_FLOAT);
        Spot s    = lspot(c, slot);

        assume(c, s, numtag(real));
        vs_push(c, numkind(real), unbox(c, s, real), 0);
        vs_remember(c, slot, &c->vs[c->sp - 1]);

        return true;
}

static bool
vs_assign_local(BcLir *c, i32 slot)
{
        BcSlot top = c->vs[c->sp - 1];

        if (top.kind == VS_MEM) {
                return false;
        }

        vs_pop(c, 1);

        if (same_local(&top, slot)) {
                return true;
        }

        vs_release(c, slot);
        box(c, &top, lspot(c, slot));
        vs_remember(c, slot, (top.kind == VS_LOCAL) ? vs_known(c, (i32)top.bits) : &top);

        return true;
}

static bool
vs_const(BcLir *c, u8 kind, u64 bits)
{
        vs_push(c, kind, LIR_NONE, bits);
        return true;
}

static bool
vs_drop(BcLir *c)
{
        if (c->vs[c->sp - 1].kind == VS_MEM) {
                return false;
        }

        vs_pop(c, 1);

        return true;
}

static bool
vs_dup(BcLir *c)
{
        if (c->vs[c->sp - 1].kind == VS_MEM) {
                return false;
        }

        c->vs[c->sp] = c->vs[c->sp - 1];
        c->sp += 1;

        return true;
}

static bool
vs_dup2_swap(BcLir *c)
{
        BcSlot pair[] = { c->vs[c->sp - 1], c->vs[c->sp - 2] };

        if (!intish(pair[0].kind) || !intish(pair[1].kind)) {
                return false;
        }

        for (i32 k = 0; k < 2; ++k) {
                if (pair[k].kind == VS_INT) {
                        pair[k].r = vop(c, LIR_MOV, LIR_I64, lir_r(pair[k].r));
                }
                c->vs[c->sp++] = pair[k];
        }

        return true;
}

static bool
vs_step(BcLir *c, bool up)
{
        BcSlot top = c->vs[c->sp - 1];

        if (!intish(top.kind)) {
                return false;
        }

        if (vs_pinned(c, c->sp - 1)) {
                vset(c, LIR_ADD, top.r, lir_r(top.r), lir_i(up ? 1 : -1));
                put(c, sspot(c, c->sp - 1), top.r, false);
                return true;
        }

        LirReg x = vreg(c, c->sp - 1);
        LirReg r = vop(c, up ? LIR_ADD : LIR_SUB, LIR_I64, lir_r(x), lir_i(1));

        c->vs[c->sp - 1] = (BcSlot) { .kind = VS_INT, .r = r };

        return true;
}

static bool
vs_negate(BcLir *c)
{
        u8 kind = c->vs[c->sp - 1].kind;

        if (!intish(kind) && !realish(kind)) {
                return false;
        }

        bool   real = realish(kind);
        LirReg x    = vreg(c, c->sp - 1);
        LirReg r    = vop(c, real ? LIR_FNEG : LIR_NEG, numcls(real), lir_r(x));

        c->vs[c->sp - 1] = (BcSlot) { .kind = numkind(real), .r = r };

        return true;
}

static bool
vs_lower(BcLir *c, BcLirNode const *node, char const *ip)
{
        u8 op = node->op;

        if (c->vs == NULL || c->dynamic) {
                return false;
        }

        if (local_op(op) && loop_lower(c, node, ip)) {
                return true;
        }

        switch (op) {
        case INSTR_INT8:             return vs_const(c, VS_CINT, (u64)(i64)(i8)ip[1]);
        case INSTR_INTEGER:          return vs_const(c, VS_CINT, peek(u64, ip + 1));
        case INSTR_REAL:             return vs_const(c, VS_CREAL, peek(u64, ip + 1));
        case INSTR_TRUE:             return vs_const(c, VS_CBOOL, 1);
        case INSTR_FALSE:            return vs_const(c, VS_CBOOL, 0);
        case INSTR_NIL:              return vs_const(c, VS_CNIL, 0);
        case INSTR_LOAD_LOCAL:       return vs_load_local(c, node, load_i32(ip + 1));
        case INSTR_ASSIGN_LOCAL:     return vs_assign_local(c, load_i32(ip + 1));
        case INSTR_TARGET_LOCAL:     return vs_mutate(c, node, ip);
        case INSTR_SUBSCRIPT:        return vs_subscript(c, node);
        case INSTR_ASSIGN_SUBSCRIPT: return vs_assign_subscript(c, ip);
        case INSTR_POP:              return vs_drop(c);
        case INSTR_DUP:              return vs_dup(c);
        case INSTR_DUP2_SWAP:        return vs_dup2_swap(c);
        case INSTR_INC:              return vs_step(c, true);
        case INSTR_DEC:              return vs_step(c, false);
        case INSTR_NEG:              return vs_negate(c);

        case INSTR_ADD:
        case INSTR_SUB:
        case INSTR_MUL:
        case INSTR_DIV:
        case INSTR_EQ:
        case INSTR_NEQ:
        case INSTR_LT:
        case INSTR_GT:
        case INSTR_LEQ:
        case INSTR_GEQ:
                return vs_binary(c, op);

        case INSTR_JUMP_IF:
        case INSTR_JUMP_IF_NOT:
        case INSTR_JUMP_IF_NIL:
        case INSTR_JEQ:
        case INSTR_JNE:
        case INSTR_JLT:
        case INSTR_JGT:
        case INSTR_JLE:
        case INSTR_JGE:
                return vs_jump(c, node);

        default:
                return false;
        }
}
