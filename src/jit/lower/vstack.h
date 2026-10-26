enum {
        VS_MEM,
        VS_INT,
        VS_REAL,
        VS_BOOL,
        VS_CINT,
        VS_CREAL,
        VS_CBOOL,
        VS_LOCAL,
        VS_CNIL,
        VS_CELL
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

static char const *
slot_label(BcLir const *c, i32 slot)
{
        Expr const *e = !from_eval(c->function) ? expr_of(c->function) : NULL;

        if (
                (e != NULL)
             && (e->fn->scope != NULL)
             && (slot >= 0)
             && (slot < vN(e->fn->scope->owned))
             && (v__(e->fn->scope->owned, slot) != NULL)
        ) {
                return v__(e->fn->scope->owned, slot)->identifier;
        }

        return "?";
}

static char const *
kind_label(u8 kind)
{
        switch (kind) {
        case VS_INT:
        case VS_CINT:  return "an Int";
        case VS_REAL:
        case VS_CREAL: return "a Float";
        case VS_BOOL:
        case VS_CBOOL: return "a Bool";
        case VS_CNIL:  return "nil";
        }

        return "a boxed value";
}

static char const *
operand_label(BcLir const *c, i32 i)
{
        static _Thread_local char buf[128];
        BcSlot const *s = &c->vs[i];

        if (s->kind == VS_LOCAL) {
                snprintf(buf, sizeof buf, "`%s`", slot_label(c, (i32)s->bits));
        } else if (s->src > 0) {
                snprintf(buf, sizeof buf, "`%s`", slot_label(c, s->src - 1));
        } else {
                snprintf(buf, sizeof buf, "the operand");
        }

        return buf;
}

#define NUM_LABEL(real) ((real) ? "a Float" : "an Int")

typedef struct {
        u8    how;
        LirOp iop;
        LirOp fop;
        LirCC icc;
        LirCC fcc;
        bool  ints;
} Numeric;

static Numeric const Numerics[] = {
        [INSTR_ADD] = { ARITH,   LIR_ADD,  LIR_FADD },
        [INSTR_SUB] = { ARITH,   LIR_SUB,  LIR_FSUB },
        [INSTR_MUL] = { ARITH,   LIR_MUL,  LIR_FMUL },
        [INSTR_DIV] = { ARITH,   LIR_SDIV, LIR_FDIV },
        [INSTR_MOD]     = { ARITH, LIR_SREM, .ints = true },
        [INSTR_BIT_AND] = { ARITH, LIR_AND,  .ints = true },
        [INSTR_BIT_OR]  = { ARITH, LIR_OR,   .ints = true },
        [INSTR_BIT_XOR] = { ARITH, LIR_XOR,  .ints = true },
        [INSTR_SHL]     = { ARITH, LIR_SHL,  .ints = true },
        [INSTR_SHR]     = { ARITH, LIR_SAR,  .ints = true },
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
        return (kind == VS_MEM) || (kind == VS_LOCAL) || (kind == VS_CELL);
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
        case INSTR_MUT_AND: return LIR_AND;
        case INSTR_MUT_OR:  return LIR_OR;
        case INSTR_MUT_XOR: return LIR_XOR;
        case INSTR_MUT_SHL: return LIR_SHL;
        case INSTR_MUT_SHR: return LIR_SAR;
        default:            return real ? LIR_FMUL : LIR_MUL;
        }
}

inline static bool
int_mutation(u8 op)
{
        switch (op) {
        case INSTR_MUT_AND:
        case INSTR_MUT_OR:
        case INSTR_MUT_XOR:
        case INSTR_MUT_SHL:
        case INSTR_MUT_SHR:
                return true;

        default:
                return false;
        }
}

inline static bool
shifting(LirOp op)
{
        return (op == LIR_SHL) || (op == LIR_SAR);
}

static LirOpnd
shift_count(BcLir *c, LirOpnd y)
{
        if (y.kind == LO_IMM) {
                return lir_i(y.imm & 63);
        }

        return lir_r(vop(c, LIR_AND, LIR_I64, y, lir_i(63)));
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
home(BcLir const *c, BcSlot const *s)
{
        return (s->kind == VS_CELL) ? (Spot) { s->r, (i32)s->bits } : lspot(c, (i32)s->bits);
}

static Spot
spot(BcLir const *c, i32 i)
{
        BcSlot const *s = &c->vs[i];

        switch (s->kind) {
        case VS_LOCAL:
        case VS_CELL:  return home(c, s);
        default:       return sspot(c, i);
        }
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
        if (s->kind == VS_LOCAL || s->kind == VS_CELL) {
                Spot from = home(c, s);
                copy(c, to.base, to.at, from.base, from.at);
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
vs_expose_pinned(BcLir *c, i32 i)
{
        if (c->vs != NULL && i >= 0 && vs_pinned(c, i) && lazy_pinned(c, i)) {
                put(c, sspot(c, i), c->vs[i].r, false);
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
vs_settle(BcLir *c, i32 n)
{
        for (i32 i = 0; i < n; ++i) {
                if (c->vs[i].kind == VS_CELL) {
                        vs_flush(c, i);
                }
        }
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
        flush_active(c);
        deopt_why(c, JIT_WHY_NUMERIC, 0);
        bail(c, c->at);
}

static LirLabel
vs_guard(BcLir *c)
{
        return coldlabel(c);
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
vs_disown(BcLir *c, i32 slot)
{
        for (i32 i = 0; i < c->nfacts; ++i) {
                if (c->facts[i].cont == slot || c->facts[i].base == slot) {
                        c->facts[i].gen = c->gen - 1;
                }
        }

        for (i32 i = 0; i < c->sp; ++i) {
                if (c->vs[i].src == slot + 1) {
                        c->vs[i].src = 0;
                }
        }

        for (i32 i = 0; c->known != NULL && i < c->bound; ++i) {
                if (c->known[i].src == slot + 1) {
                        c->known[i].src = 0;
                }
        }

        if (c->proven_gen != NULL && local_ok(c, slot)) {
                c->proven_gen[slot] = 0;
        }
}

static void
vs_release(BcLir *c, i32 slot)
{
        vs_disown(c, slot);

        for (i32 i = 0; i < c->sp; ++i) {
                if (same_local(&c->vs[i], slot)) {
                        vs_flush(c, i);
                }
        }
}

static bool
index_at(BcLir const *c, i32 p, i32 cont, i32 base, i32 *off)
{
        BcLirNode const *n = &c->nodes[p];

        if (n->op != INSTR_LOAD_LOCAL || opslot(c, p) != cont || n->next >= c->size) {
                return false;
        }

        i32 q = n->next;

        if (c->nodes[q].op != INSTR_LOAD_LOCAL || opslot(c, q) != base || c->nodes[q].next >= c->size) {
                return false;
        }

        BcLirNode const *k = next_of(c, &c->nodes[q]);
        char const      *ip = c->code + n->next + (k - &c->nodes[q]);
        i64              v;

        switch (k->op) {
        case INSTR_SUBSCRIPT:
        case INSTR_ASSIGN_SUBSCRIPT:
        case INSTR_TARGET_SUBSCRIPT:
                *off = 0;
                return true;

        case INSTR_INT8:
                v = (i8)ip[1];
                break;

        case INSTR_INTEGER:
                v = peek(i64, ip + 1);
                break;

        default:
                return false;
        }

        if (k->next >= c->size || v < -(1 << 20) || v > (1 << 20)) {
                return false;
        }

        BcLirNode const *op  = next_of(c, k);
        BcLirNode const *use = (op->next < c->size) ? next_of(c, op) : NULL;

        if (
                (use == NULL)
             || (op->op != INSTR_ADD && op->op != INSTR_SUB)
             || (use->op != INSTR_SUBSCRIPT && use->op != INSTR_ASSIGN_SUBSCRIPT && use->op != INSTR_TARGET_SUBSCRIPT)
        ) {
                return false;
        }

        *off = (op->op == INSTR_ADD) ? (i32)v : (i32)-v;

        return true;
}

static void
offsets_ahead(BcLir const *c, i32 cont, i32 base, i32 *lo, i32 *hi)
{
        for (i32 p = c->at; p < c->size; p = c->nodes[p].next) {
                BcLirNode const *n = &c->nodes[p];
                i32              off;

                if (
                        (n->next == 0)
                     || (n->sp < 0)
                     || (p != c->at && n->label != LIR_NONE)
                     || n->branch
                     || is_call(n->op)
                     || (
                                (n->op == INSTR_TARGET_LOCAL || n->op == INSTR_ASSIGN_LOCAL)
                             && (opslot(c, p) == cont || opslot(c, p) == base)
                        )
                     || captures(c, p, cont)
                     || captures(c, p, base)
                ) {
                        return;
                }

                if (index_at(c, p, cont, base, &off)) {
                        *lo = min(*lo, off);
                        *hi = max(*hi, off);
                }
        }
}

static bool
merged_bounds(BcLir *c, i32 i, LirReg idx, LirReg count, LirLabel failed)
{
        BcSlot const *x = &c->vs[i + 1];
        BcSlot const *h = &c->vs[i];
        i32           base;
        i32           off;

        if (h->kind != VS_LOCAL || getenv("TY_JIT_NO_MERGE") != NULL) {
                return false;
        }

        if (x->kind == VS_LOCAL) {
                base = (i32)x->bits;
                off  = 0;
        } else if (intish(x->kind) && x->src != 0) {
                base = x->src - 1;
                off  = x->off;
        } else {
                return false;
        }

        i32 cont = (i32)h->bits;

        for (i32 k = 0; k < c->nfacts; ++k) {
                BcFact const *f = &c->facts[k];
                if (f->gen == c->gen && f->cont == cont && f->base == base && f->lo <= off && off <= f->hi) {
                        return true;
                }
        }

        i32 lo = off;
        i32 hi = off;

        offsets_ahead(c, cont, base, &lo, &hi);

        if (lo == hi) {
                return false;
        }

        LirReg top = vop(c, LIR_ADD, LIR_I64, lir_r(idx), lir_i(hi - off));
        LirReg bot = vop(c, LIR_ADD, LIR_I64, lir_r(idx), lir_i(lo - off));

        jcc(c, LIR_GE, lir_r(top), lir_r(count), failed);
        jcc(c, LIR_LT, lir_r(bot), lir_i(0), failed);

        i32 slot = (c->nfacts < (i32)countof(c->facts)) ? c->nfacts++ : (i32)(c->gen % countof(c->facts));

        c->facts[slot] = (BcFact) { .cont = cont, .base = base, .lo = lo, .hi = hi, .gen = c->gen };

        return true;
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
array_at(BcLir *c, Spot s, LirReg idx, LirLabel slow);

static LirReg
cell(BcLir *c, i32 i, LirReg idx, LirLabel slow, bool merge)
{
        LirReg const *held = held_array(c, i);

        if (held != NULL) {
                if (!in_range(c, i + 1, i, 0) && !(merge && merged_bounds(c, i, idx, held[1], slow))) {
                        jcc(c, LIR_UGE, lir_r(idx), lir_r(held[1]), slow);
                }
                return lea(c, held[2], vop(c, LIR_SHL, LIR_I64, lir_r(idx), lir_i(VALUE_SHIFT)), 0);
        }

        Spot s = spot(c, i);

        typecheck(c, s, VALUE_ARRAY, slow);

        return array_at(c, s, idx, slow);
}

static LirReg
array_at(BcLir *c, Spot s, LirReg idx, LirLabel slow)
{
        i32    at    = s.at + VOFF(array);
        LirReg array = ldp(c, s.base, at);
        LirReg count = ldq(c, array, offsetof(Array, count));

        jcc(c, LIR_UGE, lir_r(idx), lir_r(count), slow);

        LirReg items  = ldp(c, array, offsetof(Array, items));
        LirReg scaled = vop(c, LIR_SHL, LIR_I64, lir_r(idx), lir_i(VALUE_SHIFT));

        return lea(c, items, scaled, 0);
}

static i32
container_class(BcLir *c, i32 i)
{
        BcSlot const *s = &c->vs[i];

        if (s->kind != VS_LOCAL || s->hint == T2_TYPE_INVALID) {
                return -1;
        }

        Class *class = expected_class_of(c->ctx, s->hint);

        return (class != NULL) ? class->i : -1;
}

static LirReg
blob_byte_at(BcLir *c, LirReg blob, LirReg idx, LirLabel slow)
{
        LirReg count = ldq(c, blob, offsetof(Blob, count));

        jcc(c, LIR_UGE, lir_r(idx), lir_r(count), slow);

        return lea(c, ldp(c, blob, offsetof(Blob, items)), idx, 0);
}

static LirReg
byte_cell(BcLir *c, i32 i, LirReg idx, LirLabel slow, bool merge)
{
        LirReg const *held = held_blob(c, i);

        if (held != NULL) {
                if (!in_range(c, i + 1, i, 0) && !(merge && merged_bounds(c, i, idx, held[1], slow))) {
                        jcc(c, LIR_UGE, lir_r(idx), lir_r(held[1]), slow);
                }
                return lea(c, held[2], idx, 0);
        }

        Spot s = spot(c, i);

        typecheck(c, s, VALUE_BLOB, slow);

        return blob_byte_at(c, ldp(c, s.base, s.at + VOFF(blob)), idx, slow);
}

inline static bool
bytelike(u8 kind)
{
        return intish(kind) || boxed(kind);
}

static LirReg
byte_value(BcLir *c, BcSlot value, i32 i, LirLabel slow)
{
        if (intish(value.kind)) {
                return vreg(c, i);
        }

        Spot s = spot(c, i);

        typecheck(c, s, VALUE_INTEGER, slow);

        return unbox(c, s, false);
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
        guard_note(c, "assumed the Array holds %s elements and the index is an in-bounds Int", real ? "Float" : "Int");

        LirLabel failed = vs_guard(c);
        LirReg   i      = subidx(c, c->sp - 1, failed);
        Spot     e      = { cell(c, c->sp - 2, i, failed, true), 0 };

        typecheck(c, e, numtag(real), failed);

        LirReg r = unbox(c, e, real);

        vs_seal(c, failed);
        vs_pop(c, 2);
        vs_push(c, numkind(real), r, 0);
}

static LirReg
runes(BcLir *c, LirReg str, LirReg bytes)
{
        return ccallf(c, jit_rt_runes, LT_I64, CF_PURE | LIR_FAST_PATH, preg(str), { LT_I64, lir_r(bytes) });
}

static bool
vs_count(BcLir *c)
{
        i32           i     = c->sp - 1;
        i32           class = container_class(c, i);
        LirReg const *held  = (held_array(c, i) != NULL) ? held_array(c, i) : held_blob(c, i);
        LirReg        n;

        if (held != NULL) {
                n = vop(c, LIR_MOV, LIR_I64, lir_r(held[1]));
        } else if (held_string(c, i) != NULL) {
                held = held_string(c, i);
                n    = runes(c, held[2], held[1]);
        } else if (c->speculate && class == CLASS_STRING) {
                guard_note(c, "assumed %s is a String (its static type)", operand_label(c, i));

                LirLabel failed = vs_guard(c);
                Spot     s      = spot(c, i);

                typecheck(c, s, VALUE_STRING, failed);

                n = runes(
                        c,
                        ldp(c, s.base, s.at + VOFF(str)),
                        ldx(c, LIR_LD_U32, LIR_I64, s.base, s.at + VOFF(bytes))
                );

                vs_seal(c, failed);
        } else if (c->speculate && (class == CLASS_ARRAY || class == CLASS_BLOB)) {
                bool array = (class == CLASS_ARRAY);

                guard_note(c, "assumed %s is %s (its static type)", operand_label(c, i), array ? "an Array" : "a Blob");

                LirLabel failed = vs_guard(c);
                Spot     s      = spot(c, i);

                typecheck(c, s, array ? VALUE_ARRAY : VALUE_BLOB, failed);

                n = array ? ldq(c, ldp(c, s.base, s.at + VOFF(array)), offsetof(Array, count))
                          : ldq(c, ldp(c, s.base, s.at + VOFF(blob)), offsetof(Blob, count));

                vs_seal(c, failed);
        } else {
                return false;
        }

        vs_pop(c, 1);
        vs_push(c, VS_INT, n, 0);

        return true;
}

static bool
vs_keyed(BcLir *c, BcLirNode const *node)
{
        i32 id = literal_key(c, node);

        if (id < 0 || c->vs[c->sp - 1].kind != VS_MEM || !boxed(c->vs[c->sp - 2].kind)) {
                return false;
        }

        vs_settle(c, c->sp - 2);

        Value    key  = literal_string(id);
        Spot     s    = spot(c, c->sp - 2);
        LirLabel slow = newlabel(c);
        LirLabel done = newlabel(c);

        typecheck(c, s, VALUE_DICT, slow);

        LirReg dict = ldp(c, s.base, s.at + VOFF(dict));
        LirReg item = ccall(
                c,
                dict_find_hashed,
                LT_PTR,
                preg(c->ty),
                preg(dict),
                preg(slot_of(c, c->sp - 1)),
                { LT_I64, lir_i((i64)value_hash(c->ctx, &key)) }
        );

        jz(c, item, slow);
        copy(c, c->ops, vat(c->sp - 2), item, 0);
        jump(c, done);

        bind(c, slow);
        vs_spill(c, c->sp - 2);
        tycall(c, jit_rt_subscript, LT_VOID, preg(slot_of(c, c->sp - 2)));

        bind(c, done);
        vs_pop(c, 1);
        c->vs[c->sp - 1].kind = VS_MEM;

        return true;
}

static bool
vs_subscript(BcLir *c, BcLirNode const *node)
{
        BcSlot cont = c->vs[c->sp - 2];
        BcSlot idx  = c->vs[c->sp - 1];

        if (vs_keyed(c, node)) {
                return true;
        }

        if (!indexable(cont, idx) || (cont.kind == VS_MEM && idx.kind == VS_MEM)) {
                return false;
        }

        i32 holder = container_class(c, c->sp - 2);

        if (holder == CLASS_BLOB && c->speculate) {
                guard_note(c, "assumed the Blob index is an in-bounds Int");
                LirLabel failed = vs_guard(c);
                LirReg   i      = subidx(c, c->sp - 1, failed);
                LirReg   p      = byte_cell(c, c->sp - 2, i, failed, true);
                LirReg   r      = ldx(c, LIR_LD_U8, LIR_I64, p, 0);

                vs_seal(c, failed);
                vs_pop(c, 2);
                vs_push(c, VS_INT, r, 0);

                return true;
        }

        i32 class = hinted_class(c, node);

        if (class >= 0 && (holder < 0 || holder == CLASS_ARRAY)) {
                typed_subscript(c, class == CLASS_FLOAT);
                return true;
        }

        vs_settle(c, c->sp - 2);

        LirLabel slow = newlabel(c);
        LirLabel done = newlabel(c);
        bool     held = (held_array(c, c->sp - 2) != NULL) || (held_blob(c, c->sp - 2) != NULL);

        if (!held && !intish(idx.kind)) {
                LirLabel other = newlabel(c);
                Spot     s     = spot(c, c->sp - 2);

                unless(c, ldtag(c, s), VALUE_DICT, other);
                vs_spill(c, c->sp - 1);
                dict_lookup(c, s.base, s.at, c->sp - 1, c->sp - 2, done);

                bind(c, other);
        }

        LirReg i = subidx(c, c->sp - 1, slow);

        if (held_array(c, c->sp - 2) != NULL) {
                copy(c, c->ops, vat(c->sp - 2), cell(c, c->sp - 2, i, slow, false), 0);
        } else if (held_blob(c, c->sp - 2) != NULL) {
                LirReg p = byte_cell(c, c->sp - 2, i, slow, false);

                put_scalar(c, c->sp - 2, VALUE_INTEGER, lir_r(ldx(c, LIR_LD_U8, LIR_I64, p, 0)));
        } else {
                LirLabel bytes = newlabel(c);
                Spot     s     = spot(c, c->sp - 2);
                LirReg   tag   = ldtag(c, s);

                unless(c, tag, VALUE_ARRAY, bytes);
                copy(c, c->ops, vat(c->sp - 2), array_at(c, s, i, slow), 0);
                jump(c, done);

                bind(c, bytes);
                unless(c, tag, VALUE_BLOB, slow);

                LirReg blob = ldp(c, s.base, s.at + VOFF(blob));
                LirReg p    = blob_byte_at(c, blob, i, slow);

                put_scalar(c, c->sp - 2, VALUE_INTEGER, lir_r(ldx(c, LIR_LD_U8, LIR_I64, p, 0)));
        }

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

        if (container_class(c, c->sp - 2) == CLASS_BLOB && c->speculate && bytelike(value.kind)) {
                guard_note(c, "assumed the Blob index is an in-bounds Int and the stored value is a byte");
                LirLabel failed = vs_guard(c);
                LirReg   i      = subidx(c, c->sp - 1, failed);
                LirReg   p      = byte_cell(c, c->sp - 2, i, failed, true);
                LirReg   v      = byte_value(c, value, c->sp - 3, failed);

                stb(c, p, 0, lir_r(v));
                vs_seal(c, failed);
                vs_pop(c, 2);

                return true;
        }

        vs_settle(c, c->sp - 3);

        LirLabel slow  = newlabel(c);
        LirLabel done  = newlabel(c);
        LirReg   i     = subidx(c, c->sp - 1, slow);

        if (held_blob(c, c->sp - 2) != NULL && bytelike(value.kind)) {
                LirReg q = byte_cell(c, c->sp - 2, i, slow, false);

                stb(c, q, 0, lir_r(byte_value(c, value, c->sp - 3, slow)));
                jump(c, done);
                bind(c, slow);

                for (i32 k = 3; k > 0; --k) {
                        vs_spill(c, c->sp - k);
                }

                tycall(c, jit_rt_assign_subscript, LT_VOID, preg(slot_of(c, c->sp)), imm32(1));
                bind(c, done);
                vs_pop(c, 2);

                return true;
        }

        bool     held  = held_array(c, c->sp - 2) != NULL;
        LirLabel bytes = held ? LIR_NONE : newlabel(c);
        Spot     s     = spot(c, c->sp - 2);
        LirReg   tag   = held ? LIR_NONE : ldtag(c, s);

        if (!held) {
                unless(c, tag, VALUE_ARRAY, bytes);
        }

        LirReg p = held ? cell(c, c->sp - 2, i, slow, false) : array_at(c, s, i, slow);

        if (value.kind == VS_MEM) {
                copy(c, p, 0, c->ops, vat(c->sp - 3));
        } else {
                box(c, &value, (Spot) { p, 0 });
        }

        jump(c, done);

        if (!held && bytelike(value.kind)) {
                bind(c, bytes);
                unless(c, tag, VALUE_BLOB, slow);

                LirReg blob = ldp(c, s.base, s.at + VOFF(blob));
                LirReg q    = blob_byte_at(c, blob, i, slow);
                LirReg v    = byte_value(c, value, c->sp - 3, slow);

                stb(c, q, 0, lir_r(v));
                jump(c, done);
        } else if (!held) {
                bind(c, bytes);
                jump(c, slow);
        }

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
        case INSTR_SELF_MEMBER_ACCESS:
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
        c->hints     = (expr != NULL && !from_eval(f)) ? &expr->fn->type_hints : NULL;
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
        c->proven      = new(c, LirReg, c->bound);
        c->proven_gen  = new(c, u32, c->bound);
        c->gen         = 1;

        if (expr == NULL || expr->fn->scope == NULL) {
                return true;
        }

        c->hints = &expr->fn->type_hints;

        i32 n = min(c->bound, vN(expr->fn->scope->owned));

        for (i32 slot = 0; slot < n; ++slot) {
                Symbol *sym = v__(expr->fn->scope->owned, slot);

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

        guard_note(
                c,
                real ? "assumed divisor %s is not 0.0" : "assumed divisor %s is neither 0 nor -1",
                operand_label(c, c->sp - 1)
        );

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

        if (n.ints && pair != INTS) {
                return false;
        }

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

        bool real   = (pair == REALS);
        bool divide = (op == INSTR_DIV) || (op == INSTR_MOD);

        if (divide && !checked_divisor(c, real)) {
                return false;
        }

        LirOpnd x;
        LirOpnd y;
        LirReg  d;
        u8      kind;

        operands(c, real, divide, &x, &y);

        if (shifting(n.iop)) {
                y = shift_count(c, y);
        }

        if (n.how == COMPARE) {
                LirCC cc = real ? n.fcc : n.icc;
                d    = vop(c, real ? LIR_FSETCC : LIR_SETCC, LIR_I64, lir_cc(cc), x, y);
                kind = VS_BOOL;
        } else {
                d    = vop(c, real ? n.fop : n.iop, numcls(real), x, y);
                kind = numkind(real);
        }

        BcSlot const *l    = &c->vs[c->sp - 2];
        BcSlot const *r    = &c->vs[c->sp - 1];
        bool          add  = (op == INSTR_ADD);
        bool          step = !real && (add || op == INSTR_SUB);
        i32           src  = 0;
        i64           off  = 0;

        if (step && l->src != 0 && r->kind == VS_CINT) {
                src = l->src;
                off = (i64)l->off + (add ? (i64)r->bits : -(i64)r->bits);
        } else if (step && add && r->src != 0 && l->kind == VS_CINT) {
                src = r->src;
                off = (i64)r->off + (i64)l->bits;
        }

        vs_pop(c, 2);
        vs_push(c, kind, d, 0);

        if (src != 0 && off >= -(1 << 20) && off <= (1 << 20)) {
                c->vs[c->sp - 1].src = src;
                c->vs[c->sp - 1].off = (i32)off;
        }

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
                     && !int_mutation(next->op)
                )
        ) {
                return false;
        }

        i32  slot  = load_i32(ip + 1);
        i32  class = lclass(c, slot);
        u8   rhs   = c->vs[c->sp - 1].kind;
        bool ints  = (class == CLASS_INT) && intish(rhs);
        bool reals = (class == CLASS_FLOAT) && realish(rhs) && !int_mutation(next->op);

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
                guard_note(c, "assumed `%s` holds %s before updating it in place", slot_label(c, slot), NUM_LABEL(real));
                assume(c, s, numtag(real));
        }

        c->offset    = next->next;
        c->skip_next = true;

        vs_release(c, slot);

        LirOp   op  = mutop(next->op, real);
        LirReg  cur = (known != NULL) ? numreg(c, known) : unbox(c, s, real);
        LirOpnd y   = real ? lir_r(vreg(c, c->sp - 1)) : iopnd(c, c->sp - 1);

        if (shifting(op)) {
                y = shift_count(c, y);
        }

        LirReg  r   = vop(c, op, numcls(real), lir_r(cur), y);

        put(c, s, r, real);

        c->vs[c->sp - 1] = (BcSlot) { .kind = numkind(real), .r = r };
        vs_remember(c, slot, &c->vs[c->sp - 1]);

        return true;
}

static bool
vs_mutate_cell(BcLir *c, BcLirNode const *node)
{
        if (!c->speculate || node->next >= c->size) {
                return false;
        }

        BcLirNode const *next  = next_of(c, node);
        BcSlot           value = c->vs[c->sp - 3];
        bool             array = (held_array(c, c->sp - 2) != NULL)
                              || (container_class(c, c->sp - 2) == CLASS_ARRAY);

        if (
                (next->label != LIR_NONE)
             || !array
             || !indexable(c->vs[c->sp - 2], c->vs[c->sp - 1])
             || (
                        (next->op != INSTR_MUT_ADD)
                     && (next->op != INSTR_MUT_SUB)
                     && (next->op != INSTR_MUT_MUL)
                     && !int_mutation(next->op)
                )
        ) {
                return false;
        }

        bool real = realish(value.kind) && !int_mutation(next->op);

        if (!real && !intish(value.kind)) {
                return false;
        }

        c->offset    = next->next;
        c->skip_next = true;

        guard_note(c, "assumed the Array element being updated holds %s and the index is in bounds", NUM_LABEL(real));

        LirLabel failed = vs_guard(c);
        LirReg   i      = subidx(c, c->sp - 1, failed);
        Spot     e      = { cell(c, c->sp - 2, i, failed, true), 0 };

        typecheck(c, e, numtag(real), failed);

        LirOp   op  = mutop(next->op, real);
        LirReg  cur = unbox(c, e, real);
        LirOpnd y   = real ? lir_r(vreg(c, c->sp - 3)) : iopnd(c, c->sp - 3);

        if (shifting(op)) {
                y = shift_count(c, y);
        }

        LirReg r = vop(c, op, numcls(real), lir_r(cur), y);

        put(c, e, r, real);
        vs_seal(c, failed);
        vs_pop(c, 3);
        vs_push(c, numkind(real), r, 0);

        return true;
}

typedef struct {
        char const *name;
        LirOp       ld;
        LirOp       st;
        u8          shift;
        bool        real;
} Packed;

static Packed const Packing[] = {
        { "f64", LIR_LD_F64, LIR_ST_F64, 3, true  },
        { "f32", LIR_LD_F32, LIR_ST_F32, 2, true  },
        { "i64", LIR_LD_I64, LIR_ST64,   3, false },
        { "i32", LIR_LD_I32, LIR_ST32,   2, false },
        { "u32", LIR_LD_U32, LIR_ST32,   2, false },
        { "i16", LIR_LD_I16, LIR_ST16,   1, false },
        { "u16", LIR_LD_U16, LIR_ST16,   1, false },
        { "i8",  LIR_LD_I8,  LIR_ST8,    0, false },
        { "u8",  LIR_LD_U8,  LIR_ST8,    0, false }
};

enum { VIEW_LOAD, VIEW_STORE };

static Packed const *
packing(i32 member)
{
        for (i32 i = 0; i < countof(Packing); ++i) {
                if (M_ID(Packing[i].name) == member) {
                        return &Packing[i];
                }
        }

        return NULL;
}

static bool
index_node(u8 op)
{
        return (op == INSTR_LOAD_LOCAL) || (op == INSTR_INT8) || (op == INSTR_INTEGER);
}

static i32
view_use(BcLirNode const *use, char const *at, Packed const *pk, u8 value)
{
        bool fits = pk->real ? (intish(value) || realish(value)) : intish(value);

        switch (use->op) {
        case INSTR_SUBSCRIPT:
                return VIEW_LOAD;

        case INSTR_ASSIGN_SUBSCRIPT:
                return ((u8)at[1] == 1 && fits) ? VIEW_STORE : -1;

        default:
                return -1;
        }
}

static bool
vs_load_local(BcLir *c, BcLirNode const *node, i32 slot);

static void
push_view_index(BcLir *c, BcLirNode const *ix)
{
        char const *ip = c->code + (ix - c->nodes);

        switch (ix->op) {
        case INSTR_INT8:
                vs_push(c, VS_CINT, LIR_NONE, (u64)(i64)(i8)ip[1]);
                break;

        case INSTR_INTEGER:
                vs_push(c, VS_CINT, LIR_NONE, peek(u64, ip + 1));
                break;

        default:
                if (!loop_lower(c, ix, ip)) {
                        vs_load_local(c, ix, load_i32(ip + 1));
                }
                break;
        }
}

static LirReg
packed_cell(BcLir *c, Packed const *pk, i32 i, LirReg idx, LirLabel failed)
{
        LirReg const *held = held_blob(c, i);
        LirReg        count;
        LirReg        items;

        if (held != NULL) {
                count = held[1];
                items = held[2];
        } else {
                Spot s = spot(c, i);

                typecheck(c, s, VALUE_BLOB, failed);

                LirReg blob = ldp(c, s.base, s.at + VOFF(blob));

                count = ldq(c, blob, offsetof(Blob, count));
                items = ldp(c, blob, offsetof(Blob, items));
        }

        if (held == NULL || !in_range(c, i + 1, i, pk->shift)) {
                LirReg n = vop(c, LIR_SHR, LIR_I64, lir_r(count), lir_i(pk->shift));
                jcc(c, LIR_UGE, lir_r(idx), lir_r(n), failed);
        }

        return vop(c, LIR_LEA, LIR_PTR, lir_m(items, idx, 1 << pk->shift, 0));
}

static LirReg
packed_load(BcLir *c, Packed const *pk, LirReg p)
{
        if (pk->ld == LIR_LD_F32) {
                return vop(c, LIR_FEXT, LIR_F64, lir_r(ldx(c, LIR_LD_F32, LIR_F32, p, 0)));
        }

        return ldx(c, pk->ld, pk->real ? LIR_F64 : LIR_I64, p, 0);
}

static void
packed_store(BcLir *c, Packed const *pk, LirReg p, LirOpnd v)
{
        if (pk->st == LIR_ST_F32) {
                v = lir_r(vop(c, LIR_FTRUNC, LIR_F32, v));
        }

        store(c, pk->st, p, 0, v);
}

static LirOpnd
packed_value(BcLir *c, Packed const *pk, i32 i)
{
        if (!pk->real) {
                return iopnd(c, i);
        }

        if (realish(c->vs[i].kind)) {
                return lir_r(vreg(c, i));
        }

        return lir_r(vop(c, LIR_I2F, LIR_F64, lir_r(vreg(c, i))));
}

static void
view_seal(BcLir *c, LirLabel failed, i32 sp)
{
        LirLabel ok   = newlabel(c);
        i32      keep = c->sp;

        jump(c, ok);
        bind(c, failed);
        c->sp = sp;
        vs_deopt(c);
        c->sp = keep;
        bind(c, ok);
}

static bool
vs_view(BcLir *c, BcLirNode const *node, char const *ip)
{
        Packed const *pk = packing(load_i32(ip + 1));

        if (
                !c->speculate
             || (pk == NULL)
             || (node->next >= c->size)
             || (container_class(c, c->sp - 1) != CLASS_BLOB)
        ) {
                return false;
        }

        BcLirNode const *ix = next_of(c, node);

        if (ix->label != LIR_NONE || !index_node(ix->op) || ix->next >= c->size) {
                return false;
        }

        if (ix->op == INSTR_LOAD_LOCAL && !local_ok(c, load_i32(c->code + (ix - c->nodes) + 1))) {
                return false;
        }

        BcLirNode const *use  = next_of(c, ix);
        u8               val  = (c->sp >= 2) ? c->vs[c->sp - 2].kind : VS_MEM;
        i32              mode = (use->label == LIR_NONE)
                              ? view_use(use, c->code + (use - c->nodes), pk, val)
                              : -1;

        if (mode < 0) {
                return false;
        }

        i32 sp = c->sp;

        c->offset     = use->next;
        c->skip_extra = 1;
        c->skip_next  = true;

        push_view_index(c, ix);

        guard_note(c, "assumed the index into this packed Blob view is an in-bounds Int");

        LirLabel failed = vs_guard(c);
        LirReg   i      = subidx(c, c->sp - 1, failed);
        LirReg   p      = packed_cell(c, pk, c->sp - 2, i, failed);
        if (mode == VIEW_STORE) {
                packed_store(c, pk, p, packed_value(c, pk, c->sp - 3));
                view_seal(c, failed, sp);
                vs_pop(c, 2);
                return true;
        }

        LirReg r = packed_load(c, pk, p);

        view_seal(c, failed, sp);
        vs_pop(c, 2);
        vs_push(c, pk->real ? VS_REAL : VS_INT, r, 0);

        return true;
}

static LirReg
vs_object(BcLir *c, i32 i, i32 slot, Class const *class)
{
        Spot s      = (i < 0) ? lspot(c, slot) : spot(c, i);
        bool cached = local_ok(c, slot) && (c->proven_gen != NULL);

        if (cached && c->proven_gen[slot] == c->gen) {
                return c->proven[slot];
        }

        guard_note(
                c,
                "assumed %s is a %s (its static type)",
                (i < 0) ? "`self`" : operand_label(c, i),
                class_name(c->ctx, class->i)
        );

        LirLabel failed = vs_guard(c);

        typecheck(c, s, VALUE_OBJECT, failed);
        unless(c, ldw(c, s.base, s.at + VOFF(class)), class->i, failed);
        vs_seal(c, failed);

        LirReg object = ldp(c, s.base, s.at + VOFF(object));

        if (cached) {
                c->proven[slot]     = object;
                c->proven_gen[slot] = c->gen;
        }

        return object;
}

static i32
receiver_slot(BcLir const *c, bool self, i32 i)
{
        if (self) {
                return c->self_index;
        }

        return (c->vs[i].kind == VS_LOCAL) ? (i32)c->vs[i].bits : -1;
}

static bool
vs_member(BcLir *c, BcLirNode const *node, char const *ip)
{
        bool   self   = (node->op == INSTR_SELF_MEMBER_ACCESS);
        i32    member = load_i32(ip + 1);
        i32    i      = self ? -1 : c->sp - 1;
        Class *class  = self ? self_class(c) : hint_class(c, c->at);

        if (!c->speculate || class == NULL || class->i < CLASS_PRIMITIVE) {
                return false;
        }

        if (self ? !local_ok(c, c->self_index) : !boxed(c->vs[i].kind)) {
                return false;
        }

        u16 field = offset_of(class, member, false, OFF_FIELD);

        if (field == OFF_NOT_FOUND) {
                return false;
        }

        LirReg object = vs_object(c, i, receiver_slot(c, self, i), class);
        Spot   cell   = { object, offsetof(TyObject, slots) + vat(field & OFF_MASK) };
        i32    want   = numeric_next(c, node) ? hinted_class(c, node) : -1;
        BcSlot out    = { .kind = VS_CELL, .r = object, .bits = (u64)cell.at };

        if (want == CLASS_INT || want == CLASS_FLOAT) {
                bool real = (want == CLASS_FLOAT);
                guard_note(c, "assumed this field holds %s (its static type)", NUM_LABEL(real));
                assume(c, cell, numtag(real));
                out = (BcSlot) { .kind = numkind(real), .r = unbox(c, cell, real) };
        }

        count_fast(c, SITE_MEMBER);

        if (!self) {
                vs_pop(c, 1);
        }

        c->vs[c->sp++] = out;

        return true;
}

static bool
vs_string_byte(BcLir *c, BcLirNode const *node)
{
        if (
                !c->speculate
             || (node->argc != 1)
             || (node->nkw != 0)
             || (node->member != M_ID("byte"))
             || (c->sp < 2)
             || (container_class(c, c->sp - 1) != CLASS_STRING)
             || (!intish(c->vs[c->sp - 2].kind) && !boxed(c->vs[c->sp - 2].kind))
        ) {
                return false;
        }

        guard_note(c, "assumed the receiver of `byte` is a String and the index is in range");

        LirLabel      failed = vs_guard(c);
        LirReg        i      = subidx(c, c->sp - 2, failed);
        LirReg const *held   = held_string(c, c->sp - 1);
        LirReg        n;
        LirReg        str;

        if (held != NULL) {
                n   = held[1];
                str = held[2];
        } else {
                Spot s = spot(c, c->sp - 1);

                typecheck(c, s, VALUE_STRING, failed);

                n   = ldx(c, LIR_LD_U32, LIR_I64, s.base, s.at + VOFF(bytes));
                str = ldp(c, s.base, s.at + VOFF(str));
        }

        if (held == NULL || !in_range(c, c->sp - 2, c->sp - 1, 0)) {
                jcc(c, LIR_UGE, lir_r(i), lir_r(n), failed);
        }

        LirReg r = ldx(c, LIR_LD_U8, LIR_I64, lea(c, str, i, 0), 0);

        vs_seal(c, failed);
        vs_pop(c, 2);
        vs_push(c, VS_INT, r, 0);

        return true;
}

typedef struct {
        bool    real;
        bool    flag;
        LirOpnd v;
} Lane;

static i32
lane_kind(BcLir *c, Value const *callee, i32 pos, i32 index)
{
        u8     kind  = c->vs[pos].kind;
        Class *class = param_class(c, callee, index);
        i32    want  = (class == NULL) ? -1 : class->i;

        if (want != -1 && want != CLASS_INT && want != CLASS_FLOAT) {
                return -1;
        }

        if (intish(kind)) {
                return (want == CLASS_FLOAT) ? -1 : CLASS_INT;
        }

        if (realish(kind)) {
                return (want == CLASS_INT) ? -1 : CLASS_FLOAT;
        }

        return boxed(kind) ? want : -1;
}

static Lane
lane_arg(BcLir *c, i32 pos, i32 class, LirLabel failed)
{
        bool real = (class == CLASS_FLOAT);

        if (intish(c->vs[pos].kind)) {
                return (Lane) { .real = false, .v = iopnd(c, pos) };
        }

        if (realish(c->vs[pos].kind)) {
                return (Lane) { .real = true, .v = lir_r(vreg(c, pos)) };
        }

        Spot s = spot(c, pos);

        typecheck(c, s, numtag(real), failed);

        return (Lane) { .real = real, .v = lir_r(unbox(c, s, real)) };
}

static LirOpnd
widen(BcLir *c, Lane l)
{
        if (l.real) {
                return l.v;
        }

        if (l.v.kind == LO_IMM) {
                return lir_r(fval(c, (double)l.v.imm));
        }

        return lir_r(vop(c, LIR_I2F, LIR_F64, l.v));
}

static LirOpnd
lane_divisor(BcLir *c, LirOpnd d, LirLabel failed)
{
        if (d.kind == LO_IMM) {
                return lir_r(ival(c, d.imm));
        }

        jz(c, d.reg, failed);
        jcc(c, LIR_EQ, d, lir_i(-1), failed);

        return d;
}

static bool
lane_arith(BcLir *c, u8 op, Lane *a, Lane b, bool emit, LirLabel failed)
{
        bool real   = a->real || b.real;
        bool divide = (op == TY_INLINE_DIV) || (op == TY_INLINE_MOD);

        if (
                (op == TY_INLINE_MOD && real)
             || (divide && !real && b.v.kind == LO_IMM && (b.v.imm == 0 || b.v.imm == -1))
             || a->flag
             || b.flag
        ) {
                return false;
        }

        if (!emit) {
                a->real = real;
                return true;
        }

        if (!real && divide) {
                LirOpnd x = (a->v.kind == LO_IMM) ? lir_r(ival(c, a->v.imm)) : a->v;
                LirOpnd y = lane_divisor(c, b.v, failed);
                a->v = lir_r(vop(c, Arith[op].iop, LIR_I64, x, y));
                return true;
        }

        if (!real) {
                a->v = lir_r(vop(c, Arith[op].iop, LIR_I64, a->v, b.v));
                return true;
        }

        LirOpnd x = widen(c, *a);
        LirOpnd y = widen(c, b);

        if (op == TY_INLINE_DIV) {
                nonzero_bits(c, y.reg, failed);
        }

        a->real = true;
        a->v    = lir_r(vop(c, Arith[op].fop, LIR_F64, x, y));

        return true;
}

static bool
lane_compare(BcLir *c, u8 op, Lane *a, Lane b, bool emit)
{
        bool real = a->real || b.real;

        if (a->flag || b.flag) {
                return false;
        }

        if (emit && real) {
                a->v = lir_r(vop(c, LIR_FSETCC, LIR_I64, lir_cc(Arith[op].fcc), widen(c, *a), widen(c, b)));
        } else if (emit) {
                a->v = lir_r(vop(c, LIR_SETCC, LIR_I64, lir_cc(Arith[op].icc), a->v, b.v));
        }

        a->real = false;
        a->flag = true;

        return true;
}

static bool
lane_logic(BcLir *c, u8 op, Lane *a, Lane b, bool emit)
{
        if (!a->flag || !b.flag) {
                return false;
        }

        if (emit) {
                a->v = lir_r(vop(c, (op == TY_INLINE_AND) ? LIR_AND : LIR_OR, LIR_I64, a->v, b.v));
        }

        return true;
}

static bool
lane_plan(BcLir *c, Plan const *p, i32 first, i32 const *kinds, Lane *out, bool emit, LirLabel failed)
{
        TyInlinePlan const *plan = &p->plan;
        Lane                st[TY_INLINE_MAX_STACK + 2];

        for (i32 i = 0; i < plan->count; ++i) {
                TyInlineInsn const *insn = &plan->insns[i];
                i32                 d    = plan->depths[i];
                u64                 bits = 0;

                if (d > TY_INLINE_MAX_STACK) {
                        return false;
                }

                switch (insn->op) {
                case TY_INLINE_LOCAL:
                        if (!is_arg(p, insn->local) || kinds[insn->local] < 0) {
                                return false;
                        }
                        st[d] = emit
                              ? lane_arg(c, first + insn->local, kinds[insn->local], failed)
                              : (Lane) { .real = (kinds[insn->local] == CLASS_FLOAT) };
                        break;

                case TY_INLINE_INTEGER:
                        st[d] = (Lane) { .real = false, .v = lir_i(insn->integer) };
                        break;

                case TY_INLINE_REAL:
                        memcpy(&bits, &insn->real, sizeof bits);
                        st[d] = (Lane) { .real = true, .v = emit ? lir_r(fval(c, insn->real)) : lir_i((i64)bits) };
                        break;

                case TY_INLINE_BOOLEAN:
                        st[d] = (Lane) { .flag = true, .v = lir_i(insn->integer != 0) };
                        break;

                case TY_INLINE_POP:
                case TY_INLINE_GIVEN:
                        break;

                case TY_INLINE_ADD:
                case TY_INLINE_SUB:
                case TY_INLINE_MUL:
                case TY_INLINE_DIV:
                case TY_INLINE_MOD:
                        if (d < 2 || !lane_arith(c, insn->op, &st[d - 2], st[d - 1], emit, failed)) {
                                return false;
                        }
                        break;

                case TY_INLINE_EQ:
                case TY_INLINE_NE:
                case TY_INLINE_LT:
                case TY_INLINE_GT:
                case TY_INLINE_LE:
                case TY_INLINE_GE:
                        if (d < 2 || !lane_compare(c, insn->op, &st[d - 2], st[d - 1], emit)) {
                                return false;
                        }
                        break;

                case TY_INLINE_AND:
                case TY_INLINE_OR:
                        if (d < 2 || !lane_logic(c, insn->op, &st[d - 2], st[d - 1], emit)) {
                                return false;
                        }
                        break;

                case TY_INLINE_NOT:
                        if (d < 1 || !st[d - 1].flag) {
                                return false;
                        }
                        if (st[d - 1].v.kind == LO_IMM) {
                                st[d - 1].v = lir_i(st[d - 1].v.imm == 0);
                        } else if (emit) {
                                st[d - 1].v = lir_r(vop(c, LIR_XOR, LIR_I64, st[d - 1].v, lir_i(1)));
                        }
                        break;

                default:
                        return false;
                }
        }

        *out = st[0];

        return true;
}

static bool
vs_call_global(BcLir *c, BcLirNode const *node)
{
        i32 argc  = node->argc;
        i32 first = c->sp - argc;

        if (
                !c->speculate
             || (argc <= 0)
             || (argc > TY_INLINE_MAX_STACK)
             || (node->nkw != 0)
             || (node->resume_id != 0)
        ) {
                return false;
        }

        Value const *callee = vm_global(c->ctx, node->global);
        Plan         p      = { .base = first };
        i32          kinds[TY_INLINE_MAX_STACK];
        Lane         r;

        if (!inlinable(c, callee, argc) || !analyze(&p, callee, TY_INLINE_GLOBAL, argc)) {
                return false;
        }

        for (i32 i = 0; i < argc; ++i) {
                kinds[i] = lane_kind(c, callee, first + i, i);
        }

        if (!lane_plan(c, &p, first, kinds, &r, false, LIR_NONE)) {
                return false;
        }

        guard_note(
                c,
                "inlined `%s`: assumed the global still refers to it and its arguments are numeric",
                name_of(callee)
        );

        LirLabel failed = vs_guard(c);

        guard_self(c, global_addr(c, node->global), callee, failed);
        lane_plan(c, &p, first, kinds, &r, true, failed);
        vs_seal(c, failed);
        vs_pop(c, argc);

        u8 kind = r.flag ? VS_BOOL : numkind(r.real);

        if (r.v.kind == LO_IMM) {
                vs_push(c, r.flag ? VS_CBOOL : VS_CINT, LIR_NONE, (u64)r.v.imm);
        } else {
                vs_push(c, kind, r.v.reg, 0);
        }

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

        guard_note(c, "assumed `%s` holds %s (its static type)", slot_label(c, slot), NUM_LABEL(real));
        assume(c, s, numtag(real));
        vs_push(c, numkind(real), unbox(c, s, real), 0);
        c->vs[c->sp - 1].src = slot + 1;
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
vs_string(BcLir *c, i32 id)
{
        string_literal(c, c->sp, id);
        vs_push(c, VS_MEM, LIR_NONE, 0);
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
vs_saved(BcLir *c, BcLirNode const *node)
{
        bool save = (node->op == INSTR_SAVE_STACK_POS);
        i32  s    = save ? c->at : node->saved;

        if (!virtual_save(c, s)) {
                return false;
        }

        if (save && keeps_below(c, s)) {
                vs_flush_all(c);
        }

        if (node->fall_sp < c->sp) {
                vs_pop(c, c->sp - node->fall_sp);
        }

        c->sp = node->fall_sp;

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
                if (!lazy_pinned(c, c->sp - 1)) {
                        put(c, sspot(c, c->sp - 1), top.r, false);
                }
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
vs_unary(BcLir *c, char const *ip)
{
        BcSlot top = c->vs[c->sp - 1];

        if (load_i32(ip + 1) != OP_COMPL || !intish(top.kind)) {
                return false;
        }

        if (top.kind == VS_CINT) {
                c->vs[c->sp - 1].bits = ~top.bits;
                return true;
        }

        c->vs[c->sp - 1] = (BcSlot) {
                .kind = VS_INT,
                .r    = vop(c, LIR_NOT, LIR_I64, lir_r(top.r))
        };

        return true;
}

static bool
join_eligible(BcLir const *c, i32 to)
{
        BcLirNode const *t = &c->nodes[to];

        if (t->label == LIR_NONE || t->sp <= 0 || t->osr_id != 0 || t->resume_id != 0) {
                return false;
        }

        for (i32 off = 0; off < c->size; ++off) {
                BcLirNode const *n = &c->nodes[off];

                if (!decoded(n) || n->sp < 0) {
                        continue;
                }

                if (n->branch && n->target == to) {
                        bool forward = (n->op == INSTR_JUMP) || (n->op == INSTR_JUMP_WTF);
                        if (!forward || off >= to || n->sp != t->sp) {
                                return false;
                        }
                }

                each_arm(c, n, arm_to) {
                        if (arm_to == to) {
                                return false;
                        }
                }
        }

        return true;
}

static i32
default_class(BcLir const *c, i32 to)
{
        i32 wtf = 0;
        i32 lit = -1;

        for (i32 off = 0; off < to; ++off) {
                BcLirNode const *n = &c->nodes[off];

                if (!decoded(n) || n->sp < 0 || !n->branch || n->target != to) {
                        continue;
                }

                BcLirNode const *d = next_of(c, n);

                if (n->op != INSTR_JUMP_WTF || d->next != to || d->label != LIR_NONE) {
                        return -1;
                }

                switch (d->op) {
                case INSTR_INT8:
                case INSTR_INTEGER: lit = CLASS_INT;   break;
                case INSTR_REAL:    lit = CLASS_FLOAT; break;
                default:            return -1;
                }

                wtf += 1;
        }

        return (wtf == 1) ? lit : -1;
}

static bool
join_plan(BcLir *c)
{
        if (c->vs == NULL || !c->speculate || c->dynamic || c->hints == NULL || getenv("TY_JIT_NO_JOIN") != NULL) {
                return true;
        }

        for (i32 to = 1; to < c->size; ++to) {
                BcLirNode const *t = &c->nodes[to];

                if (!decoded(t) || t->label == LIR_NONE || t->sp <= 0) {
                        continue;
                }

                i32  fallback = default_class(c, to);
                i32  class    = exact_class(find_type_hint(c->hints, to));
                bool keep     = (fallback >= 0);

                if (class < 0) {
                        class = fallback;
                }

                if (class < 0 || !join_eligible(c, to)) {
                        continue;
                }

                if (c->joins == NULL) {
                        c->joins = new(c, BcJoin, c->size);
                }

                c->joins[to] = (BcJoin) {
                        .kind = numkind(class == CLASS_FLOAT),
                        .r    = LIR_NONE,
                        .keep = keep
                };
        }

        return true;
}

static BcJoin *
vs_join_at(BcLir *c, i32 to)
{
        return (c->joins != NULL && c->joins[to].kind != 0) ? &c->joins[to] : NULL;
}

static void
vs_carry_tagged(BcLir *c, BcJoin *join, i32 i, LirReg tag)
{
        bool   real = (join->kind == VS_REAL);
        BcSlot s    = c->vs[i];

        if (join->r == LIR_NONE) {
                join->r = lir_reg(c->L, numcls(real));
        }

        if (real ? realish(s.kind) : intish(s.kind)) {
                mov(c, join->r, vreg(c, i));
                return;
        }

        if (!boxed(s.kind)) {
                guard_note(
                        c,
                        "the branches merge expecting %s (from the static type), but this branch "
                        "always produces %s, so it deopts every time it runs",
                        NUM_LABEL(real),
                        kind_label(s.kind)
                );
                vs_deopt(c);
                return;
        }

        guard_note(c, "the branches merge expecting %s (from the static type), so %s is checked and unboxed here", NUM_LABEL(real), operand_label(c, i));

        LirLabel failed = vs_guard(c);
        Spot     at     = spot(c, i);

        if (tag == LIR_NONE) {
                typecheck(c, at, numtag(real), failed);
        } else {
                jcc(c, LIR_NE, lir_r(tag), lir_i(numtag(real)), failed);
        }

        unbox_to(c, join->r, at, real);
        vs_seal(c, failed);
}

static void
vs_carry(BcLir *c, BcJoin *join, i32 i)
{
        vs_carry_tagged(c, join, i, LIR_NONE);
}

static void
vs_joined(BcLir *c, BcJoin const *join, i32 i)
{
        if (join->r == LIR_NONE) {
                c->vs[i].kind = VS_MEM;
                return;
        }

        c->vs[i] = (BcSlot) { .kind = join->kind, .r = join->r };
}

static bool
vs_join_jump(BcLir *c, BcLirNode const *node)
{
        BcJoin *join = vs_join_at(c, node->target);

        if (join == NULL || node->deopt != LIR_NONE) {
                return false;
        }

        vs_carry(c, join, c->sp - 1);
        vs_flush_below(c, c->sp - 1);
        jump(c, dest(c, node));

        return true;
}

static bool
vs_join_wtf(BcLir *c, BcLirNode const *node)
{
        BcJoin *join = vs_join_at(c, node->target);
        BcSlot  top  = c->vs[c->sp - 1];

        if (
                (join == NULL)
             || (node->deopt != LIR_NONE)
             || !(boxed(top.kind) || intish(top.kind) || realish(top.kind))
        ) {
                return false;
        }

        LirLabel none = newlabel(c);
        LirReg   tag  = LIR_NONE;

        if (!join->keep) {
                vs_flush_below(c, c->sp - 1);
        }

        if (boxed(top.kind)) {
                tag = ldtag(c, spot(c, c->sp - 1));
                jcc(c, LIR_EQ, lir_r(tag), lir_i(VALUE_NIL), none);
        }

        vs_carry_tagged(c, join, c->sp - 1, tag);
        jump(c, dest(c, node));
        bind(c, none);
        vs_pop(c, 1);

        return true;
}

static bool
vs_captured(BcLir *c, char const *ip)
{
        if (getenv("TY_JIT_NO_CELLS") != NULL) {
                return false;
        }

        vs_push(c, VS_CELL, captured(c, load_i32(ip + 1)), 0);

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
        case INSTR_INT8:               return vs_const(c, VS_CINT, (u64)(i64)(i8)ip[1]);
        case INSTR_INTEGER:            return vs_const(c, VS_CINT, peek(u64, ip + 1));
        case INSTR_REAL:               return vs_const(c, VS_CREAL, peek(u64, ip + 1));
        case INSTR_TRUE:               return vs_const(c, VS_CBOOL, 1);
        case INSTR_FALSE:              return vs_const(c, VS_CBOOL, 0);
        case INSTR_NIL:                return vs_const(c, VS_CNIL, 0);
        case INSTR_STRING:             return vs_string(c, load_i32(ip + 1));
        case INSTR_LOAD_LOCAL:         return vs_load_local(c, node, load_i32(ip + 1));
        case INSTR_LOAD_CAPTURED:      return vs_captured(c, ip);
        case INSTR_ASSIGN_LOCAL:       return vs_assign_local(c, load_i32(ip + 1));
        case INSTR_TARGET_LOCAL:       return vs_mutate(c, node, ip);
        case INSTR_SUBSCRIPT:          return vs_subscript(c, node);
        case INSTR_COUNT:              return vs_count(c);
        case INSTR_ASSIGN_SUBSCRIPT:   return vs_assign_subscript(c, ip);
        case INSTR_TARGET_SUBSCRIPT:   return vs_mutate_cell(c, node);
        case INSTR_CALL_GLOBAL:        return vs_call_global(c, node);
        case INSTR_MEMBER_ACCESS:      return vs_view(c, node, ip) || vs_member(c, node, ip);
        case INSTR_SELF_MEMBER_ACCESS: return vs_member(c, node, ip);
        case INSTR_CALL_METHOD:        return vs_string_byte(c, node);
        case INSTR_POP:                return vs_drop(c);
        case INSTR_DUP:                return vs_dup(c);
        case INSTR_DUP2_SWAP:          return vs_dup2_swap(c);
        case INSTR_INC:                return vs_step(c, true);
        case INSTR_DEC:                return vs_step(c, false);
        case INSTR_NEG:                return vs_negate(c);
        case INSTR_UNARY_OP:           return vs_unary(c, ip);

        case INSTR_ADD:
        case INSTR_SUB:
        case INSTR_MUL:
        case INSTR_DIV:
        case INSTR_MOD:
        case INSTR_BIT_AND:
        case INSTR_BIT_OR:
        case INSTR_BIT_XOR:
        case INSTR_SHL:
        case INSTR_SHR:
        case INSTR_EQ:
        case INSTR_NEQ:
        case INSTR_LT:
        case INSTR_GT:
        case INSTR_LEQ:
        case INSTR_GEQ:
                return vs_binary(c, op);

        case INSTR_SAVE_STACK_POS:
        case INSTR_RESTORE_STACK_POS:
        case INSTR_POP_STACK_POS:
        case INSTR_POP_STACK_POS_POP:
        case INSTR_POP_STACK_POS_POP2:
        case INSTR_DROP_STACK_POS:
                return vs_saved(c, node);

        case INSTR_JUMP:             return vs_join_jump(c, node);
        case INSTR_JUMP_WTF:         return vs_join_wtf(c, node);

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
