#include "impl.h"

typedef struct {
        Ty             *ty;
        vec(u8)         out;
        vec(LirBinding) holes;
        u32             ninputs;
} Writer;

typedef struct {
        u8 const *data;
        usize     size;
        usize     pos;
        bool      ok;
} Reader;

inline static bool
ishole(LirOpnd a)
{
        return (a.kind >= LO_HOLE_IMM) && (a.kind <= LO_HOLE_CALLEE);
}

static void
put(Writer *w, void const *p, usize n)
{
        Ty *ty = w->ty;

        if (n != 0) {
                svPn(w->out, (u8 const *)p, n);
        }
}

static void
put_uint(Writer *w, u64 n)
{
        u8  buf[10];
        u32 i = 0;

        do {
                buf[i++] = (n & 0x7f) | ((n >= 128) ? 0x80 : 0);
                n >>= 7;
        } while (n != 0);

        put(w, buf, i);
}

static void
put_int(Writer *w, i64 n)
{
        put_uint(w, ((u64)n << 1) ^ (u64)-(n < 0));
}

static void
put_f64(Writer *w, double x)
{
        u64 bits;
        u8  buf[8];

        memcpy(&bits, &x, sizeof bits);

        for (u32 i = 0; i < 8; ++i) {
                buf[i] = bits >> (8 * i);
        }

        put(w, buf, sizeof buf);
}

static bool
same(LirOpnd a, LirOpnd b)
{
        if (a.kind != b.kind) {
                return false;
        }

        switch (a.kind) {
        case LO_CODE:   return a.code == b.code;
        case LO_HELPER: return a.helper == b.helper;
        case LO_IMM:    return a.imm == b.imm;
        default:        return false;
        }
}

static u32
capture(Writer *w, LirOpnd a)
{
        for (u32 i = w->ninputs; i < vN(w->holes); ++i) {
                if (same(a, v__(w->holes, i).operand)) {
                        return i;
                }
        }

        Ty *ty = w->ty;

        svP(w->holes, ((LirBinding) { .operand = a }));

        return vN(w->holes) - 1;
}

static void
put_operand(Writer *w, LirOpnd a)
{
        put_uint(w, a.kind);

        switch (a.kind) {
        case LO_MEM:
                put_uint(w, a.mem.base);
                put_uint(w, a.mem.index);
                put_uint(w, a.mem.scale);
                put_int(w, a.mem.disp);
                break;

        case LO_IMM:    put_int(w, a.imm);          break;
        case LO_FIMM:   put_f64(w, a.fimm);         break;
        case LO_REG:    put_uint(w, a.reg);         break;
        case LO_LABEL:  put_uint(w, a.label);       break;
        case LO_CC:     put_uint(w, a.cc);          break;
        case LO_CODE:
        case LO_HELPER: put_uint(w, capture(w, a)); break;
        default:        put_uint(w, a.index);       break;
        }
}

static void
put_pointer(Writer *w, LirOpnd a, bool callee)
{
        if (a.kind == LO_IMM) {
                a = lir_hole(callee ? LO_HOLE_CALLEE : LO_HOLE_PTR, capture(w, a));
        }

        put_operand(w, a);
}

static void
put_sig(Writer *w, LirSig const *sig)
{
        put_uint(w, sig->ret);
        put_uint(w, sig->nparams);
        put_uint(w, sig->variadic);
        put_uint(w, sig->nfixed);

        for (u32 i = 0; i < sig->nparams; ++i) {
                put_uint(w, sig->params[i]);
        }
}

static void
put_bindings(Writer *w, LirRawBinding const *bs, u32 n)
{
        put_uint(w, n);

        for (u32 i = 0; i < n; ++i) {
                put_uint(w, bs[i].phys);
                put_uint(w, bs[i].reg);
        }
}

static void
put_raw(Writer *w, LirRaw const *raw)
{
        put_uint(w, raw->narm64);

        for (u32 i = 0; i < raw->narm64; ++i) {
                put_uint(w, raw->arm64[i]);
        }

        put_uint(w, raw->nx64);
        put(w, raw->x64, raw->nx64);
        put_bindings(w, raw->in, raw->nin);
        put_bindings(w, raw->out, raw->nout);
        put_uint(w, raw->gpr_clobber);
        put_uint(w, raw->fpr_clobber);
}

static bool
pointer_arg(Lir const *L, LirInst const *in)
{
        switch (in->op) {
        case LIR_CALL:
        case LIR_TAILCALL: return true;
        case LIR_LI:
        case LIR_MOV:      return rcls(L, in->dst) == LIR_PTR;
        case LIR_RET:      return L->sig.ret == LT_PTR;
        default:           return false;
        }
}

static void
put_inst(Writer *w, Lir const *L, LirInst const *in, u32 version)
{
        put_uint(w, in->op);
        put_uint(w, in->dst);
        put_uint(w, in->nargs);
        put_uint(w, in->span.source);
        put_uint(w, in->span.start);
        put_uint(w, in->span.end);

        u32 j = 0;

        if (in->nargs != 0 && pointer_arg(L, in)) {
                put_pointer(w, in->args[j++], iscall(in));
        }

        while (j < in->nargs) {
                put_operand(w, in->args[j++]);
        }

        if (iscall(in)) {
                put_sig(w, &in->sig);
                put_uint(w, in->flags);
                put_uint(w, in->tag);
                for (u32 i = 0; i < in->ncall_args; ++i) {
                        if (in->sig.params[i] == LT_PTR) {
                                put_pointer(w, in->call_args[i], false);
                        } else {
                                put_operand(w, in->call_args[i]);
                        }
                }
        } else if (in->op == LIR_POLL && version >= 2) {
                put_uint(w, in->flags);
                put_uint(w, in->tag);
        } else if (in->op == LIR_ENTRY && version >= 2) {
                put_uint(w, in->tag);
        } else if (LirOps[in->op].form == LF_LD && version >= 3) {
                put_uint(w, in->flags);
        } else if (in->op == LIR_SWITCH) {
                put_uint(w, in->ntargets);
                for (u32 i = 0; i < in->ntargets; ++i) {
                        put_uint(w, in->targets[i]);
                }
        } else if (in->op == LIR_RAW) {
                put_raw(w, &in->raw);
        }
}

static u32
version(Lir const *L)
{
        u32 v = 1;

        for (u32 i = 0; i < vN(L->labels); ++i) {
                if (v__(L->labels, i).cold || v__(L->labels, i).bounded) {
                        return 4;
                }
        }

        for (u32 pc = 0; pc < vN(L->insts); ++pc) {
                LirInst const *in = v_(L->insts, pc);
                if (LirOps[in->op].form == LF_LD && in->flags != 0) {
                        return 3;
                }
                if (
                        (in->op == LIR_POLL && (in->flags != 0 || in->tag != 0))
                     || (in->op == LIR_ENTRY && in->tag != 0)
                ) {
                        v = 2;
                }
        }

        return v;
}

static bool
count_inputs(Lir const *L, u32 *n)
{
        *n = 0;

        for (u32 pc = 0; pc < vN(L->insts); ++pc) {
                LirInst const *in = v_(L->insts, pc);
                for (u32 j = 0; j < nopnd(in); ++j) {
                        LirOpnd const *a = opnd(in, j);
                        if (!ishole(*a)) {
                                continue;
                        }
                        if (a->index == UINT32_MAX) {
                                return false;
                        }
                        if (a->index >= *n) {
                                *n = a->index + 1;
                        }
                }
        }

        return true;
}

bool
lir_serialize(Ty *ty, Lir *L, LirBytes *bytes, LirError *err)
{
        *bytes = (LirBytes) {0};
        ty     = lir_scratch(ty);

        if (!lir_validate(ty, L, err)) {
                return false;
        }

        Writer w = { .ty = ty };

        if (!count_inputs(L, &w.ninputs)) {
                return lir_fail(err, LE_ENCODING, LIR_NOWHERE, "hole index is too large");
        }

        while (vN(w.holes) < w.ninputs) {
                svP(w.holes, ((LirBinding) {0}));
        }

        Value     *roots = stA(Value, vN(L->roots));
        LirBinding root  = { .operand = { .kind = LO_CONST } };

        for (u32 i = 0; i < vN(L->roots); ++i) {
                roots[i]   = v__(L->roots, i);
                root.value = &roots[i];
                svP(w.holes, root);
        }

        u32 v = version(L);

        put(&w, "TYLR", 4);
        put_uint(&w, v);
        put_uint(&w, strlen(L->name));
        put(&w, L->name, strlen(L->name));
        put_sig(&w, &L->sig);
        put_uint(&w, L->mode);
        put_uint(&w, L->nvslots);
        put_uint(&w, L->pc_param);

        put_uint(&w, vN(L->regs));
        vfor(L->regs, {
                put_uint(&w, it->cls);
                put_uint(&w, it->param);
                put_uint(&w, it->pin);
        });

        put_uint(&w, vN(L->labels));
        vfor(L->labels, {
                put_uint(&w, it->pos);
                put_uint(&w, it->entry | (it->cold << 1) | (it->bounded << 2));
        });

        put_uint(&w, vN(L->roots));
        for (u32 i = 0; i < vN(L->roots); ++i) {
                put_uint(&w, w.ninputs + i);
        }

        put_uint(&w, vN(L->insts));
        vfor(L->insts, put_inst(&w, L, it, v));

        *bytes = (LirBytes) {
                .items   = vv(w.out),
                .count   = vN(w.out),
                .holes   = vv(w.holes),
                .nholes  = vN(w.holes),
                .ninputs = w.ninputs
        };

        return true;
}

static bool
take(Reader *r, void *out, usize n)
{
        if (!r->ok || n > r->size - r->pos) {
                r->ok = false;
                return false;
        }

        if (n != 0 && out != NULL) {
                memcpy(out, r->data + r->pos, n);
        }

        r->pos += n;

        return true;
}

static u64
get_uint(Reader *r)
{
        u64 n = 0;
        u8  b;

        for (u32 i = 0; i < 10; ++i) {
                if (!take(r, &b, 1) || (i == 9 && b > 1)) {
                        break;
                }
                n |= (u64)(b & 0x7f) << (7 * i);
                if ((b & 0x80) == 0) {
                        r->ok &= (i == 0 || b != 0);
                        return n;
                }
        }

        r->ok = false;

        return 0;
}

static u32
get_u32(Reader *r)
{
        u64 n = get_uint(r);

        if (n > UINT32_MAX) {
                r->ok = false;
                return 0;
        }

        return n;
}

static i64
get_int(Reader *r)
{
        u64 n    = get_uint(r);
        u64 bits = (n >> 1) ^ (u64)-(n & 1);
        i64 x;

        return *(i64 *)memcpy(&x, &bits, sizeof x);
}

static double
get_f64(Reader *r)
{
        u8     buf[8];
        u64    bits = 0;
        double x    = 0;

        if (take(r, buf, sizeof buf)) {
                for (u32 i = 0; i < 8; ++i) {
                        bits |= (u64)buf[i] << (8 * i);
                }
                memcpy(&x, &bits, sizeof x);
        }

        return x;
}

static u32
get_count(Reader *r)
{
        u32 n = get_u32(r);

        if (n > r->size - r->pos) {
                r->ok = false;
                return 0;
        }

        return n;
}

static LirMem
get_mem(Reader *r)
{
        LirMem m;

        m.base  = get_u32(r);
        m.index = get_u32(r);

        u32 scale = get_u32(r);
        i64 disp  = get_int(r);

        r->ok   &= (scale <= UINT8_MAX) && (disp >= INT32_MIN) && (disp <= INT32_MAX);
        m.scale  = scale;
        m.disp   = disp;

        return m;
}

static LirOpnd
get_operand(Reader *r, LirBinding const *holes, u32 nholes)
{
        LirOpnd a = { .kind = get_u32(r) };

        switch (a.kind) {
        case LO_IMM:   a.imm   = get_int(r);    break;
        case LO_FIMM:  a.fimm  = get_f64(r);    break;
        case LO_MEM:   a.mem   = get_mem(r);    break;
        case LO_REG:   a.reg   = get_u32(r);    break;
        case LO_LABEL: a.label = get_u32(r);    break;
        case LO_CC:    a.cc    = get_u32(r);    break;

        case LO_CODE:
        case LO_HELPER: {
                u32 i = get_u32(r);
                if (i >= nholes || holes[i].operand.kind != a.kind) {
                        r->ok = false;
                } else {
                        a = holes[i].operand;
                }
                break;
        }

        case LO_CONST:
        case LO_REFCONST:
        case LO_VSLOT:
        case LO_HOLE_IMM:
        case LO_HOLE_FIMM:
        case LO_HOLE_PTR:
        case LO_HOLE_CONST:
        case LO_HOLE_CALLEE:
                a.index = get_u32(r);
                break;

        default:
                r->ok = false;
                break;
        }

        return a;
}

static void
get_sig(Reader *r, LirSig *sig)
{
        sig->ret     = get_u32(r);
        sig->nparams = get_count(r);

        u32 variadic = get_u32(r);

        sig->nfixed   = get_u32(r);
        sig->variadic = variadic;
        r->ok        &= (variadic <= 1);

        LirType *params = xtA0(LirType, sig->nparams);

        for (u32 i = 0; i < sig->nparams; ++i) {
                params[i] = get_u32(r);
        }

        sig->params = params;
}

static LirRawBinding const *
get_bindings(Reader *r, u32 *n)
{
        *n = get_count(r);

        LirRawBinding *bs = xtA0(LirRawBinding, *n);

        for (u32 i = 0; i < *n; ++i) {
                u32 phys = get_u32(r);
                r->ok      &= (phys < LIR_MAX_PHYS);
                bs[i].phys  = phys;
                bs[i].reg   = get_u32(r);
        }

        return bs;
}

static void
get_raw(Reader *r, LirRaw *raw)
{
        raw->narm64 = get_count(r);

        u32 *words = xtA0(u32, raw->narm64);

        for (u32 i = 0; i < raw->narm64; ++i) {
                words[i] = get_u32(r);
        }

        raw->arm64 = words;
        raw->nx64  = get_count(r);

        u8 *code = xmA(raw->nx64);

        take(r, code, raw->nx64);

        raw->x64         = code;
        raw->in          = get_bindings(r, &raw->nin);
        raw->out         = get_bindings(r, &raw->nout);
        raw->gpr_clobber = get_uint(r);
        raw->fpr_clobber = get_uint(r);
}

static void
get_call(Reader *r, LirInst *in, LirBinding const *holes, u32 nholes)
{
        get_sig(r, &in->sig);

        in->flags      = get_u32(r);
        in->tag        = get_u32(r);
        in->ncall_args = in->sig.nparams;
        in->call_args  = xtA0(LirOpnd, in->ncall_args);

        for (u32 i = 0; i < in->ncall_args; ++i) {
                in->call_args[i] = get_operand(r, holes, nholes);
        }
}

static void
get_inst(Reader *r, LirInst *in, u32 version, LirBinding const *holes, u32 nholes)
{
        in->op  = get_u32(r);
        in->dst = get_u32(r);

        u32 nargs = get_u32(r);

        in->span.source = get_u32(r);
        in->span.start  = get_u32(r);
        in->span.end    = get_u32(r);

        if (in->op >= LIR_OP_COUNT || nargs > LIR_MAX_OPERANDS) {
                r->ok = false;
                return;
        }

        in->nargs = nargs;

        for (u32 j = 0; j < nargs; ++j) {
                in->args[j] = get_operand(r, holes, nholes);
        }

        if (iscall(in)) {
                get_call(r, in, holes, nholes);
        } else if (in->op == LIR_POLL && version >= 2) {
                in->flags = get_u32(r);
                in->tag   = get_u32(r);
        } else if (in->op == LIR_ENTRY && version >= 2) {
                in->tag = get_u32(r);
        } else if (LirOps[in->op].form == LF_LD && version >= 3) {
                in->flags = get_u32(r) & LIR_REFRESH;
        } else if (in->op == LIR_SWITCH) {
                in->ntargets = get_count(r);
                in->targets  = xtA0(LirLabel, in->ntargets);
                for (u32 i = 0; i < in->ntargets; ++i) {
                        in->targets[i] = get_u32(r);
                }
        } else if (in->op == LIR_RAW) {
                get_raw(r, &in->raw);
        }
}

static void
get_regs(Reader *r, Lir *L)
{
        u32 n = get_count(r);

        if (n < L->sig.nparams) {
                r->ok = false;
                return;
        }

        lvR(L->regs, n);
        vN(L->regs) = n;

        for (u32 i = 0; i < n && r->ok; ++i) {
                LirRegInfo *ri = v_(L->regs, i);

                ri->cls   = get_u32(r);
                ri->param = get_u32(r);
                ri->pin   = get_u32(r);

                if (
                        ((u32)ri->cls >= LIR_CLASS_COUNT)
                     || !param_ok(L, *ri)
                     || (i < L->sig.nparams && ri->param != i)
                ) {
                        r->ok = false;
                        return;
                }

                if (ri->pin == LIR_NONE) {
                        continue;
                }

                if (
                        (ri->pin >= LIR_MAX_PINS)
                     || (L->pins[ri->pin] != LIR_NONE)
                     || isfloat(ri->cls)
                ) {
                        r->ok = false;
                        return;
                }

                L->pins[ri->pin] = i;
        }
}

static void
get_labels(Reader *r, Lir *L)
{
        u32 n = get_count(r);

        lvR(L->labels, n);
        vN(L->labels) = n;

        for (u32 i = 0; i < n; ++i) {
                LirLabelInfo *l = v_(L->labels, i);
                u32 pos   = get_u32(r);
                u32 bits  = get_u32(r);
                r->ok      &= (bits <= 7);
                l->pos      = pos;
                l->entry    = bits & 1;
                l->cold     = (bits >> 1) & 1;
                l->bounded  = (bits >> 2) & 1;
        }
}

static void
get_roots(Reader *r, Lir *L, LirBinding const *holes, u32 nholes)
{
        u32 n = get_count(r);

        for (u32 i = 0; i < n && r->ok; ++i) {
                u32 h = get_u32(r);
                if (h >= nholes || holes[h].value == NULL) {
                        r->ok = false;
                } else {
                        lir_const(L, holes[h].value);
                }
        }
}

static void
get_insts(Reader *r, Lir *L, u32 version, LirBinding const *holes, u32 nholes)
{
        u32 n = get_count(r);

        lvR(L->insts, n);

        for (u32 i = 0; i < n && r->ok; ++i) {
                LirInst in = { .dst = LIR_NONE };
                get_inst(r, &in, version, holes, nholes);
                lvP(L->insts, in);
        }
}

static bool
fits(LirOpndKind hole, LirOpndKind kind)
{
        switch (hole) {
        case LO_HOLE_CALLEE:
                return (kind == LO_IMM) || (kind == LO_CODE) || (kind == LO_HELPER);

        case LO_HOLE_IMM:
        case LO_HOLE_PTR:  return kind == LO_IMM;
        case LO_HOLE_FIMM: return kind == LO_FIMM;
        default:           return false;
        }
}

static bool
fill(Lir *L, LirOpnd *a, LirBinding const *holes, u32 nholes)
{
        if (!ishole(*a)) {
                return true;
        }

        if (a->index >= nholes) {
                return false;
        }

        LirBinding const *h = &holes[a->index];

        if (a->kind == LO_HOLE_CONST) {
                if (h->value == NULL) {
                        return false;
                }
                *a = lir_const(L, h->value);
                return true;
        }

        if (!fits(a->kind, h->operand.kind)) {
                return false;
        }

        *a = h->operand;

        return true;
}

static bool
bind_callee(LirInst *in, LirBinding const *holes, u32 nholes, LirError *err, u32 pc)
{
        LirOpnd callee = in->args[0];

        if (!iscall(in) || callee.kind != LO_HOLE_CALLEE || callee.index >= nholes) {
                return true;
        }

        LirBinding const *b = &holes[callee.index];

        if (b->signature != NULL && !sig_equal(&in->sig, b->signature)) {
                return lir_fail(
                        err,
                        LE_SIGNATURE,
                        pc,
                        in->span,
                        "callee hole signature does not match call"
                );
        }

        in->flags |= b->flags;

        return true;
}

static bool
bind_holes(Lir *L, LirBinding const *holes, u32 nholes, LirError *err)
{
        for (u32 pc = 0; pc < vN(L->insts); ++pc) {
                LirInst *in      = v_(L->insts, pc);
                bool     changed = false;

                if (!bind_callee(in, holes, nholes, err, pc)) {
                        return false;
                }

                for (u32 j = 0; j < nopnd(in); ++j) {
                        LirOpnd *a = opnd(in, j);
                        changed = changed || ishole(*a);
                        if (!fill(L, a, holes, nholes)) {
                                return lir_fail(
                                        err,
                                        LE_ENCODING,
                                        pc,
                                        in->span,
                                        "missing or mismatched hole binding"
                                );
                        }
                }

                if (changed && !lir_check_inst(L, pc, err)) {
                        return false;
                }
        }

        return true;
}

static Lir *
garbage(Lir *L, LirError *err)
{
        lir_free(L);
        lir_fail(err, LE_ENCODING, LIR_NOWHERE, "invalid or truncated LIR encoding");
        return NULL;
}

static Lir *
decode(Ty *ty, Reader *r, LirBinding const *holes, u32 nholes, LirError *err)
{
        char magic[4];

        if (!take(r, magic, sizeof magic) || memcmp(magic, "TYLR", sizeof magic) != 0) {
                return garbage(NULL, err);
        }

        u32 version = get_u32(r);

        if (version < 1 || version > 4) {
                return garbage(NULL, err);
        }

        u32    n    = get_count(r);
        char  *name = smA(n + 1);
        LirSig sig  = {0};

        take(r, name, n);
        name[n] = '\0';

        if (!r->ok || memchr(name, '\0', n) != NULL) {
                return garbage(NULL, err);
        }

        get_sig(r, &sig);

        if (!r->ok) {
                xmF((void *)sig.params);
                return garbage(NULL, err);
        }

        Lir *L = lir_new(name, &sig, get_u32(r), err);

        xmF((void *)sig.params);

        if (L == NULL) {
                return NULL;
        }

        L->nvslots  = get_u32(r);
        L->pc_param = get_u32(r);

        if (
                (L->pc_param != LIR_NONE)
             && (L->pc_param >= L->sig.nparams || L->sig.params[L->pc_param] != LT_PTR)
        ) {
                return garbage(L, err);
        }

        get_regs(r, L);
        get_labels(r, L);
        get_roots(r, L, holes, nholes);
        get_insts(r, L, version, holes, nholes);

        if (!r->ok || r->pos != r->size) {
                return garbage(L, err);
        }

        if (
                !lir_validate(ty, L, err)
             || !bind_holes(L, holes, nholes, err)
             || !lir_resolve_mode(L, err)
        ) {
                lir_free(L);
                return NULL;
        }

        return L;
}

Lir *
lir_deserialize(
        Ty *ty,
        void const *bytes,
        usize size,
        LirBinding const *holes,
        u32 nholes,
        LirError *err
)
{
        if (bytes == NULL || (nholes != 0 && holes == NULL)) {
                return garbage(NULL, err);
        }

        Reader r = { .data = bytes, .size = size, .ok = true };

        ty = lir_scratch(ty);

        Lir *L = decode(ty, &r, holes, nholes, err);

        return L;
}
