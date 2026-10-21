enum {
        TO_FLOW,
        TO_ALT,
        TO_SLOW,
        TO_DEOPT,
        TO_TIERUP,
        TO_EXIT
};

typedef struct {
        u8          to;
        char const *callee;
        char const *why;
} Dest;

typedef struct {
        BcLir const *c;
        Lir const   *L;
        u32          n;
        u8          *role;
        u32         *note;
        u32         *origin;
        bool        *bound;
        bool        *flow;
        byte_vector  text;
} Detail;

inline static LirInst const *
inst(Detail const *d, u32 pc)
{
        return v_(d->L->insts, pc);
}

inline static u32
label_pos(Detail const *d, LirLabel l)
{
        return v__(d->L->labels, l).pos;
}

static char const *
callee_name(LirOpnd target)
{
        switch (target.kind) {
        case LO_HELPER: return target.helper->name;
        case LO_IMM:    return prof_symbolize((uptr)target.imm);
        case LO_CODE:   return (target.code->name != NULL) ? target.code->name : "jit code";
        default:        return NULL;
        }
}

static LirInst const *
def_of(Detail const *d, u32 pc, LirOpnd x, u32 *where)
{
        if (x.kind != LO_REG) {
                return NULL;
        }

        for (u32 i = pc; i-- > 0 && i + 64 > pc;) {
                if (inst(d, i)->dst == x.reg) {
                        *where = i;
                        return inst(d, i);
                }
                if (d->flow[i]) {
                        break;
                }
        }

        return NULL;
}

static bool
imm_of(Detail const *d, u32 pc, LirOpnd x, i64 *out)
{
        u32 at;

        if (x.kind == LO_IMM) {
                *out = x.imm;
                return true;
        }

        LirInst const *def = def_of(d, pc, x, &at);

        if (def == NULL || def->op != LIR_LI || def->args[0].kind != LO_IMM) {
                return false;
        }

        *out = def->args[0].imm;

        return true;
}

static i64
status_of(Detail const *d, u32 pc)
{
        LirInst const *in = inst(d, pc);
        i64            status;

        if (in->op != LIR_RET || in->nargs == 0) {
                return -1;
        }

        return imm_of(d, pc, in->args[0], &status) ? status : -1;
}

inline static i32
exit_status(Detail const *d, u32 pc)
{
        i64 status = status_of(d, pc);
        return (status < 0) ? -1 : JIT_REASON((i32)status);
}

inline static i32
resume_at(Detail const *d, u32 pc)
{
        return JIT_RESUME((i32)status_of(d, pc));
}

static char const *
guard_reason(Detail const *d, u32 from, u32 to)
{
        for (u32 pc = from; pc <= to && pc < d->n; ++pc) {
                LirInst const *in = inst(d, pc);
                if (
                        (in->op == LIR_ST32)
                     && (in->args[0].kind == LO_MEM)
                     && (in->args[0].mem.disp == offsetof(Ty, jit_guard))
                     && (in->args[1].kind == LO_IMM)
                     && (in->args[1].imm != 0)
                ) {
                        return jit_guard_text((u32)in->args[1].imm);
                }
        }

        return NULL;
}

static Dest
follow(Detail const *d, LirLabel l, u32 bc, int hops, bool rejoin)
{
        u32 start = label_pos(d, l);
        u8  flow  = rejoin ? TO_ALT : TO_FLOW;

        for (u32 pc = start; pc < d->n; ++pc) {
                LirInst const *in = inst(d, pc);

                if (pc > start && d->flow[pc]) {
                        return (Dest) { .to = flow };
                }

                switch (in->op) {
                case LIR_RET:
                        switch (exit_status(d, pc)) {
                        case JIT_DEOPT:
                                return (Dest) { .to = TO_DEOPT, .why = guard_reason(d, start, pc) };
                        case JIT_OSR:
                                return (Dest) { .to = TO_TIERUP };
                        default:
                                return (Dest) { .to = TO_EXIT };
                        }

                case LIR_CALL:
                case LIR_TAILCALL:
                        if (in->origin != bc) {
                                return (Dest) { .to = flow };
                        }
                        return (Dest) { .to = TO_SLOW, .callee = callee_name(in->args[0]) };

                case LIR_JMP:
                        if (d->flow[label_pos(d, in->args[0].label)] || hops == 0) {
                                return (Dest) { .to = flow };
                        }
                        return follow(d, in->args[0].label, bc, hops - 1, true);

                case LIR_SWITCH:
                        return (Dest) { .to = flow };

                default:
                        break;
                }
        }

        return (Dest) { .to = flow };
}

static u32
note(Detail *d, char const *fmt, ...)
{
        va_list ap;
        u32     at = vN(d->text);

        va_start(ap, fmt);
        int need = vsnprintf(NULL, 0, fmt, ap);
        va_end(ap);

        xvR(d->text, vN(d->text) + need + 1);

        va_start(ap, fmt);
        vsnprintf(vZ(d->text), need + 1, fmt, ap);
        va_end(ap);

        vN(d->text) += need + 1;

        return at;
}

inline static bool
field_at(LirOpnd m, i32 field)
{
        return (m.kind == LO_MEM)
            && (((m.mem.disp - field) % (i32)sizeof (Value)) == 0);
}

static char const *
check_text(Detail const *d, u32 pc, u32 *load, char *buf, usize size)
{
        LirInst const *in   = inst(d, pc);
        LirCC          cc   = in->args[0].cc;
        LirOpnd        x    = in->args[1];
        LirOpnd        k    = in->args[2];
        LirOpnd        m    = x;
        LirOp          op   = LIR_LD_U8;
        char const    *what = NULL;
        i64            imm;

        *load = LIR_NONE;

        if ((cc != LIR_EQ && cc != LIR_NE) || !imm_of(d, pc, k, &imm)) {
                return NULL;
        }

        if (x.kind == LO_REG) {
                LirInst const *def = def_of(d, pc, x, load);
                if (def == NULL) {
                        return NULL;
                }
                m  = def->args[0];
                op = def->op;
        }

        if (op == LIR_LD_U8 && field_at(m, offsetof(Value, type))) {
                what = TypeName(d->c->ctx, (int)imm);
        } else if (op == LIR_LD_I32 && field_at(m, offsetof(Value, class))) {
                what = class_name(d->c->ctx, (int)imm);
        }

        if (what == NULL) {
                *load = LIR_NONE;
                return NULL;
        }

        snprintf(buf, size, "%s%s", (cc == LIR_NE) ? "" : "not ", what);

        return buf;
}

static void
paint(Detail *d, u32 from, u32 to, u8 role)
{
        for (u32 pc = from; pc <= to && pc < d->n; ++pc) {
                if (d->role[pc] != JIT_ROLE_GUARD) {
                        d->role[pc] = role;
                }
        }
}

static void
paint_slow(Detail *d, u32 from)
{
        for (u32 pc = from; pc < d->n; ++pc) {
                if (pc > from && d->bound[pc]) {
                        break;
                }
                paint(d, pc, pc, JIT_ROLE_SLOW);
                if (inst(d, pc)->op == LIR_JMP || inst(d, pc)->op == LIR_RET) {
                        break;
                }
        }
}

static void
guard(Detail *d, u32 pc)
{
        LirInst const *in   = inst(d, pc);
        LirLabel       l    = in->args[3].label;
        Dest           to   = follow(d, l, d->origin[pc], 4, false);
        u32            load = LIR_NONE;
        char           buf[128];
        char const    *test = check_text(d, pc, &load, buf, sizeof buf);
        char const    *what;

        switch (to.to) {
        case TO_SLOW:   what = "slow path";  break;
        case TO_DEOPT:  what = "deopt";      break;
        case TO_TIERUP: what = "tier-up";    break;
        case TO_ALT:    what = "next case";  break;
        default:        return;
        }

        if (to.to == TO_ALT && test == NULL) {
                return;
        }

        if (to.to == TO_SLOW) {
                paint_slow(d, label_pos(d, l));
        }

        d->role[pc] = JIT_ROLE_GUARD;
        d->note[pc] = note(
                d,
                "%s%s→ %s%s%s%s%s",
                (test != NULL) ? test : "",
                (test != NULL) ? " " : "",
                what,
                (to.callee != NULL) ? ": " : "",
                (to.callee != NULL) ? to.callee : "",
                (to.why != NULL) ? " · " : "",
                (to.why != NULL) ? to.why : ""
        );

        for (u32 i = load; load != LIR_NONE && i < pc && load + 2 >= pc; ++i) {
                d->role[i] = JIT_ROLE_GUARD;
                d->note[i] = d->note[pc];
        }
}

static void
entry(Detail *d, u32 pc)
{
        for (u32 i = pc; i < d->n; ++i) {
                if (i > pc && d->bound[i]) {
                        break;
                }
                d->role[i] = JIT_ROLE_ENTRY;
                if (inst(d, i)->op == LIR_JMP) {
                        break;
                }
        }
}

static void
exits(Detail *d, u32 pc)
{
        u8 role;

        switch (exit_status(d, pc)) {
        case JIT_DEOPT: role = JIT_ROLE_DEOPT;  break;
        case JIT_OSR:   role = JIT_ROLE_TIERUP; break;
        default:        return;
        }

        u32 from = pc;

        while (from > 0 && !d->bound[from]) {
                LirOp op = inst(d, from - 1)->op;
                if (op == LIR_JMP || op == LIR_RET || op == LIR_BR) {
                        break;
                }
                from -= 1;
        }

        paint(d, from, pc, role);

        if (role == JIT_ROLE_DEOPT && d->note[from] == 0) {
                char const *why = guard_reason(d, from, pc);
                i32         at  = resume_at(d, pc);
                d->note[from] = (why != NULL)
                            ? note(d, "resume at %d · %s", at, why)
                            : note(d, "resume at %d", at);
        }
}

inline static u8
mark_role(Detail const *d, LirMark const *m)
{
        switch (m->kind) {
        case LIR_MARK_PROLOGUE: return JIT_ROLE_PROLOGUE;
        case LIR_MARK_EPILOGUE: return JIT_ROLE_EPILOGUE;
        case LIR_MARK_THUNK:    return JIT_ROLE_THUNK;
        case LIR_MARK_EDGE:     return JIT_ROLE_EDGE;
        case LIR_MARK_REBASE:   return JIT_ROLE_REBASE;
        case LIR_MARK_DATA:     return JIT_ROLE_DATA;
        case LIR_MARK_INST:     return d->role[m->pc];
        }

        switch (d->role[m->pc]) {
        case JIT_ROLE_SLOW:
        case JIT_ROLE_DEOPT:
        case JIT_ROLE_TIERUP:
                return d->role[m->pc];
        default:
                return JIT_ROLE_MOVES;
        }
}

static JitNotes
describe(BcLir const *c, LirCode const *code)
{
        Lir const *L = c->L;
        u32        n = vN(L->insts);
        Detail     d = {
                .c      = c,
                .L      = L,
                .n      = n,
                .role   = new(c, u8, n + 1),
                .note   = new(c, u32, n + 1),
                .origin = new(c, u32, n + 1),
                .bound  = new(c, bool, n + 1),
                .flow   = new(c, bool, n + 1)
        };

        xvP(d.text, '\0');

        for (u32 l = 0; l < vN(L->labels); ++l) {
                u32 pos = v__(L->labels, l).pos;
                if (pos <= n) {
                        d.bound[pos] = true;
                }
        }

        for (i32 off = 0; off < c->size; ++off) {
                LirLabel l = c->nodes[off].label;
                if (
                        decoded(&c->nodes[off])
                     && (l < vN(L->labels))
                     && (label_pos(&d, l) <= n)
                ) {
                        d.flow[label_pos(&d, l)] = true;
                }
        }

        bool body = false;

        for (u32 pc = 0; pc < n; ++pc) {
                LirInst const *in = inst(&d, pc);
                body         = body || (in->origin != 0);
                d.origin[pc] = (in->origin != 0 || pc == 0) ? in->origin : d.origin[pc - 1];
                d.role[pc]   = body ? JIT_ROLE_CODE : JIT_ROLE_PROLOGUE;
                if (in->op == LIR_POLL) {
                        d.role[pc] = JIT_ROLE_POLL;
                }
        }

        for (u32 pc = 0; pc < n; ++pc) {
                if (inst(&d, pc)->op == LIR_ENTRY) {
                        entry(&d, pc);
                }
        }

        for (u32 pc = 0; pc < n; ++pc) {
                if (inst(&d, pc)->op == LIR_RET) {
                        exits(&d, pc);
                }
        }

        for (u32 pc = 0; pc < n; ++pc) {
                if (inst(&d, pc)->op == LIR_BR) {
                        guard(&d, pc);
                }
        }

        JitNotes out = {
                .notes = calloc(code->nmarks + 1, sizeof (JitNote)),
                .text  = NULL
        };

        u32 held = 0;

        for (u32 i = 0; i < code->nmarks; ++i) {
                LirMark const *m    = &code->marks[i];
                bool           some = (m->pc != LIR_NONE) && (m->pc < n);
                u32            note = (some && m->kind == LIR_MARK_INST) ? d.note[m->pc] : 0;
                JitNote        x    = {
                        .off  = m->off,
                        .bc   = some ? d.origin[m->pc] : 0,
                        .role = mark_role(&d, m),
                        .note = (note != 0) ? note : held
                };

                if (i + 1 < code->nmarks && code->marks[i + 1].off == m->off) {
                        held = x.note;
                        continue;
                }

                held = 0;

                JitNote const *last = (out.n > 0) ? &out.notes[out.n - 1] : NULL;

                if (
                        (last != NULL)
                     && (last->bc == x.bc)
                     && (last->role == x.role)
                     && (last->note == x.note)
                ) {
                        continue;
                }

                out.notes[out.n++] = x;
        }

        out.text = malloc(vN(d.text));
        memcpy(out.text, vv(d.text), vN(d.text));

        xvF(d.text);

        return out;
}
