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

static i32
bc_vs_value_type(u8 kind)
{
        switch (kind) {
        case VS_INT:
        case VS_CINT:
                return VALUE_INTEGER;
        case VS_REAL:
        case VS_CREAL:
                return VALUE_REAL;
        case VS_CNIL:
                return VALUE_NIL;
        default:
                return VALUE_BOOLEAN;
        }
}

static bool
bc_vs_integral(u8 kind)
{
        return kind == VS_INT || kind == VS_CINT;
}

static bool
bc_vs_floating(u8 kind)
{
        return kind == VS_REAL || kind == VS_CREAL;
}

static bool
bc_vs_constant(u8 kind)
{
        return kind == VS_CINT || kind == VS_CREAL || kind == VS_CBOOL || kind == VS_CNIL;
}

static void
bc_vs_store(BcLir *c, BcSlot const *slot, LirReg base, i32 offset)
{
        if (slot->kind == VS_LOCAL) {
                bc_value_copy(c, base, offset, c->locals, (i32)slot->bits * sizeof (Value));
                return;
        }
        bc_store(c, LIR_ST64, base, offset, lir_i(bc_vs_value_type(slot->kind)));
        if (bc_vs_constant(slot->kind)) {
                bc_store(c, LIR_ST64, base, offset + offsetof(Value, z), lir_i((i64)slot->bits));
        } else if (slot->kind == VS_REAL) {
                bc_store(c, LIR_ST_F64, base, offset + offsetof(Value, real), lir_r(slot->r));
        } else {
                bc_store(c, LIR_ST64, base, offset + offsetof(Value, z), lir_r(slot->r));
        }
}

static void
bc_vs_flush(BcLir *c, i32 i)
{
        BcSlot *slot = &c->vs[i];
        if (slot->kind == VS_MEM) {
                return;
        }
        bc_vs_store(c, slot, c->ops, i * sizeof (Value));
        slot->kind = VS_MEM;
}

static void
bc_vs_flush_below(BcLir *c, i32 n)
{
        if (c->vs == NULL) {
                return;
        }
        for (i32 i = 0; i < n; ++i) {
                bc_vs_flush(c, i);
        }
}

static void
bc_vs_flush_all(BcLir *c)
{
        bc_vs_flush_below(c, c->sp);
}

static bool
bc_vs_any(BcLir const *c)
{
        if (c->vs == NULL) {
                return false;
        }
        for (i32 i = 0; i < c->sp; ++i) {
                if (c->vs[i].kind != VS_MEM) {
                        return true;
                }
        }
        return false;
}

static void
bc_vs_push(BcLir *c, u8 kind, LirReg r, u64 bits)
{
        c->vs[c->sp++] = (BcSlot) { .kind = kind, .r = r, .bits = bits };
}

static LirReg
bc_vs_int(BcLir *c, i32 i)
{
        BcSlot const *slot = &c->vs[i];
        if (slot->kind == VS_CINT) {
                LirOpnd imm = lir_i((i64)slot->bits);
                return bc_value(c, LIR_LI, LIR_I64, &imm, 1);
        }
        return slot->r;
}

static LirReg
bc_vs_real(BcLir *c, i32 i)
{
        BcSlot const *slot = &c->vs[i];
        if (slot->kind == VS_CREAL) {
                double d;
                memcpy(&d, &slot->bits, sizeof d);
                LirOpnd imm = lir_f(d);
                return bc_value(c, LIR_FLI, LIR_F64, &imm, 1);
        }
        return slot->r;
}

static LirOpnd
bc_vs_int_operand(BcLir *c, i32 i)
{
        BcSlot const *slot = &c->vs[i];
        if (slot->kind == VS_CINT) {
                return lir_i((i64)slot->bits);
        }
        return lir_r(slot->r);
}

static void
bc_vs_deopt(BcLir *c)
{
        for (i32 i = 0; i < c->sp; ++i) {
                if (c->vs[i].kind != VS_MEM) {
                        bc_vs_store(c, &c->vs[i], c->ops, i * sizeof (Value));
                }
        }
        bc_stack_count(c);
        LirOpnd result = lir_i(JIT_PACK(JIT_DEOPT, c->at));
        bc_effect(c, LIR_RET, &result, 1);
}

static LirLabel
bc_vs_guard_begin(BcLir *c)
{
        return lir_label(c->L);
}

static void
bc_vs_guard_end(BcLir *c, LirLabel failed)
{
        LirLabel ok = lir_label(c->L);
        bc_jump(c, ok);
        bc_bind(c, failed);
        bc_vs_deopt(c);
        bc_bind(c, ok);
}

static i32
bc_vs_local_class(BcLir *c, i32 slot)
{
        if (c->local_class == NULL || slot < 0 || slot >= c->bound) {
                return -1;
        }
        return c->local_class[slot];
}

static i32
bc_vs_exact(T2Type type)
{
        T2Universe *universe = t2_global_universe();
        if (type == T2_TYPE_INVALID) {
                return -1;
        }
        if (type == t2_primitive(universe, T2_TYPE_INT)) {
                return CLASS_INT;
        }
        if (type == t2_primitive(universe, T2_TYPE_FLOAT)) {
                return CLASS_FLOAT;
        }
        return -1;
}

static void
bc_vs_spill(BcLir *c, i32 i)
{
        if (c->vs[i].kind != VS_MEM) {
                bc_vs_store(c, &c->vs[i], c->ops, i * sizeof (Value));
        }
}

static BcSlot const *
bc_vs_known(BcLir const *c, i32 slot)
{
        if (c->known == NULL || slot < 0 || slot >= c->bound || c->known_gen[slot] != c->gen) {
                return NULL;
        }
        return &c->known[slot];
}

static void
bc_vs_remember(BcLir *c, i32 slot, BcSlot const *value)
{
        if (c->known == NULL || slot < 0 || slot >= c->bound) {
                return;
        }
        if (value == NULL || value->kind == VS_MEM || value->kind == VS_LOCAL) {
                c->known_gen[slot] = 0;
                return;
        }
        c->known[slot] = *value;
        c->known_gen[slot] = c->gen;
}

static void
bc_vs_forget(BcLir *c)
{
        c->gen += 1;
}

static void
bc_vs_release_local(BcLir *c, i32 slot)
{
        for (i32 i = 0; i < c->sp; ++i) {
                if (c->vs[i].kind == VS_LOCAL && (i32)c->vs[i].bits == slot) {
                        bc_vs_flush(c, i);
                }
        }
}

static LirReg
bc_vs_index(BcLir *c, i32 slot, LirLabel slow)
{
        if (bc_vs_integral(c->vs[slot].kind)) {
                return bc_vs_int(c, slot);
        }
        LirReg base = c->vs[slot].kind == VS_LOCAL ? c->locals : c->ops;
        i32 at = c->vs[slot].kind == VS_LOCAL ? (i32)c->vs[slot].bits * sizeof (Value) : slot * sizeof (Value);
        LirReg type = bc_load(c, LIR_LD_U8, LIR_I64, base, at + offsetof(Value, type));
        bc_branch(c, LIR_NE, lir_r(type), lir_i(VALUE_INTEGER), slow);
        return bc_load(c, LIR_LD_I64, LIR_I64, base, at + offsetof(Value, z));
}

static LirReg
bc_vs_element(BcLir *c, i32 container, LirReg i, LirLabel slow)
{
        BcSlot const *slot = &c->vs[container];
        LirReg base = slot->kind == VS_LOCAL ? c->locals : c->ops;
        i32 offset = slot->kind == VS_LOCAL ? (i32)slot->bits * sizeof (Value) : container * sizeof (Value);
        LirReg type = bc_load(c, LIR_LD_U8, LIR_I64, base, offset + offsetof(Value, type));
        bc_branch(c, LIR_NE, lir_r(type), lir_i(VALUE_ARRAY), slow);
        LirReg array = bc_load(c, LIR_LD_I64, LIR_PTR, base, offset + offsetof(Value, array));
        LirReg count = bc_load(c, LIR_LD_I64, LIR_I64, array, offsetof(Array, count));
        bc_branch(c, LIR_UGE, lir_r(i), lir_r(count), slow);
        LirReg items = bc_load(c, LIR_LD_I64, LIR_PTR, array, offsetof(Array, items));
        LirOpnd shift[] = { lir_r(i), lir_i(5) };
        LirReg scaled = bc_value(c, LIR_SHL, LIR_I64, shift, countof(shift));
        LirOpnd at = lir_m(items, scaled, 1, 0);
        return bc_value(c, LIR_LEA, LIR_PTR, &at, 1);
}

static bool
bc_vs_subscript(BcLir *c, BcLirNode const *node)
{
        BcSlot cont = c->vs[c->sp - 2];
        BcSlot idx = c->vs[c->sp - 1];
        if ((cont.kind != VS_MEM && cont.kind != VS_LOCAL)
            || (idx.kind != VS_MEM && idx.kind != VS_LOCAL && !bc_vs_integral(idx.kind))
            || (cont.kind == VS_MEM && idx.kind == VS_MEM)) {
                return false;
        }
        i32 element = -1;
        if (c->speculate && c->hints != NULL && node->next < c->size) {
                element = bc_vs_exact(find_type_hint(c->hints, node->next));
        }
        if (element >= 0) {
                LirLabel failed = bc_vs_guard_begin(c);
                LirReg i = bc_vs_index(c, c->sp - 1, failed);
                LirReg ptr = bc_vs_element(c, c->sp - 2, i, failed);
                LirReg type = bc_load(c, LIR_LD_U8, LIR_I64, ptr, offsetof(Value, type));
                bool real = element == CLASS_FLOAT;
                bc_branch(c, LIR_NE, lir_r(type), lir_i(real ? VALUE_REAL : VALUE_INTEGER), failed);
                LirReg r = real
                         ? bc_load(c, LIR_LD_F64, LIR_F64, ptr, offsetof(Value, real))
                         : bc_load(c, LIR_LD_I64, LIR_I64, ptr, offsetof(Value, z));
                bc_vs_guard_end(c, failed);
                c->sp -= 2;
                c->vs[c->sp + 1].kind = VS_MEM;
                bc_vs_push(c, real ? VS_REAL : VS_INT, r, 0);
                return true;
        }
        LirLabel slow = lir_label(c->L);
        LirLabel done = lir_label(c->L);
        LirReg i = bc_vs_index(c, c->sp - 1, slow);
        LirReg ptr = bc_vs_element(c, c->sp - 2, i, slow);
        bc_value_copy(c, c->ops, (c->sp - 2) * sizeof (Value), ptr, 0);
        bc_jump(c, done);
        bc_bind(c, slow);
        bc_vs_spill(c, c->sp - 2);
        bc_vs_spill(c, c->sp - 1);
        LirType types[] = { LIR_TYPE_PTR, LIR_TYPE_PTR };
        LirReg left = bc_addr(c, c->ops, (c->sp - 2) * sizeof (Value));
        LirOpnd args[] = { lir_r(c->ty), lir_r(left) };
        bc_call(c, jit_rt_subscript, LIR_VOID, types, args, countof(args));
        bc_bind(c, done);
        c->sp -= 2;
        c->vs[c->sp].kind = VS_MEM;
        c->vs[c->sp + 1].kind = VS_MEM;
        c->sp += 1;
        return true;
}

static bool
bc_vs_assign_subscript(BcLir *c, char const *ip)
{
        if ((u8)ip[1] != 1) {
                return false;
        }
        BcSlot value = c->vs[c->sp - 3];
        BcSlot cont = c->vs[c->sp - 2];
        BcSlot idx = c->vs[c->sp - 1];
        if ((cont.kind != VS_MEM && cont.kind != VS_LOCAL)
            || (idx.kind != VS_MEM && idx.kind != VS_LOCAL && !bc_vs_integral(idx.kind))
            || (cont.kind == VS_MEM && idx.kind == VS_MEM && value.kind == VS_MEM)) {
                return false;
        }
        LirLabel slow = lir_label(c->L);
        LirLabel done = lir_label(c->L);
        LirReg i = bc_vs_index(c, c->sp - 1, slow);
        LirReg ptr = bc_vs_element(c, c->sp - 2, i, slow);
        if (value.kind == VS_MEM) {
                bc_value_copy(c, ptr, 0, c->ops, (c->sp - 3) * sizeof (Value));
        } else {
                bc_vs_store(c, &value, ptr, 0);
        }
        bc_jump(c, done);
        bc_bind(c, slow);
        bc_vs_spill(c, c->sp - 3);
        bc_vs_spill(c, c->sp - 2);
        bc_vs_spill(c, c->sp - 1);
        LirType types[] = { LIR_TYPE_PTR, LIR_TYPE_PTR, LIR_TYPE_I32 };
        LirReg top = bc_addr(c, c->ops, c->sp * sizeof (Value));
        LirOpnd args[] = { lir_r(c->ty), lir_r(top), lir_i(1) };
        bc_call(c, jit_rt_assign_subscript, LIR_VOID, types, args, countof(args));
        bc_bind(c, done);
        c->sp -= 2;
        c->vs[c->sp].kind = VS_MEM;
        c->vs[c->sp + 1].kind = VS_MEM;
        return true;
}

static bool
bc_vs_numeric_use(BcLir const *c, BcLirNode const *node)
{
        if (node->next >= c->size) {
                return false;
        }
        BcLirNode const *next = &c->nodes[node->next];
        if (next->label != LIR_NONE) {
                return false;
        }
        switch (next->op) {
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
        case INSTR_JEQ:
        case INSTR_JNE:
        case INSTR_JLT:
        case INSTR_JGT:
        case INSTR_JLE:
        case INSTR_JGE:
        case INSTR_INC:
        case INSTR_DEC:
        case INSTR_NEG:
        case INSTR_ASSIGN_LOCAL:
        case INSTR_LOAD_LOCAL:
        case INSTR_INT8:
        case INSTR_INTEGER:
        case INSTR_REAL:
        case INSTR_DUP:
        case INSTR_SUBSCRIPT:
        case INSTR_ASSIGN_SUBSCRIPT:
        case INSTR_TARGET_LOCAL:
                return true;
        default:
                return false;
        }
}

static bool
bc_vs_plan(BcLir *c, Ty *ty, Value const *f)
{
        c->vs = calloc((usize)c->max_sp + 8, sizeof *c->vs);
        if (c->vs == NULL) {
                return false;
        }
        c->hints = NULL;
        Expr const *outer = expr_of(f);
        if (outer != NULL && !from_eval(f)) {
                c->hints = &outer->type_hints;
        }
        c->speculate = !c->dynamic && !c->has_try && c->nresume == c->nosr
                    && !(flags_of(f)[0] & FF_JIT_NOSPEC)
                    && getenv("TY_JIT_NO_SPECULATE") == NULL;
        if (c->bound == 0) {
                return true;
        }
        c->local_class = malloc(c->bound * sizeof *c->local_class);
        c->local_type = calloc(c->bound, sizeof *c->local_type);
        c->known = calloc(c->bound, sizeof *c->known);
        c->known_gen = calloc(c->bound, sizeof *c->known_gen);
        c->gen = 1;
        if (c->local_class == NULL || c->local_type == NULL || c->known == NULL || c->known_gen == NULL) {
                return false;
        }
        for (i32 slot = 0; slot < c->bound; ++slot) {
                c->local_class[slot] = -1;
        }
        Expr const *expr = expr_of(f);
        if (expr == NULL || expr->scope == NULL) {
                return true;
        }
        c->hints = &expr->type_hints;
        for (i32 slot = 0; slot < c->bound && slot < vN(expr->scope->owned); ++slot) {
                Symbol *symbol = v__(expr->scope->owned, slot);
                if (!SymbolIsCaptured(symbol)) {
                        c->local_type[slot] = symbol->type;
                }
        }
        for (i32 slot = 0; slot < c->bound && slot < vN(expr->scope->owned); ++slot) {
                Symbol *symbol = v__(expr->scope->owned, slot);
                if (slot == c->self_index || SymbolIsCaptured(symbol)) {
                        continue;
                }
                T2Universe *universe = t2_global_universe();
                if (symbol->type == t2_primitive(universe, T2_TYPE_INT)) {
                        c->local_class[slot] = CLASS_INT;
                } else if (symbol->type == t2_primitive(universe, T2_TYPE_FLOAT)) {
                        c->local_class[slot] = CLASS_FLOAT;
                }
        }
        return true;
}

static LirReg
bc_vs_type_of(BcLir *c, i32 i)
{
        BcSlot const *slot = &c->vs[i];
        if (slot->kind == VS_LOCAL) {
                return bc_load(c, LIR_LD_U8, LIR_I64, c->locals, (i32)slot->bits * sizeof (Value) + offsetof(Value, type));
        }
        if (slot->kind == VS_MEM) {
                return bc_load(c, LIR_LD_U8, LIR_I64, c->ops, i * sizeof (Value) + offsetof(Value, type));
        }
        LirOpnd known = lir_i(bc_vs_value_type(slot->kind));
        return bc_value(c, LIR_LI, LIR_I64, &known, 1);
}

static bool
bc_vs_nil_test(BcLir *c, u8 op, i32 *other)
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

static bool
bc_vs_binary(BcLir *c, u8 op)
{
        i32 other;
        if (bc_vs_nil_test(c, op, &other)) {
                LirReg type = bc_vs_type_of(c, other);
                LirOpnd args[] = { lir_cc(op == INSTR_EQ ? LIR_EQ : LIR_NE), lir_r(type), lir_i(VALUE_NIL) };
                LirReg d = bc_value(c, LIR_SETCC, LIR_I64, args, countof(args));
                c->sp -= 2;
                c->vs[c->sp + 1].kind = VS_MEM;
                bc_vs_push(c, VS_BOOL, d, 0);
                return true;
        }
        BcSlot a = c->vs[c->sp - 2];
        BcSlot b = c->vs[c->sp - 1];
        bool ints = bc_vs_integral(a.kind) && bc_vs_integral(b.kind);
        bool reals = bc_vs_floating(a.kind) && bc_vs_floating(b.kind);
        bool mixed = (bc_vs_integral(a.kind) && bc_vs_floating(b.kind))
                  || (bc_vs_floating(a.kind) && bc_vs_integral(b.kind));
        if (mixed && (op == INSTR_EQ || op == INSTR_NEQ)) {
                c->sp -= 2;
                c->vs[c->sp + 1].kind = VS_MEM;
                bc_vs_push(c, VS_CBOOL, LIR_NONE, op == INSTR_NEQ);
                return true;
        }
        if (mixed) {
                for (i32 i = c->sp - 2; i < c->sp; ++i) {
                        if (bc_vs_integral(c->vs[i].kind)) {
                                LirOpnd x = lir_r(bc_vs_int(c, i));
                                LirReg f = bc_value(c, LIR_I2F, LIR_F64, &x, 1);
                                c->vs[i] = (BcSlot) { .kind = VS_REAL, .r = f, .hint = c->vs[i].hint };
                        }
                }
                a = c->vs[c->sp - 2];
                b = c->vs[c->sp - 1];
                reals = true;
        }
        if (!ints && !reals) {
                return false;
        }
        LirOp iop = LIR_ADD;
        LirOp fop = LIR_FADD;
        LirCC icc = LIR_EQ;
        LirCC fcc = LIR_FEQ;
        bool compare = false;
        switch (op) {
        case INSTR_ADD: iop = LIR_ADD; fop = LIR_FADD; break;
        case INSTR_SUB: iop = LIR_SUB; fop = LIR_FSUB; break;
        case INSTR_MUL: iop = LIR_MUL; fop = LIR_FMUL; break;
        case INSTR_DIV: iop = LIR_SDIV; fop = LIR_FDIV; break;
        case INSTR_EQ:  icc = LIR_EQ; fcc = LIR_FEQ; compare = true; break;
        case INSTR_NEQ: icc = LIR_NE; fcc = LIR_FNE; compare = true; break;
        case INSTR_LT:  icc = LIR_LT; fcc = LIR_FLT; compare = true; break;
        case INSTR_GT:  icc = LIR_GT; fcc = LIR_FGT; compare = true; break;
        case INSTR_LEQ: icc = LIR_LE; fcc = LIR_FLE; compare = true; break;
        case INSTR_GEQ: icc = LIR_GE; fcc = LIR_FGE; compare = true; break;
        default:
                return false;
        }
        if (op == INSTR_DIV) {
                if (ints && (b.kind != VS_CINT || (i64)b.bits == 0 || (i64)b.bits == -1)) {
                        if (!c->speculate) {
                                return false;
                        }
                        LirLabel failed = bc_vs_guard_begin(c);
                        LirReg divisor = bc_vs_int(c, c->sp - 1);
                        bc_branch(c, LIR_EQ, lir_r(divisor), lir_i(0), failed);
                        bc_branch(c, LIR_EQ, lir_r(divisor), lir_i(-1), failed);
                        bc_vs_guard_end(c, failed);
                        c->vs[c->sp - 1] = (BcSlot) { .kind = VS_INT, .r = divisor };
                        b = c->vs[c->sp - 1];
                }
                if (reals) {
                        if (!c->speculate) {
                                return false;
                        }
                        LirLabel failed = bc_vs_guard_begin(c);
                        LirReg divisor = bc_vs_real(c, c->sp - 1);
                        LirOpnd bits = lir_r(divisor);
                        LirReg raw = bc_value(c, LIR_BITCAST, LIR_I64, &bits, 1);
                        LirOpnd shift[] = { lir_r(raw), lir_i(1) };
                        LirReg magnitude = bc_value(c, LIR_SHL, LIR_I64, shift, countof(shift));
                        bc_branch(c, LIR_EQ, lir_r(magnitude), lir_i(0), failed);
                        bc_vs_guard_end(c, failed);
                        c->vs[c->sp - 1] = (BcSlot) { .kind = VS_REAL, .r = divisor };
                        b = c->vs[c->sp - 1];
                }
        }
        LirReg d;
        u8 kind;
        if (ints) {
                LirReg left = bc_vs_int(c, c->sp - 2);
                LirOpnd right = bc_vs_int_operand(c, c->sp - 1);
                if (op == INSTR_DIV && right.kind == LIR_OPERAND_IMM) {
                        right = lir_r(bc_vs_int(c, c->sp - 1));
                }
                if (compare) {
                        LirOpnd args[] = { lir_cc(icc), lir_r(left), right };
                        d = bc_value(c, LIR_SETCC, LIR_I64, args, countof(args));
                        kind = VS_BOOL;
                } else {
                        LirOpnd args[] = { lir_r(left), right };
                        d = bc_value(c, iop, LIR_I64, args, countof(args));
                        kind = VS_INT;
                }
        } else {
                LirReg left = bc_vs_real(c, c->sp - 2);
                LirReg right = bc_vs_real(c, c->sp - 1);
                if (compare) {
                        LirOpnd args[] = { lir_cc(fcc), lir_r(left), lir_r(right) };
                        d = bc_value(c, LIR_FSETCC, LIR_I64, args, countof(args));
                        kind = VS_BOOL;
                } else {
                        LirOpnd args[] = { lir_r(left), lir_r(right) };
                        d = bc_value(c, fop, LIR_F64, args, countof(args));
                        kind = VS_REAL;
                }
        }
        c->sp -= 2;
        bc_vs_push(c, kind, d, 0);
        return true;
}

static bool
bc_vs_jump(BcLir *c, BcLirNode const *node)
{
        LirLabel target = c->nodes[node->target].label;
        if (node->deopt != LIR_NONE || target == LIR_NONE) {
                return false;
        }
        u8 op = node->op;
        if (op == INSTR_JUMP_IF || op == INSTR_JUMP_IF_NOT) {
                BcSlot top = c->vs[c->sp - 1];
                if (top.kind != VS_BOOL && top.kind != VS_CBOOL) {
                        return false;
                }
                bc_vs_flush_below(c, c->sp - 1);
                c->sp -= 1;
                c->vs[c->sp].kind = VS_MEM;
                if (top.kind == VS_CBOOL) {
                        if ((top.bits != 0) == (op == INSTR_JUMP_IF)) {
                                bc_jump(c, target);
                        }
                        return true;
                }
                bc_branch(c, op == INSTR_JUMP_IF ? LIR_NE : LIR_EQ, lir_r(top.r), lir_i(0), target);
                return true;
        }
        i32 other;
        if (bc_vs_nil_test(c, op, &other)) {
                LirReg type = bc_vs_type_of(c, other);
                bc_vs_flush_below(c, c->sp - 2);
                c->sp -= 2;
                c->vs[c->sp].kind = VS_MEM;
                c->vs[c->sp + 1].kind = VS_MEM;
                bc_branch(c, op == INSTR_JEQ ? LIR_EQ : LIR_NE, lir_r(type), lir_i(VALUE_NIL), target);
                return true;
        }
        if (op == INSTR_JUMP_IF_NIL) {
                LirReg type = bc_vs_type_of(c, c->sp - 1);
                bc_vs_flush_below(c, c->sp - 1);
                c->sp -= 1;
                c->vs[c->sp].kind = VS_MEM;
                bc_branch(c, LIR_EQ, lir_r(type), lir_i(VALUE_NIL), target);
                return true;
        }
        LirCC icc;
        LirCC fcc;
        switch (op) {
        case INSTR_JEQ: icc = LIR_EQ; fcc = LIR_FEQ; break;
        case INSTR_JNE: icc = LIR_NE; fcc = LIR_FNE; break;
        case INSTR_JLT: icc = LIR_LT; fcc = LIR_FLT; break;
        case INSTR_JGT: icc = LIR_GT; fcc = LIR_FGT; break;
        case INSTR_JLE: icc = LIR_LE; fcc = LIR_FLE; break;
        case INSTR_JGE: icc = LIR_GE; fcc = LIR_FGE; break;
        default:
                return false;
        }
        BcSlot a = c->vs[c->sp - 2];
        BcSlot b = c->vs[c->sp - 1];
        bool ints = bc_vs_integral(a.kind) && bc_vs_integral(b.kind);
        bool reals = bc_vs_floating(a.kind) && bc_vs_floating(b.kind);
        bool mixed = (bc_vs_integral(a.kind) && bc_vs_floating(b.kind))
                  || (bc_vs_floating(a.kind) && bc_vs_integral(b.kind));
        if (mixed && (op == INSTR_JEQ || op == INSTR_JNE)) {
                bc_vs_flush_below(c, c->sp - 2);
                c->sp -= 2;
                c->vs[c->sp].kind = VS_MEM;
                c->vs[c->sp + 1].kind = VS_MEM;
                if (op == INSTR_JNE) {
                        bc_jump(c, target);
                }
                return true;
        }
        if (mixed) {
                for (i32 i = c->sp - 2; i < c->sp; ++i) {
                        if (bc_vs_integral(c->vs[i].kind)) {
                                LirOpnd x = lir_r(bc_vs_int(c, i));
                                LirReg f = bc_value(c, LIR_I2F, LIR_F64, &x, 1);
                                c->vs[i] = (BcSlot) { .kind = VS_REAL, .r = f, .hint = c->vs[i].hint };
                        }
                }
                reals = true;
        }
        if (!ints && !reals) {
                return false;
        }
        bc_vs_flush_below(c, c->sp - 2);
        c->sp -= 2;
        if (ints) {
                LirReg left = bc_vs_int(c, c->sp);
                LirOpnd right = bc_vs_int_operand(c, c->sp + 1);
                c->vs[c->sp].kind = VS_MEM;
                c->vs[c->sp + 1].kind = VS_MEM;
                bc_branch(c, icc, lir_r(left), right, target);
        } else {
                LirReg left = bc_vs_real(c, c->sp);
                LirReg right = bc_vs_real(c, c->sp + 1);
                c->vs[c->sp].kind = VS_MEM;
                c->vs[c->sp + 1].kind = VS_MEM;
                LirOpnd args[] = { lir_cc(fcc), lir_r(left), lir_r(right), lir_l(target) };
                bc_effect(c, LIR_FBR, args, countof(args));
        }
        return true;
}

static bool
bc_vs_mutate_local(BcLir *c, BcLirNode const *node, char const *ip)
{
        if (!c->speculate || node->next >= c->size) {
                return false;
        }
        BcLirNode const *next = &c->nodes[node->next];
        if (next->label != LIR_NONE
            || (next->op != INSTR_MUT_ADD && next->op != INSTR_MUT_SUB && next->op != INSTR_MUT_MUL)) {
                return false;
        }
        i32 slot;
        memcpy(&slot, ip + 1, sizeof slot);
        if (c->cache_at != NULL && c->cache_at[slot] >= 0) {
                return false;
        }
        i32 class = bc_vs_local_class(c, slot);
        BcSlot rhs = c->vs[c->sp - 1];
        bool ints = class == CLASS_INT && bc_vs_integral(rhs.kind);
        bool reals = class == CLASS_FLOAT && bc_vs_floating(rhs.kind);
        if (!ints && !reals) {
                return false;
        }
        i32 at = slot * sizeof (Value);
        BcSlot const *known = bc_vs_known(c, slot);
        if (known != NULL && (ints ? !bc_vs_integral(known->kind) : !bc_vs_floating(known->kind))) {
                known = NULL;
        }
        if (known == NULL) {
                LirLabel failed = bc_vs_guard_begin(c);
                LirReg type = bc_load(c, LIR_LD_U8, LIR_I64, c->locals, at + offsetof(Value, type));
                bc_branch(c, LIR_NE, lir_r(type), lir_i(ints ? VALUE_INTEGER : VALUE_REAL), failed);
                bc_vs_guard_end(c, failed);
        }
        BcSlot current_value = known != NULL ? *known : (BcSlot) { .kind = VS_MEM };
        c->offset = next->next;
        c->skip_next = true;
        bc_vs_release_local(c, slot);
        LirOp op;
        switch (next->op) {
        case INSTR_MUT_ADD: op = ints ? LIR_ADD : LIR_FADD; break;
        case INSTR_MUT_SUB: op = ints ? LIR_SUB : LIR_FSUB; break;
        default:            op = ints ? LIR_MUL : LIR_FMUL; break;
        }
        LirReg r;
        if (ints) {
                LirReg current;
                if (current_value.kind == VS_MEM) {
                        current = bc_load(c, LIR_LD_I64, LIR_I64, c->locals, at + offsetof(Value, z));
                } else if (current_value.kind == VS_CINT) {
                        LirOpnd imm = lir_i((i64)current_value.bits);
                        current = bc_value(c, LIR_LI, LIR_I64, &imm, 1);
                } else {
                        current = current_value.r;
                }
                LirOpnd args[] = { lir_r(current), bc_vs_int_operand(c, c->sp - 1) };
                r = bc_value(c, op, LIR_I64, args, countof(args));
                bc_store(c, LIR_ST64, c->locals, at + offsetof(Value, z), lir_r(r));
        } else {
                LirReg current;
                if (current_value.kind == VS_MEM) {
                        current = bc_load(c, LIR_LD_F64, LIR_F64, c->locals, at + offsetof(Value, real));
                } else if (current_value.kind == VS_CREAL) {
                        double d;
                        memcpy(&d, &current_value.bits, sizeof d);
                        LirOpnd imm = lir_f(d);
                        current = bc_value(c, LIR_FLI, LIR_F64, &imm, 1);
                } else {
                        current = current_value.r;
                }
                LirReg operand = bc_vs_real(c, c->sp - 1);
                LirOpnd args[] = { lir_r(current), lir_r(operand) };
                r = bc_value(c, op, LIR_F64, args, countof(args));
                bc_store(c, LIR_ST_F64, c->locals, at + offsetof(Value, real), lir_r(r));
        }
        c->vs[c->sp - 1] = (BcSlot) { .kind = ints ? VS_INT : VS_REAL, .r = r };
        bc_vs_remember(c, slot, &c->vs[c->sp - 1]);
        return true;
}

static bool
bc_vs_lower(BcLir *c, BcLirNode const *node, char const *ip)
{
        if (c->vs == NULL || c->dynamic) {
                return false;
        }
        i32 slot;
        u64 bits;
        switch (node->op) {
        case INSTR_INT8:
                bc_vs_push(c, VS_CINT, LIR_NONE, (u64)(i64)(i8)ip[1]);
                return true;
        case INSTR_INTEGER:
                memcpy(&bits, ip + 1, sizeof bits);
                bc_vs_push(c, VS_CINT, LIR_NONE, bits);
                return true;
        case INSTR_REAL:
                memcpy(&bits, ip + 1, sizeof bits);
                bc_vs_push(c, VS_CREAL, LIR_NONE, bits);
                return true;
        case INSTR_TRUE:
                bc_vs_push(c, VS_CBOOL, LIR_NONE, 1);
                return true;
        case INSTR_FALSE:
                bc_vs_push(c, VS_CBOOL, LIR_NONE, 0);
                return true;
        case INSTR_NIL:
                bc_vs_push(c, VS_CNIL, LIR_NONE, 0);
                return true;
        case INSTR_LOAD_LOCAL: {
                memcpy(&slot, ip + 1, sizeof slot);
                i32 class = bc_vs_local_class(c, slot);
                if (c->cache_at != NULL && c->cache_at[slot] >= 0) {
                        return false;
                }
                BcSlot const *known = bc_vs_known(c, slot);
                if (known != NULL) {
                        c->vs[c->sp] = *known;
                        c->sp += 1;
                        return true;
                }
                if (!c->speculate || class < 0 || !bc_vs_numeric_use(c, node)) {
                        if (slot < 0 || slot >= c->bound) {
                                return false;
                        }
                        bc_vs_push(c, VS_LOCAL, LIR_NONE, (u64)slot);
                        if (c->local_type != NULL) {
                                c->vs[c->sp - 1].hint = c->local_type[slot];
                        }
                        return true;
                }
                bool real = class == CLASS_FLOAT;
                i32 at = slot * sizeof (Value);
                LirLabel failed = bc_vs_guard_begin(c);
                LirReg type = bc_load(c, LIR_LD_U8, LIR_I64, c->locals, at + offsetof(Value, type));
                bc_branch(c, LIR_NE, lir_r(type), lir_i(real ? VALUE_REAL : VALUE_INTEGER), failed);
                bc_vs_guard_end(c, failed);
                LirReg r = real
                         ? bc_load(c, LIR_LD_F64, LIR_F64, c->locals, at + offsetof(Value, real))
                         : bc_load(c, LIR_LD_I64, LIR_I64, c->locals, at + offsetof(Value, z));
                bc_vs_push(c, real ? VS_REAL : VS_INT, r, 0);
                bc_vs_remember(c, slot, &c->vs[c->sp - 1]);
                return true;
        }
        case INSTR_ASSIGN_LOCAL: {
                memcpy(&slot, ip + 1, sizeof slot);
                BcSlot top = c->vs[c->sp - 1];
                if (top.kind == VS_MEM || (c->cache_at != NULL && c->cache_at[slot] >= 0)) {
                        return false;
                }
                c->sp -= 1;
                if (top.kind == VS_LOCAL && (i32)top.bits == slot) {
                        c->vs[c->sp].kind = VS_MEM;
                        return true;
                }
                bc_vs_release_local(c, slot);
                bc_vs_store(c, &top, c->locals, slot * sizeof (Value));
                c->vs[c->sp].kind = VS_MEM;
                if (top.kind == VS_LOCAL) {
                        bc_vs_remember(c, slot, bc_vs_known(c, (i32)top.bits));
                } else {
                        bc_vs_remember(c, slot, &top);
                }
                return true;
        }
        case INSTR_SUBSCRIPT:
                return bc_vs_subscript(c, node);
        case INSTR_TARGET_LOCAL:
                return bc_vs_mutate_local(c, node, ip);
        case INSTR_ASSIGN_SUBSCRIPT:
                return bc_vs_assign_subscript(c, ip);
        case INSTR_POP:
                if (c->vs[c->sp - 1].kind == VS_MEM) {
                        return false;
                }
                c->sp -= 1;
                return true;
        case INSTR_DUP:
                if (c->vs[c->sp - 1].kind == VS_MEM) {
                        return false;
                }
                c->vs[c->sp] = c->vs[c->sp - 1];
                c->sp += 1;
                return true;
        case INSTR_INC:
        case INSTR_DEC: {
                BcSlot top = c->vs[c->sp - 1];
                if (!bc_vs_integral(top.kind)) {
                        return false;
                }
                LirReg value = bc_vs_int(c, c->sp - 1);
                LirOpnd args[] = { lir_r(value), lir_i(1) };
                LirReg r = bc_value(c, node->op == INSTR_INC ? LIR_ADD : LIR_SUB, LIR_I64, args, countof(args));
                c->vs[c->sp - 1] = (BcSlot) { .kind = VS_INT, .r = r };
                return true;
        }
        case INSTR_NEG: {
                BcSlot top = c->vs[c->sp - 1];
                if (bc_vs_integral(top.kind)) {
                        LirOpnd args[] = { lir_r(bc_vs_int(c, c->sp - 1)) };
                        LirReg r = bc_value(c, LIR_NEG, LIR_I64, args, 1);
                        c->vs[c->sp - 1] = (BcSlot) { .kind = VS_INT, .r = r };
                        return true;
                }
                if (bc_vs_floating(top.kind)) {
                        LirOpnd args[] = { lir_r(bc_vs_real(c, c->sp - 1)) };
                        LirReg r = bc_value(c, LIR_FNEG, LIR_F64, args, 1);
                        c->vs[c->sp - 1] = (BcSlot) { .kind = VS_REAL, .r = r };
                        return true;
                }
                return false;
        }
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
                return bc_vs_binary(c, node->op);
        case INSTR_JUMP_IF:
        case INSTR_JUMP_IF_NOT:
        case INSTR_JUMP_IF_NIL:
        case INSTR_JEQ:
        case INSTR_JNE:
        case INSTR_JLT:
        case INSTR_JGT:
        case INSTR_JLE:
        case INSTR_JGE:
                return bc_vs_jump(c, node);
        default:
                return false;
        }
}
