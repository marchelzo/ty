static bool
bc_loop_float(BcLir const *c, i32 slot)
{
        return c->local_class[slot] == CLASS_FLOAT;
}

static LirReg
bc_loop_reg(BcLir const *c, i32 slot)
{
        if (c->lreg == NULL || slot < 0 || slot >= c->bound) {
                return LIR_NONE;
        }
        return c->lreg[slot];
}

static bool
bc_loop_single_entry(BcLir const *c, i32 head, i32 end)
{
        for (i32 off = 0; off < c->size; ++off) {
                BcLirNode const *n = &c->nodes[off];
                if (n->next == 0 || n->sp < 0 || (off >= head && off <= end)) {
                        continue;
                }
                if (n->branch && n->target >= head && n->target <= end) {
                        return false;
                }
                if (n->op == INSTR_MATCH_TAG || n->op == INSTR_MATCH_STRING) {
                        for (i32 i = 0; i < n->argc; ++i) {
                                i32 id;
                                i32 delta;
                                char const *slot = n->kw_ip + i * 8;
                                memcpy(&id, slot, sizeof id);
                                memcpy(&delta, slot + 4, sizeof delta);
                                i32 target = slot + 8 - c->code + delta;
                                if (id != -1 && target >= head && target <= end) {
                                        return false;
                                }
                        }
                }
        }
        return true;
}

static bool
bc_loop_target_ok(BcLir const *c, BcLirNode const *node, bool floating)
{
        if (node->next <= 0 || node->next >= c->size) {
                return false;
        }
        BcLirNode const *next = &c->nodes[node->next];
        if (next->label != LIR_NONE || next->sp < 0) {
                return false;
        }
        switch (next->op) {
        case INSTR_MUT_ADD:
        case INSTR_MUT_SUB:
        case INSTR_MUT_MUL:
        case INSTR_ASSIGN:
                return true;
        case INSTR_PRE_INC:
        case INSTR_POST_INC:
        case INSTR_PRE_DEC:
        case INSTR_POST_DEC:
                return !floating;
        default:
                return false;
        }
}

static bool
bc_loop_falls(u8 op)
{
        switch (op) {
        case INSTR_JUMP:
        case INSTR_RETURN:
        case INSTR_RETURN_PRESERVE_CTX:
        case INSTR_THROW:
        case INSTR_RETHROW:
        case INSTR_HALT:
                return false;
        default:
                return true;
        }
}

static u8
bc_loop_access(BcLir const *c, BcLoop const *loop, i32 off, bool *def)
{
        BcLirNode const *node = &c->nodes[off];
        *def = false;
        if (node->op != INSTR_LOAD_LOCAL && node->op != INSTR_ASSIGN_LOCAL && node->op != INSTR_TARGET_LOCAL) {
                return 0;
        }
        i32 s;
        memcpy(&s, c->code + off + 1, sizeof s);
        for (i32 k = 0; k < loop->nslots; ++k) {
                if (loop->slots[k] == s) {
                        *def = node->op == INSTR_ASSIGN_LOCAL
                            || (node->op == INSTR_TARGET_LOCAL && c->nodes[node->next].op == INSTR_ASSIGN);
                        return 1 << k;
                }
        }
        return 0;
}

static u8
bc_loop_live_succ(BcLoop const *loop, i32 t)
{
        if (t < loop->head || t > loop->end) {
                return 0;
        }
        return loop->live[t - loop->head];
}

static bool
bc_loop_liveness(BcLir const *c, BcLoop *loop)
{
        i32 n = loop->end - loop->head + 1;
        loop->live = calloc(n, 1);
        if (loop->live == NULL) {
                return false;
        }
        bool changed = true;
        while (changed) {
                changed = false;
                for (i32 off = loop->end; off >= loop->head; --off) {
                        BcLirNode const *node = &c->nodes[off];
                        if (node->next == 0 || node->sp < 0) {
                                continue;
                        }
                        u8 out = 0;
                        if (bc_loop_falls(node->op)) {
                                out |= bc_loop_live_succ(loop, node->next);
                        }
                        if (node->branch) {
                                out |= bc_loop_live_succ(loop, node->target);
                        }
                        if (node->op == INSTR_MATCH_TAG || node->op == INSTR_MATCH_STRING) {
                                for (i32 i = 0; i < node->argc; ++i) {
                                        i32 id;
                                        i32 delta;
                                        char const *slot = node->kw_ip + i * 8;
                                        memcpy(&id, slot, sizeof id);
                                        memcpy(&delta, slot + 4, sizeof delta);
                                        if (id != -1) {
                                                out |= bc_loop_live_succ(loop, slot + 8 - c->code + delta);
                                        }
                                }
                        }
                        bool def;
                        u8 bit = bc_loop_access(c, loop, off, &def);
                        u8 in = def ? (u8)(out & ~bit) : (u8)(out | bit);
                        if (in != loop->live[off - loop->head]) {
                                loop->live[off - loop->head] = in;
                                changed = true;
                        }
                }
        }
        return true;
}

static void
bc_loop_select(BcLir *c, BcLoop *loop, u32 *uses, bool *bad)
{
        memset(uses, 0, c->bound * sizeof *uses);
        memset(bad, 0, c->bound * sizeof *bad);
        for (i32 off = loop->head; off <= loop->end; ++off) {
                BcLirNode const *n = &c->nodes[off];
                if (n->next == 0 || n->sp < 0) {
                        continue;
                }
                if (n->op != INSTR_LOAD_LOCAL && n->op != INSTR_ASSIGN_LOCAL && n->op != INSTR_TARGET_LOCAL) {
                        continue;
                }
                i32 slot;
                memcpy(&slot, c->code + off + 1, sizeof slot);
                if (slot < 0 || slot >= c->bound) {
                        continue;
                }
                uses[slot] += 1;
                if (n->op == INSTR_TARGET_LOCAL && !bc_loop_target_ok(c, n, c->local_class[slot] == CLASS_FLOAT)) {
                        bad[slot] = true;
                }
        }
        loop->nslots = 0;
        while (loop->nslots < (i32)countof(loop->slots)) {
                i32 best = -1;
                for (i32 slot = 0; slot < c->bound; ++slot) {
                        i32 class = c->local_class[slot];
                        if (
                                uses[slot] == 0
                             || bad[slot]
                             || (class != CLASS_INT && class != CLASS_FLOAT)
                        ) {
                                continue;
                        }
                        if (best < 0 || uses[slot] > uses[best]) {
                                best = slot;
                        }
                }
                if (best < 0) {
                        break;
                }
                loop->slots[loop->nslots++] = best;
                uses[best] = 0;
        }
        if (loop->nslots != 0 && !bc_loop_liveness(c, loop)) {
                loop->nslots = 0;
        }
}

static bool
bc_loop_range(BcLir const *c, BcLoop const *loop)
{
        BcLirNode const *head = &c->nodes[loop->head];
        BcLirNode const *back = &c->nodes[loop->end];
        i32 hs = head->sp;
        if (head->op != INSTR_DUP2_SWAP || hs < 2 || back->op != INSTR_JUMP) {
                return false;
        }
        i32 inc = -1;
        for (i32 off = loop->head; off <= loop->end; ++off) {
                BcLirNode const *n = &c->nodes[off];
                if (n->next == 0 || n->sp < 0) {
                        continue;
                }
                if (n->sp < hs) {
                        return false;
                }
                if (n->op == INSTR_SWAP || n->op == INSTR_DROP2) {
                        if (n->sp <= hs + 2) {
                                return false;
                        }
                }
                if (n->op == INSTR_INC && n->next == loop->end && n->sp == hs) {
                        inc = off;
                        continue;
                }
                BcLirNode const *next = n->next < c->size ? &c->nodes[n->next] : NULL;
                if (n->sp != hs || off == loop->end) {
                        continue;
                }
                if (n->op == INSTR_JUMP || n->op == INSTR_DUP2_SWAP || n->op == INSTR_ASSIGN) {
                        continue;
                }
                if (n->op == INSTR_TARGET_LOCAL && next != NULL && next->op == INSTR_ASSIGN) {
                        continue;
                }
                if (next != NULL && next->sp > hs && !n->branch) {
                        continue;
                }
                return false;
        }
        return inc >= 0;
}

static bool
bc_loop_plan(BcLir *c)
{
        if (
                c->compact
             || !c->speculate
             || c->dynamic
             || c->has_try
             || c->bound == 0
             || c->local_class == NULL
             || c->base_index == LIR_NONE
             || getenv("TY_JIT_NO_LOOP_REGS") != NULL
        ) {
                return true;
        }
        i32 nloops = 0;
        for (i32 off = 0; off < c->size; ++off) {
                BcLirNode const *n = &c->nodes[off];
                if (n->next != 0 && n->sp >= 0 && n->branch && n->target > 0 && n->target <= off) {
                        ++nloops;
                }
        }
        if (nloops == 0) {
                return true;
        }
        c->loops = calloc(nloops, sizeof *c->loops);
        c->lreg = malloc(c->bound * sizeof *c->lreg);
        c->spin = malloc(((usize)c->max_sp + 8) * sizeof *c->spin);
        c->active = malloc(nloops * sizeof *c->active);
        u32 *uses = malloc(c->bound * sizeof *uses);
        bool *bad = malloc(c->bound * sizeof *bad);
        if (
                c->loops == NULL
             || c->lreg == NULL
             || c->spin == NULL
             || c->active == NULL
             || uses == NULL
             || bad == NULL
        ) {
                free(uses);
                free(bad);
                return false;
        }
        for (i32 slot = 0; slot < c->bound; ++slot) {
                c->lreg[slot] = LIR_NONE;
        }
        for (i32 i = 0; i < c->max_sp + 8; ++i) {
                c->spin[i] = LIR_NONE;
        }
        for (i32 off = 0; off < c->size; ++off) {
                BcLirNode const *n = &c->nodes[off];
                if (n->next == 0 || n->sp < 0 || !n->branch || n->target <= 0 || n->target > off) {
                        continue;
                }
                BcLoop *loop = NULL;
                for (i32 i = 0; i < c->nloops; ++i) {
                        if (c->loops[i].head == n->target) {
                                loop = &c->loops[i];
                        }
                }
                if (loop == NULL) {
                        loop = &c->loops[c->nloops++];
                        loop->head = n->target;
                }
                loop->end = off;
        }
        for (i32 i = 0; i < c->nloops; ++i) {
                BcLoop *loop = &c->loops[i];
                BcLirNode const *head = &c->nodes[loop->head];
                if (head->label == LIR_NONE || head->sp < 0 || !bc_loop_single_entry(c, loop->head, loop->end)) {
                        continue;
                }
                for (i32 j = 0; j < i; ++j) {
                        BcLoop const *other = &c->loops[j];
                        bool overlap = other->head <= loop->end && loop->head <= other->end;
                        bool nested = (other->head <= loop->head && loop->end <= other->end)
                                   || (loop->head <= other->head && other->end <= loop->end);
                        if (overlap && !nested) {
                                head = NULL;
                        }
                }
                if (head == NULL) {
                        continue;
                }
                loop->sp = head->sp;
                bc_loop_select(c, loop, uses, bad);
                loop->stack = c->spin != NULL && bc_loop_range(c, loop);
                if (loop->nslots != 0 || loop->stack) {
                        loop->deopt = lir_label(c->L);
                }
        }
        free(uses);
        free(bad);
        return true;
}

static void
bc_loop_load(BcLir *c, i32 slot, LirReg r, LirLabel fail, bool known)
{
        bool floating = bc_loop_float(c, slot);
        BcSlot const *value = known ? bc_vs_known(c, slot) : NULL;
        i32 at = slot * sizeof (Value);
        if (value != NULL && !floating && value->kind == VS_CINT) {
                LirOpnd imm = lir_i((i64)value->bits);
                c->ok = c->ok && lir_emit_to(c->L, LIR_LI, r, &imm, 1);
                return;
        }
        if (value != NULL && floating && value->kind == VS_CREAL) {
                double d;
                memcpy(&d, &value->bits, sizeof d);
                LirOpnd imm = lir_f(d);
                c->ok = c->ok && lir_emit_to(c->L, LIR_FLI, r, &imm, 1);
                return;
        }
        if (value != NULL && value->kind == (floating ? VS_REAL : VS_INT)) {
                LirOpnd src = lir_r(value->r);
                c->ok = c->ok && lir_emit_to(c->L, LIR_MOV, r, &src, 1);
                return;
        }
        LirReg type = bc_load(c, LIR_LD_U8, LIR_I64, c->locals, at + offsetof(Value, type));
        bc_branch(c, LIR_NE, lir_r(type), lir_i(floating ? VALUE_REAL : VALUE_INTEGER), fail);
        LirOpnd mem = lir_m(c->locals, LIR_NONE, 1, at + offsetof(Value, z));
        c->ok = c->ok && lir_emit_to(c->L, floating ? LIR_LD_F64 : LIR_LD_I64, r, &mem, 1);
}

static void
bc_loop_tag(BcLir *c, i32 slot)
{
        bc_store(c, LIR_ST64, c->locals, slot * sizeof (Value),
                 lir_i(bc_loop_float(c, slot) ? VALUE_REAL : VALUE_INTEGER));
}

static void
bc_loop_load_stack(BcLir *c, i32 pos, LirReg r, LirLabel fail)
{
        i32 at = pos * sizeof (Value);
        LirReg type = bc_load(c, LIR_LD_U8, LIR_I64, c->ops, at + offsetof(Value, type));
        bc_branch(c, LIR_NE, lir_r(type), lir_i(VALUE_INTEGER), fail);
        LirOpnd mem = lir_m(c->ops, LIR_NONE, 1, at + offsetof(Value, z));
        c->ok = c->ok && lir_emit_to(c->L, LIR_LD_I64, r, &mem, 1);
}

static bool
bc_loop_pinned(BcLir const *c, i32 pos)
{
        return c->spin != NULL && c->spin[pos] != LIR_NONE;
}

static void
bc_loop_enter(BcLir *c, i32 off)
{
        if (c->loops == NULL) {
                return;
        }
        for (i32 i = 0; i < c->nloops; ++i) {
                BcLoop *loop = &c->loops[i];
                if (loop->head != off || (loop->nslots == 0 && !loop->stack)) {
                        continue;
                }
                loop->nowned = 0;
                for (i32 k = 0; k < loop->nslots; ++k) {
                        i32 slot = loop->slots[k];
                        if (c->lreg[slot] != LIR_NONE) {
                                continue;
                        }
                        LirReg r = lir_reg(c->L, bc_loop_float(c, slot) ? LIR_F64 : LIR_I64);
                        if ((loop->live[0] >> k) & 1) {
                                bc_loop_load(c, slot, r, loop->deopt, true);
                        } else {
                                bc_loop_tag(c, slot);
                        }
                        c->lreg[slot] = r;
                        loop->owned_bit[loop->nowned] = 1 << k;
                        loop->owned[loop->nowned] = slot;
                        loop->owned_reg[loop->nowned] = r;
                        loop->nowned += 1;
                }
                if (loop->stack) {
                        for (i32 k = 0; k < 2; ++k) {
                                i32 pos = loop->sp - 2 + k;
                                LirReg r = lir_reg(c->L, LIR_I64);
                                bc_loop_load_stack(c, pos, r, loop->deopt);
                                loop->sreg[k] = r;
                                c->spin[pos] = r;
                                c->vs[pos] = (BcSlot) { .kind = VS_INT, .r = r };
                        }
                }
                c->active[c->nactive++] = i;
        }
}

static void
bc_loop_leave(BcLir *c, i32 off)
{
        while (c->nactive > 0 && c->loops[c->active[c->nactive - 1]].end < off) {
                BcLoop const *loop = &c->loops[c->active[--c->nactive]];
                for (i32 k = 0; k < loop->nowned; ++k) {
                        c->lreg[loop->owned[k]] = LIR_NONE;
                }
                if (loop->stack) {
                        for (i32 k = 0; k < 2; ++k) {
                                i32 pos = loop->sp - 2 + k;
                                c->spin[pos] = LIR_NONE;
                                c->vs[pos].kind = VS_MEM;
                        }
                }
        }
}

static void
bc_loop_osr(BcLir *c, i32 off, i32 sp)
{
        if (c->loops == NULL) {
                return;
        }
        LirLabel fail = LIR_NONE;
        for (i32 i = 0; i < c->nloops; ++i) {
                BcLoop const *loop = &c->loops[i];
                if ((loop->nowned == 0 && !loop->stack) || loop->head > off || off > loop->end) {
                        continue;
                }
                if (fail == LIR_NONE) {
                        fail = lir_label(c->L);
                }
                if (loop->stack) {
                        for (i32 k = 0; k < 2; ++k) {
                                bc_loop_load_stack(c, loop->sp - 2 + k, loop->sreg[k], fail);
                        }
                }
                for (i32 k = 0; k < loop->nowned; ++k) {
                        if (loop->live[off - loop->head] & loop->owned_bit[k]) {
                                bc_loop_load(c, loop->owned[k], loop->owned_reg[k], fail, false);
                        } else {
                                bc_loop_tag(c, loop->owned[k]);
                        }
                }
        }
        if (fail == LIR_NONE) {
                return;
        }
        LirLabel go = lir_label(c->L);
        bc_jump(c, go);
        bc_bind(c, fail);
        bc_stack_count_at(c, sp);
        LirOpnd result = lir_i(JIT_PACK(JIT_DEOPT, off));
        bc_effect(c, LIR_RET, &result, 1);
        bc_bind(c, go);
}

static void
bc_loop_stubs(BcLir *c)
{
        for (i32 i = 0; i < c->nloops; ++i) {
                BcLoop const *loop = &c->loops[i];
                if (loop->nslots == 0 && !loop->stack) {
                        continue;
                }
                bc_bind(c, loop->deopt);
                bc_stack_count_at(c, loop->sp);
                LirOpnd result = lir_i(JIT_PACK(JIT_DEOPT, loop->head));
                bc_effect(c, LIR_RET, &result, 1);
        }
}

static void
bc_loop_sync(BcLir *c, i32 slot)
{
        bool floating = bc_loop_float(c, slot);
        bc_store(c, floating ? LIR_ST_F64 : LIR_ST64, c->locals, slot * sizeof (Value) + offsetof(Value, z),
                 lir_r(c->lreg[slot]));
        if (c->known_gen != NULL) {
                c->known_gen[slot] = 0;
        }
}

static void
bc_loop_copy_to(BcLir *c, LirReg d, LirReg s)
{
        LirOpnd src = lir_r(s);
        c->ok = c->ok && lir_emit_to(c->L, LIR_MOV, d, &src, 1);
}

static LirReg
bc_loop_copy(BcLir *c, i32 slot)
{
        LirReg t = lir_reg(c->L, bc_loop_float(c, slot) ? LIR_F64 : LIR_I64);
        bc_loop_copy_to(c, t, c->lreg[slot]);
        return t;
}

static bool
bc_loop_dynamic(BcSlot const *value)
{
        return value->kind == VS_MEM || value->kind == VS_LOCAL;
}

static LirReg
bc_loop_operand(BcLir *c, i32 i, bool floating)
{
        BcSlot const *value = &c->vs[i];
        if (!bc_loop_dynamic(value)) {
                if (floating) {
                        if (bc_vs_floating(value->kind)) {
                                return bc_vs_real(c, i);
                        }
                        LirOpnd x = lir_r(bc_vs_int(c, i));
                        return bc_value(c, LIR_I2F, LIR_F64, &x, 1);
                }
                return bc_vs_int(c, i);
        }
        LirReg base = value->kind == VS_LOCAL ? c->locals : c->ops;
        i32 at = value->kind == VS_LOCAL ? (i32)value->bits * sizeof (Value) : i * sizeof (Value);
        LirLabel failed = bc_vs_guard_begin(c);
        LirReg type = bc_load(c, LIR_LD_U8, LIR_I64, base, at + offsetof(Value, type));
        bc_branch(c, LIR_NE, lir_r(type), lir_i(floating ? VALUE_REAL : VALUE_INTEGER), failed);
        bc_vs_guard_end(c, failed);
        return floating
             ? bc_load(c, LIR_LD_F64, LIR_F64, base, at + offsetof(Value, real))
             : bc_load(c, LIR_LD_I64, LIR_I64, base, at + offsetof(Value, z));
}

static bool
bc_loop_accepts(BcSlot const *value, bool floating, bool exact)
{
        if (bc_loop_dynamic(value)) {
                return true;
        }
        if (floating) {
                return bc_vs_floating(value->kind) || (!exact && bc_vs_integral(value->kind));
        }
        return bc_vs_integral(value->kind);
}

static void
bc_loop_assign(BcLir *c, i32 slot, i32 i)
{
        bool floating = bc_loop_float(c, slot);
        LirReg value = bc_loop_operand(c, i, floating);
        bc_vs_release_local(c, slot);
        bc_loop_copy_to(c, c->lreg[slot], value);
        bc_loop_sync(c, slot);
}

static bool
bc_loop_lower(BcLir *c, BcLirNode const *node, char const *ip)
{
        i32 slot;
        memcpy(&slot, ip + 1, sizeof slot);
        if (bc_loop_reg(c, slot) == LIR_NONE) {
                return false;
        }
        bool floating = bc_loop_float(c, slot);
        switch (node->op) {
        case INSTR_LOAD_LOCAL:
                bc_vs_push(c, floating ? VS_REAL : VS_INT, bc_loop_copy(c, slot), 0);
                return true;
        case INSTR_ASSIGN_LOCAL: {
                BcSlot top = c->vs[c->sp - 1];
                if (top.kind == VS_LOCAL && (i32)top.bits == slot) {
                        c->sp -= 1;
                        c->vs[c->sp].kind = VS_MEM;
                        return true;
                }
                if (!bc_loop_accepts(&top, floating, true)) {
                        bc_vs_deopt(c);
                        c->sp -= 1;
                        c->vs[c->sp].kind = VS_MEM;
                        return true;
                }
                bc_loop_assign(c, slot, c->sp - 1);
                c->sp -= 1;
                c->vs[c->sp].kind = VS_MEM;
                return true;
        }
        case INSTR_TARGET_LOCAL:
                break;
        default:
                return false;
        }
        BcLirNode const *next = &c->nodes[node->next];
        if (!bc_loop_target_ok(c, node, floating)) {
                bc_vs_deopt(c);
                c->offset = next->next;
                c->skip_next = true;
                return true;
        }
        c->offset = next->next;
        c->skip_next = true;
        LirReg r = c->lreg[slot];
        switch (next->op) {
        case INSTR_ASSIGN: {
                BcSlot top = c->vs[c->sp - 1];
                if (top.kind == VS_LOCAL && (i32)top.bits == slot) {
                        return true;
                }
                if (!bc_loop_accepts(&top, floating, true)) {
                        bc_vs_deopt(c);
                        return true;
                }
                bc_loop_assign(c, slot, c->sp - 1);
                return true;
        }
        case INSTR_PRE_INC:
        case INSTR_POST_INC:
        case INSTR_PRE_DEC:
        case INSTR_POST_DEC: {
                bool inc = next->op == INSTR_PRE_INC || next->op == INSTR_POST_INC;
                bool post = next->op == INSTR_POST_INC || next->op == INSTR_POST_DEC;
                LirReg old = post ? bc_loop_copy(c, slot) : LIR_NONE;
                LirOpnd step[] = { lir_r(r), lir_i(inc ? 1 : -1) };
                c->ok = c->ok && lir_emit_to(c->L, LIR_ADD, r, step, countof(step));
                bc_loop_sync(c, slot);
                bc_vs_push(c, VS_INT, post ? old : bc_loop_copy(c, slot), 0);
                return true;
        }
        default: {
                BcSlot rhs = c->vs[c->sp - 1];
                if (!bc_loop_accepts(&rhs, floating, false)) {
                        bc_vs_deopt(c);
                        return true;
                }
                LirReg operand = bc_loop_operand(c, c->sp - 1, floating);
                LirOp op;
                switch (next->op) {
                case INSTR_MUT_ADD: op = floating ? LIR_FADD : LIR_ADD; break;
                case INSTR_MUT_SUB: op = floating ? LIR_FSUB : LIR_SUB; break;
                default:            op = floating ? LIR_FMUL : LIR_MUL; break;
                }
                LirOpnd args[] = { lir_r(r), lir_r(operand) };
                c->ok = c->ok && lir_emit_to(c->L, op, r, args, countof(args));
                bc_loop_sync(c, slot);
                c->vs[c->sp - 1] = (BcSlot) { .kind = floating ? VS_REAL : VS_INT, .r = bc_loop_copy(c, slot) };
                return true;
        }
        }
}
