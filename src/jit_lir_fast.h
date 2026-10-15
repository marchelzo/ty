static void
bc_target_subscript(Ty *ty, Value *top);

static LirReg
bc_type_at(BcLir *c, i32 slot)
{
        return bc_load(c, LIR_LD_U8, LIR_I64, c->ops, slot * sizeof (Value) + offsetof(Value, type));
}

static LirReg
bc_array_slot(BcLir *c, i32 container, i32 index, LirLabel slow)
{
        LirReg type = bc_type_at(c, container);
        bc_branch(c, LIR_NE, lir_r(type), lir_i(VALUE_ARRAY), slow);
        LirReg itype = bc_type_at(c, index);
        bc_branch(c, LIR_NE, lir_r(itype), lir_i(VALUE_INTEGER), slow);
        LirReg i = bc_load(c, LIR_LD_I64, LIR_I64, c->ops, index * sizeof (Value) + offsetof(Value, z));
        LirReg array = bc_load(c, LIR_LD_I64, LIR_PTR, c->ops, container * sizeof (Value) + offsetof(Value, array));
        LirReg count = bc_load(c, LIR_LD_I64, LIR_I64, array, offsetof(Array, count));
        bc_branch(c, LIR_UGE, lir_r(i), lir_r(count), slow);
        LirReg items = bc_load(c, LIR_LD_I64, LIR_PTR, array, offsetof(Array, items));
        LirOpnd shift[] = { lir_r(i), lir_i(5) };
        LirReg offset = bc_value(c, LIR_SHL, LIR_I64, shift, countof(shift));
        LirOpnd at = lir_m(items, offset, 1, 0);
        return bc_value(c, LIR_LEA, LIR_PTR, &at, 1);
}

static void
bc_fast_subscript(BcLir *c)
{
        LirLabel slow = lir_label(c->L);
        LirLabel done = lir_label(c->L);
        LirReg slot = bc_array_slot(c, c->sp - 2, c->sp - 1, slow);
        bc_value_copy(c, c->ops, (c->sp - 2) * sizeof (Value), slot, 0);
        bc_jump(c, done);
        bc_bind(c, slow);
        LirType types[] = { LIR_TYPE_PTR, LIR_TYPE_PTR };
        LirReg left = bc_addr(c, c->ops, (c->sp - 2) * sizeof (Value));
        LirOpnd args[] = { lir_r(c->ty), lir_r(left) };
        bc_call(c, jit_rt_subscript, LIR_VOID, types, args, countof(args));
        bc_bind(c, done);
        --c->sp;
}

static void
bc_fast_assign_subscript(BcLir *c)
{
        LirLabel slow = lir_label(c->L);
        LirLabel done = lir_label(c->L);
        LirReg slot = bc_array_slot(c, c->sp - 2, c->sp - 1, slow);
        bc_value_copy(c, slot, 0, c->ops, (c->sp - 3) * sizeof (Value));
        bc_jump(c, done);
        bc_bind(c, slow);
        LirType types[] = { LIR_TYPE_PTR, LIR_TYPE_PTR, LIR_TYPE_I32 };
        LirReg top = bc_addr(c, c->ops, c->sp * sizeof (Value));
        LirOpnd args[] = { lir_r(c->ty), lir_r(top), lir_i(1) };
        bc_call(c, jit_rt_assign_subscript, LIR_VOID, types, args, countof(args));
        bc_bind(c, done);
        c->sp -= 2;
}

static void
bc_fast_step(BcLir *c, bool up)
{
        LirLabel slow = lir_label(c->L);
        LirLabel done = lir_label(c->L);
        i32 at = (c->sp - 1) * sizeof (Value);
        LirReg type = bc_type_at(c, c->sp - 1);
        bc_branch(c, LIR_NE, lir_r(type), lir_i(VALUE_INTEGER), slow);
        LirReg z = bc_load(c, LIR_LD_I64, LIR_I64, c->ops, at + offsetof(Value, z));
        LirOpnd args[] = { lir_r(z), lir_i(1) };
        LirReg next = bc_value(c, up ? LIR_ADD : LIR_SUB, LIR_I64, args, countof(args));
        bc_store(c, LIR_ST64, c->ops, at + offsetof(Value, z), lir_r(next));
        bc_jump(c, done);
        bc_bind(c, slow);
        LirType types[] = { LIR_TYPE_PTR, LIR_TYPE_PTR };
        LirReg last = bc_addr(c, c->ops, at);
        LirOpnd call_args[] = { lir_r(c->ty), lir_r(last) };
        bc_call(c, up ? jit_rt_inc : jit_rt_dec, LIR_VOID, types, call_args, countof(call_args));
        bc_bind(c, done);
}

static bool
bc_fusable_mutation(BcLir *c, BcLirNode const *node, bool assign)
{
        if (node->next >= c->size) {
                return false;
        }
        BcLirNode const *next = &c->nodes[node->next];
        if (next->label != LIR_NONE || next->sp < 0) {
                return false;
        }
        switch (next->op) {
        case INSTR_ASSIGN:
                return assign;
        case INSTR_MUT_ADD:
        case INSTR_MUT_SUB:
        case INSTR_MUT_MUL:
        case INSTR_MUT_DIV:
                return true;
        default:
                return false;
        }
}

static void
bc_nonzero_real(BcLir *c, LirReg base, i32 offset, LirLabel slow)
{
        LirReg bits = bc_load(c, LIR_LD_I64, LIR_I64, base, offset + offsetof(Value, real));
        LirOpnd shift[] = { lir_r(bits), lir_i(1) };
        LirReg magnitude = bc_value(c, LIR_SHL, LIR_I64, shift, countof(shift));
        bc_branch(c, LIR_EQ, lir_r(magnitude), lir_i(0), slow);
}

static void
bc_inline_mutation(BcLir *c, u8 op, LirReg base, i32 offset, i32 value, LirLabel slow, LirLabel done)
{
        i32 operand = value * sizeof (Value);
        LirReg lt = bc_load(c, LIR_LD_U8, LIR_I64, base, offset + offsetof(Value, type));
        LirReg rt = bc_type_at(c, value);
        if (op == INSTR_MUT_DIV) {
                bc_branch(c, LIR_NE, lir_r(lt), lir_i(VALUE_REAL), slow);
                bc_branch(c, LIR_NE, lir_r(rt), lir_i(VALUE_REAL), slow);
                bc_nonzero_real(c, c->ops, operand, slow);
                LirReg fa = bc_load(c, LIR_LD_F64, LIR_F64, base, offset + offsetof(Value, real));
                LirReg fb = bc_load(c, LIR_LD_F64, LIR_F64, c->ops, operand + offsetof(Value, real));
                LirOpnd fargs[] = { lir_r(fa), lir_r(fb) };
                LirReg fr = bc_value(c, LIR_FDIV, LIR_F64, fargs, countof(fargs));
                bc_store(c, LIR_ST_F64, base, offset + offsetof(Value, real), lir_r(fr));
                bc_store(c, LIR_ST_F64, c->ops, operand + offsetof(Value, real), lir_r(fr));
                bc_jump(c, done);
                return;
        }
        LirLabel real = lir_label(c->L);
        bc_branch(c, LIR_NE, lir_r(lt), lir_i(VALUE_INTEGER), real);
        bc_branch(c, LIR_NE, lir_r(rt), lir_i(VALUE_INTEGER), real);
        LirReg a = bc_load(c, LIR_LD_I64, LIR_I64, base, offset + offsetof(Value, z));
        LirReg b = bc_load(c, LIR_LD_I64, LIR_I64, c->ops, operand + offsetof(Value, z));
        LirOp iop;
        LirOp fop;
        switch (op) {
        case INSTR_MUT_ADD: iop = LIR_ADD; fop = LIR_FADD; break;
        case INSTR_MUT_SUB: iop = LIR_SUB; fop = LIR_FSUB; break;
        default:            iop = LIR_MUL; fop = LIR_FMUL; break;
        }
        LirOpnd args[] = { lir_r(a), lir_r(b) };
        LirReg r = bc_value(c, iop, LIR_I64, args, countof(args));
        bc_store(c, LIR_ST64, base, offset + offsetof(Value, z), lir_r(r));
        bc_store(c, LIR_ST64, c->ops, operand + offsetof(Value, z), lir_r(r));
        bc_jump(c, done);
        bc_bind(c, real);
        bc_branch(c, LIR_NE, lir_r(lt), lir_i(VALUE_REAL), slow);
        bc_branch(c, LIR_NE, lir_r(rt), lir_i(VALUE_REAL), slow);
        LirReg fa = bc_load(c, LIR_LD_F64, LIR_F64, base, offset + offsetof(Value, real));
        LirReg fb = bc_load(c, LIR_LD_F64, LIR_F64, c->ops, operand + offsetof(Value, real));
        args[0] = lir_r(fa);
        args[1] = lir_r(fb);
        LirReg fr = bc_value(c, fop, LIR_F64, args, countof(args));
        bc_store(c, LIR_ST_F64, base, offset + offsetof(Value, real), lir_r(fr));
        bc_store(c, LIR_ST_F64, c->ops, operand + offsetof(Value, real), lir_r(fr));
        bc_jump(c, done);
}

static bool
bc_fast_target_local(BcLir *c, BcLirNode const *node, char const *ip)
{
        i32 target;
        memcpy(&target, ip + 1, sizeof target);
        if (c->cache_at != NULL && target >= 0 && target < c->bound && c->cache_at[target] >= 0) {
                return false;
        }
        if (
                node->next < c->size
             && !c->dynamic
             && c->nodes[node->next].op == INSTR_TRY_ASSIGN_NON_NIL
             && c->nodes[node->next].label == LIR_NONE
             && c->nodes[node->next].sp >= 0
             && c->nodes[c->nodes[node->next].target].label != LIR_NONE
        ) {
                BcLirNode const *next = &c->nodes[node->next];
                i32 slot;
                memcpy(&slot, ip + 1, sizeof slot);
                c->offset = next->next;
                i32 top = (c->sp - 1) * sizeof (Value);
                LirReg type = bc_load(c, LIR_LD_U8, LIR_I64, c->ops, top + offsetof(Value, type));
                bc_branch(c, LIR_EQ, lir_r(type), lir_i(VALUE_NIL), c->nodes[next->target].label);
                bc_value_copy(c, c->locals, slot * sizeof (Value), c->ops, top);
                return true;
        }
        if (
                node->next < c->size
             && !c->dynamic
             && !c->compact
             && c->nodes[node->next].label == LIR_NONE
             && c->nodes[node->next].sp >= 0
             && (
                        c->nodes[node->next].op == INSTR_PRE_INC
                     || c->nodes[node->next].op == INSTR_POST_INC
                     || c->nodes[node->next].op == INSTR_PRE_DEC
                     || c->nodes[node->next].op == INSTR_POST_DEC
                )
        ) {
                BcLirNode const *next = &c->nodes[node->next];
                bool inc = next->op == INSTR_PRE_INC || next->op == INSTR_POST_INC;
                bool post = next->op == INSTR_POST_INC || next->op == INSTR_POST_DEC;
                i32 slot;
                memcpy(&slot, ip + 1, sizeof slot);
                i32 local = slot * sizeof (Value);
                i32 top = c->sp * sizeof (Value);
                LirLabel slow = lir_label(c->L);
                LirLabel done = lir_label(c->L);
                LirReg type = bc_load(c, LIR_LD_U8, LIR_I64, c->locals, local + offsetof(Value, type));
                bc_branch(c, LIR_NE, lir_r(type), lir_i(VALUE_INTEGER), slow);
                LirReg old = bc_load(c, LIR_LD_I64, LIR_I64, c->locals, local + offsetof(Value, z));
                LirOpnd step[] = { lir_r(old), lir_i(inc ? 1 : -1) };
                LirReg now = bc_value(c, LIR_ADD, LIR_I64, step, countof(step));
                bc_store(c, LIR_ST64, c->locals, local + offsetof(Value, z), lir_r(now));
                bc_store(c, LIR_ST64, c->ops, top, lir_i(VALUE_INTEGER));
                bc_store(c, LIR_ST64, c->ops, top + offsetof(Value, z), lir_r(post ? old : now));
                bc_jump(c, done);
                bc_bind(c, slow);
                bc_target(c, ip, INSTR_TARGET_LOCAL);
                bc_state(c, next, c->code + node->next);
                bc_bind(c, done);
                c->offset = next->next;
                return true;
        }
        if (!bc_fusable_mutation(c, node, true)) {
                return false;
        }
        BcLirNode const *next = &c->nodes[node->next];
        i32 slot;
        memcpy(&slot, ip + 1, sizeof slot);
        c->offset = next->next;
        i32 local = slot * sizeof (Value);
        if (next->op == INSTR_ASSIGN) {
                bc_value_copy(c, c->locals, local, c->ops, (c->sp - 1) * sizeof (Value));
                return true;
        }
        LirLabel slow = lir_label(c->L);
        LirLabel done = lir_label(c->L);
        bc_inline_mutation(c, next->op, c->locals, local, c->sp - 1, slow, done);
        bc_bind(c, slow);
        bc_target(c, ip, INSTR_TARGET_LOCAL);
        bc_mutate(c, next->op);
        bc_bind(c, done);
        return true;
}

static bool
bc_fast_target_subscript(BcLir *c, BcLirNode const *node)
{
        if (!bc_fusable_mutation(c, node, false)) {
                return false;
        }
        BcLirNode const *next = &c->nodes[node->next];
        c->offset = next->next;
        LirLabel slow = lir_label(c->L);
        LirLabel done = lir_label(c->L);
        LirReg slot = bc_array_slot(c, c->sp - 2, c->sp - 1, slow);
        bc_inline_mutation(c, next->op, slot, 0, c->sp - 3, slow, done);
        bc_bind(c, slow);
        LirType types[] = { LIR_TYPE_PTR, LIR_TYPE_PTR };
        LirReg top = bc_addr(c, c->ops, c->sp * sizeof (Value));
        LirOpnd args[] = { lir_r(c->ty), lir_r(top) };
        bc_call(c, bc_target_subscript, LIR_VOID, types, args, countof(args));
        c->sp -= 2;
        bc_mutate(c, next->op);
        bc_bind(c, done);
        return true;
}

static void
bc_put_scalar(BcLir *c, i32 slot, i32 type, LirOpnd payload)
{
        i32 off = slot * sizeof (Value);
        for (u32 i = 0; i < sizeof (Value); i += 8) {
                bc_store(c, LIR_ST64, c->ops, off + i, lir_i(0));
        }
        bc_store(c, LIR_ST8, c->ops, off + offsetof(Value, type), lir_i(type));
        bc_store(c, LIR_ST64, c->ops, off + offsetof(Value, z), payload);
}

static bool
bc_fast_loop(BcLir *c, BcLirNode const *node)
{
        if (c->dynamic || node->next >= c->size) {
                return false;
        }
        BcLirNode const *check = &c->nodes[node->next];
        if (check->op != INSTR_LOOP_CHECK || check->label != LIR_NONE
            || check->member < 1 || check->member > 2
            || c->nodes[check->target].label == LIR_NONE) {
                return false;
        }
        LirLabel exit = c->nodes[check->target].label;
        LirLabel slow = lir_label(c->L);
        LirLabel done = lir_label(c->L);
        i32 sp = c->sp;
        c->offset = check->next;
        LirReg type = bc_type_at(c, sp - 1);
        bc_branch(c, LIR_NE, lir_r(type), lir_i(VALUE_ARRAY), slow);
        LirReg array = bc_load(c, LIR_LD_I64, LIR_PTR, c->ops, (sp - 1) * sizeof (Value) + offsetof(Value, array));
        LirReg i = bc_load(c, LIR_LD_I64, LIR_I64, c->ops, (sp - 2) * sizeof (Value) + offsetof(Value, z));
        LirReg count = bc_load(c, LIR_LD_I64, LIR_I64, array, offsetof(Array, count));
        bc_branch(c, LIR_GE, lir_r(i), lir_r(count), exit);
        LirOpnd bump[] = { lir_r(i), lir_i(1) };
        LirReg next = bc_value(c, LIR_ADD, LIR_I64, bump, countof(bump));
        bc_store(c, LIR_ST64, c->ops, (sp - 2) * sizeof (Value) + offsetof(Value, z), lir_r(next));
        bc_put_scalar(c, sp, VALUE_SENTINEL, lir_i(0));
        if (check->member == 2) {
                bc_put_scalar(c, sp + 1, VALUE_INTEGER, lir_r(i));
        }
        LirReg items = bc_load(c, LIR_LD_I64, LIR_PTR, array, offsetof(Array, items));
        LirOpnd shift[] = { lir_r(i), lir_i(5) };
        LirReg offset = bc_value(c, LIR_SHL, LIR_I64, shift, countof(shift));
        LirOpnd at = lir_m(items, offset, 1, 0);
        LirReg item = bc_value(c, LIR_LEA, LIR_PTR, &at, 1);
        bc_value_copy(c, c->ops, (sp + check->member) * sizeof (Value), item, 0);
        bc_jump(c, done);
        bc_bind(c, slow);
        LirType iter_types[] = { LIR_TYPE_PTR, LIR_TYPE_PTR };
        LirReg top = bc_addr(c, c->ops, sp * sizeof (Value));
        LirOpnd iter_args[] = { lir_r(c->ty), lir_r(top) };
        bc_call(c, jit_rt_loop_iter, LIR_VOID, iter_types, iter_args, countof(iter_args));
        LirType check_types[] = { LIR_TYPE_PTR, LIR_TYPE_I32, LIR_TYPE_PTR };
        LirReg last = bc_addr(c, c->ops, (sp + 1) * sizeof (Value));
        LirOpnd check_args[] = { lir_r(c->ty), lir_i(check->member), lir_r(last) };
        LirReg result = bc_call(c, jit_rt_loop_check, LIR_TYPE_I32, check_types, check_args, countof(check_args));
        bc_branch(c, LIR_NE, lir_r(result), lir_i(0), exit);
        bc_bind(c, done);
        return true;
}

static void
bc_fast_div(BcLir *c)
{
        i32 left = (c->sp - 2) * sizeof (Value);
        i32 right = left + sizeof (Value);
        LirLabel real = lir_label(c->L);
        LirLabel slow = lir_label(c->L);
        LirLabel done = lir_label(c->L);
        LirReg at = bc_type_at(c, c->sp - 2);
        LirReg bt = bc_type_at(c, c->sp - 1);
        bc_branch(c, LIR_NE, lir_r(at), lir_i(VALUE_INTEGER), real);
        bc_branch(c, LIR_NE, lir_r(bt), lir_i(VALUE_INTEGER), real);
        LirReg b = bc_load(c, LIR_LD_I64, LIR_I64, c->ops, right + offsetof(Value, z));
        bc_branch(c, LIR_EQ, lir_r(b), lir_i(0), slow);
        bc_branch(c, LIR_EQ, lir_r(b), lir_i(-1), slow);
        LirReg a = bc_load(c, LIR_LD_I64, LIR_I64, c->ops, left + offsetof(Value, z));
        LirOpnd args[] = { lir_r(a), lir_r(b) };
        LirReg q = bc_value(c, LIR_SDIV, LIR_I64, args, countof(args));
        bc_store(c, LIR_ST64, c->ops, left + offsetof(Value, z), lir_r(q));
        bc_jump(c, done);
        bc_bind(c, real);
        bc_branch(c, LIR_NE, lir_r(at), lir_i(VALUE_REAL), slow);
        bc_branch(c, LIR_NE, lir_r(bt), lir_i(VALUE_REAL), slow);
        bc_nonzero_real(c, c->ops, right, slow);
        LirReg fa = bc_load(c, LIR_LD_F64, LIR_F64, c->ops, left + offsetof(Value, real));
        LirReg fb = bc_load(c, LIR_LD_F64, LIR_F64, c->ops, right + offsetof(Value, real));
        args[0] = lir_r(fa);
        args[1] = lir_r(fb);
        LirReg fq = bc_value(c, LIR_FDIV, LIR_F64, args, countof(args));
        bc_store(c, LIR_ST_F64, c->ops, left + offsetof(Value, real), lir_r(fq));
        bc_jump(c, done);
        bc_bind(c, slow);
        LirType types[] = { LIR_TYPE_PTR, LIR_TYPE_PTR, LIR_TYPE_PTR, LIR_TYPE_PTR };
        LirReg out = bc_addr(c, c->ops, left);
        LirReg rhs = bc_addr(c, c->ops, right);
        LirOpnd call_args[] = { lir_r(c->ty), lir_r(out), lir_r(out), lir_r(rhs) };
        bc_call(c, jit_rt_div, LIR_VOID, types, call_args, countof(call_args));
        bc_bind(c, done);
        --c->sp;
}

static bool
bc_fast_pattern(BcLir *c, BcLirNode const *node, char const *ip, bool *fused)
{
        i32 n = 0;
        if (StepInstruction(ip) - ip >= 9) {
                memcpy(&n, ip + 5, sizeof n);
        }
        LirLabel fail = c->nodes[node->target].label;
        i32 at = (c->sp - 1) * sizeof (Value);
        LirReg type = LIR_NONE;
        switch (node->op) {
        case INSTR_ENSURE_LEN: {
                type = bc_type_at(c, c->sp - 1);
                bc_branch(c, LIR_NE, lir_r(type), lir_i(VALUE_ARRAY), fail);
                LirReg array = bc_load(c, LIR_LD_I64, LIR_PTR, c->ops, at + offsetof(Value, array));
                LirReg count = bc_load(c, LIR_LD_I64, LIR_I64, array, offsetof(Array, count));
                bc_branch(c, LIR_GT, lir_r(count), lir_i(n), fail);
                return true;
        }
        case INSTR_ENSURE_LEN_TUPLE: {
                type = bc_type_at(c, c->sp - 1);
                bc_branch(c, LIR_NE, lir_r(type), lir_i(VALUE_TUPLE), fail);
                LirReg count = bc_load(c, LIR_LD_I32, LIR_I64, c->ops, at + offsetof(Value, count));
                bc_branch(c, LIR_GT, lir_r(count), lir_i(n), fail);
                c->tuple_off = node->next;
                c->tuple_sp = c->sp - 1;
                c->tuple_min = 0;
                return true;
        }
        case INSTR_INDEX_TUPLE:
        case INSTR_TRY_INDEX_TUPLE: {
                if (n < 0) {
                        return false;
                }
                LirLabel missing = node->op == INSTR_INDEX_TUPLE ? fail : lir_label(c->L);
                LirLabel done = lir_label(c->L);
                bool known = c->tuple_off == node - c->nodes && c->tuple_sp == c->sp - 1
                          && node->label == LIR_NONE;
                if (!known) {
                        type = bc_type_at(c, c->sp - 1);
                        bc_branch(c, LIR_NE, lir_r(type), lir_i(VALUE_TUPLE), fail);
                        c->tuple_min = 0;
                }
                if (!known || n >= c->tuple_min) {
                        LirReg count = bc_load(c, LIR_LD_I32, LIR_I64, c->ops, at + offsetof(Value, count));
                        bc_branch(c, LIR_LE, lir_r(count), lir_i(n), missing);
                }
                LirReg items = bc_load(c, LIR_LD_I64, LIR_PTR, c->ops, at + offsetof(Value, items));
                BcLirNode const *next = &c->nodes[node->next];
                c->tuple_off = -1;
                if (
                        node->op == INSTR_INDEX_TUPLE
                     && node->next < c->size
                     && next->op == INSTR_ASSIGN_LOCAL
                     && next->label == LIR_NONE
                     && next->sp >= 0
                ) {
                        i32 slot;
                        memcpy(&slot, c->code + node->next + 1, sizeof slot);
                        if (slot >= 0 && slot < c->bound && (c->cache_at == NULL || c->cache_at[slot] < 0)) {
                                bc_value_copy(c, c->locals, slot * sizeof (Value), items, n * sizeof (Value));
                                c->offset = next->next;
                                c->tuple_off = next->next;
                                c->tuple_sp = c->sp - 1;
                                if (n + 1 > c->tuple_min) {
                                        c->tuple_min = n + 1;
                                }
                                *fused = true;
                                bc_bind(c, done);
                                return true;
                        }
                }
                bc_value_copy(c, c->ops, at + sizeof (Value), items, n * sizeof (Value));
                if (node->op == INSTR_TRY_INDEX_TUPLE) {
                        bc_jump(c, done);
                        bc_bind(c, missing);
                        bc_put_scalar(c, c->sp, VALUE_NIL, lir_i(0));
                }
                bc_bind(c, done);
                return true;
        }
        case INSTR_TRY_INDEX: {
                if (n < 0) {
                        return false;
                }
                bool required = (u8)ip[9];
                LirLabel missing = required ? fail : lir_label(c->L);
                LirLabel done = lir_label(c->L);
                type = bc_type_at(c, c->sp - 1);
                bc_branch(c, LIR_NE, lir_r(type), lir_i(VALUE_ARRAY), fail);
                LirReg array = bc_load(c, LIR_LD_I64, LIR_PTR, c->ops, at + offsetof(Value, array));
                LirReg count = bc_load(c, LIR_LD_I64, LIR_I64, array, offsetof(Array, count));
                bc_branch(c, LIR_LE, lir_r(count), lir_i(n), missing);
                LirReg items = bc_load(c, LIR_LD_I64, LIR_PTR, array, offsetof(Array, items));
                bc_value_copy(c, c->ops, at + sizeof (Value), items, n * sizeof (Value));
                if (!required) {
                        bc_jump(c, done);
                        bc_bind(c, missing);
                        bc_put_scalar(c, c->sp, VALUE_NIL, lir_i(0));
                }
                bc_bind(c, done);
                return true;
        }
        default:
                return false;
        }
}
