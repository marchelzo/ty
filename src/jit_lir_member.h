static LirReg
bc_field_slot(BcLir *c, LirReg value, i32 member, bool writing, LirLabel slow)
{
        LirReg type = bc_load(c, LIR_LD_U8, LIR_I64, value, offsetof(Value, type));
        bc_branch(c, LIR_NE, lir_r(type), lir_i(VALUE_OBJECT), slow);
        LirReg object = bc_load(c, LIR_LD_I64, LIR_PTR, value, offsetof(Value, object));
        LirReg class = bc_load(c, LIR_LD_I64, LIR_PTR, object, offsetof(TyObject, class));
        LirReg actual = bc_load(c, LIR_LD_I32, LIR_I64, value, offsetof(Value, class));
        LirReg declared = bc_load(c, LIR_LD_I32, LIR_I64, class, offsetof(Class, i));
        bc_branch(c, LIR_NE, lir_r(actual), lir_r(declared), slow);
        i32 count_off = writing ? offsetof(Class, offsets_w.count) : offsetof(Class, offsets_r.count);
        i32 items_off = writing ? offsetof(Class, offsets_w.items) : offsetof(Class, offsets_r.items);
        LirReg count = bc_load(c, LIR_LD_I64, LIR_I64, class, count_off);
        bc_branch(c, LIR_UGE, lir_i(member), lir_r(count), slow);
        LirReg offsets = bc_load(c, LIR_LD_I64, LIR_PTR, class, items_off);
        LirReg field = bc_load(c, LIR_LD_U16, LIR_I64, offsets, member * sizeof (u16));
        LirOpnd shift[] = { lir_r(field), lir_i(OFF_SHIFT) };
        LirReg kind = bc_value(c, LIR_SHR, LIR_I64, shift, countof(shift));
        bc_branch(c, LIR_NE, lir_r(kind), lir_i(OFF_FIELD), slow);
        LirOpnd mask[] = { lir_r(field), lir_i(OFF_MASK) };
        field = bc_value(c, LIR_AND, LIR_I64, mask, countof(mask));
        shift[0] = lir_r(field);
        shift[1] = lir_i(5);
        field = bc_value(c, LIR_SHL, LIR_I64, shift, countof(shift));
        LirOpnd address = lir_m(object, field, 1, offsetof(TyObject, slots));
        return bc_value(c, LIR_LEA, LIR_PTR, &address, 1);
}

static void
bc_member(BcLir *c, i32 member, bool self)
{
        LirLabel slow = lir_label(c->L);
        LirLabel done = lir_label(c->L);
        LirReg out = bc_addr(c, c->ops, (c->sp - !self) * sizeof (Value));
        LirReg value = out;
        if (self && c->self_index >= 0) {
                value = bc_addr(c, c->locals, c->self_index * sizeof (Value));
        }
        if (!self || c->self_index >= 0) {
                LirReg slot = bc_field_slot(c, value, member, false, slow);
                bc_value_copy(c, out, 0, slot, 0);
#ifdef TY_PROFILER
                LirOpnd counter = lir_i((uptr)&jit_stats.member_fast);
                LirReg base = bc_value(c, LIR_LI, LIR_PTR, &counter, 1);
                LirOpnd increment[] = { lir_m(base, LIR_NONE, 1, 0), lir_i(1) };
                bc_value(c, LIR_XADD, LIR_I64, increment, countof(increment));
#endif
                bc_jump(c, done);
        }
        bc_bind(c, slow);
        LirType ptr = LIR_TYPE_PTR;
        LirType types[] = { ptr, ptr, ptr, LIR_TYPE_I32 };
        LirOpnd args[] = { lir_r(c->ty), lir_r(out), self ? lir_i(0) : lir_r(out), lir_i(member) };
        bc_call(c, jit_rt_member, LIR_VOID, types, args, countof(args));
        bc_bind(c, done);
        c->sp += self;
}
