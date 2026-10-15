typedef struct bc_record_cache {
        i32 const *ids;
        i32 index;
} BcRecordCache;

static Value *
bc_record_slot(Value *value, i32 member, BcRecordCache *cell)
{
        if (value->type != VALUE_TUPLE || value->ids == NULL) {
                return NULL;
        }
        for (i32 i = 0; i < value->count; ++i) {
                if (value->ids[i] == member) {
                        cell->ids = value->ids;
                        cell->index = i;
                        return &value->items[i];
                }
        }
        return NULL;
}

static void
bc_record_path(BcLir *c, LirReg value, i32 member, LirReg slot, LirLabel other, LirLabel have, LirLabel slow)
{
        BcRecordCache *cell = calloc(1, sizeof *cell);
        if (cell == NULL) {
                c->ok = false;
                return;
        }
        LirLabel miss = lir_label(c->L);
        LirReg type = bc_load(c, LIR_LD_U8, LIR_I64, value, offsetof(Value, type));
        bc_branch(c, LIR_NE, lir_r(type), lir_i(VALUE_TUPLE), other);
        LirReg ids = bc_load(c, LIR_LD_I64, LIR_PTR, value, offsetof(Value, ids));
        LirOpnd where = lir_i((uptr)cell);
        LirReg cellptr = bc_value(c, LIR_LI, LIR_PTR, &where, 1);
        LirReg cached = bc_load(c, LIR_LD_I64, LIR_PTR, cellptr, offsetof(BcRecordCache, ids));
        bc_branch(c, LIR_NE, lir_r(ids), lir_r(cached), miss);
        LirReg index = bc_load(c, LIR_LD_I32, LIR_I64, cellptr, offsetof(BcRecordCache, index));
        LirReg items = bc_load(c, LIR_LD_I64, LIR_PTR, value, offsetof(Value, items));
        LirOpnd shift[] = { lir_r(index), lir_i(5) };
        LirReg scaled = bc_value(c, LIR_SHL, LIR_I64, shift, countof(shift));
        LirOpnd at = lir_m(items, scaled, 1, 0);
        c->ok = c->ok && lir_emit_to(c->L, LIR_LEA, slot, &at, 1);
        bc_jump(c, have);
        bc_bind(c, miss);
        LirType types[] = { LIR_TYPE_PTR, LIR_TYPE_I32, LIR_TYPE_PTR };
        LirOpnd args[] = { lir_r(value), lir_i(member), lir_r(cellptr) };
        LirReg found = bc_call_flags(c, bc_record_slot, LIR_TYPE_PTR, types, args, countof(args), LIR_READS_NO_LOCALS);
        LirOpnd move = lir_r(found);
        c->ok = c->ok && lir_emit_to(c->L, LIR_MOV, slot, &move, 1);
        bc_branch(c, LIR_EQ, lir_r(slot), lir_i(0), slow);
        bc_jump(c, have);
}

static Class *
bc_hint_class(BcLir *c, i32 offset)
{
        Expr const *expr = expr_of(c->function);
        if (expr == NULL) {
                return NULL;
        }
        T2Type type = find_type_hint(&expr->type_hints, offset);
        return type == T2_TYPE_INVALID ? NULL : expected_class_of(c->ctx, type);
}

static LirReg
bc_known_field_slot(BcLir *c, LirReg value, Class *class, i32 member, bool writing, LirLabel slow)
{
        if (class == NULL || class->i < CLASS_PRIMITIVE) {
                return LIR_NONE;
        }
        u16Vector const *offsets = writing ? &class->offsets_w : &class->offsets_r;
        if (member < 0 || member >= vN(*offsets)) {
                return LIR_NONE;
        }
        u16 field = v__(*offsets, member);
        if (field == OFF_NOT_FOUND || (field >> OFF_SHIFT) != OFF_FIELD) {
                return LIR_NONE;
        }
        LirReg type = bc_load(c, LIR_LD_U8, LIR_I64, value, offsetof(Value, type));
        bc_branch(c, LIR_NE, lir_r(type), lir_i(VALUE_OBJECT), slow);
        LirReg actual = bc_load(c, LIR_LD_I32, LIR_I64, value, offsetof(Value, class));
        bc_branch(c, LIR_NE, lir_r(actual), lir_i(class->i), slow);
        LirReg object = bc_load(c, LIR_LD_I64, LIR_PTR, value, offsetof(Value, object));
        return bc_addr(c, object, offsetof(TyObject, slots) + (field & OFF_MASK) * sizeof (Value));
}

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

static LirReg
bc_any_field_slot(BcLir *c, LirReg value, Class *class, i32 member, bool writing, LirLabel slow)
{
        LirReg known = bc_known_field_slot(c, value, class, member, writing, slow);
        if (known != LIR_NONE) {
                return known;
        }
        if (class != NULL && class->i >= CLASS_PRIMITIVE) {
                return bc_field_slot(c, value, member, writing, slow);
        }
        LirReg slot = lir_reg(c->L, LIR_PTR);
        LirLabel other = lir_label(c->L);
        LirLabel have = lir_label(c->L);
        bc_record_path(c, value, member, slot, other, have, slow);
        bc_bind(c, other);
        LirReg field = bc_field_slot(c, value, member, writing, slow);
        LirOpnd move = lir_r(field);
        c->ok = c->ok && lir_emit_to(c->L, LIR_MOV, slot, &move, 1);
        bc_bind(c, have);
        return slot;
}

static void
bc_guard_receiver(BcLir *c, LirReg value, Class *class, LirLabel miss)
{
        i32 vtype;
        switch (class->i) {
        case CLASS_INT:   vtype = VALUE_INTEGER; break;
        case CLASS_FLOAT: vtype = VALUE_REAL;    break;
        case CLASS_BOOL:  vtype = VALUE_BOOLEAN; break;
        default:          vtype = VALUE_OBJECT;  break;
        }
        LirReg type = bc_load(c, LIR_LD_U8, LIR_I64, value, offsetof(Value, type));
        bc_branch(c, LIR_NE, lir_r(type), lir_i(vtype), miss);
        if (vtype == VALUE_OBJECT) {
                LirReg actual = bc_load(c, LIR_LD_I32, LIR_I64, value, offsetof(Value, class));
                bc_branch(c, LIR_NE, lir_r(actual), lir_i(class->i), miss);
        }
        LirOpnd epoch_at = lir_i((uptr)&ClassMethodEpoch);
        LirReg epoch_ptr = bc_value(c, LIR_LI, LIR_PTR, &epoch_at, 1);
        LirReg epoch = bc_load(c, LIR_LD_I32, LIR_I64, epoch_ptr, 0);
        bc_branch(c, LIR_NE, lir_r(epoch), lir_i(0), miss);
}

static bool
bc_guardable_class(Class const *class)
{
        return class != NULL
            && (class->i >= CLASS_PRIMITIVE || class->i == CLASS_INT
                || class->i == CLASS_FLOAT || class->i == CLASS_BOOL);
}

static bool
bc_known_getter(BcLir *c, LirReg value, Class *class, i32 member, i32 out, LirLabel slow, LirLabel done)
{
        if (!bc_guardable_class(class) || member < 0 || member >= vN(class->offsets_r)) {
                return false;
        }
        u16 offset = v__(class->offsets_r, member);
        if (offset == OFF_NOT_FOUND || (offset >> OFF_SHIFT) != OFF_GETTER
            || (offset & OFF_MASK) >= vN(class->getters.values)) {
                return false;
        }
        Value const *getter = v_(class->getters.values, offset & OFF_MASK);
        if (!bc_enterable(getter, 0) || param_count_of(getter) != 0
            || getter->info[FUN_INFO_BOUND] > 32) {
                return false;
        }
        bc_guard_receiver(c, value, class, slow);
        bc_try_plan(c, getter, TY_INLINE_METHOD, 0, out, value, class, NULL, out, done);
        LirOpnd constant = lir_const(c->L, getter);
        LirReg fn = bc_value(c, LIR_MOV, LIR_PTR, &constant, 1);
        bc_inline_call(c, fn, getter, out, 0, value, slow, done);
        return true;
}

static bool
bc_numeric_getter(BcLir *c, LirReg value, Class *class, i32 member, LirLabel slow, LirLabel done)
{
        if (class == NULL || (class->i != CLASS_FLOAT && class->i != CLASS_INT)) {
                return false;
        }
        char const *name = M_NAME(member);
        bool sqrt = s_eq(name, "sqrt");
        bool abs = s_eq(name, "abs");
        bool flt = s_eq(name, "float");
        bool fl = class->i == CLASS_FLOAT;
        if ((!sqrt && !abs && !flt) || (fl && flt)) {
                return false;
        }
        Value const *getter = class_lookup_getter_i(c->ctx, class->i, member);
        if (
                getter == NULL
             || getter->type != VALUE_FUNCTION
             || from_eval(getter)
             || expr_of(getter)->mod == NULL
             || !s_eq(expr_of(getter)->mod->name, "prelude")
        ) {
                return false;
        }
        LirReg type = bc_load(c, LIR_LD_U8, LIR_I64, value, offsetof(Value, type));
        bc_branch(c, LIR_NE, lir_r(type), lir_i(fl ? VALUE_REAL : VALUE_INTEGER), slow);
        if (fl && abs) {
                LirReg bits = bc_load(c, LIR_LD_I64, LIR_I64, value, offsetof(Value, z));
                LirOpnd mask[] = { lir_r(bits), lir_i(INT64_MAX) };
                LirReg r = bc_value(c, LIR_AND, LIR_I64, mask, countof(mask));
                bc_store(c, LIR_ST64, value, offsetof(Value, z), lir_r(r));
        } else if (abs) {
                LirLabel positive = lir_label(c->L);
                LirReg z = bc_load(c, LIR_LD_I64, LIR_I64, value, offsetof(Value, z));
                bc_branch(c, LIR_GE, lir_r(z), lir_i(0), positive);
                LirOpnd arg = lir_r(z);
                LirReg r = bc_value(c, LIR_NEG, LIR_I64, &arg, 1);
                bc_store(c, LIR_ST64, value, offsetof(Value, z), lir_r(r));
                bc_bind(c, positive);
        } else {
                LirOpnd arg;
                LirReg x;
                if (fl) {
                        x = bc_load(c, LIR_LD_F64, LIR_F64, value, offsetof(Value, real));
                } else {
                        LirReg z = bc_load(c, LIR_LD_I64, LIR_I64, value, offsetof(Value, z));
                        arg = lir_r(z);
                        x = bc_value(c, LIR_I2F, LIR_F64, &arg, 1);
                }
                if (sqrt) {
                        arg = lir_r(x);
                        x = bc_value(c, LIR_FSQRT, LIR_F64, &arg, 1);
                }
                bc_store(c, LIR_ST64, value, offsetof(Value, type), lir_i(VALUE_REAL));
                bc_store(c, LIR_ST_F64, value, offsetof(Value, real), lir_r(x));
        }
        bc_jump(c, done);
        return true;
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
        if ((!self && !c->compact) || (self && c->self_index >= 0)) {
                Class *class = self ? class_get(c->ctx, c->function->info[FUN_INFO_CLASS])
                                    : bc_hint_class(c, c->at);
                if (!self && bc_numeric_getter(c, value, class, member, slow, done)) {
                        goto Slow;
                }
                LirReg slot = bc_known_field_slot(c, value, class, member, false, slow);
                if (slot == LIR_NONE
                    && bc_known_getter(c, value, class, member, c->sp - !self, slow, done)) {
                        goto Slow;
                }
                if (slot == LIR_NONE) {
                        slot = bc_any_field_slot(c, value, class, member, false, slow);
                }
                bc_value_copy(c, out, 0, slot, 0);
#ifdef TY_PROFILER
                LirOpnd counter = lir_i((uptr)&jit_stats.member_fast);
                LirReg base = bc_value(c, LIR_LI, LIR_PTR, &counter, 1);
                LirOpnd increment[] = { lir_m(base, LIR_NONE, 1, 0), lir_i(1) };
                bc_value(c, LIR_XADD, LIR_I64, increment, countof(increment));
#endif
                bc_jump(c, done);
        }
Slow:
        bc_bind(c, slow);
        LirType ptr = LIR_TYPE_PTR;
        LirType types[] = { ptr, ptr, ptr, LIR_TYPE_I32 };
        LirOpnd args[] = { lir_r(c->ty), lir_r(out), self ? lir_i(0) : lir_r(out), lir_i(member) };
        bc_call(c, jit_rt_member, LIR_VOID, types, args, countof(args));
        bc_bind(c, done);
        c->sp += self;
}
