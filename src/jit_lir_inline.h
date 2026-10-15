typedef struct bc_plan_field {
        Class *class;
        u16 offset;
} BcPlanField;

static LirReg
bc_plan_source(BcLir *c, TyInlinePlan const *plan, TyInlineKind kind, i32 base, LirReg self, i32 local)
{
        if (local >= 0 && local < plan->argc) {
                return bc_addr(c, c->ops, (base + local) * sizeof (Value));
        }
        if (kind == TY_INLINE_METHOD && local == plan->self_local) {
                return self;
        }
        return LIR_NONE;
}

static Class *
bc_param_class(BcLir *c, Value const *callee, i32 index)
{
        Expr const *expr = expr_of(callee);
        if (expr == NULL || expr->scope == NULL || index >= vN(expr->scope->owned)) {
                return NULL;
        }
        Symbol *symbol = v__(expr->scope->owned, index);
        return expected_class_of(c->ctx, symbol->type);
}

static bool
bc_plan_fields(BcLir *c, Value const *callee, TyInlinePlan const *plan, TyInlineKind kind,
               Class *self_class, Class **arg_classes, BcPlanField *fields)
{
        for (i32 i = 0; i < plan->count; ++i) {
                TyInlineInsn const *insn = &plan->insns[i];
                if (insn->op != TY_INLINE_FIELD && insn->op != TY_INLINE_STORE_FIELD) {
                        continue;
                }
                Class *class = NULL;
                if (kind == TY_INLINE_METHOD && insn->local == plan->self_local) {
                        class = self_class;
                } else if (insn->local >= 0 && insn->local < plan->argc) {
                        class = arg_classes != NULL ? arg_classes[insn->local] : NULL;
                        if (class == NULL) {
                                class = bc_param_class(c, callee, insn->local);
                        }
                }
                if (class == NULL || class->i < CLASS_PRIMITIVE
                    || insn->member < 0 || insn->member >= vN(class->offsets_r)) {
                        return false;
                }
                u16 offset = v__(class->offsets_r, insn->member);
                if (offset == OFF_NOT_FOUND || (offset >> OFF_SHIFT) != OFF_FIELD) {
                        return false;
                }
                fields[i] = (BcPlanField) { .class = class, .offset = offset };
        }
        return true;
}

static LirReg
bc_plan_float(BcLir *c, LirReg type, i32 offset, bool strict, LirLabel slow)
{
        LirLabel integer = lir_label(c->L);
        LirLabel ready = lir_label(c->L);
        LirReg x = lir_reg(c->L, LIR_F64);
        bc_branch(c, LIR_NE, lir_r(type), lir_i(VALUE_REAL), strict ? slow : integer);
        LirOpnd mem = lir_m(c->ops, LIR_NONE, 1, offset + offsetof(Value, real));
        c->ok = c->ok && lir_emit_to(c->L, LIR_LD_F64, x, &mem, 1);
        bc_jump(c, ready);
        bc_bind(c, integer);
        if (!strict) {
                bc_branch(c, LIR_NE, lir_r(type), lir_i(VALUE_INTEGER), slow);
                LirReg z = bc_load(c, LIR_LD_I64, LIR_I64, c->ops, offset + offsetof(Value, z));
                LirOpnd convert = lir_r(z);
                c->ok = c->ok && lir_emit_to(c->L, LIR_I2F, x, &convert, 1);
        } else {
                bc_jump(c, slow);
        }
        bc_bind(c, ready);
        return x;
}

static void
bc_plan_arith(BcLir *c, u8 op, i32 left, i32 right, LirLabel slow)
{
        i32 a = left * sizeof (Value);
        i32 b = right * sizeof (Value);
        LirLabel reals = lir_label(c->L);
        LirLabel done = lir_label(c->L);
        LirReg at = bc_type_at(c, left);
        LirReg bt = bc_type_at(c, right);
        bc_branch(c, LIR_NE, lir_r(at), lir_i(VALUE_INTEGER), reals);
        bc_branch(c, LIR_NE, lir_r(bt), lir_i(VALUE_INTEGER), reals);
        LirReg x = bc_load(c, LIR_LD_I64, LIR_I64, c->ops, a + offsetof(Value, z));
        LirReg y = bc_load(c, LIR_LD_I64, LIR_I64, c->ops, b + offsetof(Value, z));
        LirOp iop;
        LirOp fop;
        bool compare = false;
        LirCC icc = LIR_EQ;
        LirCC fcc = LIR_FEQ;
        switch (op) {
        case TY_INLINE_ADD: iop = LIR_ADD; fop = LIR_FADD; break;
        case TY_INLINE_SUB: iop = LIR_SUB; fop = LIR_FSUB; break;
        case TY_INLINE_MUL: iop = LIR_MUL; fop = LIR_FMUL; break;
        case TY_INLINE_DIV: iop = LIR_SDIV; fop = LIR_FDIV; break;
        case TY_INLINE_EQ:  iop = LIR_ADD; fop = LIR_FADD; icc = LIR_EQ; fcc = LIR_FEQ; compare = true; break;
        case TY_INLINE_NE:  iop = LIR_ADD; fop = LIR_FADD; icc = LIR_NE; fcc = LIR_FNE; compare = true; break;
        case TY_INLINE_LT:  iop = LIR_ADD; fop = LIR_FADD; icc = LIR_LT; fcc = LIR_FLT; compare = true; break;
        case TY_INLINE_GT:  iop = LIR_ADD; fop = LIR_FADD; icc = LIR_GT; fcc = LIR_FGT; compare = true; break;
        case TY_INLINE_LE:  iop = LIR_ADD; fop = LIR_FADD; icc = LIR_LE; fcc = LIR_FLE; compare = true; break;
        default:            iop = LIR_ADD; fop = LIR_FADD; icc = LIR_GE; fcc = LIR_FGE; compare = true; break;
        }
        if (op == TY_INLINE_DIV) {
                bc_branch(c, LIR_EQ, lir_r(y), lir_i(0), slow);
                bc_branch(c, LIR_EQ, lir_r(y), lir_i(-1), slow);
        }
        LirReg r;
        if (compare) {
                LirOpnd args[] = { lir_cc(icc), lir_r(x), lir_r(y) };
                r = bc_value(c, LIR_SETCC, LIR_I64, args, countof(args));
                bc_store(c, LIR_ST64, c->ops, a, lir_i(VALUE_BOOLEAN));
        } else {
                LirOpnd args[] = { lir_r(x), lir_r(y) };
                r = bc_value(c, iop, LIR_I64, args, countof(args));
        }
        bc_store(c, LIR_ST64, c->ops, a + offsetof(Value, z), lir_r(r));
        bc_jump(c, done);
        bc_bind(c, reals);
        bool equality = op == TY_INLINE_EQ || op == TY_INLINE_NE;
        LirReg fx = bc_plan_float(c, at, a, equality, slow);
        LirReg fy = bc_plan_float(c, bt, b, equality, slow);
        if (op == TY_INLINE_DIV) {
                LirOpnd bits = lir_r(fy);
                LirReg raw = bc_value(c, LIR_BITCAST, LIR_I64, &bits, 1);
                LirOpnd shift[] = { lir_r(raw), lir_i(1) };
                LirReg magnitude = bc_value(c, LIR_SHL, LIR_I64, shift, countof(shift));
                bc_branch(c, LIR_EQ, lir_r(magnitude), lir_i(0), slow);
        }
        if (compare) {
                LirOpnd args[] = { lir_cc(fcc), lir_r(fx), lir_r(fy) };
                LirReg flag = bc_value(c, LIR_FSETCC, LIR_I64, args, countof(args));
                bc_store(c, LIR_ST64, c->ops, a, lir_i(VALUE_BOOLEAN));
                bc_store(c, LIR_ST64, c->ops, a + offsetof(Value, z), lir_r(flag));
        } else {
                LirOpnd args[] = { lir_r(fx), lir_r(fy) };
                LirReg fr = bc_value(c, fop, LIR_F64, args, countof(args));
                bc_store(c, LIR_ST64, c->ops, a, lir_i(VALUE_REAL));
                bc_store(c, LIR_ST_F64, c->ops, a + offsetof(Value, real), lir_r(fr));
        }
        bc_bind(c, done);
}

static bool
bc_emit_plan(BcLir *c, Value const *callee, TyInlinePlan const *plan, TyInlineKind kind,
             i32 base, LirReg self, Class *self_class, Class **arg_classes, i32 out, LirLabel slow)
{
        BcPlanField fields[TY_INLINE_MAX_INSNS] = {0};
        if (plan->count == 0 || plan->depths[plan->count] != 1
            || !bc_plan_fields(c, callee, plan, kind, self_class, arg_classes, fields)) {
                return false;
        }
        i32 scratch = c->sp;
        bool guarded[TY_INLINE_MAX_ARGS + 1] = {0};
        for (i32 i = 0; i < plan->count; ++i) {
                TyInlineInsn const *insn = &plan->insns[i];
                if (insn->op != TY_INLINE_FIELD && insn->op != TY_INLINE_STORE_FIELD) {
                        continue;
                }
                if (kind == TY_INLINE_METHOD && insn->local == plan->self_local) {
                        continue;
                }
                if (guarded[insn->local]) {
                        continue;
                }
                guarded[insn->local] = true;
                LirReg source = bc_plan_source(c, plan, kind, base, self, insn->local);
                LirReg type = bc_load(c, LIR_LD_U8, LIR_I64, source, offsetof(Value, type));
                bc_branch(c, LIR_NE, lir_r(type), lir_i(VALUE_OBJECT), slow);
                LirReg id = bc_load(c, LIR_LD_I32, LIR_I64, source, offsetof(Value, class));
                bc_branch(c, LIR_NE, lir_r(id), lir_i(fields[i].class->i), slow);
        }
        LirLabel labels[TY_INLINE_MAX_INSNS + 1];
        for (i32 i = 0; i <= plan->count; ++i) {
                labels[i] = LIR_NONE;
        }
        for (i32 i = 0; i < plan->count; ++i) {
                TyInlineInsn const *insn = &plan->insns[i];
                if ((insn->op == TY_INLINE_BRANCH_TRUE || insn->op == TY_INLINE_JUMP)
                    && labels[insn->target] == LIR_NONE) {
                        labels[insn->target] = lir_label(c->L);
                }
        }
        for (i32 i = 0; i < plan->count; ++i) {
                if (labels[i] != LIR_NONE) {
                        bc_bind(c, labels[i]);
                }
                i32 depth = plan->depths[i];
                i32 top = scratch + depth;
                TyInlineInsn const *insn = &plan->insns[i];
                switch (insn->op) {
                case TY_INLINE_LOCAL: {
                        LirReg source = bc_plan_source(c, plan, kind, base, self, insn->local);
                        bc_value_copy(c, c->ops, top * sizeof (Value), source, 0);
                        break;
                }
                case TY_INLINE_FIELD: {
                        LirReg source = bc_plan_source(c, plan, kind, base, self, insn->local);
                        LirReg object = bc_load(c, LIR_LD_I64, LIR_PTR, source, offsetof(Value, object));
                        i32 slot = offsetof(TyObject, slots) + (fields[i].offset & OFF_MASK) * sizeof (Value);
                        bc_value_copy(c, c->ops, top * sizeof (Value), object, slot);
                        break;
                }
                case TY_INLINE_INTEGER:
                        bc_put_scalar(c, top, VALUE_INTEGER, lir_i(insn->integer));
                        break;
                case TY_INLINE_REAL: {
                        u64 bits;
                        memcpy(&bits, &insn->real, sizeof bits);
                        bc_put_scalar(c, top, VALUE_REAL, lir_i((i64)bits));
                        break;
                }
                case TY_INLINE_BOOLEAN:
                        bc_put_scalar(c, top, VALUE_BOOLEAN, lir_i(insn->integer != 0));
                        break;
                case TY_INLINE_STORE_FIELD: {
                        bc_put_scalar(c, top, VALUE_BOOLEAN, lir_i(insn->integer != 0));
                        LirReg source = bc_plan_source(c, plan, kind, base, self, insn->local);
                        LirReg object = bc_load(c, LIR_LD_I64, LIR_PTR, source, offsetof(Value, object));
                        i32 slot = offsetof(TyObject, slots) + (fields[i].offset & OFF_MASK) * sizeof (Value);
                        bc_value_copy(c, object, slot, c->ops, top * sizeof (Value));
                        break;
                }
                case TY_INLINE_POP:
                        break;
                case TY_INLINE_ADD:
                case TY_INLINE_SUB:
                case TY_INLINE_MUL:
                case TY_INLINE_DIV:
                case TY_INLINE_EQ:
                case TY_INLINE_NE:
                case TY_INLINE_LT:
                case TY_INLINE_GT:
                case TY_INLINE_LE:
                case TY_INLINE_GE:
                        bc_plan_arith(c, insn->op, top - 2, top - 1, slow);
                        break;
                case TY_INLINE_BRANCH_TRUE: {
                        LirReg flag = bc_load(c, LIR_LD_I64, LIR_I64, c->ops,
                                              (top - 1) * sizeof (Value) + offsetof(Value, z));
                        bc_branch(c, LIR_NE, lir_r(flag), lir_i(0), labels[insn->target]);
                        break;
                }
                case TY_INLINE_JUMP:
                        bc_jump(c, labels[insn->target]);
                        break;
                default:
                        return false;
                }
        }
        if (labels[plan->count] != LIR_NONE) {
                bc_bind(c, labels[plan->count]);
        }
        bc_value_copy(c, c->ops, out * sizeof (Value), c->ops, scratch * sizeof (Value));
        return true;
}

static bool
bc_try_plan(BcLir *c, Value const *callee, TyInlineKind kind, i32 argc, i32 base, LirReg self,
            Class *self_class, Class **arg_classes, i32 out, LirLabel done)
{
        TyInlinePlan plan;
        BcPlanField fields[TY_INLINE_MAX_INSNS] = {0};
        if (getenv("TY_JIT_NO_INLINE") != NULL || !ty_inline_analyze(callee, kind, argc, &plan)
            || plan.count == 0 || plan.depths[plan.count] != 1
            || c->sp + plan.max_stack + 1 > c->max_sp + 200
            || !bc_plan_fields(c, callee, &plan, kind, self_class, arg_classes, fields)) {
                return false;
        }
        LirLabel bail = lir_label(c->L);
        bc_emit_plan(c, callee, &plan, kind, base, self, self_class, arg_classes, out, bail);
        bc_jump(c, done);
        bc_bind(c, bail);
        return true;
}

static Class *
bc_slot_class(BcLir *c, i32 slot)
{
        if (c->vs == NULL || slot < 0 || c->vs[slot].hint == T2_TYPE_INVALID) {
                return NULL;
        }
        return expected_class_of(c->ctx, c->vs[slot].hint);
}

static bool
bc_inline_operator(BcLir *c, u8 instr)
{
        if (c->vs == NULL || c->dynamic || c->sp < 2) {
                return false;
        }
        Class *left = bc_slot_class(c, c->sp - 2);
        Class *right = bc_slot_class(c, c->sp - 1);
        if (left == NULL || right == NULL || left->i < CLASS_PRIMITIVE || right->i < CLASS_PRIMITIVE) {
                return false;
        }
        int op;
        switch (instr) {
        case INSTR_ADD: op = OP_ADD; break;
        case INSTR_SUB: op = OP_SUB; break;
        case INSTR_MUL: op = OP_MUL; break;
        case INSTR_LT:  op = OP_LT;  break;
        case INSTR_GT:  op = OP_GT;  break;
        case INSTR_LEQ: op = OP_LEQ; break;
        case INSTR_GEQ: op = OP_GEQ; break;
        default:
                return false;
        }
        int ref = op_dispatch(c->ctx, op, left->i, right->i);
        if (ref < 0 || ref >= vN(Globals)) {
                return false;
        }
        Value *callee = v_(Globals, ref);
        TyInlinePlan plan;
        BcPlanField fields[TY_INLINE_MAX_INSNS] = {0};
        Class *args[2] = { left, right };
        bool inline_plan = getenv("TY_JIT_NO_INLINE") == NULL
                        && ty_inline_analyze(callee, TY_INLINE_OPERATOR, 2, &plan)
                        && plan.count != 0 && plan.depths[plan.count] == 1
                        && bc_plan_fields(c, callee, &plan, TY_INLINE_OPERATOR, NULL, args, fields);
        bool native = callee->type == VALUE_FUNCTION && param_count_of(callee) == 2
                   && rest_idx_of(callee) == -1 && kwargs_idx_of(callee) == -1
                   && !is_starred(callee) && callee->info[FUN_INFO_BOUND] <= 34;
        if (!inline_plan && !native) {
                return false;
        }
        TyInlineTarget *target = ty_inline_operator_target(left, right, op, ref, callee);
        LirLabel slow = lir_label(c->L);
        LirLabel done = lir_label(c->L);
        LirReg a = bc_addr(c, c->ops, (c->sp - 2) * sizeof (Value));
        LirReg b = bc_addr(c, c->ops, (c->sp - 1) * sizeof (Value));
        LirType types[] = { LIR_TYPE_PTR, LIR_TYPE_PTR, LIR_TYPE_PTR, LIR_TYPE_PTR };
        LirOpnd call[] = { lir_r(c->ty), lir_r(a), lir_r(b), lir_i((uptr)target) };
        LirReg ok = bc_call(c, ty_inline_guard_operator, LIR_TYPE_BOOL, types, call, countof(call));
        bc_branch(c, LIR_EQ, lir_r(ok), lir_i(0), slow);
        if (inline_plan) {
                bc_emit_plan(c, callee, &plan, TY_INLINE_OPERATOR, c->sp - 2, LIR_NONE, NULL, args, c->sp - 2, slow);
                bc_jump(c, done);
        } else {
                LirOpnd where = lir_i((uptr)&Globals.items);
                LirReg address = bc_value(c, LIR_LI, LIR_PTR, &where, 1);
                LirReg globals = bc_load(c, LIR_LD_I64, LIR_PTR, address, 0);
                LirReg fn = bc_addr(c, globals, ref * sizeof (Value));
                bc_inline_call(c, fn, callee, c->sp - 2, 2, LIR_NONE, slow, done);
        }
        bc_bind(c, slow);
        bc_numeric(c, instr);
        bc_bind(c, done);
        return true;
}
