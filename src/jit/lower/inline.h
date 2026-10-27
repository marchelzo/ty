typedef struct {
        Class *class;
        u16    offset;
} PlanField;

typedef struct {
        Value const   *callee;
        TyInlinePlan   plan;
        TyInlineKind   kind;
        i32            base;
        LirReg         self;
        Class         *self_class;
        Class        **arg_classes;
        PlanField      fields[TY_INLINE_MAX_INSNS];
} Plan;

static struct {
        LirOp iop;
        LirOp fop;
        LirCC icc;
        LirCC fcc;
        bool  cmp;
} const Arith[] = {
        [TY_INLINE_ADD] = { LIR_ADD,  LIR_FADD },
        [TY_INLINE_SUB] = { LIR_SUB,  LIR_FSUB },
        [TY_INLINE_MUL] = { LIR_MUL,  LIR_FMUL },
        [TY_INLINE_DIV] = { LIR_SDIV, LIR_FDIV },
        [TY_INLINE_MOD] = { LIR_SREM },
        [TY_INLINE_EQ]  = { .icc = LIR_EQ, .fcc = LIR_FEQ, .cmp = true },
        [TY_INLINE_NE]  = { .icc = LIR_NE, .fcc = LIR_FNE, .cmp = true },
        [TY_INLINE_LT]  = { .icc = LIR_LT, .fcc = LIR_FLT, .cmp = true },
        [TY_INLINE_GT]  = { .icc = LIR_GT, .fcc = LIR_FGT, .cmp = true },
        [TY_INLINE_LE]  = { .icc = LIR_LE, .fcc = LIR_FLE, .cmp = true },
        [TY_INLINE_GE]  = { .icc = LIR_GE, .fcc = LIR_FGE, .cmp = true }
};

inline static bool
is_self(Plan const *p, i32 local)
{
        return (p->kind == TY_INLINE_METHOD) && (local == p->plan.self_local);
}

inline static bool
is_arg(Plan const *p, i32 local)
{
        return (local >= 0) && (local < p->plan.argc);
}

inline static bool
touches_field(TyInlineInsn const *insn)
{
        return (insn->op == TY_INLINE_FIELD)
            || (insn->op == TY_INLINE_STORE_FIELD)
            || (insn->op == TY_INLINE_SET_FIELD);
}

static LirReg
plan_source(BcLir *c, Plan const *p, i32 local)
{
        if (is_arg(p, local)) {
                return slot_of(c, p->base + local);
        }

        return is_self(p, local) ? p->self : LIR_NONE;
}

static Class *
param_class(BcLir *c, Value const *callee, i32 index)
{
        Expr const *expr = expr_of(callee);

        if (expr == NULL || expr->fn->scope == NULL || index >= vN(expr->fn->scope->owned)) {
                return NULL;
        }

        return expected_class_of(c->ctx, v__(expr->fn->scope->owned, index)->type);
}

static Class *
local_class(BcLir *c, Plan const *p, i32 local)
{
        if (is_self(p, local)) {
                return p->self_class;
        }

        if (!is_arg(p, local)) {
                return NULL;
        }

        Class *class = (p->arg_classes != NULL) ? p->arg_classes[local] : NULL;

        return (class != NULL) ? class : param_class(c, p->callee, local);
}

static bool
plan_fields(BcLir *c, Plan *p)
{
        for (i32 i = 0; i < p->plan.count; ++i) {
                TyInlineInsn const *insn = &p->plan.insns[i];

                if (!touches_field(insn)) {
                        continue;
                }

                Class *class = local_class(c, p, insn->local);

                if (class == NULL || class->i < CLASS_PRIMITIVE) {
                        return false;
                }

                u16 off = offset_of(class, insn->member, false, OFF_FIELD);

                if (off == OFF_NOT_FOUND) {
                        return false;
                }

                p->fields[i] = (PlanField) { .class = class, .offset = off };
        }

        return true;
}

static bool
analyze(Plan *p, Value const *callee, TyInlineKind kind, i32 argc)
{
        p->callee = callee;
        p->kind   = kind;

        return (getenv("TY_JIT_NO_INLINE") == NULL)
            && ty_inline_analyze(callee, kind, argc, &p->plan)
            && (p->plan.count != 0)
            && (p->plan.depths[p->plan.count] == 1);
}

static void
nonzero_bits(BcLir *c, LirReg f, LirLabel slow)
{
        LirReg raw = unop(c, LIR_BITCAST, LIR_I64, lir_r(f));
        LirReg mag = binop(c, LIR_SHL, LIR_I64, lir_r(raw), lir_i(1));

        jz(c, mag, slow);
}

static void
plan_arith(BcLir *c, u8 op, i32 left, i32 right, LirLabel slow)
{
        i32      a     = vat(left);
        i32      b     = vat(right);
        LirLabel reals = newlabel(c);
        LirLabel done  = newlabel(c);
        LirReg   at    = tag_of(c, left);
        LirReg   bt    = tag_of(c, right);
        bool     cmp   = Arith[op].cmp;
        bool     div   = (op == TY_INLINE_DIV) || (op == TY_INLINE_MOD);
        bool     eq    = (op == TY_INLINE_EQ) || (op == TY_INLINE_NE);

        unless(c, at, VALUE_INTEGER, reals);
        unless(c, bt, VALUE_INTEGER, reals);

        LirReg x = ldq(c, c->ops, a + VOFF(z));
        LirReg y = ldq(c, c->ops, b + VOFF(z));

        if (div) {
                no_overflow_div(c, y, slow);
        }

        if (cmp) {
                LirReg r = setcc(c, LIR_SETCC, Arith[op].icc, x, y);
                stq(c, c->ops, a, lir_i(VALUE_BOOLEAN));
                stq(c, c->ops, a + VOFF(z), lir_r(r));
        } else {
                stq(c, c->ops, a + VOFF(z), lir_r(binr(c, Arith[op].iop, LIR_I64, x, y)));
        }

        jump(c, done);

        bind(c, reals);

        if (op == TY_INLINE_MOD) {
                jump(c, slow);
                bind(c, done);
                return;
        }

        LirReg fx = as_real(c, at, c->ops, a, eq, slow);
        LirReg fy = as_real(c, bt, c->ops, b, eq, slow);

        if (div) {
                nonzero_bits(c, fy, slow);
        }

        if (cmp) {
                LirReg r = setcc(c, LIR_FSETCC, Arith[op].fcc, fx, fy);
                stq(c, c->ops, a, lir_i(VALUE_BOOLEAN));
                stq(c, c->ops, a + VOFF(z), lir_r(r));
        } else {
                put_real(c, c->ops, a, binr(c, Arith[op].fop, LIR_F64, fx, fy));
        }

        bind(c, done);
}

static LirReg
plan_flag(BcLir *c, i32 slot, LirLabel slow)
{
        expect(c, c->ops, vat(slot), VALUE_BOOLEAN, slow);
        return ldx(c, LIR_LD_U8, LIR_I64, c->ops, vat(slot) + VOFF(boolean));
}

static void
plan_logic(BcLir *c, u8 op, i32 left, i32 right, LirLabel slow)
{
        LirReg x = plan_flag(c, left, slow);
        LirReg y = plan_flag(c, right, slow);
        LirOp  o = (op == TY_INLINE_AND) ? LIR_AND : LIR_OR;

        put_scalar(c, left, VALUE_BOOLEAN, lir_r(binr(c, o, LIR_I64, x, y)));
}

static void
plan_not(BcLir *c, i32 slot, LirLabel slow)
{
        LirReg x = plan_flag(c, slot, slow);

        put_scalar(c, slot, VALUE_BOOLEAN, lir_r(binop(c, LIR_XOR, LIR_I64, lir_r(x), lir_i(1))));
}

static void
guard_plan(BcLir *c, Plan const *p, LirLabel slow)
{
        bool guarded[TY_INLINE_MAX_ARGS + 1] = {0};

        for (i32 i = 0; i < p->plan.count; ++i) {
                TyInlineInsn const *insn = &p->plan.insns[i];

                if (
                        !touches_field(insn)
                     || is_self(p, insn->local)
                     || guarded[insn->local]
                ) {
                        continue;
                }

                guarded[insn->local] = true;
                guard_class(c, plan_source(c, p, insn->local), p->fields[i].class->i, slow);
        }
}

inline static i32
field_slot_of(Plan const *p, i32 i)
{
        return offsetof(TyObject, slots) + vat(p->fields[i].offset & OFF_MASK);
}

static LirReg
field_object(BcLir *c, Plan const *p, TyInlineInsn const *insn, i32 i, i32 *slot)
{
        *slot = field_slot_of(p, i);
        return ldp(c, plan_source(c, p, insn->local), VOFF(object));
}

static bool
plan_insn(BcLir *c, Plan const *p, i32 i, i32 top, LirLabel const *labels, LirLabel slow)
{
        TyInlineInsn const *insn = &p->plan.insns[i];
        i32                 slot;
        u64                 bits;

        switch (insn->op) {
        case TY_INLINE_LOCAL:
                copy(c, c->ops, vat(top), plan_source(c, p, insn->local), 0);
                break;

        case TY_INLINE_FIELD: {
                LirReg object = field_object(c, p, insn, i, &slot);
                copy(c, c->ops, vat(top), object, slot);
                break;
        }

        case TY_INLINE_STORE_FIELD: {
                put_scalar(c, top, VALUE_BOOLEAN, lir_i(insn->integer != 0));
                LirReg object = field_object(c, p, insn, i, &slot);
                copy(c, object, slot, c->ops, vat(top));
                break;
        }

        case TY_INLINE_SET_FIELD: {
                LirReg object = field_object(c, p, insn, i, &slot);
                copy(c, object, slot, c->ops, vat(top - 1));
                break;
        }

        case TY_INLINE_GIVEN: {
                LirReg arg = plan_source(c, p, insn->local);
                jcc(c, LIR_EQ, lir_r(tagat(c, arg, 0)), lir_i(VALUE_NIL), slow);
                break;
        }

        case TY_INLINE_INTEGER:
                put_scalar(c, top, VALUE_INTEGER, lir_i(insn->integer));
                break;

        case TY_INLINE_REAL:
                memcpy(&bits, &insn->real, sizeof bits);
                put_scalar(c, top, VALUE_REAL, lir_i((i64)bits));
                break;

        case TY_INLINE_BOOLEAN:
                put_scalar(c, top, VALUE_BOOLEAN, lir_i(insn->integer != 0));
                break;

        case TY_INLINE_POP:
                break;

        case TY_INLINE_ADD:
        case TY_INLINE_SUB:
        case TY_INLINE_MUL:
        case TY_INLINE_DIV:
        case TY_INLINE_MOD:
        case TY_INLINE_EQ:
        case TY_INLINE_NE:
        case TY_INLINE_LT:
        case TY_INLINE_GT:
        case TY_INLINE_LE:
        case TY_INLINE_GE:
                plan_arith(c, insn->op, top - 2, top - 1, slow);
                break;

        case TY_INLINE_AND:
        case TY_INLINE_OR:
                plan_logic(c, insn->op, top - 2, top - 1, slow);
                break;

        case TY_INLINE_NOT:
                plan_not(c, top - 1, slow);
                break;

        case TY_INLINE_BRANCH_TRUE: {
                LirReg flag = ldq(c, c->ops, vat(top - 1) + VOFF(z));
                jnz(c, flag, labels[insn->target]);
                break;
        }

        case TY_INLINE_JUMP:
                jump(c, labels[insn->target]);
                break;

        default:
                return false;
        }

        return true;
}

static void
emit_plan(BcLir *c, Plan const *p, i32 out, LirLabel slow)
{
        TyInlinePlan const *plan    = &p->plan;
        i32                 scratch = c->sp;
        LirLabel            labels[TY_INLINE_MAX_INSNS + 1];

        guard_plan(c, p, slow);

        for (i32 i = 0; i <= plan->count; ++i) {
                labels[i] = LIR_NONE;
        }

        for (i32 i = 0; i < plan->count; ++i) {
                TyInlineInsn const *insn = &plan->insns[i];
                bool jumps = (insn->op == TY_INLINE_BRANCH_TRUE)
                          || (insn->op == TY_INLINE_JUMP);
                if (jumps && labels[insn->target] == LIR_NONE) {
                        labels[insn->target] = newlabel(c);
                }
        }

        for (i32 i = 0; i < plan->count; ++i) {
                if (labels[i] != LIR_NONE) {
                        bind(c, labels[i]);
                }
                if (!plan_insn(c, p, i, scratch + plan->depths[i], labels, slow)) {
                        return;
                }
        }

        if (labels[plan->count] != LIR_NONE) {
                bind(c, labels[plan->count]);
        }

        copy(c, c->ops, vat(out), c->ops, vat(scratch));
}

static i32
same_field(TyInlinePlan const *plan, i32 i)
{
        TyInlineInsn const *insn = &plan->insns[i];

        for (i32 j = 0; j < i; ++j) {
                TyInlineInsn const *other = &plan->insns[j];

                if (
                        touches_field(other)
                     && (other->local == insn->local)
                     && (other->member == insn->member)
                ) {
                        return j;
                }
        }

        return i;
}

static bool
lane_method(BcLir *c, Plan const *p, i32 out, LirLabel failed);

static bool
try_plan(
        BcLir *c,
        Value const *callee,
        TyInlineKind kind,
        i32 argc,
        i32 base,
        LirReg self,
        Class *self_class,
        Class **arg_classes,
        i32 out,
        LirLabel done
)
{
        Plan p = {
                .base        = base,
                .self        = self,
                .self_class  = self_class,
                .arg_classes = arg_classes
        };

        if (
                !analyze(&p, callee, kind, argc)
             || (c->sp + p.plan.max_stack + 1 > c->max_sp + 200)
             || !plan_fields(c, &p)
        ) {
                return false;
        }

        LirLabel bail = newlabel(c);

        if (!lane_method(c, &p, out, bail)) {
                emit_plan(c, &p, out, bail);
        }

        jump(c, done);

        bind(c, bail);

        return true;
}

static Class *
slot_class(BcLir *c, i32 slot)
{
        if (c->vs == NULL || slot < 0 || c->vs[slot].hint == T2_TYPE_INVALID) {
                return NULL;
        }

        return expected_class_of(c->ctx, c->vs[slot].hint);
}

static int
binary_op(u8 instr)
{
        switch (instr) {
        case INSTR_ADD: return OP_ADD;
        case INSTR_SUB: return OP_SUB;
        case INSTR_MUL: return OP_MUL;
        case INSTR_LT:  return OP_LT;
        case INSTR_GT:  return OP_GT;
        case INSTR_LEQ: return OP_LEQ;
        case INSTR_GEQ: return OP_GEQ;
        default:        return -1;
        }
}

static bool
binary_native(Value const *fn)
{
        return (fn->type == VALUE_FUNCTION)
            && (param_count_of(fn) == 2)
            && (rest_idx_of(fn) == -1)
            && (kwargs_idx_of(fn) == -1)
            && !is_starred(fn)
            && (fn->info[FUN_INFO_BOUND] <= 34);
}

static bool
user_class(Class const *class)
{
        return (class != NULL) && (class->i >= CLASS_PRIMITIVE);
}

static bool
inline_operator(BcLir *c, u8 instr)
{
        if (c->vs == NULL || c->dynamic || c->sp < 2) {
                return false;
        }

        Class *left  = slot_class(c, c->sp - 2);
        Class *right = slot_class(c, c->sp - 1);
        int    op    = binary_op(instr);

        if (!user_class(left) || !user_class(right) || op < 0) {
                return false;
        }

        u32 epoch = atomic_load_explicit(&OperatorEpoch, memory_order_acquire);
        int ref   = op_dispatch(c->ctx, op, left->i, right->i);

        if (ref < 0 || ref >= vN(Globals)) {
                return false;
        }

        Value *callee = v_(Globals, ref);
        Class *args[] = { left, right };
        Plan   p      = {
                .base        = c->sp - 2,
                .self        = LIR_NONE,
                .arg_classes = args
        };
        bool   inlined = analyze(&p, callee, TY_INLINE_OPERATOR, 2) && plan_fields(c, &p);

        if (!inlined && !binary_native(callee)) {
                return false;
        }

        TyInlineTarget *target  = ty_inline_operator_target(left, right, op, ref, callee);
        LirLabel        slow    = newlabel(c);
        LirLabel        done    = newlabel(c);
        LirLabel        recheck = newlabel(c);
        LirLabel        checked = newlabel(c);
        LirReg          a       = slot_of(c, c->sp - 2);
        LirReg          b       = slot_of(c, c->sp - 1);

        guard_class(c, a, left->i, slow);
        guard_class(c, b, right->i, slow);
        unless(c, ldw(c, pval(c, &OperatorEpoch), 0), epoch, recheck);

        LirReg defined = global_addr(c, ref);

        expect(c, defined, 0, VALUE_FUNCTION, recheck);
        same_ptr(c, ldp(c, defined, VOFF(info)), callee->info, recheck);
        same_ptr(c, ldp(c, defined, VOFF(env)), callee->env, recheck);
        jump(c, checked);

        bind(c, recheck);

        LirReg ok = tycall(
                c,
                ty_inline_guard_operator,
                LT_BOOL,
                preg(a),
                preg(b),
                pimm(target)
        );

        jz(c, ok, slow);

        bind(c, checked);

        if (inlined) {
                emit_plan(c, &p, c->sp - 2, slow);
                jump(c, done);
        } else {
                inline_call(c, global_addr(c, ref), callee, c->sp - 2, 2, LIR_NONE, slow, done);
        }

        bind(c, slow);
        numeric(c, instr);

        bind(c, done);

        return true;
}
