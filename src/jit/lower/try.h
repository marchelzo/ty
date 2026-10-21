static void
dynamic_ops(BcLir *c)
{
        LirReg base  = ldp(c, c->ty, offsetof(Ty, stack.items));
        LirReg count = ldq(c, c->ty, offsetof(Ty, stack.count));
        LirReg index = binop(c, LIR_SUB, LIR_I64, lir_r(count), lir_i(c->sp));

        index = binop(c, LIR_SHL, LIR_I64, lir_r(index), lir_i(5));
        vset(c, LIR_LEA, c->ops, lir_m(base, index, 1, 0));
}

static void
restore_locals(BcLir *c)
{
        LirReg base = ldp(c, c->ty, offsetof(Ty, stack.items));
        vset(c, LIR_LEA, c->locals, lir_m(base, c->fp, 1, 0));
}

static void *
push_try(Ty *ty, Value *top, char *catch, char *finally, char *end)
{
        ty->stack.count = top - ty->stack.items;
        return vm_jit_push_try(ty, catch, finally, end);
}

static void
sps_save(Ty *ty)
{
        xvP(ty->st->sps, ty->stack.count);
}

static void
sps_restore(Ty *ty)
{
        ty->stack.count = v_L(ty->st->sps);
}

static void
sps_pop(Ty *ty)
{
        ty->stack.count = vXx(ty->st->sps);
}

static void
sps_pop1(Ty *ty)
{
        ty->stack.count = vXx(ty->st->sps) - 1;
}

static void
sps_pop2(Ty *ty)
{
        ty->stack.count = vXx(ty->st->sps) - 2;
}

static void
sps_drop(Ty *ty)
{
        vXx(ty->st->sps);
}

static void
clear_extra(Ty *ty)
{
        while (ty->stack.items[ty->stack.count - 1].type != VALUE_SENTINEL) {
                ty->stack.count -= 1;
        }

        ty->stack.count -= 1;
}

static void
inline_sps_save(BcLir *c, LirReg st, LirReg n)
{
        LirLabel slow = newlabel(c);
        LirLabel done = newlabel(c);
        LirReg   cap  = ldq(c, st, offsetof(co_state, sps.capacity));

        jcc(c, LIR_UGE, lir_r(n), lir_r(cap), slow);

        LirReg top = (c->sp == 0) ? c->base_index : plus(c, c->base_index, c->sp);
        LirReg xs  = ldp(c, st, offsetof(co_state, sps.items));

        vset(c, LIR_ST64, LIR_NONE, lir_m(xs, n, sizeof (usize), 0), lir_r(top));
        stq(c, st, offsetof(co_state, sps.count), lir_r(plus(c, n, 1)));
        jump(c, done);

        bind(c, slow);
        tycall(c, sps_save, LT_VOID);

        bind(c, done);
}

static bool
inline_sps(BcLir *c, u8 op)
{
        i32 drop;

        switch (op) {
        case INSTR_SAVE_STACK_POS:     drop = -1; break;
        case INSTR_DROP_STACK_POS:     drop = -2; break;
        case INSTR_POP_STACK_POS:      drop =  0; break;
        case INSTR_POP_STACK_POS_POP:  drop =  1; break;
        case INSTR_POP_STACK_POS_POP2: drop =  2; break;
        default:                       return false;
        }

        if (c->dynamic || c->compact || c->base_index == LIR_NONE) {
                return false;
        }

        LirReg st = ldp(c, c->ty, offsetof(Ty, st));
        LirReg n  = ldq(c, st, offsetof(co_state, sps.count));

        if (drop == -1) {
                inline_sps_save(c, st, n);
                return true;
        }

        LirReg last = plus(c, n, -1);

        stq(c, st, offsetof(co_state, sps.count), lir_r(last));

        if (drop >= 0) {
                LirReg  xs    = ldp(c, st, offsetof(co_state, sps.items));
                LirOpnd at    = lir_m(xs, last, sizeof (usize), 0);
                LirReg  count = unop(c, LIR_LD_I64, LIR_I64, at);

                count = (drop == 0) ? count : plus(c, count, -drop);
                stq(c, c->ty, offsetof(Ty, stack.count), lir_r(count));
        }

        return true;
}

static void
saved_stack(BcLir *c, u8 op)
{
        void *helper;

        switch (op) {
        case INSTR_SAVE_STACK_POS:     helper = sps_save;    break;
        case INSTR_RESTORE_STACK_POS:  helper = sps_restore; break;
        case INSTR_POP_STACK_POS:      helper = sps_pop;     break;
        case INSTR_POP_STACK_POS_POP:  helper = sps_pop1;    break;
        case INSTR_POP_STACK_POS_POP2: helper = sps_pop2;    break;
        case INSTR_DROP_STACK_POS:     helper = sps_drop;    break;
        default:                       helper = clear_extra; break;
        }

        if (
                c->dynamic
             || (op == INSTR_SAVE_STACK_POS)
             || (op == INSTR_DROP_STACK_POS)
             || (op == INSTR_CLEAR_EXTRA)
        ) {
                sync_sp(c);
        }

        if (!inline_sps(c, op)) {
                tycall(c, helper, LT_VOID);
        }
}

static bool
sync_after(u8 op)
{
        switch (op) {
        case INSTR_TRY_YIELD_FROM:
        case INSTR_TAIL_CALL:
        case INSTR_DEFINE_TAG:
        case INSTR_DEFINE_CLASS:
        case INSTR_INIT_STATIC_FIELD:
        case INSTR_BAD_CALL:
        case INSTR_BAD_ASSIGN:
        case INSTR_BAD_DISPATCH:
        case INSTR_EXEC_CODE:
        case INSTR_DEBUG:
        case INSTR_REVERSE:
        case INSTR_RENDER_TEMPLATE:
        case INSTR_NAMESPACE:
        case INSTR_TRACE:
        case INSTR_OPERATOR:
        case INSTR_READ_INDEX:
        case INSTR_UNARY_OP:
        case INSTR_QUESTION:
        case INSTR_TO_REGEX:
        case INSTR_COMPILE_REGEX:
        case INSTR_EVAL:
        case INSTR_GET_TAG:
        case INSTR_NONE_IF_NIL:
        case INSTR_RETURN_IF_NOT_NONE:
        case INSTR_BINARY_OP:
        case INSTR_SLICE:
        case INSTR_GET_NEXT:
        case INSTR_FIX_TO:
        case INSTR_FIX_EXTRA:
        case INSTR_TRAP:
        case INSTR_TRAP_TY:
        case INSTR_JUMP_WTF:
        case INSTR_NONE_IF_NOT:
        case INSTR_SKIP_CHECK:
        case INSTR_ENSURE_LEN:
        case INSTR_ENSURE_LEN_TUPLE:
        case INSTR_ENSURE_EQUALS_VAR:
        case INSTR_TRY_UNAPPLY:
        case INSTR_TRY_ASSIGN_NON_NIL:
        case INSTR_TRY_RANGE:
        case INSTR_TRY_INCRANGE:
        case INSTR_ENSURE_DICT:
        case INSTR_ENSURE_CONTAINS:
        case INSTR_ENSURE_SAME_KEYS:
        case INSTR_TRY_INDEX:
        case INSTR_INDEX_TUPLE:
        case INSTR_TRY_INDEX_TUPLE:
        case INSTR_TRY_MEMBER:
        case INSTR_TRY_TUPLE_MEMBER:
        case INSTR_TRY_TAG_POP:
        case INSTR_TRY_REGEX:
        case INSTR_TRY_STEAL_TAG:
        case INSTR_ARRAY_REST:
        case INSTR_TUPLE_REST:
        case INSTR_RECORD_REST:
        case INSTR_JNI:
        case INSTR_JII:
        case INSTR_MATCH_TAG:
        case INSTR_MATCH_STRING:
        case INSTR_ARRAY_COMPR:
        case INSTR_SET_COMPR:
        case INSTR_DICT_COMPR:
        case INSTR_LOOP_ITER:
        case INSTR_LOOP_CHECK:
        case INSTR_SPREAD_CHECK:
        case INSTR_GATHER_TUPLE:
        case INSTR_ARRAY:
        case INSTR_SET:
        case INSTR_DICT:
        case INSTR_DEFAULT_DICT:
        case INSTR_RETHROW:
        case INSTR_FINALLY:
        case INSTR_END_TRY:
        case INSTR_RESTORE_STACK_POS:
        case INSTR_POP_STACK_POS:
        case INSTR_POP_STACK_POS_POP2:
        case INSTR_POP_STACK_POS_POP:
        case INSTR_CLEAR_EXTRA:
        case INSTR_THROW:
        case INSTR_RETURN:
        case INSTR_RETURN_PRESERVE_CTX:
        case INSTR_JUMP:
                return false;

        default:
                return true;
        }
}

inline static void const *
code_at(BcLir const *c, i32 off)
{
        return (off < 0) ? NULL : c->code + off;
}

inline static LirLabel
label_at(BcLir const *c, i32 off)
{
        return c->nodes[off].label;
}

static void
lower_try(BcLir *c, BcLirNode const *t)
{
        LirLabel normal  = newlabel(c);
        LirLabel closing = newlabel(c);
        LirReg   top    = slot_of(c, c->sp);
        LirReg   env    = tycall(
                c,
                push_try,
                LT_PTR,
                preg(top),
                pimm(code_at(c, t->catch_to)),
                pimm(code_at(c, t->finally_to)),
                pimm(code_at(c, t->end_to))
        );
        LirReg status = ccallf(c, _setjmp, LT_I32, LIR_RETURNS_TWICE, preg(env));

        jz(c, status, normal);
        restore_locals(c);
        stq(c, c->ty, offsetof(Ty, ip), lir_i((uptr)&JIT));
        if (t->finally_to >= 0) {
                jcc(c, LIR_EQ, lir_r(status), lir_i(2), closing);
        }
        jump(c, label_at(c, t->catch_to));

        if (t->finally_to >= 0) {
                bind(c, closing);
                jump(c, label_at(c, t->finally_to));
        }

        bind(c, normal);
}

static void
lower_end_try(BcLir *c, BcLirNode const *node, BcLirNode const *t)
{
        LirLabel returned = newlabel(c);
        LirReg   end;

        sync_sp(c);
        end = tycall(c, jit_rt_end_try, LT_PTR);
        jnz(c, end, returned);
        tycall(c, vm_jit_end_try_rethrow, LT_VOID);
        v__(c->L->insts, c->last_call).flags |= LIR_NORETURN;

        bind(c, returned);

#define RESUME(off) jcc(        \
        c,                              \
        LIR_EQ,                         \
        lir_r(end),                     \
        lir_i((uptr)code_at(c, (off))), \
        label_at(c, (off))              \
)
        if (t->end_to >= 0) {
                RESUME(t->end_to);
        }

        for (i32 off = 0; off < c->size; ++off) {
                BcLirNode const *f = &c->nodes[off];
                if (
                        (f->next != 0)
                     && (f->op == INSTR_FINALLY)
                     && (f->owner == node->owner)
                     && (f->sp >= 0)
                ) {
                        RESUME(f->next);
                }
        }
#undef RESUME

        if (t->end_to >= 0) {
                jump(c, label_at(c, t->end_to));
        }
}

static void
lower_tryop(BcLir *c, BcLirNode const *node)
{
        BcLirNode const *t = &c->nodes[node->owner];

        switch (node->op) {
        case INSTR_TRY:
                lower_try(c, t);
                break;

        case INSTR_CATCH:
                tycall(c, jit_rt_catch, LT_VOID);
                break;

        case INSTR_POP_TRY:
                tycall(c, jit_rt_pop_try, LT_VOID);
                break;

        case INSTR_RETHROW:
                tycall(c, jit_rt_rethrow_setup, LT_VOID);
                jump(c, label_at(c, t->finally_to));
                break;

        case INSTR_FINALLY:
                tycall(c, jit_rt_finally_enter, LT_VOID, pimm(c->code + node->next));
                jump(c, label_at(c, t->finally_to));
                break;

        case INSTR_END_TRY:
                lower_end_try(c, node, t);
                break;

        default:
                c->ok = false;
                break;
        }
}
