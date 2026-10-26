static bool
fast_complement(BcLir *c, BcLirNode const *node, char const *ip)
{
        if (node->op != INSTR_UNARY_OP || load_i32(ip + 1) != OP_COMPL) {
                return false;
        }

        LirLabel slow = newlabel(c);
        LirLabel done = newlabel(c);
        i32      top  = c->sp - 1;

        unless(c, tag_of(c, top), VALUE_INTEGER, slow);
        stq(c, c->ops, vat(top) + VOFF(z), lir_r(unop(c, LIR_NOT, LIR_I64, lir_r(int_at(c, top)))));
        jump(c, done);

        bind(c, slow);
        sync_sp(c);
        tycall(c, vm_jit_misc, LT_VOID, imm32(node->op), imm32(OP_COMPL), pimm(ip + 5));

        bind(c, done);

        return true;
}

static void
misc(BcLir *c, BcLirNode const *node, char const *ip)
{
        i32         n    = 0;
        void const *data = NULL;

        if (fast_complement(c, node, ip)) {
                return;
        }

        if (node->op == INSTR_JUMP_WTF && !c->dynamic && dest(c, node) != LIR_NONE) {
                jcc(c, LIR_NE, lir_r(tag_of(c, c->sp - 1)), lir_i(VALUE_NIL), dest(c, node));
                return;
        }

        sync_sp(c);

        switch (node->op) {
        case INSTR_TRAP_TY:
                flush_active(c);
                deopt_why(c, JIT_WHY_TRAP, 0);
                leave(c, JIT_PACK(JIT_DEOPT, ip - c->code));
                return;

        case INSTR_RETURN_IF_NOT_NONE: {
                LirReg   type = tag_of(c, c->sp - 1);
                LirLabel next = newlabel(c);
                jcc(c, LIR_EQ, lir_r(type), lir_i(VALUE_NONE), next);
                leave(c, JIT_RETURN);
                bind(c, next);
                return;
        }

        case INSTR_JUMP_WTF:
        case INSTR_NONE_IF_NOT:
        case INSTR_SKIP_CHECK: {
                LirReg taken = tycall(c, vm_jit_extra_branch, LT_BOOL, imm32(node->op));
                jnz(c, taken, dest(c, node));
                return;
        }

        case INSTR_UNARY_OP:
        case INSTR_BINARY_OP:
        case INSTR_FIX_TO:
        case INSTR_REVERSE:
        case INSTR_OPERATOR:
                n    = load_i32(ip + 1);
                data = ip + 5;
                break;

        case INSTR_EXEC_CODE:
        case INSTR_EVAL:
        case INSTR_RENDER_TEMPLATE:
        case INSTR_NAMESPACE:
                data = peek(void const *, ip + 1);
                break;

        case INSTR_COMPILE_REGEX:
        case INSTR_DEBUG:
                data = ip + 1;
                break;
        }

        tycall(c, vm_jit_misc, LT_VOID, imm32(node->op), imm32(n), pimm(data));

        if (node->op == INSTR_TRAP) {
                never_returns(c);
        }
}

static bool
static_push(u8 op)
{
        return (op == INSTR_BIND_STATIC)
            || (op == INSTR_SELF_STATIC_ACCESS)
            || (op == INSTR_STATIC_MEMBER_ACCESS);
}

static void
state(BcLir *c, BcLirNode const *node, char const *ip)
{
        u8          op   = node->op;
        i32         n    = 0;
        i32         z    = 0;
        void const *info = NULL;

        switch (op) {
        case INSTR_DECORATE:
                info = peek(void const *, ip + 1);
                break;

        case INSTR_TARGET_STATIC_MEMBER:
        case INSTR_STATIC_MEMBER_ACCESS:
        case INSTR_BIND_INSTANCE:
        case INSTR_BIND_GETTER:
        case INSTR_BIND_SETTER:
        case INSTR_BIND_STATIC:
                z = load_i32(ip + 5);
        case INSTR_LOAD_THREAD_LOCAL:
        case INSTR_TARGET_GLOBAL:
        case INSTR_TARGET_THREAD_LOCAL:
        case INSTR_TARGET_SELF_STATIC:
        case INSTR_INTO_METHOD:
        case INSTR_BIND_CLASS:
        case INSTR_SELF_STATIC_ACCESS:
                n = load_i32(ip + 1);
                break;
        }

        sync_sp(c);

        switch (op) {
        case INSTR_JUMP_IF_INIT: {
                LirReg init = tycall(c, vm_jit_check_init, LT_BOOL);
                jnz(c, init, dest(c, node));
                return;
        }

        case INSTR_LOAD_THREAD_LOCAL: {
                LirReg slot = tycall(c, vm_jit_state_slot, LT_PTR, imm32(n), bimm(true));
                copy(c, c->ops, vat(c->sp++), slot, 0);
                return;
        }

        case INSTR_TARGET_GLOBAL:
        case INSTR_TARGET_THREAD_LOCAL:
        case INSTR_TARGET_SELF_STATIC:
        case INSTR_TARGET_STATIC_MEMBER:
        case INSTR_TARGET_DYN_MEMBER:
                tycall(c, vm_jit_target, LT_VOID, imm32(op), imm32(n), imm32(z));
                c->sp -= (op == INSTR_TARGET_DYN_MEMBER) ? 2 : 0;
                return;

        case INSTR_PRE_INC:
        case INSTR_POST_INC:
        case INSTR_PRE_DEC:
        case INSTR_POST_DEC:
                tycall(c, vm_jit_mutation, LT_VOID, imm32(op));
                c->sp += 1;
                return;

        case INSTR_DROP:
        case INSTR_DISCARD_DROP_GROUP:
        case INSTR_PUSH_DROP_GROUP:
        case INSTR_PUSH_DROP:
        case INSTR_PUSH_DEFER_GROUP:
        case INSTR_DEFER:
        case INSTR_CLEANUP:
        case INSTR_ENTER:
                tycall(c, vm_jit_scope, LT_VOID, imm32(op));
                c->sp -= (op == INSTR_DEFER);
                return;

        default:
                tycall(
                        c,
                        vm_jit_binding,
                        LT_VOID,
                        imm32(op),
                        imm32(n),
                        imm32(z),
                        pimm(info)
                );
                c->sp += static_push(op);
                return;
        }
}

static void
reserve(Ty *ty, Value *base, i32 n)
{
        usize need = base - ty->stack.items + n;

        if (need > ty->stack.capacity) {
                xvR(ty->stack, need);
        }
}

static void
tail(Ty *ty, Value *locals, Value *args, i32 argc, i32 bound, i32 kept)
{
        jit_rt_tail_loop(locals, args, argc, bound, kept);
        ty->stack.count = locals - ty->stack.items + bound;
}

static void
tail_call(BcLir *c, BcLirNode const *node)
{
        safepoint(c, node->deopt);

        count_entry(c);

        if (
                !c->dynamic
             && (c->base_index != LIR_NONE)
             && (node->argc <= 16)
             && (c->bound <= 48)
        ) {
                restart(c, c->sp - node->argc, node->argc, node->member);
                return;
        }

        LirReg args = slot_of(c, c->sp - node->argc);

        tycall(
                c,
                tail,
                LT_VOID,
                preg(c->locals),
                preg(args),
                imm32(node->argc),
                imm32(c->bound),
                imm32(node->member)
        );

        jump(c, c->nodes[0].label);
}

static void
finish_op(BcLir *c, BcLirNode const *node, char const *ip)
{
        sync_sp(c);

        switch (node->op) {
        case INSTR_TRY_YIELD_FROM: {
                LirReg direct = tycall(c, vm_jit_yield_from, LT_BOOL);
                jnz(c, direct, dest(c, node));
                return;
        }

        case INSTR_TAIL_CALL:
                tail_call(c, node);
                return;

        case INSTR_DEFINE_TAG:
        case INSTR_DEFINE_CLASS:
        case INSTR_INIT_STATIC_FIELD:
                tycall(c, vm_jit_declaration, LT_VOID, pimm(ip));
                return;

        default:
                tycall(c, vm_jit_failure, LT_VOID, imm32(node->op), pimm(ip));
                leave(c, JIT_RETURN);
                return;
        }
}
