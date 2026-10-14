static i32
bc_prepare_call(Ty *ty, Value *out, Value *fn, i32 argc)
{
        Value value = *fn;
        usize count = out - ty->stack.items + argc;
        gP(&value);
        ty->stack.count = count;
        JitFn *jit = jit_linkable_global(&value, argc) ? try_jit(ty, &value) : NULL;
        if (jit != NULL) {
                jit_fast_frame(ty, &value, NULL, argc);
                STAT(global_jit_call_fast);
                gX();
                return 1;
        }
        i32 result = jit_rt_call_trampoline(ty, ty->stack.items + count - argc, &value, argc);
        gX();
        return result;
}

static void
bc_sync_call(Ty *ty, Value *out, Value *fn, i32 argc)
{
        if (bc_prepare_call(ty, out, fn, argc) != 0) {
                vm_trampoline(ty);
        }
}

static void
bc_baked_method(Ty *ty, Value *top, Value *method, i64 packed, i32 argc, i32 op,
                char *ip)
{
        usize count = top - ty->stack.items;
        bool explicit = op == INSTR_CALL_METHOD || op == INSTR_TRY_CALL_METHOD;
        Value self = explicit ? top[-1] : *vm_get_self(ty);
        gP(&self);
        ty->stack.count = count - explicit;
        bool handled = jit_rt_baked_call(ty, &self, method, packed, argc) != 0;
        if (!handled) {
                bc_method(ty, ty->stack.items + count, op, 0, (i32)packed,
                          argc, 0, ip);
        }
        gX();
}

static bool
bc_method_fast(BcLir *c, BcLirNode const *node)
{
        if (node->nkw != 0 || node->argc < 0
            || (node->op != INSTR_CALL_METHOD && node->op != INSTR_TRY_CALL_METHOD
                && node->op != INSTR_CALL_SELF_METHOD)) {
                return false;
        }
        Class *class;
        if (node->op == INSTR_CALL_SELF_METHOD && c->self_index >= 0) {
                class = class_get(c->ctx, c->function->info[FUN_INFO_CLASS]);
        } else {
                Expr const *expr = expr_of(c->function);
                T2Type type = find_type_hint(&expr->type_hints, node - c->nodes);
                class = type == T2_TYPE_INVALID ? NULL : expected_class_of(c->ctx, type);
        }
        if (class == NULL || node->member < 0) {
                return false;
        }
        int value_type;
        BuiltinMethod *builtin = bc_resolve_builtin_method(class, node->member, &value_type);
        if (builtin != NULL && node->op != INSTR_TRY_CALL_METHOD) {
                bool explicit = node->op == INSTR_CALL_METHOD;
                LirReg out = bc_addr(c, c->ops, (c->sp - explicit - node->argc) * sizeof (Value));
                LirReg self = explicit ? bc_addr(c, c->ops, (c->sp - 1) * sizeof (Value)) : LIR_NONE;
                LirType types[] = { LIR_TYPE_PTR, LIR_TYPE_PTR, LIR_TYPE_PTR,
                                    LIR_TYPE_PTR, LIR_TYPE_I64, LIR_TYPE_I32 };
                i64 packed = ((u64)(u32)value_type << 32) | (u32)node->member;
                LirOpnd args[] = { lir_r(c->ty), lir_r(out), explicit ? lir_r(self) : lir_i(0),
                                  lir_i((uptr)builtin), lir_i(packed), lir_i(node->argc) };
                bc_call(c, jit_rt_call_builtin_method, LIR_VOID, types, args, countof(args));
                return true;
        }
        if (builtin != NULL || node->member >= vN(class->offsets_r)) {
                return false;
        }
        u16 offset = v__(class->offsets_r, node->member);
        if ((offset >> OFF_SHIFT) == OFF_METHOD) {
                Value *method = v_(class->methods.values, offset & OFF_MASK);
                if (!jit_linkable_function(method, node->argc)) {
                        return false;
                }
                LirOpnd constant = lir_const(c->L, method);
                LirReg target = bc_value(c, LIR_MOV, LIR_PTR, &constant, 1);
                LirReg top = bc_addr(c, c->ops, c->sp * sizeof (Value));
                LirType types[] = { LIR_TYPE_PTR, LIR_TYPE_PTR, LIR_TYPE_PTR,
                                    LIR_TYPE_I64, LIR_TYPE_I32, LIR_TYPE_I32, LIR_TYPE_PTR };
                i64 packed = ((u64)(u32)class->i << 32) | (u32)node->member;
                LirOpnd args[] = { lir_r(c->ty), lir_r(top), lir_r(target),
                                  lir_i(packed), lir_i(node->argc), lir_i(node->op),
                                  lir_i((uptr)node->kw_ip) };
                bc_call(c, bc_baked_method, LIR_VOID, types, args, countof(args));
                return true;
        }
        return false;
}
