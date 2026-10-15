static bool
bc_try_plan(BcLir *c, Value const *callee, TyInlineKind kind, i32 argc, i32 base, LirReg self,
            Class *self_class, Class **arg_classes, i32 out, LirLabel done);

static LirReg
bc_type_at(BcLir *c, i32 slot);

static Class *
bc_hint_class(BcLir *c, i32 offset);

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

static bool
bc_enterable(Value const *fn, i32 argc)
{
        return fn->type == VALUE_FUNCTION
            && argc <= param_count_of(fn)
            && rest_idx_of(fn) == -1
            && kwargs_idx_of(fn) == -1
            && !is_starred(fn)
            && !is_overload(fn);
}

static Frame *
bc_push_frame(Ty *ty, Value const *fn, Value const *self, i32 argc)
{
        jit_fast_frame(ty, fn, self, argc);
        vvL(ty->st->frames)->jit_code = jit_of(fn);
        if (ty->stack.count + 256 > ty->stack.capacity) {
                xvR(ty->stack, ty->stack.count + 256);
        }
        ty->st->exec_depth += 2;
        return vvL(ty->st->frames);
}

static Frame *
bc_call_enter(Ty *ty, Value *out, Value *fn, i32 argc)
{
        Value value = *fn;
        usize count = out - ty->stack.items + argc;
        Frame *frame = NULL;
        ty->stack.count = count;
        if (value.type == VALUE_BUILTIN_FUNCTION) {
                Value kwargs = NIL;
                Value result = (*value.builtin_function)(ty, argc, &kwargs);
                ty->stack.count = count - argc;
                xvP(ty->stack, result);
                return NULL;
        }
        gP(&value);
        if (value.type == VALUE_CLASS && value.class > CLASS_PRIMITIVE) {
                Value const *init = class_ctor(ty, value.class);
                if (bc_enterable(init, argc)
                    && (argc > 0 || !expr_of(init)->inert)
                    && try_jit(ty, init) != NULL) {
                        Value callee = *init;
                        Value object = RawObject(value.class);
                        xvI(ty->stack, object, out - ty->stack.items);
                        frame = bc_push_frame(ty, &callee, &object, argc);
                }
        } else if (jit_linkable_global(&value, argc) && try_jit(ty, &value) != NULL) {
                frame = bc_push_frame(ty, &value, NULL, argc);
        }
        if (frame == NULL) {
                DoCallEx(ty, &value, argc, &NIL, true);
        }
        gX();
        return frame;
}

static Frame *
bc_method_enter(Ty *ty, Value *top, i32 op, i32 member, i32 argc, char *kw_ip)
{
        bool explicit = op != INSTR_CALL_SELF_METHOD;
        Value self = explicit ? top[-1] : *vm_get_self(ty);
        if (self.type == VALUE_OBJECT) {
                Class *class = class_get(ty, self.class);
                u16 offset = member < vN(class->offsets_r) ? v__(class->offsets_r, member) : OFF_NOT_FOUND;
                if (offset != OFF_NOT_FOUND && (offset >> OFF_SHIFT) == OFF_METHOD) {
                        Value callee = *v_(class->methods.values, offset & OFF_MASK);
                        if (bc_enterable(&callee, argc) && try_jit(ty, &callee) != NULL) {
                                ty->stack.count = top - ty->stack.items - explicit;
                                return bc_push_frame(ty, &callee, &self, argc);
                        }
                }
        }
        bc_method(ty, top, op, 0, member, argc, 0, kw_ip);
        return NULL;
}

static void
bc_call_leave(Ty *ty, Value *out)
{
        Frame *frame = vvL(ty->st->frames);
        Value *base = ty->stack.items + frame->fp;
        Value v = ty->stack.items[ty->stack.count - 1];
        ty->ip = *vvL(ty->st->calls);
        ty->st->calls.count -= 1;
        if (base == out) {
                ty->stack.count = frame->fp + 1;
                *base = v;
        } else {
                ty->stack.count = frame->fp;
        }
        ty->st->frames.count -= 1;
        ty->st->exec_depth -= 2;
}

static void
bc_native_invoke(BcLir *c, LirReg frame, LirReg out)
{
        LirLabel done = lir_label(c->L);
        LirLabel returned = lir_label(c->L);
        bc_branch(c, LIR_EQ, lir_r(frame), lir_i(0), done);
        LirReg code = bc_load(c, LIR_LD_I64, LIR_PTR, frame, offsetof(Frame, jit_code));
        LirReg env = bc_load(c, LIR_LD_I64, LIR_PTR, frame, offsetof(Frame, f) + offsetof(Value, env));
        LirReg fp = bc_load(c, LIR_LD_I64, LIR_I64, frame, offsetof(Frame, fp));
        LirReg base = bc_load(c, LIR_LD_I64, LIR_PTR, c->ty, offsetof(Ty, stack.items));
        LirOpnd shift[] = { lir_r(fp), lir_i(5) };
        LirReg offset = bc_value(c, LIR_SHL, LIR_I64, shift, countof(shift));
        LirOpnd at = lir_m(base, offset, 1, 0);
        LirReg argv = bc_value(c, LIR_LEA, LIR_PTR, &at, 1);
        LirReg pc = bc_addr(c, frame, offsetof(Frame, jit_pc));
        LirType jit_types[] = { LIR_TYPE_PTR, LIR_TYPE_I32, LIR_TYPE_PTR, LIR_TYPE_PTR, LIR_TYPE_PTR };
        LirOpnd jit_args[] = { lir_r(c->ty), lir_i(0), lir_r(argv), lir_r(env), lir_r(pc) };
        LirReg rc = bc_call_target(c, lir_r(code), LIR_TYPE_I32, jit_types, jit_args, countof(jit_args),
                                   LIR_MAY_GC | LIR_MAY_THROW | LIR_CALL_SITE | LIR_WRITES_LOCALS);
        bc_branch(c, LIR_EQ, lir_r(rc), lir_i(JIT_RETURN), returned);
        LirType resume_types[] = { LIR_TYPE_PTR, LIR_TYPE_I32 };
        LirOpnd resume_args[] = { lir_r(c->ty), lir_r(rc) };
        bc_call(c, vm_trampoline_resume, LIR_VOID, resume_types, resume_args, countof(resume_args));
        bc_jump(c, done);
        bc_bind(c, returned);
        LirType leave_types[] = { LIR_TYPE_PTR, LIR_TYPE_PTR };
        LirOpnd leave_args[] = { lir_r(c->ty), lir_r(out) };
        bc_call_flags(c, bc_call_leave, LIR_VOID, leave_types, leave_args, 2, LIR_READS_NO_LOCALS);
        bc_bind(c, done);
}

static void
bc_native_call(BcLir *c, LirOpnd *enter_args)
{
        LirType types[] = { LIR_TYPE_PTR, LIR_TYPE_PTR, LIR_TYPE_PTR, LIR_TYPE_I32 };
        LirReg frame = bc_call(c, bc_call_enter, LIR_TYPE_PTR, types, enter_args, 4);
        bc_native_invoke(c, frame, enter_args[1].reg);
}

static void
bc_sync_call(Ty *ty, Value *out, Value *fn, i32 argc)
{
        if (bc_prepare_call(ty, out, fn, argc) != 0) {
                vm_trampoline(ty);
        }
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
        return false;
}

static LirReg
bc_field(BcLir *c, LirOp op, LirClass cls, LirReg base, usize offset)
{
        return bc_load(c, op, cls, base, (i32)offset);
}

static void
bc_inline_call(BcLir *c, LirReg fn, Value const *callee, i32 out, i32 argc, LirReg self,
               LirLabel miss, LirLabel done)
{
        if (c->compact) {
                bc_jump(c, miss);
                return;
        }
        i32 bound = callee->info[FUN_INFO_BOUND];
        i32 np = param_count_of(callee);
        LirLabel finish = lir_label(c->L);
        LirReg info;
        if (self == LIR_NONE) {
                LirReg type = bc_load(c, LIR_LD_U8, LIR_I64, fn, offsetof(Value, type));
                bc_branch(c, LIR_NE, lir_r(type), lir_i(VALUE_FUNCTION), miss);
                info = bc_load(c, LIR_LD_I64, LIR_PTR, fn, offsetof(Value, info));
                LirOpnd expected = lir_i((uptr)callee->info);
                LirReg want = bc_value(c, LIR_LI, LIR_PTR, &expected, 1);
                bc_branch(c, LIR_NE, lir_r(info), lir_r(want), miss);
        } else {
                LirOpnd known = lir_i((uptr)callee->info);
                info = bc_value(c, LIR_LI, LIR_PTR, &known, 1);
        }
        LirReg code = bc_load(c, LIR_LD_I64, LIR_PTR, info, FUN_JIT);
        bc_branch(c, LIR_ULT, lir_r(code), lir_i(JIT_PENDING), miss);
        LirReg st = bc_field(c, LIR_LD_I64, LIR_PTR, c->ty, offsetof(Ty, st));
        LirReg nframes = bc_field(c, LIR_LD_I64, LIR_I64, st, offsetof(co_state, frames.count));
        bc_branch(c, LIR_UGE, lir_r(nframes), lir_i(TY_MAX_CALL_DEPTH), miss);
        LirReg fcap = bc_field(c, LIR_LD_I64, LIR_I64, st, offsetof(co_state, frames.capacity));
        bc_branch(c, LIR_UGE, lir_r(nframes), lir_r(fcap), miss);
        LirReg ncalls = bc_field(c, LIR_LD_I64, LIR_I64, st, offsetof(co_state, calls.count));
        LirReg ccap = bc_field(c, LIR_LD_I64, LIR_I64, st, offsetof(co_state, calls.capacity));
        bc_branch(c, LIR_UGE, lir_r(ncalls), lir_r(ccap), miss);
        LirReg items = bc_field(c, LIR_LD_I64, LIR_PTR, c->ty, offsetof(Ty, stack.items));
        LirReg args = bc_addr(c, c->ops, out * sizeof (Value));
        LirOpnd bits = lir_r(args);
        LirReg raw = bc_value(c, LIR_BITCAST, LIR_I64, &bits, 1);
        bits = lir_r(items);
        LirReg base = bc_value(c, LIR_BITCAST, LIR_I64, &bits, 1);
        LirOpnd diff[] = { lir_r(raw), lir_r(base) };
        LirReg bytes = bc_value(c, LIR_SUB, LIR_I64, diff, countof(diff));
        LirOpnd shr[] = { lir_r(bytes), lir_i(5) };
        LirReg fp = bc_value(c, LIR_SHR, LIR_I64, shr, countof(shr));
        LirOpnd room[] = { lir_r(fp), lir_i(bound + 256) };
        LirReg need = bc_value(c, LIR_ADD, LIR_I64, room, countof(room));
        LirReg scap = bc_field(c, LIR_LD_I64, LIR_I64, c->ty, offsetof(Ty, stack.capacity));
        bc_branch(c, LIR_UGT, lir_r(need), lir_r(scap), miss);
        if (self != LIR_NONE) {
                LirReg want = bc_addr(c, args, np * sizeof (Value));
                LirLabel placed = lir_label(c->L);
                bc_branch(c, LIR_EQ, lir_r(self), lir_r(want), placed);
                bc_value_copy(c, args, np * sizeof (Value), self, 0);
                bc_bind(c, placed);
        }
        for (i32 i = argc; i < bound; ++i) {
                if (self == LIR_NONE || i != np) {
                        bc_store(c, LIR_ST64, args, i * sizeof (Value), lir_i(VALUE_NIL));
                }
        }
        LirOpnd top[] = { lir_r(fp), lir_i(bound) };
        LirReg count = bc_value(c, LIR_ADD, LIR_I64, top, countof(top));
        bc_store(c, LIR_ST64, c->ty, offsetof(Ty, stack.count), lir_r(count));
        LirReg frames = bc_field(c, LIR_LD_I64, LIR_PTR, st, offsetof(co_state, frames.items));
        LirOpnd fshift[] = { lir_r(nframes), lir_i(sizeof (Frame)) };
        LirReg foff = bc_value(c, LIR_MUL, LIR_I64, fshift, countof(fshift));
        LirOpnd fat = lir_m(frames, foff, 1, 0);
        LirReg frame = bc_value(c, LIR_LEA, LIR_PTR, &fat, 1);
        LirReg ip = bc_field(c, LIR_LD_I64, LIR_I64, c->ty, offsetof(Ty, ip));
        bc_store(c, LIR_ST64, frame, offsetof(Frame, fp), lir_r(fp));
        bc_store(c, LIR_ST64, frame, offsetof(Frame, ip), lir_r(ip));
        bc_value_copy(c, frame, offsetof(Frame, f), fn, 0);
        bc_store(c, LIR_ST8, frame, offsetof(Frame, f) + offsetof(Value, type), lir_i(VALUE_NATIVE_FUNCTION));
        bc_store(c, LIR_ST16, frame, offsetof(Frame, f) + offsetof(Value, tags), lir_i(0));
        bc_store(c, LIR_ST32, frame, offsetof(Frame, jit_resume), lir_i(0));
        bc_store(c, LIR_ST64, frame, offsetof(Frame, jit_pc), lir_i(0));
        bc_store(c, LIR_ST64, frame, offsetof(Frame, jit_code), lir_r(code));
        LirReg calls = bc_field(c, LIR_LD_I64, LIR_PTR, st, offsetof(co_state, calls.items));
        LirOpnd cshift[] = { lir_r(ncalls), lir_i(3) };
        LirReg coff = bc_value(c, LIR_SHL, LIR_I64, cshift, countof(cshift));
        LirOpnd cat = lir_m(calls, coff, 1, 0);
        LirReg slot = bc_value(c, LIR_LEA, LIR_PTR, &cat, 1);
        bc_store(c, LIR_ST64, slot, 0, lir_r(ip));
        LirOpnd one[] = { lir_r(ncalls), lir_i(1) };
        LirReg ncalls1 = bc_value(c, LIR_ADD, LIR_I64, one, countof(one));
        bc_store(c, LIR_ST64, st, offsetof(co_state, calls.count), lir_r(ncalls1));
        one[0] = lir_r(nframes);
        LirReg nframes1 = bc_value(c, LIR_ADD, LIR_I64, one, countof(one));
        bc_store(c, LIR_ST64, st, offsetof(co_state, frames.count), lir_r(nframes1));
        bc_store(c, LIR_ST64, c->ty, offsetof(Ty, ip), lir_i((uptr)&JIT));
        LirReg depth = bc_field(c, LIR_LD_I32, LIR_I64, st, offsetof(co_state, exec_depth));
        LirOpnd two[] = { lir_r(depth), lir_i(2) };
        LirReg depth2 = bc_value(c, LIR_ADD, LIR_I64, two, countof(two));
        bc_store(c, LIR_ST32, st, offsetof(co_state, exec_depth), lir_r(depth2));
        LirReg env = bc_load(c, LIR_LD_I64, LIR_PTR, frame, offsetof(Frame, f) + offsetof(Value, env));
        LirReg pc = bc_addr(c, frame, offsetof(Frame, jit_pc));
        LirType types[] = { LIR_TYPE_PTR, LIR_TYPE_I32, LIR_TYPE_PTR, LIR_TYPE_PTR, LIR_TYPE_PTR };
        LirOpnd call[] = { lir_r(c->ty), lir_i(0), lir_r(args), lir_r(env), lir_r(pc) };
        LirReg rc = bc_call_target(c, lir_r(code), LIR_TYPE_I32, types, call, countof(call),
                                   LIR_MAY_GC | LIR_MAY_THROW | LIR_CALL_SITE | LIR_WRITES_LOCALS);
        bc_branch(c, LIR_NE, lir_r(rc), lir_i(JIT_RETURN), finish);
        st = bc_field(c, LIR_LD_I64, LIR_PTR, c->ty, offsetof(Ty, st));
        depth = bc_field(c, LIR_LD_I32, LIR_I64, st, offsetof(co_state, exec_depth));
        two[0] = lir_r(depth);
        two[1] = lir_i(-2);
        depth2 = bc_value(c, LIR_ADD, LIR_I64, two, countof(two));
        bc_store(c, LIR_ST32, st, offsetof(co_state, exec_depth), lir_r(depth2));
        nframes = bc_field(c, LIR_LD_I64, LIR_I64, st, offsetof(co_state, frames.count));
        one[0] = lir_r(nframes);
        one[1] = lir_i(-1);
        nframes1 = bc_value(c, LIR_ADD, LIR_I64, one, countof(one));
        bc_store(c, LIR_ST64, st, offsetof(co_state, frames.count), lir_r(nframes1));
        ncalls = bc_field(c, LIR_LD_I64, LIR_I64, st, offsetof(co_state, calls.count));
        one[0] = lir_r(ncalls);
        ncalls1 = bc_value(c, LIR_ADD, LIR_I64, one, countof(one));
        bc_store(c, LIR_ST64, st, offsetof(co_state, calls.count), lir_r(ncalls1));
        calls = bc_field(c, LIR_LD_I64, LIR_PTR, st, offsetof(co_state, calls.items));
        cshift[0] = lir_r(ncalls1);
        coff = bc_value(c, LIR_SHL, LIR_I64, cshift, countof(cshift));
        LirOpnd back = lir_m(calls, coff, 1, 0);
        LirReg saved = bc_value(c, LIR_LD_I64, LIR_I64, &back, 1);
        bc_store(c, LIR_ST64, c->ty, offsetof(Ty, ip), lir_r(saved));
        items = bc_field(c, LIR_LD_I64, LIR_PTR, c->ty, offsetof(Ty, stack.items));
        count = bc_field(c, LIR_LD_I64, LIR_I64, c->ty, offsetof(Ty, stack.count));
        LirOpnd rshift[] = { lir_r(count), lir_i(5) };
        LirReg roff = bc_value(c, LIR_SHL, LIR_I64, rshift, countof(rshift));
        LirOpnd rat = lir_m(items, roff, 1, -(i32)sizeof (Value));
        LirReg result = bc_value(c, LIR_LEA, LIR_PTR, &rat, 1);
        bc_value_copy(c, c->ops, out * sizeof (Value), result, 0);
        bc_stack_count_at(c, out + 1);
        bc_jump(c, done);
        bc_bind(c, finish);
        LirType resume_types[] = { LIR_TYPE_PTR, LIR_TYPE_I32 };
        LirOpnd resume_args[] = { lir_r(c->ty), lir_r(rc) };
        bc_call(c, vm_trampoline_resume, LIR_VOID, resume_types, resume_args, countof(resume_args));
        bc_jump(c, done);
}

static bool
bc_inline_method(BcLir *c, BcLirNode const *node, LirLabel *done)
{
        bool explicit = node->op == INSTR_CALL_METHOD;
        if (node->nkw != 0 || node->argc < 0 || node->member < 0
            || (node->op != INSTR_CALL_METHOD && node->op != INSTR_CALL_SELF_METHOD)
            || (!explicit && c->self_index < 0)) {
                return false;
        }
        Class *class = explicit ? bc_hint_class(c, node - c->nodes)
                                : class_get(c->ctx, c->function->info[FUN_INFO_CLASS]);
        if (class == NULL || class->i < CLASS_PRIMITIVE || node->member >= vN(class->offsets_r)) {
                return false;
        }
        u16 offset = v__(class->offsets_r, node->member);
        if (offset == OFF_NOT_FOUND || (offset >> OFF_SHIFT) != OFF_METHOD) {
                return false;
        }
        Value const *method = v_(class->methods.values, offset & OFF_MASK);
        if (!bc_enterable(method, node->argc)
            || method->info[FUN_INFO_BOUND] - node->argc > 32) {
                return false;
        }
        LirLabel miss = lir_label(c->L);
        LirReg self = explicit
                    ? bc_addr(c, c->ops, (c->sp - 1) * sizeof (Value))
                    : bc_addr(c, c->locals, c->self_index * sizeof (Value));
        LirReg type = bc_load(c, LIR_LD_U8, LIR_I64, self, offsetof(Value, type));
        bc_branch(c, LIR_NE, lir_r(type), lir_i(VALUE_OBJECT), miss);
        LirReg actual = bc_load(c, LIR_LD_I32, LIR_I64, self, offsetof(Value, class));
        bc_branch(c, LIR_NE, lir_r(actual), lir_i(class->i), miss);
        LirOpnd epoch_at = lir_i((uptr)&ClassMethodEpoch);
        LirReg epoch_ptr = bc_value(c, LIR_LI, LIR_PTR, &epoch_at, 1);
        LirReg epoch = bc_load(c, LIR_LD_I32, LIR_I64, epoch_ptr, 0);
        bc_branch(c, LIR_NE, lir_r(epoch), lir_i(0), miss);
        LirOpnd constant = lir_const(c->L, method);
        LirReg fn = bc_value(c, LIR_MOV, LIR_PTR, &constant, 1);
        *done = lir_label(c->L);
        i32 first = c->sp - explicit - node->argc;
        bc_try_plan(c, method, TY_INLINE_METHOD, node->argc, first, self, class, NULL, first, *done);
        bc_inline_call(c, fn, method, first, node->argc, self, miss, *done);
        bc_bind(c, miss);
        return true;
}

Value builtin_min(Ty *ty, int argc, Value *kwargs);
Value builtin_max(Ty *ty, int argc, Value *kwargs);
Value builtin_sin(Ty *ty, int argc, Value *kwargs);
Value builtin_cos(Ty *ty, int argc, Value *kwargs);
Value builtin_tan(Ty *ty, int argc, Value *kwargs);
Value builtin_sqrt(Ty *ty, int argc, Value *kwargs);
Value builtin_exp(Ty *ty, int argc, Value *kwargs);
Value builtin_log(Ty *ty, int argc, Value *kwargs);
Value builtin_atan(Ty *ty, int argc, Value *kwargs);

static void
bc_call_builtin(Ty *ty, Value *out, BuiltinFunction *fn, i32 argc)
{
        Value kwargs = NIL;
        usize count = out - ty->stack.items + argc;
        ty->stack.count = count;
        Value result = (*fn)(ty, argc, &kwargs);
        ty->stack.count = count - argc;
        xvP(ty->stack, result);
}

static void *
bc_libm(BuiltinFunction *fn)
{
        if (fn == builtin_sin) {
                return (void *)(double (*)(double))sin;
        }
        if (fn == builtin_cos) {
                return (void *)(double (*)(double))cos;
        }
        if (fn == builtin_tan) {
                return (void *)(double (*)(double))tan;
        }
        if (fn == builtin_sqrt) {
                return (void *)(double (*)(double))sqrt;
        }
        if (fn == builtin_exp) {
                return (void *)(double (*)(double))exp;
        }
        if (fn == builtin_log) {
                return (void *)(double (*)(double))log;
        }
        if (fn == builtin_atan) {
                return (void *)(double (*)(double))atan;
        }
        return NULL;
}

static LirReg
bc_float_arg(BcLir *c, i32 slot, LirLabel slow)
{
        LirLabel integer = lir_label(c->L);
        LirLabel ready = lir_label(c->L);
        LirReg x = lir_reg(c->L, LIR_F64);
        i32 at = slot * sizeof (Value);
        LirReg type = bc_load(c, LIR_LD_U8, LIR_I64, c->ops, at + offsetof(Value, type));
        bc_branch(c, LIR_NE, lir_r(type), lir_i(VALUE_REAL), integer);
        LirOpnd mem = lir_m(c->ops, LIR_NONE, 1, at + offsetof(Value, real));
        c->ok = c->ok && lir_emit_to(c->L, LIR_LD_F64, x, &mem, 1);
        bc_jump(c, ready);
        bc_bind(c, integer);
        bc_branch(c, LIR_NE, lir_r(type), lir_i(VALUE_INTEGER), slow);
        LirReg z = bc_load(c, LIR_LD_I64, LIR_I64, c->ops, at + offsetof(Value, z));
        LirOpnd convert = lir_r(z);
        c->ok = c->ok && lir_emit_to(c->L, LIR_I2F, x, &convert, 1);
        bc_bind(c, ready);
        return x;
}

static void
bc_select_extreme(BcLir *c, i32 out, bool greatest, LirLabel slow, LirLabel done)
{
        i32 a = out * sizeof (Value);
        i32 b = a + sizeof (Value);
        LirLabel reals = lir_label(c->L);
        LirLabel take = lir_label(c->L);
        LirReg at = bc_type_at(c, out);
        LirReg bt = bc_type_at(c, out + 1);
        bc_branch(c, LIR_NE, lir_r(at), lir_i(VALUE_INTEGER), reals);
        bc_branch(c, LIR_NE, lir_r(bt), lir_i(VALUE_INTEGER), slow);
        LirReg x = bc_load(c, LIR_LD_I64, LIR_I64, c->ops, a + offsetof(Value, z));
        LirReg y = bc_load(c, LIR_LD_I64, LIR_I64, c->ops, b + offsetof(Value, z));
        bc_branch(c, greatest ? LIR_GT : LIR_LT, lir_r(y), lir_r(x), take);
        bc_jump(c, done);
        bc_bind(c, reals);
        bc_branch(c, LIR_NE, lir_r(at), lir_i(VALUE_REAL), slow);
        bc_branch(c, LIR_NE, lir_r(bt), lir_i(VALUE_REAL), slow);
        LirReg fx = bc_load(c, LIR_LD_F64, LIR_F64, c->ops, a + offsetof(Value, real));
        LirReg fy = bc_load(c, LIR_LD_F64, LIR_F64, c->ops, b + offsetof(Value, real));
        LirOpnd nan_x[] = { lir_cc(LIR_FNE), lir_r(fx), lir_r(fx), lir_l(slow) };
        bc_effect(c, LIR_FBR, nan_x, countof(nan_x));
        LirOpnd nan_y[] = { lir_cc(LIR_FNE), lir_r(fy), lir_r(fy), lir_l(slow) };
        bc_effect(c, LIR_FBR, nan_y, countof(nan_y));
        LirOpnd better[] = { lir_cc(greatest ? LIR_FGT : LIR_FLT), lir_r(fy), lir_r(fx), lir_l(take) };
        bc_effect(c, LIR_FBR, better, countof(better));
        bc_jump(c, done);
        bc_bind(c, take);
        bc_value_copy(c, c->ops, a, c->ops, b);
        bc_jump(c, done);
}

static bool
bc_builtin_call(BcLir *c, LirReg fn, Value const *callee, i32 out, i32 argc, LirLabel miss, LirLabel done)
{
        BuiltinFunction *builtin = callee->builtin_function;
        LirReg type = bc_load(c, LIR_LD_U8, LIR_I64, fn, offsetof(Value, type));
        bc_branch(c, LIR_NE, lir_r(type), lir_i(VALUE_BUILTIN_FUNCTION), miss);
        LirReg pointer = bc_load(c, LIR_LD_I64, LIR_PTR, fn, offsetof(Value, builtin_function));
        LirOpnd expected = lir_i((uptr)builtin);
        LirReg want = bc_value(c, LIR_LI, LIR_PTR, &expected, 1);
        bc_branch(c, LIR_NE, lir_r(pointer), lir_r(want), miss);
        LirLabel slow = lir_label(c->L);
        void *libm = bc_libm(builtin);
        if (libm != NULL && argc == 1) {
                LirReg x = bc_float_arg(c, out, slow);
                LirType types[] = { LIR_TYPE_F64 };
                LirOpnd args[] = { lir_r(x) };
                LirReg y = bc_call_flags(c, libm, LIR_TYPE_F64, types, args, 1, LIR_READS_NO_LOCALS);
                bc_store(c, LIR_ST64, c->ops, out * sizeof (Value), lir_i(VALUE_REAL));
                bc_store(c, LIR_ST_F64, c->ops, out * sizeof (Value) + offsetof(Value, real), lir_r(y));
                bc_jump(c, done);
        } else if ((builtin == builtin_max || builtin == builtin_min) && argc == 2) {
                bc_select_extreme(c, out, builtin == builtin_max, slow, done);
        }
        bc_bind(c, slow);
        LirReg at = bc_addr(c, c->ops, out * sizeof (Value));
        LirType types[] = { LIR_TYPE_PTR, LIR_TYPE_PTR, LIR_TYPE_PTR, LIR_TYPE_I32 };
        LirOpnd args[] = { lir_r(c->ty), lir_r(at), lir_i((uptr)builtin), lir_i(argc) };
        bc_call(c, bc_call_builtin, LIR_VOID, types, args, countof(args));
        bc_jump(c, done);
        return true;
}

static void
bc_raw_object(Ty *ty, Value *dst, i32 class)
{
        *dst = RawObject(class);
}

static void
bc_call_init(Ty *ty, Value *args, Value *init, Value *self, i32 argc)
{
        usize base = args - ty->stack.items;
        Value object = *self;
        Value method = *init;
        ty->stack.count = base + argc;
        gP(&object);
        vm_call_method(ty, &object, &method, argc);
        gX();
        ty->stack.count = base;
}

static bool
bc_inline_ctor(BcLir *c, LirReg fn, Value const *callee, i32 out, i32 argc, LirLabel *ready)
{
        if (callee->class <= CLASS_PRIMITIVE) {
                return false;
        }
        Class *class = class_get(c->ctx, callee->class);
        if (!class->really_final) {
                return false;
        }
        Value const *init = &class->init;
        if (!bc_enterable(init, argc) || (argc == 0 && expr_of(init)->inert)
            || init->info[FUN_INFO_BOUND] - argc > 32) {
                return false;
        }
        LirLabel miss = lir_label(c->L);
        LirLabel done = lir_label(c->L);
        LirReg type = bc_load(c, LIR_LD_U8, LIR_I64, fn, offsetof(Value, type));
        bc_branch(c, LIR_NE, lir_r(type), lir_i(VALUE_CLASS), miss);
        LirReg id = bc_load(c, LIR_LD_I32, LIR_I64, fn, offsetof(Value, class));
        bc_branch(c, LIR_NE, lir_r(id), lir_i(class->i), miss);
        LirOpnd epoch_at = lir_i((uptr)&ClassMethodEpoch);
        LirReg epoch_ptr = bc_value(c, LIR_LI, LIR_PTR, &epoch_at, 1);
        LirReg epoch = bc_load(c, LIR_LD_I32, LIR_I64, epoch_ptr, 0);
        bc_branch(c, LIR_NE, lir_r(epoch), lir_i(0), miss);
        LirOpnd init_at = lir_i((uptr)init);
        LirReg ctor = bc_value(c, LIR_LI, LIR_PTR, &init_at, 1);
        LirReg code = bc_load(c, LIR_LD_I64, LIR_PTR, ctor, offsetof(Value, info));
        code = bc_load(c, LIR_LD_I64, LIR_PTR, code, FUN_JIT);
        bc_branch(c, LIR_ULT, lir_r(code), lir_i(JIT_PENDING), miss);
        for (i32 i = argc; i-- > 0;) {
                bc_value_copy(c, c->ops, (out + i + 1) * sizeof (Value), c->ops, (out + i) * sizeof (Value));
        }
        bc_stack_count_at(c, out + argc + 1);
        LirReg object = bc_addr(c, c->ops, out * sizeof (Value));
        LirType types[] = { LIR_TYPE_PTR, LIR_TYPE_PTR, LIR_TYPE_I32 };
        LirOpnd args[] = { lir_r(c->ty), lir_r(object), lir_i(class->i) };
        bc_call(c, bc_raw_object, LIR_VOID, types, args, countof(args));
        object = bc_addr(c, c->ops, out * sizeof (Value));
        LirLabel failed = lir_label(c->L);
        LirLabel finished = lir_label(c->L);
        bc_inline_call(c, ctor, init, out + 1, argc, object, failed, finished);
        bc_bind(c, failed);
        LirReg at = bc_addr(c, c->ops, (out + 1) * sizeof (Value));
        LirReg self = bc_addr(c, c->ops, out * sizeof (Value));
        LirType call_types[] = { LIR_TYPE_PTR, LIR_TYPE_PTR, LIR_TYPE_PTR, LIR_TYPE_PTR, LIR_TYPE_I32 };
        LirOpnd call_args[] = { lir_r(c->ty), lir_r(at), lir_r(ctor), lir_r(self), lir_i(argc) };
        bc_call(c, bc_call_init, LIR_VOID, call_types, call_args, countof(call_args));
        bc_bind(c, finished);
        bc_stack_count_at(c, out + 1);
        bc_jump(c, done);
        bc_bind(c, miss);
        *ready = done;
        return true;
}
