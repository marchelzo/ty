static Class *
hint_class(BcLir *c, i32 offset);

static i32
prepare_call(Ty *ty, Value *out, Value *fn, i32 argc)
{
        Value  value = *fn;
        usize  count = out - ty->stack.items + argc;
        Value *argv  = ty->stack.items + count - argc;
        i32    rc    = 1;

        gP(&value);
        ty->stack.count = count;

        if (jit_linkable_global(&value, argc) && try_jit(ty, &value) != NULL) {
                jit_fast_frame(ty, &value, NULL, argc);
                STAT(global_jit_call_fast);
        } else {
                rc = jit_rt_call_trampoline(ty, argv, &value, argc);
        }

        gX();

        return rc;
}

static bool
enterable(Value const *fn, i32 argc)
{
        return (fn->type == VALUE_FUNCTION)
            && (argc <= param_count_of(fn))
            && (rest_idx_of(fn) == -1)
            && (kwargs_idx_of(fn) == -1)
            && !is_starred(fn)
            && !is_overload(fn);
}

static bool
roomy(Value const *fn, i32 argc)
{
        return enterable(fn, argc) && (fn->info[FUN_INFO_BOUND] - argc <= 32);
}

static Frame *
push_frame(Ty *ty, Value const *fn, Value const *self, i32 argc, void *code)
{
        jit_fast_frame(ty, fn, self, argc);
        vvL(ty->st->frames)->jit_code = code;

        if (vN(ty->stack) + 256 > vC(ty->stack)) {
                xvR(ty->stack, vN(ty->stack) + 256);
        }

        ty->st->exec_depth += 2;

        return vvL(ty->st->frames);
}

[[gnu::always_inline]]
inline static void
push_result(Ty *ty, usize base, Value v)
{
        ty->stack.count = base;
        xvP(ty->stack, v);
}

static Frame *
call_enter(Ty *ty, Value *out, Value *fn, i32 argc, JitCallProfile *site)
{
        Value  value = *fn;
        usize  count = out - ty->stack.items + argc;
        Value *argv  = ty->stack.items + count - argc;
        Frame *frame = NULL;
        JitFn *jit   = NULL;

        ty->stack.count = count;

        if (site != NULL) {
                bool known = (value.type == VALUE_FUNCTION) && !from_eval(&value);
                jit_profile_note(site, known ? (uptr)value.info : 0);
        }

        if (value.type == VALUE_BUILTIN_FUNCTION) {
                push_result(ty, count - argc, value.builtin_function(ty, argc, &NIL));
                return NULL;
        }

        gP(&value);

        if (value.type == VALUE_JIT_FUNCTION && value.jit_entry != NULL) {
                Value result = NIL;
                value.jit_entry(ty, &result, argv, argc);
                push_result(ty, count - argc, result);
        } else if (value.type == VALUE_CLASS && value.class > CLASS_PRIMITIVE) {
                Value const *init = class_ctor(ty, value.class);
                JitFn *code = (
                        enterable(init, argc)
                     && (argc > 0 || !expr_of(init)->fn->inert)
                ) ? try_jit(ty, init) : NULL;
                if (code != NULL) {
                        Value callee = *init;
                        Value object = RawObject(value.class);
                        xvI(ty->stack, object, out - ty->stack.items);
                        frame = push_frame(ty, &callee, &object, argc, code);
                } else {
                        DoCallEx(ty, &value, argc, &NIL, true);
                }
        } else if (jit_linkable_global(&value, argc) && (jit = try_jit(ty, &value)) != NULL) {
                frame = push_frame(ty, &value, NULL, argc, jit);
        } else {
                DoCallEx(ty, &value, argc, &NIL, true);
        }

        gX();

        return frame;
}

[[gnu::always_inline]]
inline static Value const *
method_of(Class *class, i32 member)
{
        u16 off = offset_of(class, member, false, OFF_METHOD);
        return (off == OFF_NOT_FOUND) ? NULL : v_(class->methods.values, off & OFF_MASK);
}

static i32
value_class(Value const *v)
{
        switch (v->type) {
        case VALUE_OBJECT:    return v->class;
        case VALUE_INTEGER:   return CLASS_INT;
        case VALUE_REAL:      return CLASS_FLOAT;
        case VALUE_BOOLEAN:   return CLASS_BOOL;
        case VALUE_STRING:    return CLASS_STRING;
        case VALUE_ARRAY:     return CLASS_ARRAY;
        case VALUE_DICT:      return CLASS_DICT;
        case VALUE_SET:       return CLASS_SET;
        case VALUE_BLOB:      return CLASS_BLOB;
        case VALUE_QUEUE:     return CLASS_QUEUE;
        case VALUE_GENERATOR: return CLASS_GENERATOR;
        default:              return -1;
        }
}

static i32
class_value(Class const *class)
{
        switch (class->i) {
        case CLASS_INT:       return VALUE_INTEGER;
        case CLASS_FLOAT:     return VALUE_REAL;
        case CLASS_BOOL:      return VALUE_BOOLEAN;
        case CLASS_STRING:    return VALUE_STRING;
        case CLASS_ARRAY:     return VALUE_ARRAY;
        case CLASS_DICT:      return VALUE_DICT;
        case CLASS_SET:       return VALUE_SET;
        case CLASS_BLOB:      return VALUE_BLOB;
        case CLASS_QUEUE:     return VALUE_QUEUE;
        case CLASS_GENERATOR: return VALUE_GENERATOR;
        default:              return (class->i >= CLASS_PRIMITIVE) ? VALUE_OBJECT : -1;
        }
}

static Value const *
builtin_class_method(Ty *ty, Class *class, i32 member)
{
        if (class_value(class) < 0 || jit_builtin_method(class, member, NULL) != NULL) {
                return NULL;
        }

        return class_lookup_method_i(ty, class->i, member);
}

static Frame *
method_enter(Ty *ty, Value *top, i32 op, i32 member, i32 argc, char *kw_ip, JitCallProfile *site)
{
        bool  explicit = (op != INSTR_CALL_SELF_METHOD);
        Value self     = explicit ? top[-1] : *vm_get_self(ty);
        i32   class    = value_class(&self);

        if (site != NULL) {
                jit_profile_note(site, (class > 0) ? (uptr)class : 0);
        }

        if (class >= 0) {
                Class       *c      = class_get(ty, class);
                Value const *method = (self.type == VALUE_OBJECT)
                                    ? method_of(c, member)
                                    : builtin_class_method(ty, c, member);
                Value        callee = (method != NULL) ? *method : NIL;
                JitFn       *code   = enterable(&callee, argc) ? try_jit(ty, &callee) : NULL;
                if (code != NULL) {
                        ty->stack.count = top - ty->stack.items - explicit;
                        return push_frame(ty, &callee, &self, argc, code);
                }
                if (self.type != VALUE_OBJECT && callee.type == VALUE_FUNCTION) {
                        usize base = top - ty->stack.items - explicit - argc;
                        ty->stack.count = base + argc;
                        push_result(ty, base, vm_call_method(ty, &self, &callee, argc));
                        return NULL;
                }
        }

        rt_method(ty, top, op, 0, member, argc, 0, kw_ip);

        return NULL;
}

static void
call_leave(Ty *ty, Value *out)
{
        Frame       *frame = vvL(ty->st->frames);
        Value       *base  = ty->stack.items + frame->fp;
        Value const *v     = vvL(ty->stack);

        ty->ip = *vvL(ty->st->calls);
        ty->st->calls.count -= 1;

        if (base == out) {
                ty->stack.count = frame->fp + 1;
                MoveJitResult(base, v);
        } else {
                ty->stack.count = frame->fp;
        }

        ty->st->frames.count -= 1;
        ty->st->exec_depth   -= 2;
}

static LirReg
enter_frame(BcLir *c, LirReg code, LirReg frame, LirReg argv, LirReg env)
{
        LirReg pc = addr(c, frame, offsetof(Frame, jit_pc));

        return jcall(c, code, preg(c->ty), imm32(0), preg(argv), preg(env), preg(pc));
}

static void
resume(BcLir *c, LirReg rc)
{
        tycall(c, vm_trampoline_resume, LT_VOID, reg32(rc));
}

static void
native_invoke(BcLir *c, LirReg frame, LirReg out)
{
        LirLabel done     = newlabel(c);
        LirLabel returned = newlabel(c);

        jz(c, frame, done);

        LirReg code = ldp(c, frame, offsetof(Frame, jit_code));
        LirReg env  = ldp(c, frame, offsetof(Frame, f) + VOFF(env));
        LirReg fp   = ldq(c, frame, offsetof(Frame, fp));
        LirReg base = ldp(c, c->ty, offsetof(Ty, stack.items));
        LirReg argv = elem(c, base, fp, 0);
        LirReg rc   = enter_frame(c, code, frame, argv, env);

        jcc(c, LIR_EQ, lir_r(rc), lir_i(JIT_RETURN), returned);
        resume(c, rc);
        jump(c, done);

        bind(c, returned);
        ccallf(c, call_leave, LT_VOID, CF_PURE, preg(c->ty), preg(out));

        bind(c, done);
}

static void
native_call(BcLir *c, LirOpnd *enter)
{
        LirReg frame = ccall(
                c,
                call_enter,
                LT_PTR,
                { LT_PTR, enter[0] },
                { LT_PTR, enter[1] },
                { LT_PTR, enter[2] },
                { LT_I32, enter[3] },
                { LT_PTR, enter[4] }
        );

        native_invoke(c, frame, enter[1].reg);
}

static void
sync_call(Ty *ty, Value *out, Value *fn, i32 argc)
{
        if (prepare_call(ty, out, fn, argc) != 0) {
                vm_trampoline(ty);
        }
}

static Class *
self_class(BcLir const *c)
{
        return class_get(c->ctx, c->function->info[FUN_INFO_CLASS]);
}

static Class *
receiver_class(BcLir *c, BcLirNode const *node)
{
        if (node->op == INSTR_CALL_SELF_METHOD && c->self_index >= 0) {
                return self_class(c);
        }

        T2Type type = find_type_hint(&expr_of(c->function)->fn->type_hints, node - c->nodes);

        return (type == T2_TYPE_INVALID) ? NULL : expected_class_of(c->ctx, type);
}

static bool
string_byte(BcLir *c, BcLirNode const *node, BuiltinMethod *method, i64 packed)
{
        if (node->op != INSTR_CALL_METHOD || node->argc != 1 || node->member != M_ID("byte")) {
                return false;
        }

        i32      text = c->sp - 1;
        i32      at   = c->sp - 2;
        LirLabel slow = newlabel(c);
        LirLabel done = newlabel(c);

        expect(c, c->ops, vat(text), VALUE_STRING, slow);
        expect(c, c->ops, vat(at), VALUE_INTEGER, slow);

        LirReg i = int_at(c, at);
        LirReg n = ldx(c, LIR_LD_U32, LIR_I64, c->ops, vat(text) + VOFF(bytes));

        jcc(c, LIR_UGE, lir_r(i), lir_r(n), slow);

        LirReg p = lea(c, ldp(c, c->ops, vat(text) + VOFF(str)), i, 0);

        put_scalar(c, at, VALUE_INTEGER, lir_r(ldx(c, LIR_LD_U8, LIR_I64, p, 0)));
        jump(c, done);

        bind(c, slow);
        miss_site(c);
        tycall(
                c,
                jit_rt_call_builtin_method,
                LT_VOID,
                preg(slot_of(c, at)),
                preg(slot_of(c, text)),
                pimm(method),
                imm64(packed),
                imm32(1)
        );

        bind(c, done);

        return true;
}

static bool
method_fast(BcLir *c, BcLirNode const *node)
{
        if (
                (node->nkw != 0)
             || (node->argc < 0)
             || (node->member < 0)
             || (node->op != INSTR_CALL_METHOD && node->op != INSTR_CALL_SELF_METHOD)
        ) {
                return false;
        }

        Class *class = receiver_class(c, node);

        if (class == NULL) {
                return false;
        }

        int            vtype;
        BuiltinMethod *method   = jit_builtin_method(class, node->member, &vtype);
        bool           explicit = (node->op == INSTR_CALL_METHOD);

        if (method == NULL) {
                return false;
        }

        i64     packed = ((u64)(u32)vtype << 32) | (u32)node->member;

        if (class->i == CLASS_STRING && string_byte(c, node, method, packed)) {
                return true;
        }

        LirReg  out    = slot_of(c, c->sp - explicit - node->argc);
        LirOpnd self   = explicit ? lir_r(slot_of(c, c->sp - 1)) : lir_i(0);

        miss_site(c);
        tycall(
                c,
                jit_rt_call_builtin_method,
                LT_VOID,
                preg(out),
                { LT_PTR, self },
                pimm(method),
                imm64(packed),
                imm32(node->argc)
        );

        return true;
}

static LirReg
guard_callee(BcLir *c, LirReg fn, Value const *callee, LirReg self, LirLabel miss)
{
        if (self != LIR_NONE) {
                return pval(c, callee->info);
        }

        expect(c, fn, 0, VALUE_FUNCTION, miss);

        LirReg info = ldp(c, fn, VOFF(info));
        same_ptr(c, info, callee->info, miss);

        return info;
}

typedef struct {
        LirReg st;
        LirReg nframes;
        LirReg ncalls;
} Depth;

static Depth
guard_depth(BcLir *c, LirLabel miss)
{
        LirReg st      = ldp(c, c->ty, offsetof(Ty, st));
        LirReg nframes = ldq(c, st, offsetof(co_state, frames.count));

        jcc(c, LIR_UGE, lir_r(nframes), lir_i(TY_MAX_CALL_DEPTH), miss);

        LirReg fcap = ldq(c, st, offsetof(co_state, frames.capacity));

        jcc(c, LIR_UGE, lir_r(nframes), lir_r(fcap), miss);

        LirReg ncalls = ldq(c, st, offsetof(co_state, calls.count));
        LirReg ccap   = ldq(c, st, offsetof(co_state, calls.capacity));

        jcc(c, LIR_UGE, lir_r(ncalls), lir_r(ccap), miss);

        return (Depth) { .st = st, .nframes = nframes, .ncalls = ncalls };
}

static void
guard_stack(BcLir *c, LirReg fp, i32 bound, LirLabel miss)
{
        LirReg need = plus(c, fp, bound + 256);
        LirReg scap = ldq(c, c->ty, offsetof(Ty, stack.capacity));

        jcc(c, LIR_UGT, lir_r(need), lir_r(scap), miss);
}

static LirReg
frame_index(BcLir *c, i32 out, LirReg *argv)
{
        LirReg items = ldp(c, c->ty, offsetof(Ty, stack.items));
        LirReg args  = (*argv = slot_of(c, out));
        LirReg raw   = unop(c, LIR_BITCAST, LIR_I64, lir_r(args));
        LirReg base  = unop(c, LIR_BITCAST, LIR_I64, lir_r(items));
        LirReg bytes = binop(c, LIR_SUB, LIR_I64, lir_r(raw), lir_r(base));

        return binop(c, LIR_SHR, LIR_I64, lir_r(bytes), lir_i(5));
}

static void
place_args(BcLir *c, LirReg args, Value const *callee, i32 argc, LirReg self)
{
        i32 bound = callee->info[FUN_INFO_BOUND];
        i32 np    = param_count_of(callee);

        if (self != LIR_NONE) {
                LirLabel placed = newlabel(c);
                jcc(c, LIR_EQ, lir_r(self), lir_r(addr(c, args, vat(np))), placed);
                copy(c, args, vat(np), self, 0);
                bind(c, placed);
        }

        for (i32 i = argc; i < bound; ++i) {
                if (self == LIR_NONE || i != np) {
                        stq(c, args, vat(i), lir_i(VALUE_NIL));
                }
        }
}

static LirReg
push_native_frame(BcLir *c, Depth d, LirReg fn, LirReg code, LirReg fp)
{
        LirReg st      = d.st;
        LirReg nframes = d.nframes;
        LirReg ncalls  = d.ncalls;
        LirReg frames  = ldp(c, st, offsetof(co_state, frames.items));
        LirReg foff    = binop(c, LIR_MUL, LIR_I64, lir_r(nframes), lir_i(sizeof (Frame)));
        LirReg frame   = lea(c, frames, foff, 0);
        LirReg ip      = ldq(c, c->ty, offsetof(Ty, ip));

#define F(field) offsetof(Frame, field)
        stq(c, frame, F(fp), lir_r(fp));
        stq(c, frame, F(ip), lir_r(ip));
        copy(c, frame, F(f), fn, 0);
        stb(c, frame, F(f) + VOFF(type), lir_i(VALUE_NATIVE_FUNCTION));
        store(c, LIR_ST16, frame, F(f) + VOFF(tags), lir_i(0));
        stq(c, frame, F(jit_resume), lir_i(0));
        stq(c, frame, F(jit_pc), lir_i(0));
        stq(c, frame, F(jit_code), lir_r(code));
#undef F

        LirReg calls = ldp(c, st, offsetof(co_state, calls.items));

        veff(c, LIR_ST64, lir_m(calls, ncalls, sizeof (char *), 0), lir_r(ip));
        stq(c, st, offsetof(co_state, calls.count), lir_r(plus(c, ncalls, 1)));
        stq(c, st, offsetof(co_state, frames.count), lir_r(plus(c, nframes, 1)));
        stq(c, c->ty, offsetof(Ty, ip), lir_i((uptr)&JIT));
        bumpw(c, st, offsetof(co_state, exec_depth), 2);

        return frame;
}

static void
pop_native_frame(BcLir *c, i32 out)
{
        LirReg st = ldp(c, c->ty, offsetof(Ty, st));

        bumpw(c, st, offsetof(co_state, exec_depth), -2);
        bump(c, st, offsetof(co_state, frames.count), -1);

        LirReg ncalls = bump(c, st, offsetof(co_state, calls.count), -1);
        LirReg calls  = ldp(c, st, offsetof(co_state, calls.items));
        LirReg saved  = unop(c, LIR_LD_I64, LIR_I64, lir_m(calls, ncalls, sizeof (char *), 0));

        stq(c, c->ty, offsetof(Ty, ip), lir_r(saved));

        LirReg items  = ldp(c, c->ty, offsetof(Ty, stack.items));
        LirReg count  = ldq(c, c->ty, offsetof(Ty, stack.count));
        LirReg result = elem(c, items, count, -(i32)sizeof (Value));

        copy(c, c->ops, vat(out), result, 0);
        count_at(c, out + 1);
}

static void
inline_call(
        BcLir *c,
        LirReg fn,
        Value const *callee,
        i32 out,
        i32 argc,
        LirReg self,
        LirLabel miss,
        LirLabel done
)
{
        if (c->compact) {
                jump(c, miss);
                return;
        }

        i32      bound  = callee->info[FUN_INFO_BOUND];
        LirLabel finish = newlabel(c);
        LirReg   info   = guard_callee(c, fn, callee, self, miss);
        LirReg   code   = ldp(c, info, FUN_JIT);

        jcc(c, LIR_ULT, lir_r(code), lir_i(JIT_PENDING), miss);

        Depth  d  = guard_depth(c, miss);
        LirReg args;
        LirReg fp = frame_index(c, out, &args);

        guard_stack(c, fp, bound, miss);
        place_args(c, args, callee, argc, self);
        stq(c, c->ty, offsetof(Ty, stack.count), lir_r(plus(c, fp, bound)));

        LirReg frame = push_native_frame(c, d, fn, code, fp);
        LirReg env   = ldp(c, frame, offsetof(Frame, f) + VOFF(env));
        LirReg rc    = enter_frame(c, code, frame, args, env);

        unless(c, rc, JIT_RETURN, finish);
        pop_native_frame(c, out);
        jump(c, done);

        bind(c, finish);
        resume(c, rc);
        jump(c, done);
}

inline static bool
extended(Class const *class)
{
        return (class != NULL) && (class->i > CLASS_PRIMITIVE) && class->extended;
}

static void
same_member(BcLir *c, LirReg value, i32 member, bool getter, Value const *fn, LirLabel miss)
{
        expect(c, value, 0, VALUE_OBJECT, miss);

        LirReg object = ldp(c, value, VOFF(object));
        LirReg class  = ldp(c, object, offsetof(TyObject, class));

        jcc(c, LIR_UGE, lir_i(member), lir_r(ldq(c, class, offsetof(Class, offsets_r.count))), miss);

        LirReg offsets = ldp(c, class, offsetof(Class, offsets_r.items));
        LirReg entry   = ldx(c, LIR_LD_U16, LIR_I64, offsets, member * sizeof (u16));
        LirReg kind    = binop(c, LIR_SHR, LIR_I64, lir_r(entry), lir_i(OFF_SHIFT));
        LirReg index   = binop(c, LIR_AND, LIR_I64, lir_r(entry), lir_i(OFF_MASK));

        i32    table   = getter ? offsetof(Class, getters.values.items) : offsetof(Class, methods.values.items);

        unless(c, kind, getter ? OFF_GETTER : OFF_METHOD, miss);

        LirReg target = elem(c, ldp(c, class, table), index, 0);

        expect(c, target, 0, fn->type, miss);
        same_ptr(c, ldp(c, target, VOFF(info)), fn->info, miss);
}

[[gnu::always_inline]]
inline static Value const *
getter_of(Class *class, i32 member)
{
        u16 off = offset_of(class, member, false, OFF_GETTER);
        return (off == OFF_NOT_FOUND || (off & OFF_MASK) >= vN(class->getters.values))
             ? NULL
             : v_(class->getters.values, off & OFF_MASK);
}

static bool
descends(Class const *class, Class const *base)
{
        for (Class const *k = class->super; k != NULL; k = k->super) {
                if (k == base) {
                        return true;
                }
        }

        return false;
}

static i32
kin(BcLir *c, Class const *class, i32 member, bool getter, Value const *fn, Class **out, i32 max)
{
        i32 n     = 0;
        i32 count = class_count(c->ctx);

        for (i32 i = class->i + 1; i < count && n < max; ++i) {
                Class *k = class_get(c->ctx, i);

                if (k == NULL || !k->final || !descends(k, class)) {
                        continue;
                }

                Value const *m = getter ? getter_of(k, member) : method_of(k, member);

                if (m != NULL && m->type == fn->type && m->info == fn->info) {
                        out[n++] = k;
                }
        }

        return n;
}

static void
kin_arms(
        BcLir *c,
        LirReg self,
        Class const *class,
        i32 member,
        bool getter,
        Value const *fn,
        i32 argc,
        i32 first,
        LirLabel call,
        LirLabel done
)
{
        Class *arms[4];
        i32    n = kin(c, class, member, getter, fn, arms, countof(arms));

        for (i32 i = 0; i < n; ++i) {
                LirLabel next = newlabel(c);

                guard_class(c, self, arms[i]->i, next);
                guard_epoch(c, next);
                try_plan(c, fn, TY_INLINE_METHOD, argc, first, self, arms[i], NULL, first, done);
                jump(c, call);

                bind(c, next);
        }
}

static i32
union_classes(BcLir *c, i32 offset, Class **out, i32 max)
{
        Expr const *expr = expr_of(c->function);
        T2Universe *u    = t2_global_universe();

        if (expr == NULL) {
                return 0;
        }

        T2Type type = find_type_hint(&expr->fn->type_hints, offset);

        if (type == T2_TYPE_INVALID || t2_type_kind(u, t2_type_scheme_body(u, type)) != T2_TYPE_UNION) {
                return 0;
        }

        type = t2_type_scheme_body(u, type);

        i32 n = 0;

        for (usize i = 0; i < t2_type_arity(u, type); ++i) {
                T2Type arm   = t2_type_child(u, type, i);
                Class *class = expected_class_of(c->ctx, arm);

                if (t2_type_kind(u, arm) == T2_TYPE_NIL) {
                        continue;
                }

                if (class == NULL || class->i <= CLASS_PRIMITIVE || n == max) {
                        return 0;
                }

                out[n++] = class;
        }

        return n;
}

static void
method_arm(
        BcLir *c,
        BcLirNode const *node,
        Class *class,
        Value const *method,
        i32 first,
        LirReg self,
        bool fallback,
        LirLabel next,
        LirLabel miss,
        LirLabel done
)
{
        LirLabel other = (fallback && extended(class)) ? newlabel(c) : next;
        LirLabel call  = newlabel(c);
        i32      type  = class_value(class);

        if (type == VALUE_OBJECT) {
                guard_class(c, self, class->i, other);
        } else {
                expect(c, self, 0, type, other);
        }

        guard_epoch(c, other);

        bool planned = try_plan(
                c,
                method,
                TY_INLINE_METHOD,
                node->argc,
                first,
                self,
                class,
                NULL,
                first,
                done
        );

        bind(c, call);
        inline_call(c, konst(c, method), method, first, node->argc, self, miss, done);

        if (other != next) {
                bind(c, other);
                if (planned) {
                        kin_arms(c, self, class, node->member, false, method, node->argc, first, call, done);
                }
                same_member(c, self, node->member, false, method, next);
                jump(c, call);
        }
}

static Value const *
arm_method(BcLir *c, Class *class, i32 member)
{
        return (class->i >= CLASS_PRIMITIVE)
             ? method_of(class, member)
             : builtin_class_method(c->ctx, class, member);
}

static i32
profiled_classes(BcLir *c, BcLirNode const *node, Class **out, i32 max)
{
        uptr keys[JIT_PROFILE_WAYS];
        u32  n = seen_keys(c, node, keys);
        i32  k = 0;

        for (u32 i = 0; i < n && k < max; ++i) {
                if (keys[i] >= (uptr)class_count(c->ctx)) {
                        continue;
                }

                Class       *class = class_get(c->ctx, keys[i]);
                Value const *m     = arm_method(c, class, node->member);

                if (
                        (class_value(class) >= 0)
                     && (class->i < CLASS_PRIMITIVE || class->final)
                     && (m != NULL)
                     && roomy(m, node->argc)
                ) {
                        out[k++] = class;
                }
        }

        return k;
}

static void
profiled_call(BcLir *c, BcLirNode const *node, LirReg fn, i32 first, LirLabel *done)
{
        uptr keys[JIT_PROFILE_WAYS];
        u32  n = c->compact ? 0 : seen_keys(c, node, keys);

        for (u32 i = 0; i < n; ++i) {
                Value callee = { .type = VALUE_FUNCTION };

                callee.info = (i32 *)keys[i];

                if (
                        (callee.info == c->function->info)
                     || !jit_linkable_global(&callee, node->argc)
                     || !roomy(&callee, node->argc)
                ) {
                        continue;
                }

                LirLabel next = newlabel(c);

                if (*done == LIR_NONE) {
                        *done = newlabel(c);
                }

                expect(c, fn, 0, VALUE_FUNCTION, next);
                same_ptr(c, ldp(c, fn, VOFF(info)), callee.info, next);
                jnz(c, ldq(c, fn, VOFF(xinfo)), next);

                try_plan(c, &callee, TY_INLINE_GLOBAL, node->argc, first, LIR_NONE, NULL, NULL, first, *done);
                inline_call(c, fn, &callee, first, node->argc, LIR_NONE, next, *done);

                bind(c, next);
        }
}

static bool
inline_method(BcLir *c, BcLirNode const *node, LirLabel *done)
{
        bool explicit = (node->op == INSTR_CALL_METHOD);

        if (
                (node->nkw != 0)
             || (node->argc < 0)
             || (node->member < 0)
             || (node->op != INSTR_CALL_METHOD && node->op != INSTR_CALL_SELF_METHOD)
             || (!explicit && c->self_index < 0)
        ) {
                return false;
        }

        Class       *classes[4];
        Value const *methods[4];
        Class       *class = explicit ? hint_class(c, node - c->nodes) : self_class(c);
        i32          n     = (class != NULL)
                           ? 1
                           : (explicit ? union_classes(c, node - c->nodes, classes, countof(classes)) : 0);

        if (class != NULL) {
                classes[0] = class;
        }

        if (n == 0 && explicit && !c->compact) {
                n = profiled_classes(c, node, classes, countof(classes));
        }

        for (i32 i = 0; i < n; ++i) {
                if (class_value(classes[i]) < 0) {
                        return false;
                }

                methods[i] = arm_method(c, classes[i], node->member);

                if (methods[i] == NULL || !roomy(methods[i], node->argc)) {
                        return false;
                }
        }

        if (n == 0) {
                return false;
        }

        LirLabel miss  = newlabel(c);
        i32      first = c->sp - explicit - node->argc;
        LirReg   self  = explicit
                       ? slot_of(c, c->sp - 1)
                       : addr(c, c->locals, vat(c->self_index));

        *done = newlabel(c);

        for (i32 i = 0; i < n; ++i) {
                LirLabel next = (i + 1 < n) ? newlabel(c) : miss;

                method_arm(c, node, classes[i], methods[i], first, self, n == 1, next, miss, *done);

                if (next != miss) {
                        bind(c, next);
                }
        }

        bind(c, miss);

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
call_builtin(Ty *ty, Value *out, BuiltinFunction *fn, i32 argc)
{
        usize count = out - ty->stack.items + argc;

        ty->stack.count = count;
        push_result(ty, count - argc, fn(ty, argc, &NIL));
}

static void *
libm(BuiltinFunction *fn)
{
        static struct {
                BuiltinFunction *builtin;
                double         (*f)(double);
        } const Libm[] = {
                { builtin_sin,  sin  },
                { builtin_cos,  cos  },
                { builtin_tan,  tan  },
                { builtin_sqrt, sqrt },
                { builtin_exp,  exp  },
                { builtin_log,  log  },
                { builtin_atan, atan }
        };

        for (int i = 0; i < countof(Libm); ++i) {
                if (Libm[i].builtin == fn) {
                        return (void *)Libm[i].f;
                }
        }

        return NULL;
}

static LirReg
real_arg(BcLir *c, i32 slot, LirLabel slow)
{
        return as_real(c, tag_of(c, slot), c->ops, vat(slot), false, slow);
}

static void
fbr(BcLir *c, LirCC cc, LirReg a, LirReg b, LirLabel target)
{
        veff(c, LIR_FBR, lir_cc(cc), lir_r(a), lir_r(b), lir_l(target));
}

static void
extreme(BcLir *c, i32 out, bool max, LirLabel slow, LirLabel done)
{
        i32      a     = vat(out);
        i32      b     = vat(out + 1);
        LirLabel reals = newlabel(c);
        LirLabel take  = newlabel(c);
        LirReg   at    = tag_of(c, out);
        LirReg   bt    = tag_of(c, out + 1);

        unless(c, at, VALUE_INTEGER, reals);
        unless(c, bt, VALUE_INTEGER, slow);

        LirReg x = ldq(c, c->ops, a + VOFF(z));
        LirReg y = ldq(c, c->ops, b + VOFF(z));

        jcc(c, max ? LIR_GT : LIR_LT, lir_r(y), lir_r(x), take);
        jump(c, done);

        bind(c, reals);
        unless(c, at, VALUE_REAL, slow);
        unless(c, bt, VALUE_REAL, slow);

        LirReg fx = ldf(c, c->ops, a + VOFF(real));
        LirReg fy = ldf(c, c->ops, b + VOFF(real));

        fbr(c, LIR_FNE, fx, fx, slow);
        fbr(c, LIR_FNE, fy, fy, slow);
        fbr(c, max ? LIR_FGT : LIR_FLT, fy, fx, take);
        jump(c, done);

        bind(c, take);
        copy(c, c->ops, a, c->ops, b);
        jump(c, done);
}

static bool
builtin_call(
        BcLir *c,
        LirReg fn,
        Value const *callee,
        i32 out,
        i32 argc,
        LirLabel miss,
        LirLabel done
)
{
        BuiltinFunction *builtin = callee->builtin_function;
        void            *f       = libm(builtin);
        LirLabel         slow    = newlabel(c);

        expect(c, fn, 0, VALUE_BUILTIN_FUNCTION, miss);
        same_ptr(c, ldp(c, fn, VOFF(builtin_function)), builtin, miss);

        if (f != NULL && argc == 1) {
                LirReg x = real_arg(c, out, slow);
                LirReg y = ccallf(c, f, LT_F64, CF_PURE, freg(x));
                put_real(c, c->ops, vat(out), y);
                jump(c, done);
        } else if ((builtin == builtin_max || builtin == builtin_min) && argc == 2) {
                extreme(c, out, builtin == builtin_max, slow, done);
        }

        bind(c, slow);
        tycall(
                c,
                call_builtin,
                LT_VOID,
                preg(slot_of(c, out)),
                pimm(builtin),
                imm32(argc)
        );
        jump(c, done);

        return true;
}

static bool
kernel_scalar(LirType type, bool param)
{
        switch (type) {
        case LT_VAL:  return param;
        case LT_VOID: return !param;
        case LT_REF:  return false;
        default:      return type < LT_COUNT;
        }
}

static bool
kernel_ok(LirCode const *code, i32 argc)
{
        if (
                (code == NULL)
             || (code->body == NULL)
             || (code->interp_state != NULL)
             || code->release
             || (code->nvslots != 0)
             || (code->sig.nfixed != code->sig.nparams)
             || ((i32)code->sig.nparams != argc)
             || (argc > 8)
             || !kernel_scalar(code->sig.ret, false)
        ) {
                return false;
        }

        for (u32 i = 0; i < code->sig.nparams; ++i) {
                if (!kernel_scalar(code->sig.params[i], true)) {
                        return false;
                }
        }

        return true;
}

static LirReg
kernel_ptr(BcLir *c, LirReg tag, i32 at, LirLabel slow)
{
        LirLabel blob  = newlabel(c);
        LirLabel ready = newlabel(c);
        LirReg   p     = lir_reg(c->L, LIR_PTR);

        unless(c, tag, VALUE_PTR, blob);
        vset(c, LIR_LD_I64, p, mref(c->ops, at + VOFF(ptr)));
        jump(c, ready);

        bind(c, blob);
        unless(c, tag, VALUE_BLOB, slow);

        LirReg b = ldp(c, c->ops, at + VOFF(blob));
        vset(c, LIR_LD_I64, p, mref(b, offsetof(Blob, items)));

        bind(c, ready);

        return p;
}

static LirReg
kernel_arg(BcLir *c, LirType type, i32 slot, LirLabel slow)
{
        i32 at = vat(slot);

        switch (type) {
        case LT_VAL:
                return slot_of(c, slot);

        case LT_F64:
                return real_arg(c, slot, slow);

        case LT_F32:
                return unop(c, LIR_FTRUNC, LIR_F32, lir_r(real_arg(c, slot, slow)));

        case LT_BOOL:
                expect(c, c->ops, at, VALUE_BOOLEAN, slow);
                return ldx(c, LIR_LD_U8, LIR_I64, c->ops, at + VOFF(boolean));

        case LT_PTR:
                return kernel_ptr(c, tag_of(c, slot), at, slow);

        default:
                expect(c, c->ops, at, VALUE_INTEGER, slow);
                return ldq(c, c->ops, at + VOFF(z));
        }
}

static void
kernel_box(BcLir *c, i32 out, LirType type, LirReg value)
{
        i32 at = vat(out);

        for (u32 i = VOFF(z) + 8; i < sizeof (Value); i += 8) {
                stq(c, c->ops, at + i, lir_i(0));
        }

        switch (type) {
        case LT_VOID:
                stq(c, c->ops, at + VOFF(z),    lir_i(0));
                stq(c, c->ops, at + VOFF(type), lir_i(VALUE_NIL));
                break;

        case LT_F32:
                value = unop(c, LIR_FEXT, LIR_F64, lir_r(value));
        case LT_F64:
                stf(c, c->ops, at + VOFF(real), lir_r(value));
                stq(c, c->ops, at + VOFF(type), lir_i(VALUE_REAL));
                break;

        case LT_BOOL:
                stq(c, c->ops, at + VOFF(z),       lir_i(0));
                stb(c, c->ops, at + VOFF(boolean), lir_r(value));
                stq(c, c->ops, at + VOFF(type),    lir_i(VALUE_BOOLEAN));
                break;

        case LT_PTR:
                stq(c, c->ops, at + VOFF(ptr),  lir_r(value));
                stq(c, c->ops, at + VOFF(type), lir_i(VALUE_PTR));
                break;

        default:
                stq(c, c->ops, at + VOFF(z),    lir_r(value));
                stq(c, c->ops, at + VOFF(type), lir_i(VALUE_INTEGER));
                break;
        }
}

static bool
kernel_call(
        BcLir *c,
        LirReg fn,
        Value const *callee,
        i32 out,
        i32 argc,
        LirLabel miss,
        LirLabel done
)
{
        LirCode const *code = callee->jit_code;

        if (c->compact || !kernel_ok(code, argc)) {
                return false;
        }

        expect(c, fn, 0, VALUE_JIT_FUNCTION, miss);

        LirReg live = ldp(c, fn, VOFF(jit_code));
        jcc(c, LIR_NE, lir_r(ldq(c, live, offsetof(LirCode, serial))), lir_i((i64)code->serial), miss);

        LirOpnd args[8];

        for (i32 i = 0; i < argc; ++i) {
                args[i] = lir_r(kernel_arg(c, code->sig.params[i], out + i, miss));
        }

        u32    flags  = (code->mode == LIR_MODE_DETACHED) ? CF_PURE : CF_VM;
        LirReg result = call_target(
                c,
                lir_i((uptr)code->body),
                code->sig.ret,
                code->sig.params,
                args,
                argc,
                flags
        );

        kernel_box(c, out, code->sig.ret, result);
        jump(c, done);

        return true;
}

static void
raw_object(Ty *ty, Value *dst, i32 class)
{
        TyObject *obj = class_new_instance(ty, class);
        u64       w[] = { VALUE_OBJECT, (u32)class, (uptr)obj, 0 };

        memcpy(dst, w, sizeof w);
}

static void
call_init(Ty *ty, Value *args, Value *init, Value *self, i32 argc)
{
        usize base   = args - ty->stack.items;
        Value object = *self;
        Value method = *init;

        ty->stack.count = base + argc;
        gP(&object);
        vm_call_method(ty, &object, &method, argc);
        gX();
        ty->stack.count = base;
}

static bool
inline_ctor(BcLir *c, LirReg fn, Value const *callee, i32 out, i32 argc, LirLabel *ready)
{
        if (callee->class <= CLASS_PRIMITIVE) {
                return false;
        }

        Class       *class = class_get(c->ctx, callee->class);
        Value const *init  = &class->init;

        if (
                !class->really_final
             || !roomy(init, argc)
             || (argc == 0 && expr_of(init)->fn->inert)
        ) {
                return false;
        }

        LirLabel miss = newlabel(c);
        LirLabel done = newlabel(c);

        expect(c, fn, 0, VALUE_CLASS, miss);
        unless(c, ldw(c, fn, VOFF(class)), class->i, miss);
        guard_epoch(c, miss);

        LirReg ctor = pval(c, init);
        LirReg code = ldp(c, ldp(c, ctor, VOFF(info)), FUN_JIT);

        jcc(c, LIR_ULT, lir_r(code), lir_i(JIT_PENDING), miss);

        for (i32 i = argc; i-- > 0;) {
                copy(c, c->ops, vat(out + i + 1), c->ops, vat(out + i));
        }

        count_at(c, out + argc + 1);
        tycall(c, raw_object, LT_VOID, preg(slot_of(c, out)), imm32(class->i));

        LirLabel failed   = newlabel(c);
        LirLabel finished = newlabel(c);

        c->sp += 1;
        try_plan(c, init, TY_INLINE_METHOD, argc, out + 1, slot_of(c, out), class, NULL, out + 1, finished);
        c->sp -= 1;

        inline_call(c, ctor, init, out + 1, argc, slot_of(c, out), failed, finished);

        bind(c, failed);

        LirReg args = slot_of(c, out + 1);
        LirReg self = slot_of(c, out);

        tycall(
                c,
                call_init,
                LT_VOID,
                preg(args),
                preg(ctor),
                preg(self),
                imm32(argc)
        );

        bind(c, finished);
        count_at(c, out + 1);
        jump(c, done);

        bind(c, miss);
        *ready = done;

        return true;
}
