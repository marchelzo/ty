#define LIR_NATIVE
#define main scalar_fixture_main
#include "lir_interp.c"
#undef main

static jmp_buf Errors;
static i32 Expected;
static i32 Actual;
static i32 BadArg;
static LirType BadType;
static u32 Unlocks;
static u32 Locks;
static u32 PtrCalls;
static bool Interpreted;

static void
arity_error(Ty *ty, i32 expected, i32 actual)
{
        (void)ty;
        Expected = expected;
        Actual = actual;
        _longjmp(Errors, 1);
}

static void
arg_type_error(Ty *ty, i32 index, LirType type, Value const *value)
{
        (void)ty;
        (void)value;
        BadArg = index;
        BadType = type;
        _longjmp(Errors, 2);
}

static void
rebase(Ty *ty, LirEntryFrame *frame)
{
        uptr base = (uptr)frame->base;
        uptr end = base + frame->capacity * sizeof (Value);
        uptr a = (uptr)frame->args;
        uptr o = (uptr)frame->out;
        if (base != 0 && a >= base && a <= end) {
                frame->args = (void *)((uptr)ty->stack.items + a - base);
        }
        if (base != 0 && o >= base && o < end) {
                frame->out = (void *)((uptr)ty->stack.items + o - base);
        }
        frame->base     = ty->stack.items;
        frame->capacity = ty->stack.capacity;
}

static void
grow(Ty *ty, usize n)
{
        Value *items = calloc(n + 8, sizeof *items);
        CHECK(items != NULL);
        if (ty->stack.count != 0) {
                memcpy(items, ty->stack.items, ty->stack.count * sizeof *items);
        }
        free(ty->stack.items);
        ty->stack.items = items;
        ty->stack.capacity = n + 8;
}

static void
reserve(Ty *ty, LirEntryFrame *frame, u32 n)
{
        frame->base     = ty->stack.items;
        frame->capacity = ty->stack.capacity;
        frame->top      = ty->stack.count;
        if (ty->stack.count + n > ty->stack.capacity) {
                grow(ty, ty->stack.count + n);
        }
        rebase(ty, frame);
        for (u32 i = 0; i < n; ++i) {
                ty->stack.items[ty->stack.count++] = (Value) {0};
        }
}

static Value *
restore(Ty *ty, LirEntryFrame *frame)
{
        rebase(ty, frame);
        ty->stack.count = frame->top;
        return frame->out;
}

static void
unlock(Ty *ty)
{
        CHECK(ty->locked);
        ty->locked = false;
        ++Unlocks;
}

static void
lock(Ty *ty)
{
        CHECK(!ty->locked);
        ty->locked = true;
        ++Locks;
}

static void *
pointer_from(Ty *ty, LirEntryFrame *frame, i32 index)
{
        CHECK(ty->locked);
        ++PtrCalls;
        Value v = frame->args[index];
        void *p = NULL;
        switch (v.type) {
        case VALUE_NIL: break;
        case VALUE_STRING: p = (void *)v.str; break;
        case VALUE_OBJECT:
                grow(ty, ty->stack.count + 32);
                p = v.object;
                break;
        default:
                arg_type_error(ty, index, LIR_TYPE_PTR, &v);
        }
        rebase(ty, frame);
        return p;
}

static void *
reference_from(Ty *ty, Value const *value, i32 index)
{
        if (value->type != VALUE_ARRAY) {
                arg_type_error(ty, index, LIR_TYPE_REF, value);
        }
        return value->array;
}

static LirRuntime const Runtime = {
        .interrupt = &Interrupt,
        .poll = handle_poll,
        .current_ty = current_ty,
        .arity_error = arity_error,
        .arg_type_error = arg_type_error,
        .ptr_from = pointer_from,
        .ref_from = reference_from,
        .reserve = reserve,
        .restore = restore,
        .unlock = unlock,
        .lock = lock
};

static LirCode *
finish_entry(Lir *L)
{
        LirError err;
        LirCode *code = Interpreted ? lir_finish_interpreted(L, true, &err) : lir_finish(L, true, &err);
        CHECK(code != NULL);
        if (code == NULL) {
                fprintf(stderr, "entry op %u: %s\n", err.op, err.message);
                lir_dump(L, stderr);
                exit(1);
        }
        CHECK(code->entry != NULL && code->entry_code != NULL);
        return code;
}

static Value
invoke(LirCode *code, Ty *ty, Value const *args, i32 argc)
{
        Value out;
        memset(&out, 0xff, sizeof out);
        CurrentTy = ty;
        code->entry(ty, &out, args, argc);
        CHECK(ty->locked);
        return out;
}

static void
check_identity(void)
{
        LirType types[] = {
                LIR_TYPE_I8, LIR_TYPE_U8, LIR_TYPE_I16, LIR_TYPE_U16,
                LIR_TYPE_I32, LIR_TYPE_U32, LIR_TYPE_I64, LIR_TYPE_U64,
                LIR_TYPE_F32, LIR_TYPE_F64, LIR_TYPE_BOOL, LIR_TYPE_PTR,
                LIR_TYPE_VAL, LIR_TYPE_REF
        };
        Ty ty = { .locked = true };
        Array array = {0};
        for (u32 i = 0; i < countof(types); ++i) {
                LirType type = types[i];
                Lir *L = function(type, &type, 1);
                ret(L, lir_r(L->params[0]));
                LirCode *code = finish_entry(L);
                Value arg = INTEGER(-123456789);
                if (type == LIR_TYPE_F32 || type == LIR_TYPE_F64) {
                        arg = REAL(1.1);
                } else if (type == LIR_TYPE_BOOL) {
                        arg = BOOLEAN(true);
                } else if (type == LIR_TYPE_PTR) {
                        arg = PTR(&array);
                } else if (type == LIR_TYPE_REF) {
                        arg = ARRAY(&array);
                } else if (type == LIR_TYPE_VAL) {
                        arg = REAL(5.25);
                }
                u32 unlocks = Unlocks;
                u32 locks = Locks;
                Value out = invoke(code, &ty, &arg, 1);
                if (type <= LIR_TYPE_U64) {
                        i64 expected = arg.z;
                        switch (type) {
                        case LIR_TYPE_I8: expected = (i8)arg.z; break;
                        case LIR_TYPE_U8: expected = (u8)arg.z; break;
                        case LIR_TYPE_I16: expected = (i16)arg.z; break;
                        case LIR_TYPE_U16: expected = (u16)arg.z; break;
                        case LIR_TYPE_I32: expected = (i32)arg.z; break;
                        case LIR_TYPE_U32: expected = (u32)arg.z; break;
                        default: break;
                        }
                        CHECK(out.type == VALUE_INTEGER && out.z == expected);
                } else if (type == LIR_TYPE_F32 || type == LIR_TYPE_F64) {
                        CHECK(out.type == VALUE_REAL);
                        CHECK(out.real == (type == LIR_TYPE_F32 ? (double)(float)arg.real : arg.real));
                        arg = INTEGER(57);
                        out = invoke(code, &ty, &arg, 1);
                        CHECK(out.type == VALUE_REAL && out.real == 57.0);
                } else if (type == LIR_TYPE_BOOL) {
                        CHECK(out.type == VALUE_BOOLEAN && out.boolean);
                } else if (type == LIR_TYPE_PTR || type == LIR_TYPE_REF) {
                        CHECK(out.type == VALUE_PTR && out.ptr == &array);
                        CHECK(out.gcptr == (type == LIR_TYPE_REF ? &array : NULL));
                } else {
                        CHECK(memcmp(&out, &arg, sizeof out) == 0);
                        code->entry(&ty, &arg, &arg, 1);
                        CHECK(arg.type == VALUE_REAL && arg.real == 5.25);
                }
                bool detached = code->mode == LIR_MODE_DETACHED;
                CHECK(detached ? Unlocks > unlocks && Locks > locks : Unlocks == unlocks && Locks == locks);
                CHECK(ty.stack.count == 0);
                lir_code_free(code);
                lir_free(L);
        }
        free(ty.stack.items);
}

static void
check_errors(void)
{
        Ty ty = { .locked = true };
        LirType type = LIR_TYPE_I64;
        Lir *L = function(type, &type, 1);
        ret(L, lir_r(L->params[0]));
        LirCode *code = finish_entry(L);
        Value arg = REAL(1.25);
        Value out = {0};
        CurrentTy = &ty;
        if (_setjmp(Errors) == 0) {
                code->entry(&ty, &out, &arg, 0);
                CHECK(false);
        } else {
                CHECK(Expected == 1 && Actual == 0);
                CHECK(ty.locked && ty.stack.count == 0);
        }
        if (_setjmp(Errors) == 0) {
                code->entry(&ty, &out, &arg, 1);
                CHECK(false);
        } else {
                CHECK(BadArg == 0 && BadType == LIR_TYPE_I64);
                CHECK(ty.locked && ty.stack.count == 0);
        }
        lir_code_free(code);
        lir_free(L);
        free(ty.stack.items);
}

static void
check_vslots(void)
{
        Ty ty = { .locked = true };
        Lir *L = function(LIR_TYPE_I64, NULL, 0);
        LirReg slot = lir_vslot(L);
        LirOpnd mem = lir_m(slot, LIR_NONE, 1, offsetof(Value, z));
        emit(L, LIR_ST64, LIR_NONE, (LirOpnd[]) { mem, lir_i(42) }, 2);
        LirReg r = lir_reg(L, LIR_I64);
        emit(L, LIR_LD_I64, r, &mem, 1);
        ret(L, lir_r(r));
        LirCode *code = finish_entry(L);
        CHECK(code->nvslots == 1);
        Value out = invoke(code, &ty, NULL, 0);
        CHECK(out.type == VALUE_INTEGER && out.z == 42);
        CHECK(ty.stack.count == 0 && ty.stack.items[0].z == 42);
        lir_code_free(code);
        lir_free(L);
        free(ty.stack.items);
}

static i64
observe_lock(void)
{
        return CurrentTy->locked;
}

static void
check_lock(void)
{
        Ty ty = { .locked = true };
        CurrentTy = &ty;
        for (u32 i = 0; i < 2; ++i) {
                Lir *L = function(LIR_TYPE_I64, NULL, 0);
                L->mode = i ? LIR_MODE_ATTACHED : LIR_MODE_DETACHED;
                LirReg r = lir_reg(L, LIR_I64);
                LirInst call = {
                        .op = LIR_CALL, .dst = r,
                        .args = { lir_i((uptr)observe_lock) }, .nargs = 1,
                        .sig = { .ret = LIR_TYPE_I64 }
                };
                CHECK(lir_emit(L, &call));
                ret(L, lir_r(r));
                LirCode *code = finish_entry(L);
                Value out = invoke(code, &ty, NULL, 0);
                CHECK(out.type == VALUE_INTEGER && out.z == i);
                lir_code_free(code);
                lir_free(L);
        }
}

static void
check_pointer_rebase(void)
{
        Ty ty = { .locked = true };
        ty.stack.items = calloc(3, sizeof (Value));
        ty.stack.count = ty.stack.capacity = 3;
        ty.stack.items[0] = OBJECT((TyObject *)0x1234, 0);
        ty.stack.items[1] = INTEGER(123);
        LirType types[] = { LIR_TYPE_PTR, LIR_TYPE_I64 };
        Lir *L = function(LIR_TYPE_I64, types, countof(types));
        ret(L, lir_r(L->params[1]));
        LirCode *code = finish_entry(L);
        u32 before = PtrCalls;
        CurrentTy = &ty;
        code->entry(&ty, &ty.stack.items[2], ty.stack.items, 2);
        CHECK(PtrCalls == before + 1);
        CHECK(ty.stack.items[2].type == VALUE_INTEGER && ty.stack.items[2].z == 123);
        CHECK(ty.stack.count == 3 && ty.locked);
        lir_code_free(code);
        lir_free(L);
        free(ty.stack.items);
}

static void
grow_current(void)
{
        grow(CurrentTy, CurrentTy->stack.count + 64);
}

static void
check_call_rebase(void)
{
        Ty ty = { .locked = true };
        grow(&ty, 1);
        ty.stack.items[ty.stack.count++] = INTEGER(42);
        LirType type = LIR_TYPE_VAL;
        Lir *L = function(LIR_TYPE_I64, &type, 1);
        LirReg slots[48];
        LirReg local = lir_reg(L, LIR_PTR);
        emit(L, LIR_ALLOCA, local, (LirOpnd[]) { lir_i(65536), lir_i(16) }, 2);
        emit(L, LIR_ST64, LIR_NONE,
             (LirOpnd[]) { lir_m(local, LIR_NONE, 1, 0), lir_i(5) }, 2);
        for (u32 i = 0; i < countof(slots); ++i) {
                slots[i] = lir_vslot(L);
                emit(L, LIR_ST64, LIR_NONE,
                     (LirOpnd[]) { lir_m(slots[i], LIR_NONE, 1, offsetof(Value, z)), lir_i(i) }, 2);
        }
        LirInst call = {
                .op = LIR_CALL, .dst = LIR_NONE, .nargs = 1,
                .args = { lir_i((uptr)grow_current) },
                .sig = { .ret = LIR_VOID }, .flags = LIR_MAY_GC
        };
        CHECK(lir_emit(L, &call));
        LirReg sum = lir_reg(L, LIR_I64);
        LirOpnd mem = lir_m(L->params[0], LIR_NONE, 1, offsetof(Value, z));
        emit(L, LIR_LD_I64, sum, &mem, 1);
        LirReg x = lir_reg(L, LIR_I64);
        mem = lir_m(local, LIR_NONE, 1, 0);
        emit(L, LIR_LD_I64, x, &mem, 1);
        emit(L, LIR_ADD, sum, (LirOpnd[]) { lir_r(sum), lir_r(x) }, 2);
        for (u32 i = 0; i < countof(slots); ++i) {
                mem = lir_m(slots[i], LIR_NONE, 1, offsetof(Value, z));
                emit(L, LIR_LD_I64, x, &mem, 1);
                emit(L, LIR_ADD, sum, (LirOpnd[]) { lir_r(sum), lir_r(x) }, 2);
        }
        ret(L, lir_r(sum));
        LirCode *code = finish_entry(L);
        Value out = invoke(code, &ty, ty.stack.items, 1);
        CHECK(out.type == VALUE_INTEGER && out.z == 1175);
        CHECK(ty.stack.count == 1 && ty.stack.items[0].z == 42);
        lir_code_free(code);
        lir_free(L);
        free(ty.stack.items);
}

static Array NestedArray;

static void
observe_nested_roots(void)
{
        bool value = false;
        bool root = false;
        for (usize i = 0; i < CurrentTy->stack.count; ++i) {
                Value const *v = &CurrentTy->stack.items[i];
                value = value || (v->type == VALUE_INTEGER && v->z == 42);
                root = root || (v->type == VALUE_PTR && v->gcptr == &NestedArray && v->extra == &LirRefRoot);
        }
        CHECK(value && root);
        grow(CurrentTy, CurrentTy->stack.count + 64);
}

static void
check_nested_slots(void)
{
        Ty ty = { .locked = true };
        Lir *child = function(LIR_VOID, NULL, 0);
        for (u32 i = 0; i < 5; ++i) {
                LirReg slot = lir_vslot(child);
                emit(child, LIR_ST8, LIR_NONE,
                     (LirOpnd[]) { lir_m(slot, LIR_NONE, 1, offsetof(Value, type)), lir_i(VALUE_INTEGER) }, 2);
                emit(child, LIR_ST64, LIR_NONE,
                     (LirOpnd[]) { lir_m(slot, LIR_NONE, 1, offsetof(Value, z)), lir_i(99 + i) }, 2);
        }
        LirInst observe = { .op = LIR_CALL, .dst = LIR_NONE, .nargs = 1,
                            .args = { lir_i((uptr)observe_nested_roots) },
                            .sig = { .ret = LIR_VOID }, .flags = LIR_MAY_GC };
        CHECK(lir_emit(child, &observe));
        emit(child, LIR_RET, LIR_NONE, NULL, 0);
        LirCode *callee = finish_entry(child);
        LirType type = LIR_TYPE_REF;
        Lir *L = function(LIR_TYPE_REF, &type, 1);
        LirReg slot = lir_vslot(L);
        emit(L, LIR_ST8, LIR_NONE,
             (LirOpnd[]) { lir_m(slot, LIR_NONE, 1, offsetof(Value, type)), lir_i(VALUE_INTEGER) }, 2);
        emit(L, LIR_ST64, LIR_NONE,
             (LirOpnd[]) { lir_m(slot, LIR_NONE, 1, offsetof(Value, z)), lir_i(42) }, 2);
        LirInst call = { .op = LIR_CALL, .dst = LIR_NONE, .nargs = 1,
                         .args = { { .kind = LIR_OPERAND_CODE, .code = callee } },
                         .sig = { .ret = LIR_VOID }, .flags = LIR_MAY_GC | LIR_MAY_THROW };
        CHECK(lir_emit(L, &call));
        ret(L, lir_r(L->params[0]));
        LirCode *caller = finish_entry(L);
        Value arg = ARRAY(&NestedArray);
        Value out = invoke(caller, &ty, &arg, 1);
        CHECK(out.type == VALUE_PTR && out.gcptr == &NestedArray);
        CHECK(ty.stack.count == 0);
        lir_code_free(caller);
        lir_code_free(callee);
        lir_free(L);
        lir_free(child);
        free(ty.stack.items);
}

int
main(void)
{
        lir_set_runtime(&Runtime);
        for (u32 i = 0; i < 2; ++i) {
                Interpreted = i != 0;
                check_identity();
                check_errors();
                check_vslots();
                check_lock();
                check_pointer_rebase();
                check_call_rebase();
                check_nested_slots();
        }
        lir_set_runtime(NULL);
        CurrentTy = &EmptyTy;
        CHECK(jm_stats().nchunks == 0);
        printf("LIR entry: %u checks, %u failures\n", checks, failures);
        return failures != 0;
}
