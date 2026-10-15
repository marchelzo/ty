#include <setjmp.h>

#include "test.h"

static jmp_buf Errors;
static i32     Expected;
static i32     Actual;
static i32     BadArg;
static LirType BadType;
static u32     Unlocks;
static u32     Locks;
static u32     PtrCalls;
static bool    Interpreted;
static Array   NestedArray;

static void
arity_error(Ty *ty, i32 expected, i32 actual)
{
        Expected = expected;
        Actual   = actual;
        _longjmp(Errors, 1);
}

static void
arg_type_error(Ty *ty, i32 index, LirType type, Value const *value)
{
        BadArg  = index;
        BadType = type;
        _longjmp(Errors, 2);
}

inline static void *
moved(void const *p, uptr base, uptr end, Value const *items)
{
        uptr q = (uptr)p;

        if (base != 0 && q >= base && q < end) {
                q += (uptr)items - base;
        }

        return (void *)q;
}

static void
rebase(Ty *ty, LirEntryFrame *frame)
{
        uptr base = (uptr)frame->base;
        uptr end  = base + frame->capacity * sizeof (Value);

        frame->args     = moved(frame->args, base, end + 1, vv(ty->stack));
        frame->out      = moved(frame->out, base, end, vv(ty->stack));

        frame->base     = vv(ty->stack);
        frame->capacity = vC(ty->stack);
}

static void
grow(Ty *ty, usize n)
{
        Value *items = xtA0(Value, n + 8);

        if (vN(ty->stack) != 0) {
                memcpy(items, vv(ty->stack), vN(ty->stack) * sizeof *items);
        }

        xmF(vv(ty->stack));

        vv(ty->stack) = items;
        vC(ty->stack) = n + 8;
}

static void
reserve(Ty *ty, LirEntryFrame *frame, u32 n)
{
        frame->base     = vv(ty->stack);
        frame->capacity = vC(ty->stack);
        frame->top      = vN(ty->stack);

        if (vN(ty->stack) + n > vC(ty->stack)) {
                grow(ty, vN(ty->stack) + n);
        }

        rebase(ty, frame);

        for (u32 i = 0; i < n; ++i) {
                vPx(ty->stack, (Value) {0});
        }
}

static Value *
restore(Ty *ty, LirEntryFrame *frame)
{
        rebase(ty, frame);
        vN(ty->stack) = frame->top;
        return frame->out;
}

static void
unlock(Ty *ty)
{
        CHECK(ty->locked);
        ty->locked = false;
        Unlocks   += 1;
}

static void
lock(Ty *ty)
{
        CHECK(!ty->locked);
        ty->locked = true;
        Locks     += 1;
}

static void *
pointer_from(Ty *ty, LirEntryFrame *frame, i32 index)
{
        CHECK(ty->locked);
        PtrCalls += 1;

        Value v = frame->args[index];
        void *p = NULL;

        if (frame->base == NULL) {
                frame->base     = vv(ty->stack);
                frame->capacity = vC(ty->stack);
        }

        switch (v.type) {
        case VALUE_NIL:
                break;

        case VALUE_STRING:
                p = (void *)v.str;
                break;

        case VALUE_OBJECT:
                grow(ty, vN(ty->stack) + 32);
                p = v.object;
                break;

        default:
                arg_type_error(ty, index, LT_PTR, &v);
        }

        rebase(ty, frame);

        return p;
}

static void *
reference_from(Ty *ty, Value const *value, i32 index)
{
        if (value->type != VALUE_ARRAY) {
                arg_type_error(ty, index, LT_REF, value);
        }

        return value->array;
}

static LirRuntime const Runtime = {
        .interrupt      = &Interrupt,
        .poll           = handle_poll,
        .current_ty     = current_ty,
        .arity_error    = arity_error,
        .arg_type_error = arg_type_error,
        .ptr_from       = pointer_from,
        .ref_from       = reference_from,
        .reserve        = reserve,
        .restore        = restore,
        .unlock         = unlock,
        .lock           = lock
};

static LirCode *
finish(Lir *L)
{
        LirError err;
        LirCode *code = Interpreted
                      ? lir_finish_interpreted(ty, L, true, &err)
                      : lir_finish(ty, L, true, &err);

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
enter(LirCode *code, Ty *vm, Value const *args, i32 argc)
{
        Value out;

        memset(&out, 0xff, sizeof out);
        CurrentTy = vm;
        code->entry(vm, &out, args, argc);
        CHECK(vm->locked);

        return out;
}

static void
discard(LirCode *code, Lir *L)
{
        lir_code_free(code);
        lir_free(L);
}

static i64
narrowed(LirType type, i64 z)
{
        switch (type) {
        case LT_I8:  return (i8)z;
        case LT_U8:  return (u8)z;
        case LT_I16: return (i16)z;
        case LT_U16: return (u16)z;
        case LT_I32: return (i32)z;
        case LT_U32: return (u32)z;
        default:     return z;
        }
}

static Value
sample(LirType type, Array *array)
{
        switch (type) {
        case LT_F32:
        case LT_F64:  return REAL(1.1);
        case LT_BOOL: return BOOLEAN(true);
        case LT_PTR:  return PTR(array);
        case LT_REF:  return ARRAY(array);
        case LT_VAL:  return REAL(5.25);
        default:      return INTEGER(-123456789);
        }
}

static void
check_identity(void)
{
        static LirType const types[] = {
                LT_I8,  LT_U8,  LT_I16,  LT_U16,
                LT_I32, LT_U32, LT_I64,  LT_U64,
                LT_F32, LT_F64, LT_BOOL, LT_PTR,
                LT_VAL, LT_REF
        };

        Ty    vm    = { .locked = true };
        Array array = {0};

        for (u32 i = 0; i < countof(types); ++i) {
                LirType  type = types[i];
                Lir     *L    = fn(type, type);

                ret(L, L->params[0]);

                LirCode *code    = finish(L);
                Value    arg     = sample(type, &array);
                u32      unlocks = Unlocks;
                u32      locks   = Locks;
                Value    out     = enter(code, &vm, &arg, 1);

                switch (type) {
                case LT_F32:
                case LT_F64:
                        CHECK(out.type == VALUE_REAL);
                        CHECK(out.real == ((type == LT_F32) ? (float)arg.real : arg.real));
                        arg = INTEGER(57);
                        out = enter(code, &vm, &arg, 1);
                        CHECK(out.type == VALUE_REAL && out.real == 57.0);
                        break;

                case LT_BOOL:
                        CHECK(out.type == VALUE_BOOLEAN && out.boolean);
                        break;

                case LT_PTR:
                case LT_REF:
                        CHECK(out.type == VALUE_PTR && out.ptr == &array);
                        CHECK(out.gcptr == ((type == LT_REF) ? &array : NULL));
                        break;

                case LT_VAL:
                        CHECK(memcmp(&out, &arg, sizeof out) == 0);
                        code->entry(&vm, &arg, &arg, 1);
                        CHECK(arg.type == VALUE_REAL && arg.real == 5.25);
                        break;

                default:
                        CHECK(out.type == VALUE_INTEGER && out.z == narrowed(type, arg.z));
                        break;
                }

                bool kept = (Unlocks == unlocks) && (Locks == locks);

                CHECK(!code->release && kept);
                CHECK(vN(vm.stack) == 0);

                discard(code, L);
        }

        xmF(vv(vm.stack));
}

static void
check_errors(void)
{
        Ty   vm = { .locked = true };
        Lir *L  = fn(LT_I64, LT_I64);

        ret(L, L->params[0]);

        LirCode *code = finish(L);
        Value    arg  = REAL(1.25);
        Value    out  = {0};

        CurrentTy = &vm;

        if (_setjmp(Errors) == 0) {
                code->entry(&vm, &out, &arg, 0);
                CHECK(false);
        } else {
                CHECK(Expected == 1 && Actual == 0);
                CHECK(vm.locked && vN(vm.stack) == 0);
        }

        if (_setjmp(Errors) == 0) {
                code->entry(&vm, &out, &arg, 1);
                CHECK(false);
        } else {
                CHECK(BadArg == 0 && BadType == LT_I64);
                CHECK(vm.locked && vN(vm.stack) == 0);
        }

        discard(code, L);
        xmF(vv(vm.stack));
}

static void
check_vslots(void)
{
        Ty      vm   = { .locked = true };
        Lir    *L    = fn(LT_I64);
        LirReg  slot = lir_vslot(L);
        LirReg  r    = lir_reg(L, LIR_I64);
        LirOpnd mem  = field(slot, z);

        put(L, LIR_ST64, LIR_NONE, mem, lir_i(42));
        put(L, LIR_LD_I64, r, mem);
        ret(L, r);

        LirCode *code = finish(L);

        CHECK(code->nvslots == 1);

        Value out = enter(code, &vm, NULL, 0);

        CHECK(out.type == VALUE_INTEGER && out.z == 42);
        CHECK(vN(vm.stack) == 0 && v__(vm.stack, 0).z == 42);

        discard(code, L);
        xmF(vv(vm.stack));
}

static i64
observe_lock(void)
{
        return CurrentTy->locked;
}

static void
check_lock(void)
{
        Ty vm = { .locked = true };

        CurrentTy = &vm;

        for (u32 i = 0; i < 2; ++i) {
                Lir   *L = fn(LT_I64);
                LirReg r = lir_reg(L, LIR_I64);

                L->mode = i ? LIR_MODE_ATTACHED : LIR_MODE_DETACHED;

                push(L, call(callee(observe_lock), r, sig(LT_I64, NULL, 0), NULL));
                ret(L, r);

                LirCode *code = finish(L);
                Value    out  = enter(code, &vm, NULL, 0);

                CHECK(out.type == VALUE_INTEGER && out.z == i);

                discard(code, L);
        }

        CurrentTy = &EmptyTy;
}

static void
check_pointer_rebase(void)
{
        Value *items = xtA0(Value, 3);

        items[0] = OBJECT((TyObject *)0x1234, 0);
        items[1] = INTEGER(123);

        Ty vm = {
                .locked = true,
                .stack  = { .items = items, .count = 3, .capacity = 3 }
        };

        Lir *L = fn(LT_I64, LT_PTR, LT_I64);

        ret(L, L->params[1]);

        LirCode *code   = finish(L);
        u32      before = PtrCalls;

        CurrentTy = &vm;
        code->entry(&vm, v_(vm.stack, 2), vv(vm.stack), 2);

        CHECK(PtrCalls == before + 1);
        CHECK(v__(vm.stack, 2).type == VALUE_INTEGER && v__(vm.stack, 2).z == 123);
        CHECK(vN(vm.stack) == 3 && vm.locked);

        discard(code, L);
        xmF(vv(vm.stack));
}

static void
grow_current(void)
{
        grow(CurrentTy, vN(CurrentTy->stack) + 64);
}

static void
check_call_rebase(void)
{
        Ty vm = { .locked = true };

        grow(&vm, 1);
        vPx(vm.stack, INTEGER(42));

        Lir   *L     = fn(LT_I64, LT_VAL);
        LirReg local = lir_reg(L, LIR_PTR);
        LirReg slots[48];

        put(L, LIR_ALLOCA, local, lir_i(65536), lir_i(16));
        put(L, LIR_ST64, LIR_NONE, deref(local, 0), lir_i(5));

        for (u32 i = 0; i < countof(slots); ++i) {
                slots[i] = lir_vslot(L);
                put(L, LIR_ST64, LIR_NONE, field(slots[i], z), lir_i(i));
        }

        LirInst gc = vcall(callee(grow_current));
        gc.flags = LIR_MAY_GC;
        push(L, gc);

        LirReg sum = lir_reg(L, LIR_I64);
        LirReg x   = lir_reg(L, LIR_I64);

        put(L, LIR_LD_I64, sum, field(L->params[0], z));
        put(L, LIR_LD_I64, x, deref(local, 0));
        put(L, LIR_ADD, sum, lir_r(sum), lir_r(x));

        for (u32 i = 0; i < countof(slots); ++i) {
                put(L, LIR_LD_I64, x, field(slots[i], z));
                put(L, LIR_ADD, sum, lir_r(sum), lir_r(x));
        }

        ret(L, sum);

        LirCode *code = finish(L);
        Value    out  = enter(code, &vm, vv(vm.stack), 1);

        CHECK(out.type == VALUE_INTEGER && out.z == 1175);
        CHECK(vN(vm.stack) == 1 && v__(vm.stack, 0).z == 42);

        discard(code, L);
        xmF(vv(vm.stack));
}

static bool
nested_root(Value const *v)
{
        return (v->type == VALUE_PTR)
            && (v->gcptr == &NestedArray)
            && (v->extra == &LirRefRoot);
}

static void
observe_nested_roots(void)
{
        bool value = false;
        bool root  = false;

        vfor(CurrentTy->stack, {
                value |= (it->type == VALUE_INTEGER) && (it->z == 42);
                root  |= nested_root(it);
        });

        CHECK(value && root);
        grow(CurrentTy, vN(CurrentTy->stack) + 64);
}

static void
integer_slot(Lir *L, i64 z)
{
        LirReg slot = lir_vslot(L);

        put(L, LIR_ST8, LIR_NONE, field(slot, type), lir_i(VALUE_INTEGER));
        put(L, LIR_ST64, LIR_NONE, field(slot, z), lir_i(z));
}

static void
check_nested_slots(void)
{
        Ty   vm    = { .locked = true };
        Lir *child = fn(LT_VOID);

        for (u32 i = 0; i < 5; ++i) {
                integer_slot(child, 99 + i);
        }

        LirInst observe = vcall(callee(observe_nested_roots));
        observe.flags = LIR_MAY_GC;
        push(child, observe);
        ret(child, LIR_NONE);

        LirCode *inner = finish(child);
        Lir     *L      = fn(LT_REF, LT_REF);

        integer_slot(L, 42);

        LirInst in = vcall((LirOpnd) { .kind = LO_CODE, .code = inner });
        in.flags = LIR_MAY_GC | LIR_MAY_THROW;
        push(L, in);
        ret(L, L->params[0]);

        LirCode *outer = finish(L);
        Value    arg   = ARRAY(&NestedArray);
        Value    out   = enter(outer, &vm, &arg, 1);

        CHECK(out.type == VALUE_PTR && out.gcptr == &NestedArray);
        CHECK(vN(vm.stack) == 0);

        discard(outer, L);
        discard(inner, child);
        xmF(vv(vm.stack));
}

int
main(void)
{
        lir_set_runtime(&Runtime);

        for (u32 i = 0; i < 2; ++i) {
                Interpreted = (i != 0);
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

        return report("LIR entry");
}
