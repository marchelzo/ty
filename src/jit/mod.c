#include <stdlib.h>
#include <string.h>

#include "jit/jitmod.h"
#include "jit/lir.h"
#include "value.h"
#include "vm.h"
#include "dict.h"
#include "gc.h"
#include "functions.h"
#include "compiler.h"
#include "scope.h"

#define ASM(i)  asm_arg(ty, &ARG(i))
#define CODE(i) code_arg(ty, &ARG(i))
#define INT(i)  integer(ty, &ARG(i))

#define snew(T, n) ((T *)smA((usize)(n) * sizeof (T)))

#define GC_THROW (LIR_MAY_GC | LIR_MAY_THROW)

typedef struct {
        Value *out;
        isize  index;
        usize  top;
} Slot;

inline static bool
isgc(Value const *v, int type)
{
        return (v->type == VALUE_PTR)
            && (v->gcptr != NULL)
            && (ALLOC_OF(v->gcptr)->type == type);
}

inline static bool
inrange(Value const *v, i64 lo, i64 hi)
{
        return (v->type == VALUE_INTEGER) && (v->z >= lo) && (v->z < hi);
}

inline static LirOpnd
lcode(LirCode *code)
{
        return (LirOpnd) { .kind = LO_CODE, .code = code };
}

inline static LirOpnd
lhelper(LirHelper const *helper)
{
        return (LirOpnd) { .kind = LO_HELPER, .helper = helper };
}

inline static u32
code_flags(LirCode const *code)
{
        return (code->mode == LIR_MODE_ATTACHED) ? GC_THROW : 0;
}

static Lir *
asm_arg(Ty *ty, Value const *v)
{
        if (!isgc(v, GC_LIR)) {
                zP("jit: expected an assembler handle");
        }

        return v->ptr;
}

static LirCode *
code_arg(Ty *ty, Value const *v)
{
        if (v->type == VALUE_JIT_FUNCTION) {
                return v->jit_code;
        }

        if (!isgc(v, GC_JIT_CODE)) {
                zP("jit: expected a code object");
        }

        return v->gcptr;
}

static i64
integer(Ty *ty, Value const *v)
{
        if (v->type != VALUE_INTEGER) {
                zP("jit: expected an integer");
        }

        return v->z;
}

static LirType
ctype(Ty *ty, Value const *v)
{
        i64 n = integer(ty, v);

        if (n < 0 || n >= LT_COUNT) {
                zP("jit: invalid C type %" PRId64, n);
        }

        return n;
}

static LirType *
ctypes(Ty *ty, Array const *xs)
{
        LirType *ts = snew(LirType, vN(*xs));

        for (usize i = 0; i < vN(*xs); ++i) {
                ts[i] = ctype(ty, v_(*xs, i));
        }

        return ts;
}

static LirType
ffi_ctype(Ty *ty, ffi_type const *type)
{
        switch (type->type) {
        case FFI_TYPE_VOID:    return LT_VOID;
        case FFI_TYPE_SINT8:   return LT_I8;
        case FFI_TYPE_UINT8:   return LT_U8;
        case FFI_TYPE_SINT16:  return LT_I16;
        case FFI_TYPE_UINT16:  return LT_U16;
        case FFI_TYPE_INT:
        case FFI_TYPE_SINT32:  return LT_I32;
        case FFI_TYPE_UINT32:  return LT_U32;
        case FFI_TYPE_SINT64:  return LT_I64;
        case FFI_TYPE_UINT64:  return LT_U64;
        case FFI_TYPE_FLOAT:   return LT_F32;
        case FFI_TYPE_DOUBLE:  return LT_F64;
        case FFI_TYPE_POINTER: return LT_PTR;
        }

        zP("jit: this foreign signature uses a non-scalar C type");
}

static void
arity(Value const *v, LirSig *sig)
{
        if (v->xinfo != NULL && v->xinfo->ffi_signature) {
                sig->nfixed   = v->xinfo->ffi_nfixed;
                sig->variadic = v->xinfo->ffi_variadic;
        }
#if defined(__APPLE__) && defined(__aarch64__)
        else if (v->ffi->aarch64_nfixedargs != 0) {
                sig->nfixed   = v->ffi->aarch64_nfixedargs;
                sig->variadic = true;
        }
#endif
}

static LirSig *
foreign_sig(Ty *ty, Value const *v)
{
        ffi_cif const *cif = v->ffi;
        LirSig        *sig = snew(LirSig, 1);
        LirType       *ps  = snew(LirType, cif->nargs);

        for (u32 i = 0; i < cif->nargs; ++i) {
                ps[i] = ffi_ctype(ty, cif->arg_types[i]);
        }

        *sig = (LirSig) {
                .ret     = ffi_ctype(ty, cif->rtype),
                .params  = ps,
                .nparams = cif->nargs,
                .nfixed  = cif->nargs
        };

        arity(v, sig);

        return sig;
}

static Value
types_of(Ty *ty, LirSig const *sig)
{
        Value ts = ARRAY(vA());

        for (u32 i = 0; i < sig->nparams; ++i) {
                vAp(ts.array, INTEGER(sig->params[i]));
        }

        return ts;
}

static Value
error_value(Ty *ty, LirError const *err)
{
        GC_STOP();

        Value out = vT(5);

        out.items[0] = vSsz(err->message);
        out.items[1] = INTEGER((err->op == LIR_NONE) ? -1 : (i64)err->op);
        out.items[2] = INTEGER(err->span.source);
        out.items[3] = INTEGER(err->span.start);
        out.items[4] = INTEGER(err->span.end);

        GC_RESUME();

        return out;
}

static Value
outcome(Ty *ty, Value v, LirError const *err)
{
        GC_STOP();
        Value out = (err == NULL) ? PAIR(v, NIL) : PAIR(NIL, error_value(ty, err));
        GC_RESUME();

        return out;
}

static Value *
field(Value const *meta, char const *key)
{
        return (meta->type == VALUE_DICT) ? dict_get_member(NULL, meta->dict, key) : NULL;
}

static Array *
list(Value const *v)
{
        return (v != NULL && v->type == VALUE_ARRAY) ? v->array : NULL;
}

static i64
optint(Ty *ty, Value const *meta, char const *key, i64 fallback)
{
        Value const *v = field(meta, key);
        return (v == NULL) ? fallback : integer(ty, v);
}

static Slot
slot(Ty *ty, Value *out)
{
        uptr p    = (uptr)out;
        uptr base = (uptr)vv(ty->stack);
        uptr end  = base + vN(ty->stack) * sizeof (Value);
        bool on   = (base != 0) && (p >= base) && (p < end);

        return (Slot) {
                .out   = out,
                .index = on ? (isize)((p - base) / sizeof (Value)) : -1,
                .top   = vN(ty->stack)
        };
}

static Value *
where(Ty *ty, Slot const *s)
{
        return (s->index < 0) ? s->out : v_(ty->stack, s->index);
}

static void
put(Ty *ty, Slot const *s, Value v)
{
        *where(ty, s) = v;
        vN(ty->stack) = s->top;
}

static void
rt_call(Ty *ty, Value *out, Value const *f, Value const *args)
{
        Slot         s  = slot(ty, out);
        Value        fn = *f;
        Value        xs = *args;
        Value const *items;
        usize        n;

        switch (xs.type) {
        case VALUE_ARRAY: items = vv(*xs.array); n = vN(*xs.array); break;
        case VALUE_TUPLE: items = xs.items;      n = xs.count;      break;
        default:          zP("jit.rt.call: expected an array or tuple of arguments");
        }

        gP(&fn);
        gP(&xs);

        for (usize i = 0; i < n; ++i) {
                vm_push(ty, &items[i]);
        }

        put(ty, &s, vm_call(ty, &fn, n));

        gX();
        gX();
}

static void
rt_array_new(Ty *ty, Value *out)
{
        Slot s = slot(ty, out);
        put(ty, &s, ARRAY(vA()));
}

static void
rt_array_push(Ty *ty, Value *out, Value const *array, Value const *value)
{
        Slot  s  = slot(ty, out);
        Value xs = *array;
        Value v  = *value;

        if (xs.type != VALUE_ARRAY) {
                zP("jit.rt.array-push: expected an array");
        }

        gP(&xs);
        gP(&v);
        vAp(xs.array, v);
        put(ty, &s, xs);
        gX();
        gX();
}

static void
rt_binary(Ty *ty, Value *out, Value const *a, Value const *b, int op)
{
        Slot  s = slot(ty, out);
        Value x = *a;
        Value y = *b;

        gP(&x);
        gP(&y);
        put(ty, &s, vm_2op(ty, op, &x, &y));
        gX();
        gX();
}

#define BINARY(name, op)                                                \
        static void                                                     \
        rt_##name(Ty *ty, Value *out, Value const *a, Value const *b)   \
        {                                                               \
                rt_binary(ty, out, a, b, op);                           \
        }

BINARY(add, OP_ADD)
BINARY(sub, OP_SUB)
BINARY(mul, OP_MUL)
BINARY(div, OP_DIV)
BINARY(mod, OP_MOD)
BINARY(eq,  OP_EQL)
BINARY(ne,  OP_NEQ)
BINARY(lt,  OP_LT)
BINARY(le,  OP_LEQ)
BINARY(gt,  OP_GT)
BINARY(ge,  OP_GEQ)
BINARY(cmp, OP_CMP)

#undef BINARY

static void
rt_pow(Ty *ty, Value *out, Value const *a, Value const *b)
{
        Slot  s = slot(ty, out);
        Value x = *a;
        Value y = *b;

        gP(&x);
        gP(&y);
        vm_push(ty, &x);
        vm_push(ty, &y);
        put(ty, &s, builtin_pow(ty, 2, NULL));
        gX();
        gX();
}

static void
rt_subscript(Ty *ty, Value *out, Value const *a, Value const *b)
{
        Slot  s   = slot(ty, out);
        Value x   = *a;
        Value key = *b;

        vm_push(ty, &x);
        vm_push(ty, &key);
        DoSubscript(ty, true);
        put(ty, &s, *vm_pop(ty));
}

static void
rt_subscript_set(Ty *ty, Value *out, Value const *a, Value const *b, Value const *c)
{
        Slot  s     = slot(ty, out);
        Value x     = *a;
        Value key   = *b;
        Value value = *c;

        vm_push(ty, &value);
        vm_push(ty, &x);
        vm_push(ty, &key);
        DoAssignSubscript(ty, 1, true);
        put(ty, &s, *vm_pop(ty));
}

static i32
member_id(Ty *ty, Value const *key)
{
        if (key->type != VALUE_STRING) {
                zP("jit.rt.member: expected a string member name");
        }

        return M_ID(TY_C_STR(*key));
}

static void
rt_member(Ty *ty, Value *out, Value const *a, Value const *b)
{
        Slot  s  = slot(ty, out);
        Value x  = *a;
        i32   id = member_id(ty, b);

        vm_push(ty, &x);
        put(ty, &s, vm_jit_member_access(ty, id));
}

static void
rt_member_set(Ty *ty, Value *out, Value const *a, Value const *b, Value const *c)
{
        Slot  s     = slot(ty, out);
        Value x     = *a;
        Value value = *c;
        i32   id    = member_id(ty, b);

        gP(&x);
        vm_push(ty, &value);
        vm_jit_target_member(ty, &x, id);
        DoAssignExec(ty);
        put(ty, &s, *vm_pop(ty));
        gX();
}

static void
rt_call_method(Ty *ty, Value *out, Value const *a, Value const *b, Value const *c)
{
        Slot  s    = slot(ty, out);
        Value self = *a;
        Value key  = *b;
        Value args = *c;

        gP(&self);
        gP(&args);

        i32 id = member_id(ty, &key);

        vm_push(ty, &self);

        Value fn = vm_jit_member_access(ty, id);

        rt_call(ty, where(ty, &s), &fn, &args);
        vN(ty->stack) = s.top;

        gX();
        gX();
}

static void
rt_dict_new(Ty *ty, Value *out)
{
        Slot s = slot(ty, out);
        put(ty, &s, DICT(dict_new(ty)));
}

static void
rt_dict_get(Ty *ty, Value *out, Value const *a, Value const *b)
{
        Slot  s    = slot(ty, out);
        Value dict = *a;
        Value key  = *b;

        if (dict.type != VALUE_DICT) {
                zP("jit.rt.dict-get: expected a dictionary");
        }

        gP(&dict);
        gP(&key);

        Value *v = dict_get_value(ty, dict.dict, &key);

        put(ty, &s, (v == NULL) ? NIL : *v);
        gX();
        gX();
}

static void
rt_dict_set(Ty *ty, Value *out, Value const *a, Value const *b, Value const *c)
{
        Slot  s     = slot(ty, out);
        Value dict  = *a;
        Value key   = *b;
        Value value = *c;

        if (dict.type != VALUE_DICT) {
                zP("jit.rt.dict-set: expected a dictionary");
        }

        gP(&dict);
        gP(&key);
        gP(&value);
        dict_put_value(ty, dict.dict, key, value);
        put(ty, &s, dict);
        gX();
        gX();
        gX();
}

static void
rt_str_concat(Ty *ty, Value *out, Value const *a, Value const *b)
{
        if (a->type != VALUE_STRING || b->type != VALUE_STRING) {
                zP("jit.rt.str-concat: expected two strings");
        }

        rt_binary(ty, out, a, b, OP_ADD);
}

static void
rt_to_string(Ty *ty, Value *out, Value const *a)
{
        Slot  s = slot(ty, out);
        Value v = *a;

        gP(&v);

        if (v.type == VALUE_PTR) {
                v = vSsz(VSC(&v));
        } else if (v.type != VALUE_STRING && v.type != VALUE_NIL) {
                vm_push(ty, &v);
                CallMethod(ty, NAMES._str_, 0, 0, false, true);
                v = *vm_pop(ty);
        }

        put(ty, &s, v);
        gX();
}

static void
rt_hash(Ty *ty, Value *out, Value const *a)
{
        Slot  s = slot(ty, out);
        Value v = *a;

        gP(&v);
        put(ty, &s, INTEGER(value_hash(ty, &v)));
        gX();
}

static void
rt_throw(Ty *ty, Value const *a)
{
        Value v = *a;
        vm_throw(ty, &v);
}

static void
rt_alloc_object(Ty *ty, Value *out, Value const *a)
{
        Slot s = slot(ty, out);

        if (a->type != VALUE_CLASS) {
                zP("jit.rt.alloc-object: expected a class");
        }

        put(ty, &s, RawObject(a->class));
}

static void
rt_arity_error(Ty *ty, i32 expected, i32 actual)
{
        lir_runtime()->arity_error(ty, expected, actual);
}

static void
rt_arg_type_error(Ty *ty, i32 index, i32 type, Value const *v)
{
        lir_runtime()->arg_type_error(ty, index, type, v);
}

static void
rt_kernel_error(Ty *ty, i32 kind, Value const *v, i64 n)
{
        Value err;

        switch (kind) {
        case 0:
                err = TAGGED(TAG_INDEX_ERR, *v, INTEGER(n));
                vm_throw(ty, &err);

        case 1:
                ZeroDividePanic(ty);

        case 2:
                zP("kernel: argument %d has the wrong type: %s", (int)n + 1, VSC(v));

        case 3:
                zP("kernel: element %lld has the wrong type: %s", (long long)n, VSC(v));

        default:
                zP("kernel: reached the end of a function that must return a value");
        }
}

static LirType const V1[]        = { LT_PTR, LT_VAL };
static LirType const V2[]        = { LT_PTR, LT_VAL, LT_VAL };
static LirType const V3[]        = { LT_PTR, LT_VAL, LT_VAL, LT_VAL };
static LirType const V4[]        = { LT_PTR, LT_VAL, LT_VAL, LT_VAL, LT_VAL };
static LirType const Arity[]     = { LT_PTR, LT_I32, LT_I32 };
static LirType const TypeError[] = { LT_PTR, LT_I32, LT_I32, LT_VAL };
static LirType const Kernel[]    = { LT_PTR, LT_I32, LT_VAL, LT_I64 };

#define H(n, f, ps, fl) {                       \
        .name    = n,                           \
        .address = f,                           \
        .flags   = fl,                          \
        .sig     = {                            \
                .ret     = LT_VOID,             \
                .params  = ps,                  \
                .nparams = countof(ps),         \
                .nfixed  = countof(ps)          \
        }                                       \
}

static LirHelper const Helpers[] = {
        H("add",            rt_add,            V3,        GC_THROW),
        H("sub",            rt_sub,            V3,        GC_THROW),
        H("mul",            rt_mul,            V3,        GC_THROW),
        H("div",            rt_div,            V3,        GC_THROW),
        H("mod",            rt_mod,            V3,        GC_THROW),
        H("pow",            rt_pow,            V3,        GC_THROW),
        H("eq",             rt_eq,             V3,        LIR_MAY_THROW),
        H("ne",             rt_ne,             V3,        LIR_MAY_THROW),
        H("lt",             rt_lt,             V3,        LIR_MAY_THROW),
        H("le",             rt_le,             V3,        LIR_MAY_THROW),
        H("gt",             rt_gt,             V3,        LIR_MAY_THROW),
        H("ge",             rt_ge,             V3,        LIR_MAY_THROW),
        H("cmp",            rt_cmp,            V3,        LIR_MAY_THROW),
        H("subscript",      rt_subscript,      V3,        GC_THROW),
        H("subscript-set",  rt_subscript_set,  V4,        GC_THROW),
        H("member",         rt_member,         V3,        GC_THROW),
        H("member-set",     rt_member_set,     V4,        GC_THROW),
        H("call",           rt_call,           V3,        GC_THROW),
        H("call-method",    rt_call_method,    V4,        GC_THROW),
        H("array-new",      rt_array_new,      V1,        GC_THROW),
        H("array-push",     rt_array_push,     V3,        GC_THROW),
        H("dict-new",       rt_dict_new,       V1,        GC_THROW),
        H("dict-get",       rt_dict_get,       V3,        GC_THROW),
        H("dict-set",       rt_dict_set,       V4,        GC_THROW),
        H("str-concat",     rt_str_concat,     V3,        GC_THROW),
        H("to-string",      rt_to_string,      V2,        GC_THROW),
        H("hash",           rt_hash,           V2,        LIR_MAY_THROW),
        H("throw",          rt_throw,          V1,        GC_THROW | LIR_NORETURN),
        H("alloc-object",   rt_alloc_object,   V2,        GC_THROW),
        H("arity-error",    rt_arity_error,    Arity,     GC_THROW | LIR_NORETURN),
        H("arg-type-error", rt_arg_type_error, TypeError, GC_THROW | LIR_NORETURN),
        H("kernel-error",   rt_kernel_error,   Kernel,    GC_THROW | LIR_NORETURN),
};

#undef H

static bool
helper_pointer(void const *p)
{
        for (usize i = 0; i < countof(Helpers); ++i) {
                if (p == &Helpers[i]) {
                        return true;
                }
        }

        return false;
}

static i64
immediate(Ty *ty, Lir *L, Value const *x)
{
        switch (x->type) {
        case VALUE_PTR:
                if (x->gcptr != NULL) {
                        lir_const(L, x);
                }
                return (uptr)x->ptr;

        case VALUE_FOREIGN_FUNCTION:
                lir_const(L, x);
                return (uptr)x->ff;

        default:
                return integer(ty, x);
        }
}

static bool
operand(Ty *ty, Lir *L, Value const *v, LirOpnd *out)
{
        if (
                (v->type != VALUE_ARRAY)
             || (vN(*v->array) < 2)
             || (v__(*v->array, 0).type != VALUE_INTEGER)
        ) {
                return false;
        }

        LirOpndKind  kind = v__(*v->array, 0).z;
        Value const *x    = v_(*v->array, 1);

        switch (kind) {
        case LO_HOLE_IMM:
        case LO_HOLE_FIMM:
        case LO_HOLE_PTR:
        case LO_HOLE_CONST:
        case LO_HOLE_CALLEE:
                *out = lir_hole(kind, integer(ty, x));
                return true;

        case LO_CONST:
        case LO_REFCONST:
        case LO_VSLOT:
                *out = (LirOpnd) { .kind = kind, .index = integer(ty, x) };
                return true;

        case LO_REG:   *out = lir_r(integer(ty, x));      return true;
        case LO_LABEL: *out = lir_l(integer(ty, x));      return true;
        case LO_CC:    *out = lir_cc(integer(ty, x));     return true;
        case LO_IMM:   *out = lir_i(immediate(ty, L, x)); return true;

        case LO_FIMM:
                *out = lir_f(x->real);
                return x->type == VALUE_REAL;

        case LO_MEM:
                if (vN(*v->array) != 6) {
                        return false;
                }
                *out = lir_m(
                        integer(ty, x),
                        integer(ty, x + 1),
                        integer(ty, x + 2),
                        integer(ty, x + 3)
                );
                return true;

        case LO_CODE:
                if (x->type != VALUE_JIT_FUNCTION) {
                        return false;
                }
                lir_const(L, x);
                *out = lcode(x->jit_code);
                return true;

        case LO_HELPER:
                *out = lhelper(x->ptr);
                return x->type == VALUE_PTR;

        default:
                return false;
        }
}

static bool
operands(Ty *ty, Lir *L, Array const *xs, LirOpnd *out)
{
        for (usize i = 0; i < vN(*xs); ++i) {
                if (!operand(ty, L, v_(*xs, i), &out[i])) {
                        return false;
                }
        }

        return true;
}

static bool
call(Ty *ty, Lir *L, LirInst *in, Value const *meta)
{
        Array       *ps  = list(field(meta, "types"));
        Array       *xs  = list(field(meta, "args"));
        Value const *ret = field(meta, "ret");
        Value const *va  = field(meta, "variadic");

        if (ps == NULL || xs == NULL || ret == NULL) {
                return false;
        }

        in->sig.ret      = ctype(ty, ret);
        in->sig.nparams  = vN(*ps);
        in->sig.nfixed   = optint(ty, meta, "nfixed", vN(*ps));
        in->sig.variadic = (va != NULL) && va->boolean;
        in->sig.params   = ctypes(ty, ps);
        in->ncall_args   = vN(*xs);
        in->call_args    = snew(LirOpnd, vN(*xs));

        return operands(ty, L, xs, in->call_args);
}

static bool
table(Ty *ty, LirInst *in, Value const *meta)
{
        Array *ls = list(field(meta, "targets"));

        if (ls == NULL) {
                return false;
        }

        in->ntargets = vN(*ls);
        in->targets  = snew(LirLabel, vN(*ls));

        for (usize i = 0; i < vN(*ls); ++i) {
                in->targets[i] = integer(ty, v_(*ls, i));
        }

        return true;
}

static bool
words(Ty *ty, Value const *v, LirRaw *raw)
{
        if (v == NULL || v->type == VALUE_NIL) {
                return true;
        }

        if (v->type != VALUE_ARRAY) {
                return false;
        }

        u32 *ws = snew(u32, vN(*v->array));

        for (usize i = 0; i < vN(*v->array); ++i) {
                Value const *w = v_(*v->array, i);
                if (!inrange(w, 0, (i64)UINT32_MAX + 1)) {
                        return false;
                }
                ws[i] = w->z;
        }

        raw->arm64  = ws;
        raw->narm64 = vN(*v->array);

        return true;
}

static bool
bytes(Value const *v, LirRaw *raw)
{
        if (v == NULL || v->type == VALUE_NIL) {
                return true;
        }

        if (v->type != VALUE_BLOB || vN(*v->blob) > UINT32_MAX) {
                return false;
        }

        raw->x64  = vv(*v->blob);
        raw->nx64 = vN(*v->blob);

        return true;
}

static bool
bindings(Ty *ty, Value const *v, LirRawBinding const **out, u32 *n)
{
        if (v == NULL || v->type == VALUE_NIL) {
                return true;
        }

        if (v->type != VALUE_ARRAY) {
                return false;
        }

        LirRawBinding *bs = snew(LirRawBinding, vN(*v->array));

        for (usize i = 0; i < vN(*v->array); ++i) {
                Value const *b = v_(*v->array, i);

                if (b->type != VALUE_ARRAY || vN(*b->array) != 2) {
                        return false;
                }

                Value const *phys = v_(*b->array, 0);
                Value const *reg  = v_(*b->array, 1);

                if (!inrange(phys, 0, LIR_MAX_PHYS) || !inrange(reg, 0, LIR_NONE)) {
                        return false;
                }

                bs[i] = (LirRawBinding) { .phys = phys->z, .reg = reg->z };
        }

        *out = bs;
        *n   = vN(*v->array);

        return true;
}

static bool
raw(Ty *ty, LirInst *in, Value const *meta)
{
        LirRaw *r = &in->raw;

        r->gpr_clobber = optint(ty, meta, "gpr-clobber", 0);
        r->fpr_clobber = optint(ty, meta, "fpr-clobber", 0);

        return words(ty, field(meta, "arm64"), r)
            && bytes(field(meta, "x64"), r)
            && bindings(ty, field(meta, "in"), &r->in, &r->nin)
            && bindings(ty, field(meta, "out"), &r->out, &r->nout);
}

static bool
decode(Ty *ty, Lir *L, LirInst *in, Array const *args, Value const *meta)
{
        if (vN(*args) > LIR_MAX_OPERANDS || !operands(ty, L, args, in->args)) {
                return false;
        }

        Value const *span = field(meta, "span");

        if (span != NULL && span->type == VALUE_ARRAY && vN(*span->array) == 3) {
                in->span = (LirSpan) {
                        .source = integer(ty, v_(*span->array, 0)),
                        .start  = integer(ty, v_(*span->array, 1)),
                        .end    = integer(ty, v_(*span->array, 2))
                };
        }

        in->nargs = vN(*args);
        in->flags = optint(ty, meta, "flags", 0);
        in->tag   = optint(ty, meta, "tag", 0);

        switch (in->op) {
        case LIR_CALL:
        case LIR_TAILCALL: return call(ty, L, in, meta);
        case LIR_SWITCH:   return table(ty, in, meta);
        case LIR_RAW:      return raw(ty, in, meta);
        case LIR_ENTRY:    return (in->nargs == 1) && (in->args[0].kind == LO_LABEL);
        default:           return true;
        }
}

static bool
emit(Lir *L, LirInst const *in)
{
        if (in->op != LIR_ENTRY) {
                return lir_emit(L, in);
        }

        if (!lir_entry(L, in->args[0].label)) {
                return false;
        }

        vvL(L->insts)->tag  = in->tag;
        vvL(L->insts)->span = in->span;

        return true;
}

static Value
finish(Ty *ty, Lir *L, Value cls, bool interpreted)
{
        LirError err;
        LirCode *code = interpreted
                      ? lir_finish_interpreted(ty, L, true, &err)
                      : lir_finish(ty, L, true, &err);

        if (code == NULL) {
                return outcome(ty, NIL, &err);
        }

        GC_STOP();

        code = lir_code_adopt(ty, code);

        FunUserInfo *info = mAo0(sizeof *info, GC_ANY);

        info->name  = code->name;
        info->class = cls.class;

        Value out = PAIR(JIT_FUN(code, code->entry, info), NIL);

        GC_RESUME();

        return out;
}

static LirBinding
input(Ty *ty, Value *v)
{
        LirBinding b = { .value = v, .operand = { .kind = LO_CONST } };

        switch (v->type) {
        case VALUE_INTEGER:          b.operand = lir_i(v->z);            break;
        case VALUE_REAL:             b.operand = lir_f(v->real);         break;
        case VALUE_BOOLEAN:          b.operand = lir_i(v->boolean);      break;
        case VALUE_FOREIGN_FUNCTION: b.operand = lir_i((uptr)v->ff);     break;
        case VALUE_JIT_FUNCTION:     b.operand = lcode(v->jit_code);     break;

        case VALUE_PTR:
                b.operand = helper_pointer(v->ptr) ? lhelper(v->ptr) : lir_i((uptr)v->ptr);
                break;
        }

        if (v->type == VALUE_FOREIGN_FUNCTION) {
                b.signature = foreign_sig(ty, v);
        } else if (v->type == VALUE_JIT_FUNCTION) {
                b.signature = &v->jit_code->sig;
                b.flags     = code_flags(v->jit_code);
        } else if (b.operand.kind == LO_HELPER) {
                b.signature = &b.operand.helper->sig;
                b.flags     = b.operand.helper->flags;
        }

        return b;
}

static bool
capture(LirBinding *b, Value *pair)
{
        if (
                (pair->type != VALUE_ARRAY)
             || (vN(*pair->array) != 2)
             || (v__(*pair->array, 0).type != VALUE_INTEGER)
        ) {
                return false;
        }

        Value *v = v_(*pair->array, 1);

        b->value        = v;
        b->operand.kind = v__(*pair->array, 0).z;

        switch (b->operand.kind) {
        case LO_CONST:
                return true;

        case LO_CODE:
                b->operand = lcode(v->gcptr);
                return isgc(v, GC_JIT_CODE);

        case LO_HELPER:
                b->operand = lhelper(v->ptr);
                return (v->type == VALUE_PTR) && helper_pointer(v->ptr);

        case LO_IMM:
                b->operand = lir_i((uptr)v->ptr);
                return v->type == VALUE_PTR;

        default:
                return false;
        }
}

static LirBinding *
bind(Ty *ty, Array *inputs, Array *captures)
{
        LirBinding *bs = snew(LirBinding, vN(*inputs) + vN(*captures));

        for (usize i = 0; i < vN(*inputs); ++i) {
                bs[i] = input(ty, v_(*inputs, i));
        }

        for (usize i = 0; i < vN(*captures); ++i) {
                bs[vN(*inputs) + i] = (LirBinding) {0};
                if (!capture(&bs[vN(*inputs) + i], v_(*captures, i))) {
                        return NULL;
                }
        }

        return bs;
}

static bool
anchor(Lir *L, Array *inputs, LirError *err)
{
        for (usize i = 0; i < vN(*inputs); ++i) {
                Value const *v = v_(*inputs, i);

                if (
                        (v->type != VALUE_FOREIGN_FUNCTION)
                     && (v->type != VALUE_JIT_FUNCTION)
                     && (v->type != VALUE_PTR || v->gcptr == NULL)
                ) {
                        continue;
                }

                if (lir_const(L, v).kind != LO_CONST) {
                        *err = L->error;
                        return false;
                }
        }

        return true;
}

static Value
listing(Ty *ty, Lir const *L, LirAlloc const *alloc)
{
        char  *text = NULL;
        usize  size = 0;
        FILE  *f    = open_memstream(&text, &size);

        if (f == NULL) {
                zP("jit: cannot open dump stream");
        }

        lir_dump(L, f);

        if (alloc != NULL) {
                lir_dump_alloc(L, alloc, f);
        }

        fclose(f);

        Value out = vSs(text, size);

        free(text);

        return out;
}

static bool
allocate(
        Ty *ty,
        Lir *L,
        LirConstraint const *cs,
        u32 n,
        LirCFG *cfg,
        LirAlloc *alloc,
        LirError *err
)
{
        LirTarget const *target = lir_target();

        return lir_cfg(ty, L, cfg, err)
            && lir_allocate(ty, L, cfg, target, cs, n, alloc, err);
}

static Value
opdict(Ty *ty, bool sigs)
{
        GC_STOP();

        Value out = DICT(dict_new(ty));

        for (u32 i = 0; i < LIR_OP_COUNT; ++i) {
                Value v = sigs ? vSsz(LirOps[i].signature) : INTEGER(i);
                dict_put_member(ty, out.dict, LirOps[i].name, v);
        }

        GC_RESUME();

        return out;
}

static Value
global(Ty *ty, Symbol const *s)
{
        if (
                !IsTopLevel(s)
             || (s->flags & SYM_THREAD_LOCAL)
             || (s->i < 0)
             || (s->i >= Globals.count)
        ) {
                return NIL;
        }

        Value v = *vm_global(ty, s->i);

        return (v.type == VALUE_UNINITIALIZED) ? NIL : v;
}

Value
builtin_jit_static_value(Ty *ty, int argc, Value *kwargs)
{
        ASSERT_ARGC("jit._static-value", 1);

        Value ast = ARG(0);
        Expr *e   = TyToCExpr(ty, &ast);

        if (e == NULL) {
                return NIL;
        }

        if (e->type == EXPRESSION_VALUE) {
                return *e->v;
        }

        bool named = (e->type == EXPRESSION_IDENTIFIER) && (e->symbol != NULL);

        if (!named && !compiler_symbolize_expression(ty, e, NULL)) {
                return NIL;
        }

        if (e->type != EXPRESSION_IDENTIFIER || e->symbol == NULL) {
                return NIL;
        }

        return global(ty, e->symbol);
}

Value
builtin_jit_arch(Ty *ty, int argc, Value *kwargs)
{
        ASSERT_ARGC("jit._arch", 0);
#if defined(__aarch64__)
        return vSsz("arm64");
#elif defined(__x86_64__) && !defined(_WIN32)
        return vSsz("x64");
#else
        return vSsz("none");
#endif
}

Value
builtin_jit_new(Ty *ty, int argc, Value *kwargs)
{
        ASSERT_ARGC("jit._new", 4);

        Value  name = ARGx(0, VALUE_STRING);
        Array *ps   = ARGx(1, VALUE_ARRAY).array;

        SCRATCH_SAVE();

        LirError err;
        LirSig   sig = {
                .ret     = ctype(ty, &ARG(2)),
                .params  = ctypes(ty, ps),
                .nparams = vN(*ps),
                .nfixed  = vN(*ps)
        };

        Lir *L = lir_new(TY_C_STR(name), &sig, INT(3), &err);

        SCRATCH_RESTORE();

        if (L == NULL) {
                zP("jit: %s", err.message);
        }

        L = lir_adopt(ty, L);

        return GCPTR(L, L);
}

Value
builtin_jit_params(Ty *ty, int argc, Value *kwargs)
{
        ASSERT_ARGC("jit._params", 1);

        Lir *L = ASM(0);

        GC_STOP();

        Value out = ARRAY(vA());

        for (u32 i = 0; i < L->sig.nparams; ++i) {
                LirReg r = L->params[i];
                vAp(out.array, PAIR(INTEGER(r), INTEGER(v__(L->regs, r).cls)));
        }

        GC_RESUME();

        return out;
}

Value
builtin_jit_reg(Ty *ty, int argc, Value *kwargs)
{
        ASSERT_ARGC("jit._reg", 2);
        return INTEGER(lir_reg(ASM(0), INT(1)));
}

Value
builtin_jit_label(Ty *ty, int argc, Value *kwargs)
{
        ASSERT_ARGC("jit._label", 1);
        return INTEGER(lir_label(ASM(0)));
}

Value
builtin_jit_bind(Ty *ty, int argc, Value *kwargs)
{
        ASSERT_ARGC("jit._bind", 2);

        Lir *L = ASM(0);

        return lir_bind(L, INT(1)) ? NIL : error_value(ty, &L->error);
}

Value
builtin_jit_const(Ty *ty, int argc, Value *kwargs)
{
        ASSERT_ARGC("jit._const", 3);

        Lir  *L   = ASM(0);
        Value v   = ARG(1);
        bool  ref = ARGx(2, VALUE_BOOLEAN).boolean;

        if (
                ref
             && ((v.type & ~VALUE_TAGGED) == VALUE_STRING)
             && (v.ro || v.str0 == NULL)
        ) {
                v = vSs(v.str, v.bytes);
        }

        return INTEGER((ref ? lir_ref_const : lir_const)(L, &v).index);
}

Value
builtin_jit_vslot(Ty *ty, int argc, Value *kwargs)
{
        ASSERT_ARGC("jit._vslot", 1);
        return INTEGER(lir_vslot(ASM(0)));
}

Value
builtin_jit_emit(Ty *ty, int argc, Value *kwargs)
{
        ASSERT_ARGC("jit._emit", 5);

        Lir    *L    = ASM(0);
        Array  *args = ARGx(3, VALUE_ARRAY).array;
        Value   meta = ARG(4);
        Value   out  = NIL;
        LirInst in   = { .op = INT(1), .dst = INT(2) };

        SCRATCH_SAVE();

        if (!decode(ty, L, &in, args, &meta)) {
                out = error_value(
                        ty,
                        &(LirError) {
                                .kind    = LE_OPERAND,
                                .op      = vN(L->insts),
                                .span    = in.span,
                                .message = "invalid instruction payload"
                        }
                );
        } else if (!emit(L, &in)) {
                out = error_value(ty, &L->error);
        }

        SCRATCH_RESTORE();

        return out;
}

Value
builtin_jit_finish(Ty *ty, int argc, Value *kwargs)
{
        ASSERT_ARGC("jit._finish", 2);
        return finish(ty, ASM(0), ARGx(1, VALUE_CLASS), false);
}

Value
builtin_jit_interp(Ty *ty, int argc, Value *kwargs)
{
        ASSERT_ARGC("jit._interp", 2);
        return finish(ty, ASM(0), ARGx(1, VALUE_CLASS), true);
}

Value
builtin_jit_serialize(Ty *ty, int argc, Value *kwargs)
{
        ASSERT_ARGC("jit._serialize", 1);

        SCRATCH_SAVE();

        LirBytes bytes;
        LirError err;
        bool     ok = lir_serialize(ty, ASM(0), &bytes, &err);

        GC_STOP();

        Value out      = vT(4);
        Value captures = ARRAY(vA());

        out.items[0] = NIL;
        out.items[1] = INTEGER(ok ? bytes.ninputs : 0);
        out.items[2] = captures;
        out.items[3] = ok ? NIL : error_value(ty, &err);

        if (ok) {
                Value blob = BLOB(value_blob_new(ty));

                uvPn(*blob.blob, bytes.items, bytes.count);

                for (u32 i = bytes.ninputs; i < bytes.nholes; ++i) {
                        LirBinding const *b    = &bytes.holes[i];
                        Value             pair = ARRAY(vA());
                        Value             v;

                        switch (b->operand.kind) {
                        case LO_CONST:  v = *b->value;                               break;
                        case LO_CODE:   v = GCPTR(b->operand.code, b->operand.code); break;
                        case LO_HELPER: v = PTR((void *)b->operand.helper);          break;
                        case LO_IMM:    v = PTR((void *)(uptr)b->operand.imm);       break;
                        default:        v = NIL;                                     break;
                        }

                        vAp(pair.array, INTEGER(b->operand.kind));
                        vAp(pair.array, v);
                        vAp(captures.array, pair);
                }

                out.items[0] = blob;
        }

        GC_RESUME();
        SCRATCH_RESTORE();

        return out;
}

Value
builtin_jit_load(Ty *ty, int argc, Value *kwargs)
{
        ASSERT_ARGC("jit._load", 5);

        Blob  *blob     = ARGx(0, VALUE_BLOB).blob;
        i64    ninputs  = INT(1);
        Array *captures = ARGx(2, VALUE_ARRAY).array;
        Array *inputs   = ARGx(3, VALUE_ARRAY).array;
        Value  cls      = ARGx(4, VALUE_CLASS);
        Lir   *L        = NULL;
        Value  out;

        LirError err = {
                .kind    = LE_ENCODING,
                .op      = LIR_NONE,
                .message = "invalid serialized bindings"
        };

        SCRATCH_SAVE();

        LirBinding *bs = (ninputs == vN(*inputs)) ? bind(ty, inputs, captures) : NULL;

        if (bs != NULL) {
                L = lir_deserialize(
                        ty,
                        vv(*blob),
                        vN(*blob),
                        bs,
                        vN(*inputs) + vN(*captures),
                        &err
                );
        }

        if (L != NULL && anchor(L, inputs, &err)) {
                out = finish(ty, L, cls, false);
        } else {
                out = outcome(ty, NIL, &err);
        }

        lir_free(L);

        SCRATCH_RESTORE();

        return out;
}

Value
builtin_jit_dump(Ty *ty, int argc, Value *kwargs)
{
        ASSERT_ARGC("jit._dump", 2);

        Lir  *L     = ASM(0);
        Bytes stage = s_bytes(ARGx(1, VALUE_STRING));

        if (bytes_eq(stage, z_bytes("lir"))) {
                return outcome(ty, listing(ty, L, NULL), NULL);
        }

        bool           regs  = bytes_eq(stage, z_bytes("alloc"));
        LirConstraint *cs    = NULL;
        u32            ncs   = 0;
        Lir           *legal = NULL;
        LirCFG         cfg   = {0};
        LirAlloc       alloc = {0};
        LirError       err;
        Value          out;

        SCRATCH_SAVE();

        bool ok = lir_validate(ty, L, &err)
               && ((legal = lir_clone(L, &err)) != NULL)
               && lir_legalize(ty, legal, lir_target(), &cs, &ncs, &err)
               && (!regs || allocate(ty, legal, cs, ncs, &cfg, &alloc, &err));

        if (ok) {
                out = outcome(ty, listing(ty, legal, regs ? &alloc : NULL), NULL);
        } else {
                out = outcome(ty, NIL, &err);
        }

        lir_free(legal);

        SCRATCH_RESTORE();

        return out;
}

Value
builtin_jit_op_signatures(Ty *ty, int argc, Value *kwargs)
{
        ASSERT_ARGC("jit._op-signatures", 0);
        return opdict(ty, true);
}

Value
builtin_jit_ops(Ty *ty, int argc, Value *kwargs)
{
        ASSERT_ARGC("jit._ops", 0);
        return opdict(ty, false);
}

Value
builtin_jit_sig(Ty *ty, int argc, Value *kwargs)
{
        ASSERT_ARGC("jit._sig", 1);

        Value         f     = ARG(0);
        LirSig const *sig   = NULL;
        u32           flags = 0;

        SCRATCH_SAVE();

        switch (f.type) {
        case VALUE_JIT_FUNCTION:
                sig   = &f.jit_code->sig;
                flags = code_flags(f.jit_code);
                break;

        case VALUE_FOREIGN_FUNCTION:
                sig = foreign_sig(ty, &f);
                break;

        default:
                zP("jit: target has no known C signature");
        }

        GC_STOP();

        Value out = vT(5);

        out.items[0] = INTEGER(sig->ret);
        out.items[1] = types_of(ty, sig);
        out.items[2] = INTEGER(sig->nfixed);
        out.items[3] = BOOLEAN(sig->variadic);
        out.items[4] = INTEGER(flags);

        GC_RESUME();

        SCRATCH_RESTORE();

        return out;
}

Value
builtin_jit_ptr(Ty *ty, int argc, Value *kwargs)
{
        ASSERT_ARGC("jit._ptr", 1);

        LirCode *code = CODE(0);

        return GCPTR(code->body, code);
}

Value
builtin_jit_code(Ty *ty, int argc, Value *kwargs)
{
        ASSERT_ARGC("jit._code", 1);

        LirCode *code = CODE(0);

        return GCPTR(code, code);
}

Value
builtin_jit_name(Ty *ty, int argc, Value *kwargs)
{
        ASSERT_ARGC("jit._name", 1);
        return vSsz(name_of(&ARG(0)));
}

Value
builtin_jit_code_size(Ty *ty, int argc, Value *kwargs)
{
        ASSERT_ARGC("jit._code-size", 1);

        LirCode const *code  = CODE(0);
        LirCode const *entry = code->entry_code;

        return INTEGER(code->size + ((entry == NULL) ? 0 : entry->size));
}

Value
builtin_jit_code_lir(Ty *ty, int argc, Value *kwargs)
{
        ASSERT_ARGC("jit._code-lir", 1);
        return listing(ty, CODE(0)->lir, NULL);
}

Value
builtin_jit_code_bytes(Ty *ty, int argc, Value *kwargs)
{
        ASSERT_ARGC("jit._code-bytes", 1);

        LirCode *code = CODE(0);
        Blob    *blob = mAo0(sizeof *blob, GC_BLOB);

        uvPn(*blob, code->body, code->size);

        return BLOB(blob);
}

Value
builtin_jit_code_sites(Ty *ty, int argc, Value *kwargs)
{
        ASSERT_ARGC("jit._code-sites", 1);

        LirCode const *code = CODE(0);

        GC_STOP();

        Value out = ARRAY(vA());

        for (u32 i = 0; i < code->nsites; ++i) {
                LirSite const *s = &code->sites[i];
                vAp(out.array, PAIR(INTEGER(s->pc), INTEGER(s->tag)));
        }

        GC_RESUME();

        return out;
}

Value
builtin_jit_stats(Ty *ty, int argc, Value *kwargs)
{
        ASSERT_ARGC("jit._stats", 0);

        JitMemStats s = jm_stats();

        return TRIPLE(INTEGER(s.allocated), INTEGER(s.used), INTEGER(s.nchunks));
}

Value
builtin_jit_current_ty(Ty *ty, int argc, Value *kwargs)
{
        ASSERT_ARGC("jit._current-ty", 0);
        return PTR(GetMyTy);
}

Value
builtin_jit_helpers(Ty *ty, int argc, Value *kwargs)
{
        ASSERT_ARGC("jit._helpers", 0);

        GC_STOP();

        Value out = ARRAY(vA());

        for (usize i = 0; i < countof(Helpers); ++i) {
                LirHelper const *h = &Helpers[i];
                Value            x = vT(5);

                x.items[0] = vSsz(h->name);
                x.items[1] = PTR((void *)h);
                x.items[2] = INTEGER(h->sig.ret);
                x.items[3] = types_of(ty, &h->sig);
                x.items[4] = INTEGER(h->flags);

                vAp(out.array, x);
        }

        GC_RESUME();

        return out;
}

#define FIELD(name, x) #name, INTEGER(x),

#define CONTAINER(T, cap) vTn(                          \
        "OFF_ITEMS",    INTEGER(offsetof(T, items)),    \
        "OFF_COUNT",    INTEGER(offsetof(T, count)),    \
        "OFF_CAPACITY", INTEGER(offsetof(T, cap))       \
)

Value
builtin_jit_layout(Ty *ty, int argc, Value *kwargs)
{
        ASSERT_ARGC("jit._layout", 0);

        GC_STOP();

        Value out = vTn(
                JIT_LAYOUT(FIELD)
                "Array", CONTAINER(Array, capacity),
                "Blob",  CONTAINER(Blob, capacity),
                "Dict",  CONTAINER(Dict, size)
        );

        GC_RESUME();

        return out;
}

Value
builtin_jit_tags(Ty *ty, int argc, Value *kwargs)
{
        ASSERT_ARGC("jit._tags", 0);
        return vTn(JIT_TAGS(FIELD) "TAGGED", INTEGER(VALUE_TAGGED));
}
