#include <stdlib.h>
#include <string.h>

#include "jitmod.h"
#include "lir.h"
#include "value.h"
#include "vm.h"
#include "dict.h"
#include "gc.h"
#include "functions.h"
#include "compiler.h"
#include "scope.h"

Value
builtin_jit_static_value(Ty *ty, int argc, Value *kwargs)
{
        ASSERT_ARGC("jit._static-value", 1);
        Value ast = ARG(0);
        Expr *e = TyToCExpr(ty, &ast);
        if (e == NULL) {
                return NIL;
        }
        if (e->type == EXPRESSION_VALUE) {
                return *e->v;
        }
        if (e->type != EXPRESSION_IDENTIFIER || e->symbol == NULL) {
                if (!compiler_symbolize_expression(ty, e, NULL)) {
                        return NIL;
                }
        }
        if (e->type == EXPRESSION_IDENTIFIER && e->symbol != NULL) {
                Symbol const *s = e->symbol;
                if (IsTopLevel(s) && !(s->flags & SYM_THREAD_LOCAL)
                    && s->i >= 0 && s->i < Globals.count) {
                        Value value = *vm_global(ty, s->i);
                        if (value.type != VALUE_UNINITIALIZED) {
                                return value;
                        }
                }
        }
        return NIL;
}

static Lir *
asm_arg(Ty *ty, Value const *value)
{
        if (value->type != VALUE_PTR || value->gcptr == NULL
            || ALLOC_OF(value->gcptr)->type != GC_LIR) {
                zP("jit: expected an assembler handle");
        }
        return value->ptr;
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

static LirCode *
code_arg(Ty *ty, Value const *value)
{
        if (value->type == VALUE_JIT_FUNCTION) {
                return value->jit_code;
        }
        if (value->type == VALUE_PTR && value->gcptr != NULL
            && ALLOC_OF(value->gcptr)->type == GC_JIT_CODE) {
                return value->gcptr;
        }
        zP("jit: expected a code object");
}

static Value
error_value(Ty *ty, LirError const *error)
{
        GC_STOP();
        Value out = vT(5);
        out.items[0] = vSsz(error->message);
        out.items[1] = INTEGER(error->op == LIR_NONE ? -1 : (i64)error->op);
        out.items[2] = INTEGER(error->span.source);
        out.items[3] = INTEGER(error->span.start);
        out.items[4] = INTEGER(error->span.end);
        GC_RESUME();
        return out;
}

static i64
integer(Ty *ty, Value const *value)
{
        if (value->type != VALUE_INTEGER) {
                zP("jit: expected an integer");
        }
        return value->z;
}

static LirType
ctype(Ty *ty, Value const *value)
{
        i64 n = integer(ty, value);
        if (n < 0 || n >= LIR_TYPE_COUNT) {
                zP("jit: invalid C type %" PRId64, n);
        }
        return n;
}

static LirType
ffi_ctype(Ty *ty, ffi_type const *type)
{
        switch (type->type) {
        case FFI_TYPE_VOID: return LIR_VOID;
        case FFI_TYPE_SINT8: return LIR_TYPE_I8;
        case FFI_TYPE_UINT8: return LIR_TYPE_U8;
        case FFI_TYPE_SINT16: return LIR_TYPE_I16;
        case FFI_TYPE_UINT16: return LIR_TYPE_U16;
        case FFI_TYPE_INT:
        case FFI_TYPE_SINT32: return LIR_TYPE_I32;
        case FFI_TYPE_UINT32: return LIR_TYPE_U32;
        case FFI_TYPE_SINT64: return LIR_TYPE_I64;
        case FFI_TYPE_UINT64: return LIR_TYPE_U64;
        case FFI_TYPE_FLOAT: return LIR_TYPE_F32;
        case FFI_TYPE_DOUBLE: return LIR_TYPE_F64;
        case FFI_TYPE_POINTER: return LIR_TYPE_PTR;
        default:
                zP("jit: this foreign signature uses a non-scalar C type");
        }
}

static void
foreign_arity(Value const *v, u32 *fixed, bool *variadic)
{
        *fixed = v->ffi->nargs;
        *variadic = false;
        if (v->xinfo != NULL && v->xinfo->ffi_signature) {
                *fixed = v->xinfo->ffi_nfixed;
                *variadic = v->xinfo->ffi_variadic;
        }
#if defined(__APPLE__) && defined(__aarch64__)
        else if (v->ffi->aarch64_nfixedargs != 0) {
                *fixed = v->ffi->aarch64_nfixedargs;
                *variadic = true;
        }
#endif
}

static bool
operand(Ty *ty, Lir *L, Value const *value, LirOpnd *out)
{
        Value const *xs;
        usize n;
        if (value->type != VALUE_ARRAY || value->array->count == 0) {
                return false;
        }
        xs = value->array->items;
        n = value->array->count;
        if (xs[0].type != VALUE_INTEGER || n < 2) {
                return false;
        }
        LirOperandKind kind = xs[0].z;
        switch (kind) {
        case LIR_HOLE_IMM:
        case LIR_HOLE_FIMM:
        case LIR_HOLE_PTR:
        case LIR_HOLE_CONST:
        case LIR_HOLE_CALLEE:
                *out = lir_hole(kind, integer(ty, &xs[1]));
                break;
        case LIR_OPERAND_REG: *out = lir_r(integer(ty, &xs[1])); break;
        case LIR_OPERAND_IMM:
                if (xs[1].type == VALUE_PTR) {
                        if (xs[1].gcptr != NULL) {
                                lir_const(L, &xs[1]);
                        }
                        *out = lir_i((uptr)xs[1].ptr);
                } else if (xs[1].type == VALUE_FOREIGN_FUNCTION) {
                        lir_const(L, &xs[1]);
                        *out = lir_i((uptr)xs[1].ff);
                } else {
                        *out = lir_i(integer(ty, &xs[1]));
                }
                break;
        case LIR_OPERAND_FIMM:
                if (xs[1].type != VALUE_REAL) {
                        return false;
                }
                *out = lir_f(xs[1].real);
                break;
        case LIR_OPERAND_MEM:
                if (n != 6) {
                        return false;
                }
                *out = lir_m(integer(ty, &xs[1]), integer(ty, &xs[2]),
                             integer(ty, &xs[3]), integer(ty, &xs[4]));
                break;
        case LIR_OPERAND_LABEL: *out = lir_l(integer(ty, &xs[1])); break;
        case LIR_OPERAND_CC: *out = lir_cc(integer(ty, &xs[1])); break;
        case LIR_OPERAND_CONST:
        case LIR_OPERAND_REFCONST:
        case LIR_OPERAND_VSLOT:
                *out = (LirOpnd) { .kind = kind, .index = integer(ty, &xs[1]) };
                break;
        case LIR_OPERAND_CODE:
                if (xs[1].type != VALUE_JIT_FUNCTION) {
                        return false;
                }
                lir_const(L, &xs[1]);
                *out = (LirOpnd) { .kind = kind, .code = xs[1].jit_code };
                break;
        case LIR_OPERAND_HELPER:
                if (xs[1].type != VALUE_PTR) {
                        return false;
                }
                *out = (LirOpnd) { .kind = kind, .helper = xs[1].ptr };
                break;
        default:
                return false;
        }
        return true;
}

static Value *
field(Value const *meta, char const *key)
{
        return meta->type == VALUE_DICT ? dict_get_member(NULL, meta->dict, key) : NULL;
}

Value
builtin_jit_new(Ty *ty, int argc, Value *kwargs)
{
        ASSERT_ARGC("jit._new", 4);
        Value name = ARGx(0, VALUE_STRING);
        Value params = ARGx(1, VALUE_ARRAY);
        LirType types[params.array->count + 1];
        for (usize i = 0; i < params.array->count; ++i) {
                types[i] = ctype(ty, &params.array->items[i]);
        }
        LirSig sig = { .ret = ctype(ty, &ARG(2)), .params = types,
                       .nparams = params.array->count, .nfixed = params.array->count };
        LirError err;
        Lir *L = lir_new(TY_C_STR(name), &sig, integer(ty, &ARG(3)), &err);
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
        Lir *L = asm_arg(ty, &ARG(0));
        GC_STOP();
        Value out = ARRAY(vA());
        for (u32 i = 0; i < L->sig.nparams; ++i) {
                Value pair = PAIR(INTEGER(L->params[i]), INTEGER(L->regs[L->params[i]].cls));
                vAp(out.array, pair);
        }
        GC_RESUME();
        return out;
}

Value
builtin_jit_reg(Ty *ty, int argc, Value *kwargs)
{
        ASSERT_ARGC("jit._reg", 2);
        return INTEGER(lir_reg(asm_arg(ty, &ARG(0)), integer(ty, &ARG(1))));
}

Value
builtin_jit_label(Ty *ty, int argc, Value *kwargs)
{
        ASSERT_ARGC("jit._label", 1);
        return INTEGER(lir_label(asm_arg(ty, &ARG(0))));
}

Value
builtin_jit_bind(Ty *ty, int argc, Value *kwargs)
{
        ASSERT_ARGC("jit._bind", 2);
        Lir *L = asm_arg(ty, &ARG(0));
        if (!lir_bind(L, integer(ty, &ARG(1)))) {
                return error_value(ty, &L->error);
        }
        return NIL;
}

Value
builtin_jit_const(Ty *ty, int argc, Value *kwargs)
{
        ASSERT_ARGC("jit._const", 3);
        Lir *L = asm_arg(ty, &ARG(0));
        Value v = ARG(1);
        Value ref = ARGx(2, VALUE_BOOLEAN);
        if (ref.boolean && (v.type & ~VALUE_TAGGED) == VALUE_STRING
            && (v.ro || v.str0 == NULL)) {
                v = vSs(v.str, v.bytes);
        }
        LirOpnd c = ref.boolean ? lir_ref_const(L, &v) : lir_const(L, &v);
        return INTEGER(c.index);
}

Value
builtin_jit_vslot(Ty *ty, int argc, Value *kwargs)
{
        ASSERT_ARGC("jit._vslot", 1);
        return INTEGER(lir_vslot(asm_arg(ty, &ARG(0))));
}

static bool
raw_bindings(Value const *v, LirRawBinding **out, u32 *n)
{
        if (v == NULL || v->type == VALUE_NIL) {
                return true;
        }
        if (v->type != VALUE_ARRAY || v->array->count > UINT32_MAX) {
                return false;
        }
        *n = v->array->count;
        *out = calloc((usize)*n + 1, sizeof **out);
        if (*out == NULL) {
                return false;
        }
        for (u32 i = 0; i < *n; ++i) {
                Value const *binding = &v->array->items[i];
                if (binding->type != VALUE_ARRAY || binding->array->count != 2) {
                        return false;
                }
                Value const *p = &binding->array->items[0];
                Value const *r = &binding->array->items[1];
                if (p->type != VALUE_INTEGER || r->type != VALUE_INTEGER
                    || p->z < 0 || p->z >= LIR_MAX_PHYS || r->z < 0 || r->z >= LIR_NONE) {
                        return false;
                }
                (*out)[i] = (LirRawBinding) { .phys = p->z, .reg = r->z };
        }
        return true;
}

Value
builtin_jit_emit(Ty *ty, int argc, Value *kwargs)
{
        ASSERT_ARGC("jit._emit", 5);
        Lir *L = asm_arg(ty, &ARG(0));
        Value operands = ARGx(3, VALUE_ARRAY);
        Value meta = ARG(4);
        LirInst in = { .op = integer(ty, &ARG(1)), .dst = integer(ty, &ARG(2)),
                       .nargs = operands.array->count };
        LirOpnd *call_args = NULL;
        LirType *types = NULL;
        LirLabel *targets = NULL;
        LirRawBinding *raw_in = NULL;
        LirRawBinding *raw_out = NULL;
        u32 *words = NULL;
        Value *v;
        Value out = NIL;
        if (in.nargs > LIR_MAX_OPERANDS) {
                goto BadOperand;
        }
        for (u32 i = 0; i < in.nargs; ++i) {
                if (!operand(ty, L, &operands.array->items[i], &in.args[i])) {
                        goto BadOperand;
                }
        }
        if ((v = field(&meta, "span")) != NULL && v->type == VALUE_ARRAY && v->array->count == 3) {
                in.span = (LirSpan) { .source = integer(ty, &v->array->items[0]),
                                     .start = integer(ty, &v->array->items[1]),
                                     .end = integer(ty, &v->array->items[2]) };
        }
        if ((v = field(&meta, "flags")) != NULL) {
                in.flags = integer(ty, v);
        }
        if ((v = field(&meta, "tag")) != NULL) {
                in.tag = integer(ty, v);
        }
        if (in.op == LIR_CALL || in.op == LIR_TAILCALL) {
                Value *ps = field(&meta, "types");
                Value *xs = field(&meta, "args");
                Value *ret = field(&meta, "ret");
                if (ps == NULL || xs == NULL || ret == NULL
                    || ps->type != VALUE_ARRAY || xs->type != VALUE_ARRAY) {
                        goto BadOperand;
                }
                in.sig.ret = ctype(ty, ret);
                in.sig.nparams = ps->array->count;
                in.sig.nfixed = in.sig.nparams;
                if ((v = field(&meta, "nfixed")) != NULL) {
                        in.sig.nfixed = integer(ty, v);
                }
                if ((v = field(&meta, "variadic")) != NULL) {
                        in.sig.variadic = v->boolean;
                }
                in.ncall_args = xs->array->count;
                call_args = calloc((usize)in.ncall_args + 1, sizeof *call_args);
                types = calloc((usize)in.sig.nparams + 1, sizeof *types);
                if (call_args == NULL || types == NULL) {
                        goto NoMemory;
                }
                for (u32 i = 0; i < in.sig.nparams; ++i) {
                        types[i] = ctype(ty, &ps->array->items[i]);
                }
                for (u32 i = 0; i < in.ncall_args; ++i) {
                        if (!operand(ty, L, &xs->array->items[i], &call_args[i])) {
                                goto BadOperand;
                        }
                }
                in.sig.params = types;
                in.call_args = call_args;
        } else if (in.op == LIR_SWITCH) {
                Value *ls = field(&meta, "targets");
                if (ls == NULL || ls->type != VALUE_ARRAY) {
                        goto BadOperand;
                }
                in.ntargets = ls->array->count;
                targets = calloc((usize)in.ntargets + 1, sizeof *targets);
                if (targets == NULL) {
                        goto NoMemory;
                }
                for (u32 i = 0; i < in.ntargets; ++i) {
                        targets[i] = integer(ty, &ls->array->items[i]);
                }
                in.targets = targets;
        }
        if (in.op == LIR_RAW) {
                if ((v = field(&meta, "arm64")) != NULL && v->type != VALUE_NIL) {
                        if (v->type != VALUE_ARRAY || v->array->count > UINT32_MAX) {
                                goto BadOperand;
                        }
                        in.raw.narm64 = v->array->count;
                        words = calloc((usize)in.raw.narm64 + 1, sizeof *words);
                        if (words == NULL) {
                                goto NoMemory;
                        }
                        for (u32 i = 0; i < in.raw.narm64; ++i) {
                                Value const *word = &v->array->items[i];
                                if (word->type != VALUE_INTEGER || word->z < 0 || word->z > UINT32_MAX) {
                                        goto BadOperand;
                                }
                                words[i] = word->z;
                        }
                        in.raw.arm64 = words;
                }
                if ((v = field(&meta, "x64")) != NULL && v->type != VALUE_NIL) {
                        if (v->type != VALUE_BLOB || v->blob->count > UINT32_MAX) {
                                goto BadOperand;
                        }
                        in.raw.x64 = v->blob->items;
                        in.raw.nx64 = v->blob->count;
                }
                if (!raw_bindings(field(&meta, "in"), &raw_in, &in.raw.nin)
                    || !raw_bindings(field(&meta, "out"), &raw_out, &in.raw.nout)) {
                        goto BadOperand;
                }
                in.raw.in = raw_in;
                in.raw.out = raw_out;
                if ((v = field(&meta, "gpr-clobber")) != NULL) {
                        in.raw.gpr_clobber = integer(ty, v);
                }
                if ((v = field(&meta, "fpr-clobber")) != NULL) {
                        in.raw.fpr_clobber = integer(ty, v);
                }
        }
        if (in.op == LIR_ENTRY) {
                if (in.nargs != 1 || in.args[0].kind != LIR_OPERAND_LABEL) {
                        goto BadOperand;
                }
                if (!lir_entry(L, in.args[0].label)) {
                        out = error_value(ty, &L->error);
                } else {
                        L->insts[L->ninsts - 1].tag = in.tag;
                        L->insts[L->ninsts - 1].span = in.span;
                }
        } else if (!lir_emit(L, &in)) {
                out = error_value(ty, &L->error);
        }
        goto End;
BadOperand:
        out = error_value(ty, &(LirError) { .kind = LIR_ERROR_OPERAND, .op = L->ninsts,
                                          .span = in.span, .message = "invalid instruction payload" });
        goto End;
NoMemory:
        out = error_value(ty, &(LirError) { .kind = LIR_ERROR_MEMORY, .op = L->ninsts,
                                          .span = in.span, .message = "out of memory copying instruction" });
End:
        free(call_args);
        free(types);
        free(targets);
        free(words);
        free(raw_in);
        free(raw_out);
        return out;
}

static Value
finish_lir(Ty *ty, Lir *L, Value cls, bool interpreted)
{
        LirError err;
        LirCode *code = interpreted ? lir_finish_interpreted(L, true, &err) : lir_finish(L, true, &err);
        if (code == NULL) {
                GC_STOP();
                Value out = PAIR(NIL, error_value(ty, &err));
                GC_RESUME();
                return out;
        }
        GC_STOP();
        code = lir_code_adopt(ty, code);
        FunUserInfo *info = mAo0(sizeof *info, GC_ANY);
        info->name  = code->name;
        info->class = cls.class;
        Value fn = JIT_FUN(code, code->entry, info);
        Value out = PAIR(fn, NIL);
        GC_RESUME();
        return out;
}

Value
builtin_jit_finish(Ty *ty, int argc, Value *kwargs)
{
        ASSERT_ARGC("jit._finish", 2);
        return finish_lir(ty, asm_arg(ty, &ARG(0)), ARGx(1, VALUE_CLASS), false);
}

Value
builtin_jit_interp(Ty *ty, int argc, Value *kwargs)
{
        ASSERT_ARGC("jit._interp", 2);
        return finish_lir(ty, asm_arg(ty, &ARG(0)), ARGx(1, VALUE_CLASS), true);
}

static bool
helper_pointer(void const *p);

Value
builtin_jit_serialize(Ty *ty, int argc, Value *kwargs)
{
        ASSERT_ARGC("jit._serialize", 1);
        LirBytes bytes;
        LirError err;
        if (!lir_serialize(asm_arg(ty, &ARG(0)), &bytes, &err)) {
                GC_STOP();
                Value out = vT(4);
                out.items[0] = NIL;
                out.items[1] = INTEGER(0);
                out.items[2] = ARRAY(vA());
                out.items[3] = error_value(ty, &err);
                GC_RESUME();
                return out;
        }
        GC_STOP();
        Value out = vT(4);
        Value blob = BLOB(value_blob_new(ty));
        uvPn(*blob.blob, bytes.items, bytes.count);
        Value captures = ARRAY(vA());
        for (u32 i = bytes.ninputs; i < bytes.nholes; ++i) {
                LirBinding const *b = &bytes.holes[i];
                Value value;
                switch (b->operand.kind) {
                case LIR_OPERAND_CONST: value = *b->value; break;
                case LIR_OPERAND_CODE: value = GCPTR(b->operand.code, b->operand.code); break;
                case LIR_OPERAND_HELPER: value = PTR((void *)b->operand.helper); break;
                case LIR_OPERAND_IMM: value = PTR((void *)(uptr)b->operand.imm); break;
                default: value = NIL; break;
                }
                Value pair = ARRAY(vA());
                vAp(pair.array, INTEGER(b->operand.kind));
                vAp(pair.array, value);
                vAp(captures.array, pair);
        }
        out.items[0] = blob;
        out.items[1] = INTEGER(bytes.ninputs);
        out.items[2] = captures;
        out.items[3] = NIL;
        lir_bytes_free(&bytes);
        GC_RESUME();
        return out;
}

static LirBinding
input_binding(Value *v)
{
        LirBinding b = { .value = v };
        switch (v->type) {
        case VALUE_INTEGER: b.operand = lir_i(v->z); break;
        case VALUE_REAL: b.operand = lir_f(v->real); break;
        case VALUE_BOOLEAN: b.operand = lir_i(v->boolean); break;
        case VALUE_PTR:
                b.operand = helper_pointer(v->ptr)
                          ? (LirOpnd) { .kind = LIR_OPERAND_HELPER, .helper = v->ptr } : lir_i((uptr)v->ptr);
                break;
        case VALUE_FOREIGN_FUNCTION: b.operand = lir_i((uptr)v->ff); break;
        case VALUE_JIT_FUNCTION: b.operand = (LirOpnd) { .kind = LIR_OPERAND_CODE, .code = v->jit_code }; break;
        default: b.operand.kind = LIR_OPERAND_CONST; break;
        }
        return b;
}

Value
builtin_jit_load(Ty *ty, int argc, Value *kwargs)
{
        ASSERT_ARGC("jit._load", 5);
        Value blob = ARGx(0, VALUE_BLOB);
        i64 ninputs = integer(ty, &ARG(1));
        Value captures = ARGx(2, VALUE_ARRAY);
        Value inputs = ARGx(3, VALUE_ARRAY);
        Value cls = ARGx(4, VALUE_CLASS);
        LirError err = { .kind = LIR_ERROR_ENCODING, .op = LIR_NONE,
                         .message = "invalid serialized bindings" };
        LirBinding *bindings = NULL;
        LirSig *signatures = NULL;
        LirType *types = NULL;
        Lir *L = NULL;
        Value out;
        if (ninputs < 0 || ninputs > UINT32_MAX || ninputs != inputs.array->count
            || captures.array->count > UINT32_MAX - (u64)ninputs) {
                goto Bad;
        }
        usize ntypes = 0;
        for (u32 i = 0; i < ninputs; ++i) {
                Value const *v = &inputs.array->items[i];
                if (v->type == VALUE_FOREIGN_FUNCTION) {
                        ffi_cif const *sig = v->ffi;
                        ffi_ctype(ty, sig->rtype);
                        for (u32 j = 0; j < sig->nargs; ++j) {
                                ffi_ctype(ty, sig->arg_types[j]);
                        }
                        if (sig->nargs > SIZE_MAX / sizeof *types - ntypes) {
                                goto Bad;
                        }
                        ntypes += sig->nargs;
                }
        }
        u32 n = ninputs + captures.array->count;
        bindings = calloc((usize)n + 1, sizeof *bindings);
        signatures = calloc((usize)ninputs + 1, sizeof *signatures);
        types = calloc(ntypes + 1, sizeof *types);
        if (bindings == NULL || signatures == NULL || types == NULL) {
                err.kind = LIR_ERROR_MEMORY;
                snprintf(err.message, sizeof err.message, "out of memory filling serialized bindings");
                goto Bad;
        }
        usize ti = 0;
        for (u32 i = 0; i < ninputs; ++i) {
                Value *v = &inputs.array->items[i];
                LirBinding *b = &bindings[i];
                *b = input_binding(v);
                if (v->type == VALUE_FOREIGN_FUNCTION) {
                        ffi_cif const *sig = v->ffi;
                        LirSig *cs = &signatures[i];
                        *cs = (LirSig) { .ret = ffi_ctype(ty, sig->rtype), .params = types + ti,
                                         .nparams = sig->nargs, .nfixed = sig->nargs };
                        foreign_arity(v, &cs->nfixed, &cs->variadic);
                        for (u32 j = 0; j < sig->nargs; ++j) {
                                types[ti++] = ffi_ctype(ty, sig->arg_types[j]);
                        }
                        b->signature = cs;
                } else if (v->type == VALUE_JIT_FUNCTION) {
                        b->signature = &v->jit_code->sig;
                        b->flags = v->jit_code->mode == LIR_MODE_ATTACHED ? LIR_MAY_GC | LIR_MAY_THROW : 0;
                } else if (b->operand.kind == LIR_OPERAND_HELPER) {
                        b->signature = &b->operand.helper->sig;
                        b->flags = b->operand.helper->flags;
                }
        }
        for (u32 i = 0; i < captures.array->count; ++i) {
                Value const *pair = &captures.array->items[i];
                if (pair->type != VALUE_ARRAY || pair->array->count != 2
                    || pair->array->items[0].type != VALUE_INTEGER) {
                        goto Bad;
                }
                Value *v = &pair->array->items[1];
                LirBinding *b = &bindings[ninputs + i];
                b->value = v;
                b->operand.kind = pair->array->items[0].z;
                switch (b->operand.kind) {
                case LIR_OPERAND_CONST: break;
                case LIR_OPERAND_CODE:
                        if (v->type != VALUE_PTR || v->gcptr == NULL
                            || ALLOC_OF(v->gcptr)->type != GC_JIT_CODE) {
                                goto Bad;
                        }
                        b->operand = (LirOpnd) { .kind = LIR_OPERAND_CODE, .code = v->gcptr };
                        break;
                case LIR_OPERAND_HELPER:
                        if (v->type != VALUE_PTR || !helper_pointer(v->ptr)) {
                                goto Bad;
                        }
                        b->operand = (LirOpnd) { .kind = LIR_OPERAND_HELPER, .helper = v->ptr };
                        break;
                case LIR_OPERAND_IMM:
                        if (v->type != VALUE_PTR) {
                                goto Bad;
                        }
                        b->operand = lir_i((uptr)v->ptr);
                        break;
                default: goto Bad;
                }
        }
        L = lir_deserialize(blob.blob->items, blob.blob->count, bindings, n, &err);
        if (L == NULL) {
                goto Bad;
        }
        for (u32 i = 0; i < ninputs; ++i) {
                Value *v = &inputs.array->items[i];
                if ((v->type == VALUE_PTR && v->gcptr != NULL)
                    || v->type == VALUE_FOREIGN_FUNCTION || v->type == VALUE_JIT_FUNCTION) {
                        if (lir_const(L, v).kind != LIR_OPERAND_CONST) {
                                err = L->error;
                                goto Bad;
                        }
                }
        }
        out = finish_lir(ty, L, cls, false);
        goto End;
Bad:
        GC_STOP();
        out = PAIR(NIL, error_value(ty, &err));
        GC_RESUME();
End:
        free(bindings);
        free(signatures);
        free(types);
        lir_free(L);
        return out;
}

static Value
lir_string(Ty *ty, Lir const *L, LirAlloc const *alloc)
{
        char *text = NULL;
        usize size = 0;
        FILE *stream = open_memstream(&text, &size);
        if (stream == NULL) {
                zP("jit: cannot open dump stream");
        }
        lir_dump(L, stream);
        if (alloc != NULL) {
                for (u32 r = 0; r < alloc->nintervals; ++r) {
                        LirInterval const *i = &alloc->intervals[r];
                        if (i->spilled) {
                                fprintf(stream, "  r%u: spill+%u\n", r, i->spill);
                        } else {
                                fprintf(stream, "  r%u: %c%u\n", r,
                                        L->regs[r].cls == LIR_F32 || L->regs[r].cls == LIR_F64 ? 'v' : 'x', i->phys);
                        }
                }
        }
        fclose(stream);
        Value out = vSs(text, size);
        free(text);
        return out;
}

Value
builtin_jit_dump(Ty *ty, int argc, Value *kwargs)
{
        ASSERT_ARGC("jit._dump", 2);
        Lir *L = asm_arg(ty, &ARG(0));
        Value stage = ARGx(1, VALUE_STRING);
        if (sN(stage) == 3 && memcmp(ss(stage), "lir", 3) == 0) {
                GC_STOP();
                Value out = PAIR(lir_string(ty, L, NULL), NIL);
                GC_RESUME();
                return out;
        }
        LirError err;
        Lir *legal = NULL;
        LirConstraint *constraints = NULL;
        u32 nconstraints = 0;
        LirCFG cfg = {0};
        LirAlloc alloc = {0};
        Value result = NIL;
        if (!lir_validate(L, &err)) {
                goto Bad;
        }
        legal = lir_clone(L, &err);
        if (legal == NULL || !lir_legalize(legal, lir_target(), &constraints, &nconstraints, &err)) {
                goto Bad;
        }
        bool allocation = sN(stage) == 5 && memcmp(ss(stage), "alloc", 5) == 0;
        if (allocation && (!lir_cfg(legal, &cfg, &err)
                           || !lir_allocate(legal, &cfg, lir_target(), constraints, nconstraints, &alloc, &err)
                           || !lir_allocate_workspaces(legal, lir_target(), &alloc, &err))) {
                goto Bad;
        }
        GC_STOP();
        result = PAIR(lir_string(ty, legal, allocation ? &alloc : NULL), NIL);
        GC_RESUME();
        goto End;
Bad:
        GC_STOP();
        result = PAIR(NIL, error_value(ty, &err));
        GC_RESUME();
End:
        free(constraints);
        lir_free(legal);
        lir_alloc_free(&alloc);
        lir_cfg_free(&cfg);
        return result;
}

Value
builtin_jit_op_signatures(Ty *ty, int argc, Value *kwargs)
{
        ASSERT_ARGC("jit._op-signatures", 0);
        GC_STOP();
        Value out = DICT(dict_new(ty));
        for (u32 i = 0; i < LIR_OP_COUNT; ++i) {
                dict_put_member(ty, out.dict, LirOps[i].name, vSsz(LirOps[i].signature));
        }
        GC_RESUME();
        return out;
}

Value
builtin_jit_ops(Ty *ty, int argc, Value *kwargs)
{
        ASSERT_ARGC("jit._ops", 0);
        GC_STOP();
        Value out = DICT(dict_new(ty));
        for (u32 i = 0; i < LIR_OP_COUNT; ++i) {
                dict_put_member(ty, out.dict, LirOps[i].name, INTEGER(i));
        }
        GC_RESUME();
        return out;
}

Value
builtin_jit_sig(Ty *ty, int argc, Value *kwargs)
{
        ASSERT_ARGC("jit._sig", 1);
        Value target = ARG(0);
        if (target.type == VALUE_FOREIGN_FUNCTION) {
                ffi_ctype(ty, target.ffi->rtype);
                for (u32 i = 0; i < target.ffi->nargs; ++i) {
                        ffi_ctype(ty, target.ffi->arg_types[i]);
                }
        }
        GC_STOP();
        Value params = ARRAY(vA());
        LirType ret;
        u32 fixed;
        bool variadic = false;
        u32 flags = 0;
        if (target.type == VALUE_JIT_FUNCTION) {
                LirSig const *sig = &target.jit_code->sig;
                ret = sig->ret;
                fixed = sig->nfixed;
                variadic = sig->variadic;
                flags = target.jit_code->mode == LIR_MODE_ATTACHED ? LIR_MAY_GC | LIR_MAY_THROW : 0;
                for (u32 i = 0; i < sig->nparams; ++i) {
                        vAp(params.array, INTEGER(sig->params[i]));
                }
        } else if (target.type == VALUE_FOREIGN_FUNCTION) {
                ffi_cif *sig = target.ffi;
                ret = ffi_ctype(ty, sig->rtype);
                fixed = sig->nargs;
                foreign_arity(&target, &fixed, &variadic);
                for (u32 i = 0; i < sig->nargs; ++i) {
                        vAp(params.array, INTEGER(ffi_ctype(ty, sig->arg_types[i])));
                }
        } else {
                GC_RESUME();
                zP("jit: target has no known C signature");
        }
        Value out = vT(5);
        out.items[0] = INTEGER(ret);
        out.items[1] = params;
        out.items[2] = INTEGER(fixed);
        out.items[3] = BOOLEAN(variadic);
        out.items[4] = INTEGER(flags);
        GC_RESUME();
        return out;
}

Value
builtin_jit_ptr(Ty *ty, int argc, Value *kwargs)
{
        ASSERT_ARGC("jit._ptr", 1);
        LirCode *code = code_arg(ty, &ARG(0));
        return GCPTR(code->body, code);
}

Value
builtin_jit_code(Ty *ty, int argc, Value *kwargs)
{
        ASSERT_ARGC("jit._code", 1);
        LirCode *code = code_arg(ty, &ARG(0));
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
        LirCode *code = code_arg(ty, &ARG(0));
        return INTEGER(code->size + (code->entry_code == NULL ? 0 : code->entry_code->size));
}

Value
builtin_jit_code_lir(Ty *ty, int argc, Value *kwargs)
{
        ASSERT_ARGC("jit._code-lir", 1);
        return lir_string(ty, code_arg(ty, &ARG(0))->lir, NULL);
}

Value
builtin_jit_code_bytes(Ty *ty, int argc, Value *kwargs)
{
        ASSERT_ARGC("jit._code-bytes", 1);
        LirCode *code = code_arg(ty, &ARG(0));
        Blob *blob = mAo0(sizeof *blob, GC_BLOB);
        uvPn(*blob, code->body, code->size);
        return BLOB(blob);
}

Value
builtin_jit_stats(Ty *ty, int argc, Value *kwargs)
{
        ASSERT_ARGC("jit._stats", 0);
        JitMemStats stats = jm_stats();
        return TRIPLE(INTEGER(stats.allocated), INTEGER(stats.used), INTEGER(stats.nchunks));
}

Value
builtin_jit_current_ty(Ty *ty, int argc, Value *kwargs)
{
        ASSERT_ARGC("jit._current-ty", 0);
        return PTR(GetMyTy);
}

typedef struct jit_result {
        Value *out;
        isize index;
        usize top;
} JitResult;

static JitResult
result_slot(Ty *ty, Value *out)
{
        uptr p = (uptr)out;
        uptr base = (uptr)ty->stack.items;
        uptr end = base + ty->stack.count * sizeof (Value);
        return (JitResult) {
                .out = out,
                .index = base != 0 && p >= base && p < end ? (p - base) / sizeof (Value) : -1,
                .top = ty->stack.count
        };
}

static void
put_result(Ty *ty, JitResult const *slot, Value value)
{
        Value *out = slot->index < 0 ? slot->out : ty->stack.items + slot->index;
        *out = value;
        ty->stack.count = slot->top;
}

static void
rt_call(Ty *ty, Value *out, Value const *f, Value const *args)
{
        JitResult slot = result_slot(ty, out);
        Value fn = *f;
        Value xs = *args;
        Value const *items;
        usize n;
        if (xs.type == VALUE_ARRAY) {
                items = xs.array->items;
                n = xs.array->count;
        } else if (xs.type == VALUE_TUPLE) {
                items = xs.items;
                n = xs.count;
        } else {
                zP("jit.rt.call: expected an array or tuple of arguments");
        }
        gP(&fn);
        gP(&xs);
        for (usize i = 0; i < n; ++i) {
                vm_push(ty, &items[i]);
        }
        Value result = vm_call(ty, &fn, n);
        put_result(ty, &slot, result);
        gX();
        gX();
}

static void
rt_array_new(Ty *ty, Value *out)
{
        JitResult slot = result_slot(ty, out);
        put_result(ty, &slot, ARRAY(vA()));
}

static void
rt_array_push(Ty *ty, Value *out, Value const *array, Value const *value)
{
        JitResult slot = result_slot(ty, out);
        Value xs = *array;
        Value v = *value;
        if (xs.type != VALUE_ARRAY) {
                zP("jit.rt.array-push: expected an array");
        }
        gP(&xs);
        gP(&v);
        vAp(xs.array, v);
        put_result(ty, &slot, xs);
        gX();
        gX();
}

static void
rt_binary(Ty *ty, Value *out, Value const *a, Value const *b, int op)
{
        JitResult slot = result_slot(ty, out);
        Value x = *a;
        Value y = *b;
        gP(&x);
        gP(&y);
        Value value = vm_2op(ty, op, &x, &y);
        put_result(ty, &slot, value);
        gX();
        gX();
}

#define RT_BINARY(name, op) \
        static void \
        rt_##name(Ty *ty, Value *out, Value const *a, Value const *b) \
        { \
                rt_binary(ty, out, a, b, op); \
        }

RT_BINARY(add, OP_ADD)
RT_BINARY(sub, OP_SUB)
RT_BINARY(mul, OP_MUL)
RT_BINARY(div, OP_DIV)
RT_BINARY(mod, OP_MOD)
RT_BINARY(eq, OP_EQL)
RT_BINARY(ne, OP_NEQ)
RT_BINARY(lt, OP_LT)
RT_BINARY(le, OP_LEQ)
RT_BINARY(gt, OP_GT)
RT_BINARY(ge, OP_GEQ)
RT_BINARY(cmp, OP_CMP)
#undef RT_BINARY

static void
rt_pow(Ty *ty, Value *out, Value const *a, Value const *b)
{
        JitResult slot = result_slot(ty, out);
        Value x = *a;
        Value y = *b;
        gP(&x);
        gP(&y);
        vm_push(ty, &x);
        vm_push(ty, &y);
        Value value = builtin_pow(ty, 2, NULL);
        put_result(ty, &slot, value);
        gX();
        gX();
}

static void
rt_subscript(Ty *ty, Value *out, Value const *a, Value const *b)
{
        JitResult slot = result_slot(ty, out);
        Value x = *a;
        Value key = *b;
        vm_push(ty, &x);
        vm_push(ty, &key);
        DoSubscript(ty, true);
        put_result(ty, &slot, *vm_pop(ty));
}

static void
rt_subscript_set(Ty *ty, Value *out, Value const *a, Value const *b, Value const *c)
{
        JitResult slot = result_slot(ty, out);
        Value x = *a;
        Value key = *b;
        Value value = *c;
        vm_push(ty, &value);
        vm_push(ty, &x);
        vm_push(ty, &key);
        DoAssignSubscript(ty, 1, true);
        put_result(ty, &slot, *vm_pop(ty));
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
        JitResult slot = result_slot(ty, out);
        Value x = *a;
        Value key = *b;
        i32 id = member_id(ty, &key);
        vm_push(ty, &x);
        Value value = vm_jit_member_access(ty, id);
        put_result(ty, &slot, value);
}

static void
rt_member_set(Ty *ty, Value *out, Value const *a, Value const *b, Value const *c)
{
        JitResult slot = result_slot(ty, out);
        Value x = *a;
        Value key = *b;
        Value value = *c;
        i32 id = member_id(ty, &key);
        gP(&x);
        vm_push(ty, &value);
        vm_jit_target_member(ty, &x, id);
        DoAssignExec(ty);
        put_result(ty, &slot, *vm_pop(ty));
        gX();
}

static void
rt_call_method(Ty *ty, Value *out, Value const *a, Value const *b, Value const *c)
{
        JitResult slot = result_slot(ty, out);
        Value receiver = *a;
        Value key = *b;
        Value args = *c;
        gP(&receiver);
        gP(&args);
        i32 id = member_id(ty, &key);
        vm_push(ty, &receiver);
        Value fn = vm_jit_member_access(ty, id);
        out = slot.index < 0 ? slot.out : ty->stack.items + slot.index;
        rt_call(ty, out, &fn, &args);
        ty->stack.count = slot.top;
        gX();
        gX();
}

static void
rt_dict_new(Ty *ty, Value *out)
{
        JitResult slot = result_slot(ty, out);
        put_result(ty, &slot, DICT(dict_new(ty)));
}

static void
rt_dict_get(Ty *ty, Value *out, Value const *a, Value const *b)
{
        JitResult slot = result_slot(ty, out);
        Value dict = *a;
        Value key = *b;
        if (dict.type != VALUE_DICT) {
                zP("jit.rt.dict-get: expected a dictionary");
        }
        gP(&dict);
        gP(&key);
        Value *value = dict_get_value(ty, dict.dict, &key);
        put_result(ty, &slot, value == NULL ? NIL : *value);
        gX();
        gX();
}

static void
rt_dict_set(Ty *ty, Value *out, Value const *a, Value const *b, Value const *c)
{
        JitResult slot = result_slot(ty, out);
        Value dict = *a;
        Value key = *b;
        Value value = *c;
        if (dict.type != VALUE_DICT) {
                zP("jit.rt.dict-set: expected a dictionary");
        }
        gP(&dict);
        gP(&key);
        gP(&value);
        dict_put_value(ty, dict.dict, key, value);
        put_result(ty, &slot, dict);
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
        JitResult slot = result_slot(ty, out);
        Value value = *a;
        gP(&value);
        if (value.type == VALUE_PTR) {
                value = vSsz(VSC(&value));
        } else if (value.type != VALUE_STRING && value.type != VALUE_NIL) {
                vm_push(ty, &value);
                CallMethod(ty, NAMES._str_, 0, 0, false, true);
                value = *vm_pop(ty);
        }
        put_result(ty, &slot, value);
        gX();
}

static void
rt_hash(Ty *ty, Value *out, Value const *a)
{
        JitResult slot = result_slot(ty, out);
        Value value = *a;
        gP(&value);
        u64 hash = value_hash(ty, &value);
        put_result(ty, &slot, INTEGER(hash));
        gX();
}

static void
rt_throw(Ty *ty, Value const *a)
{
        Value value = *a;
        vm_throw(ty, &value);
}

static void
rt_alloc_object(Ty *ty, Value *out, Value const *a)
{
        JitResult slot = result_slot(ty, out);
        Value cls = *a;
        if (cls.type != VALUE_CLASS) {
                zP("jit.rt.alloc-object: expected a class");
        }
        put_result(ty, &slot, RawObject(cls.class));
}

static void
rt_arity_error(Ty *ty, i32 expected, i32 actual)
{
        lir_runtime()->arity_error(ty, expected, actual);
}

static void
rt_arg_type_error(Ty *ty, i32 index, i32 type, Value const *value)
{
        lir_runtime()->arg_type_error(ty, index, type, value);
}

static LirType const RT_TWO[] = { LIR_TYPE_PTR, LIR_TYPE_VAL };
static LirType const RT_THREE[] = { LIR_TYPE_PTR, LIR_TYPE_VAL, LIR_TYPE_VAL };
static LirType const RT_FOUR[] = { LIR_TYPE_PTR, LIR_TYPE_VAL, LIR_TYPE_VAL, LIR_TYPE_VAL };
static LirType const RT_FIVE[] = { LIR_TYPE_PTR, LIR_TYPE_VAL, LIR_TYPE_VAL, LIR_TYPE_VAL, LIR_TYPE_VAL };
static LirType const RT_ARITY[] = { LIR_TYPE_PTR, LIR_TYPE_I32, LIR_TYPE_I32 };
static LirType const RT_TYPE_ERROR[] = { LIR_TYPE_PTR, LIR_TYPE_I32, LIR_TYPE_I32, LIR_TYPE_VAL };
static LirHelper const Helpers[] = {
        { .name = "add", .address = rt_add,
          .sig = { .ret = LIR_VOID, .params = RT_FOUR, .nparams = 4, .nfixed = 4 },
          .flags = LIR_MAY_GC | LIR_MAY_THROW },
        { .name = "sub", .address = rt_sub,
          .sig = { .ret = LIR_VOID, .params = RT_FOUR, .nparams = 4, .nfixed = 4 },
          .flags = LIR_MAY_GC | LIR_MAY_THROW },
        { .name = "mul", .address = rt_mul,
          .sig = { .ret = LIR_VOID, .params = RT_FOUR, .nparams = 4, .nfixed = 4 },
          .flags = LIR_MAY_GC | LIR_MAY_THROW },
        { .name = "div", .address = rt_div,
          .sig = { .ret = LIR_VOID, .params = RT_FOUR, .nparams = 4, .nfixed = 4 },
          .flags = LIR_MAY_GC | LIR_MAY_THROW },
        { .name = "mod", .address = rt_mod,
          .sig = { .ret = LIR_VOID, .params = RT_FOUR, .nparams = 4, .nfixed = 4 },
          .flags = LIR_MAY_GC | LIR_MAY_THROW },
        { .name = "pow", .address = rt_pow,
          .sig = { .ret = LIR_VOID, .params = RT_FOUR, .nparams = 4, .nfixed = 4 },
          .flags = LIR_MAY_GC | LIR_MAY_THROW },
        { .name = "eq", .address = rt_eq,
          .sig = { .ret = LIR_VOID, .params = RT_FOUR, .nparams = 4, .nfixed = 4 },
          .flags = LIR_MAY_THROW },
        { .name = "ne", .address = rt_ne,
          .sig = { .ret = LIR_VOID, .params = RT_FOUR, .nparams = 4, .nfixed = 4 },
          .flags = LIR_MAY_THROW },
        { .name = "lt", .address = rt_lt,
          .sig = { .ret = LIR_VOID, .params = RT_FOUR, .nparams = 4, .nfixed = 4 },
          .flags = LIR_MAY_THROW },
        { .name = "le", .address = rt_le,
          .sig = { .ret = LIR_VOID, .params = RT_FOUR, .nparams = 4, .nfixed = 4 },
          .flags = LIR_MAY_THROW },
        { .name = "gt", .address = rt_gt,
          .sig = { .ret = LIR_VOID, .params = RT_FOUR, .nparams = 4, .nfixed = 4 },
          .flags = LIR_MAY_THROW },
        { .name = "ge", .address = rt_ge,
          .sig = { .ret = LIR_VOID, .params = RT_FOUR, .nparams = 4, .nfixed = 4 },
          .flags = LIR_MAY_THROW },
        { .name = "cmp", .address = rt_cmp,
          .sig = { .ret = LIR_VOID, .params = RT_FOUR, .nparams = 4, .nfixed = 4 },
          .flags = LIR_MAY_THROW },
        { .name = "subscript", .address = rt_subscript,
          .sig = { .ret = LIR_VOID, .params = RT_FOUR, .nparams = 4, .nfixed = 4 },
          .flags = LIR_MAY_GC | LIR_MAY_THROW },
        { .name = "subscript-set", .address = rt_subscript_set,
          .sig = { .ret = LIR_VOID, .params = RT_FIVE, .nparams = 5, .nfixed = 5 },
          .flags = LIR_MAY_GC | LIR_MAY_THROW },
        { .name = "member", .address = rt_member,
          .sig = { .ret = LIR_VOID, .params = RT_FOUR, .nparams = 4, .nfixed = 4 },
          .flags = LIR_MAY_GC | LIR_MAY_THROW },
        { .name = "member-set", .address = rt_member_set,
          .sig = { .ret = LIR_VOID, .params = RT_FIVE, .nparams = 5, .nfixed = 5 },
          .flags = LIR_MAY_GC | LIR_MAY_THROW },
        { .name = "call", .address = rt_call,
          .sig = { .ret = LIR_VOID, .params = RT_FOUR, .nparams = 4, .nfixed = 4 },
          .flags = LIR_MAY_GC | LIR_MAY_THROW },
        { .name = "call-method", .address = rt_call_method,
          .sig = { .ret = LIR_VOID, .params = RT_FIVE, .nparams = 5, .nfixed = 5 },
          .flags = LIR_MAY_GC | LIR_MAY_THROW },
        { .name = "array-new", .address = rt_array_new,
          .sig = { .ret = LIR_VOID, .params = RT_TWO, .nparams = 2, .nfixed = 2 },
          .flags = LIR_MAY_GC | LIR_MAY_THROW },
        { .name = "array-push", .address = rt_array_push,
          .sig = { .ret = LIR_VOID, .params = RT_FOUR, .nparams = 4, .nfixed = 4 },
          .flags = LIR_MAY_GC | LIR_MAY_THROW },
        { .name = "dict-new", .address = rt_dict_new,
          .sig = { .ret = LIR_VOID, .params = RT_TWO, .nparams = 2, .nfixed = 2 },
          .flags = LIR_MAY_GC | LIR_MAY_THROW },
        { .name = "dict-get", .address = rt_dict_get,
          .sig = { .ret = LIR_VOID, .params = RT_FOUR, .nparams = 4, .nfixed = 4 },
          .flags = LIR_MAY_GC | LIR_MAY_THROW },
        { .name = "dict-set", .address = rt_dict_set,
          .sig = { .ret = LIR_VOID, .params = RT_FIVE, .nparams = 5, .nfixed = 5 },
          .flags = LIR_MAY_GC | LIR_MAY_THROW },
        { .name = "str-concat", .address = rt_str_concat,
          .sig = { .ret = LIR_VOID, .params = RT_FOUR, .nparams = 4, .nfixed = 4 },
          .flags = LIR_MAY_GC | LIR_MAY_THROW },
        { .name = "to-string", .address = rt_to_string,
          .sig = { .ret = LIR_VOID, .params = RT_THREE, .nparams = 3, .nfixed = 3 },
          .flags = LIR_MAY_GC | LIR_MAY_THROW },
        { .name = "hash", .address = rt_hash,
          .sig = { .ret = LIR_VOID, .params = RT_THREE, .nparams = 3, .nfixed = 3 },
          .flags = LIR_MAY_THROW },
        { .name = "throw", .address = rt_throw,
          .sig = { .ret = LIR_VOID, .params = RT_TWO, .nparams = 2, .nfixed = 2 },
          .flags = LIR_MAY_GC | LIR_MAY_THROW | LIR_NORETURN },
        { .name = "alloc-object", .address = rt_alloc_object,
          .sig = { .ret = LIR_VOID, .params = RT_THREE, .nparams = 3, .nfixed = 3 },
          .flags = LIR_MAY_GC | LIR_MAY_THROW },
        { .name = "arity-error", .address = rt_arity_error,
          .sig = { .ret = LIR_VOID, .params = RT_ARITY, .nparams = 3, .nfixed = 3 },
          .flags = LIR_MAY_GC | LIR_MAY_THROW | LIR_NORETURN },
        { .name = "arg-type-error", .address = rt_arg_type_error,
          .sig = { .ret = LIR_VOID, .params = RT_TYPE_ERROR, .nparams = 4, .nfixed = 4 },
          .flags = LIR_MAY_GC | LIR_MAY_THROW | LIR_NORETURN },
};

static bool
helper_pointer(void const *p)
{
        for (u32 i = 0; i < countof(Helpers); ++i) {
                if (p == &Helpers[i]) {
                        return true;
                }
        }
        return false;
}

Value
builtin_jit_helpers(Ty *ty, int argc, Value *kwargs)
{
        ASSERT_ARGC("jit._helpers", 0);
        GC_STOP();
        Value out = ARRAY(vA());
        for (u32 i = 0; i < countof(Helpers); ++i) {
                LirHelper const *helper = &Helpers[i];
                Value types = ARRAY(vA());
                for (u32 p = 0; p < helper->sig.nparams; ++p) {
                        vAp(types.array, INTEGER(helper->sig.params[p]));
                }
                Value record = vT(5);
                record.items[0] = vSsz(helper->name);
                record.items[1] = PTR(helper);
                record.items[2] = INTEGER(helper->sig.ret);
                record.items[3] = types;
                record.items[4] = INTEGER(helper->flags);
                vAp(out.array, record);
        }
        GC_RESUME();
        return out;
}

Value
builtin_jit_layout(Ty *ty, int argc, Value *kwargs)
{
        ASSERT_ARGC("jit._layout", 0);
        static struct { char const *name; usize offset; } const offsets[] = {
                { "VALUE_SIZE", sizeof (Value) },
                { "OFF_TYPE", offsetof(Value, type) },
                { "OFF_TAGS", offsetof(Value, tags) },
                { "OFF_Z", offsetof(Value, z) },
                { "OFF_REAL", offsetof(Value, real) },
                { "OFF_BOOL", offsetof(Value, boolean) },
                { "OFF_PTR", offsetof(Value, ptr) },
                { "OFF_CLASS", offsetof(Value, class) },
                { "OFF_OBJECT", offsetof(Value, object) },
                { "OFF_STR", offsetof(Value, str) },
                { "OFF_BYTES", offsetof(Value, bytes) },
                { "OFF_COUNT", offsetof(Value, count) },
                { "OFF_ITEMS", offsetof(Value, items) },
                { "ARRAY_OFF_ITEMS", offsetof(Array, items) },
                { "ARRAY_OFF_COUNT", offsetof(Array, count) },
                { "ARRAY_OFF_CAPACITY", offsetof(Array, capacity) },
                { "BLOB_OFF_ITEMS", offsetof(Blob, items) },
                { "BLOB_OFF_COUNT", offsetof(Blob, count) },
                { "BLOB_OFF_CAPACITY", offsetof(Blob, capacity) },
                { "DICT_OFF_ITEMS", offsetof(Dict, items) },
                { "DICT_OFF_COUNT", offsetof(Dict, count) },
                { "DICT_OFF_CAPACITY", offsetof(Dict, size) },
                { "OFF_SLOTS", offsetof(TyObject, slots) }
        };
        GC_STOP();
        Value out = DICT(dict_new(ty));
        for (u32 i = 0; i < countof(offsets); ++i) {
                dict_put_member(ty, out.dict, offsets[i].name, INTEGER(offsets[i].offset));
        }
        GC_RESUME();
        return out;
}

Value
builtin_jit_tags(Ty *ty, int argc, Value *kwargs)
{
        ASSERT_ARGC("jit._tags", 0);
        static struct { char const *name; u8 tag; } const tags[] = {
                { "ZERO", VALUE_ZERO },
                { "INT", VALUE_INTEGER },
                { "FLOAT", VALUE_REAL },
                { "BOOL", VALUE_BOOLEAN },
                { "NIL", VALUE_NIL },
                { "STRING", VALUE_STRING },
                { "ARRAY", VALUE_ARRAY },
                { "DICT", VALUE_DICT },
                { "SET", VALUE_SET },
                { "HEAP", VALUE_HEAP },
                { "BLOB", VALUE_BLOB },
                { "TUPLE", VALUE_TUPLE },
                { "OBJECT", VALUE_OBJECT },
                { "PTR", VALUE_PTR },
                { "REF", VALUE_REF },
                { "FUNCTION", VALUE_FUNCTION },
                { "BOUND_FUNCTION", VALUE_BOUND_FUNCTION },
                { "STAR_FUNCTION", VALUE_STAR_FUNCTION },
                { "FOREIGN_FUNCTION", VALUE_FOREIGN_FUNCTION },
                { "JIT_FUNCTION", VALUE_JIT_FUNCTION },
                { "NATIVE_FUNCTION", VALUE_NATIVE_FUNCTION },
                { "BUILTIN_FUNCTION", VALUE_BUILTIN_FUNCTION },
                { "METHOD", VALUE_METHOD },
                { "BUILTIN_METHOD", VALUE_BUILTIN_METHOD },
                { "CLASS", VALUE_CLASS },
                { "GENERATOR", VALUE_GENERATOR },
                { "GENERATOR_0", VALUE_GENERATOR_0 },
                { "TAG", VALUE_TAG },
                { "OPERATOR", VALUE_OPERATOR },
                { "TYPE", VALUE_TYPE },
                { "REGEX", VALUE_REGEX },
                { "QUEUE", VALUE_QUEUE },
                { "SHARED_QUEUE", VALUE_SHARED_QUEUE },
                { "THREAD", VALUE_THREAD },
                { "SENTINEL", VALUE_SENTINEL },
                { "INDEX", VALUE_INDEX },
                { "NONE", VALUE_NONE },
                { "UNINITIALIZED", VALUE_UNINITIALIZED },
                { "NAMESPACE", VALUE_NAMESPACE },
                { "MODULE", VALUE_MODULE },
                { "TRACE", VALUE_TRACE },
                { "BREAK", VALUE_BREAK },
                { "TOMBSTONE", VALUE_TOMBSTONE },
                { "FUN_META", VALUE_FUN_META },
                { "ANY", VALUE_ANY },
                { "TAGGED", VALUE_TAGGED }
        };
        GC_STOP();
        Value out = DICT(dict_new(ty));
        for (u32 i = 0; i < countof(tags); ++i) {
                dict_put_member(ty, out.dict, tags[i].name, INTEGER(tags[i].tag));
        }
        GC_RESUME();
        return out;
}
