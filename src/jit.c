// jit.c - JIT compiler for ty

#include <stddef.h>
#include <stdint.h>
#include <stdbool.h>
#include <string.h>
#include <sys/mman.h>

#ifdef __APPLE__
#include <libkern/OSCacheControl.h>
#endif

#include "ty.h"
#include "value.h"
#include "ast.h"
#include "types.h"
#include "scope.h"
#include "class.h"
#include "jit.h"
#include "log.h"
#include "vm.h"
#include "str.h"
#include "array.h"
#include "dict.h"
#include "blob.h"
#include "itable.h"

#define VALUE_SIZE (sizeof (Value))

// ============================================================================
// Value field offsets (must match struct value layout)
// ============================================================================
#define VAL_OFF_TYPE    offsetof(Value, type)    // u8 type
#define VAL_OFF_TAGS    offsetof(Value, tags)    // u16 tags
#define VAL_OFF_SRC     offsetof(Value, src)     // u16 src
#define VAL_OFF_Z       offsetof(Value, z)       // intmax_t z (for VALUE_INTEGER)
#define VAL_OFF_BOOL    offsetof(Value, boolean) // intmax_t z (for VALUE_INTEGER)
#define VAL_OFF_CLASS   offsetof(Value, class)   // u16 class (for VALUE_CLASS / VALUE_OBJECT)
#define VAL_OFF_OBJECT  offsetof(Value, object)  // void *object (for VALUE_OBJECT)

#define OFF_TY_STACK  offsetof(Ty, stack)
#define OFF_TY_ST     offsetof(Ty, st)
#define OFF_ST_FRAMES offsetof(co_state, frames)
#define OFF_FRAME_FP  offsetof(Frame, fp)
#define OFF_VEC_DATA  offsetof(ValueVector, items)
#define OFF_VEC_LEN   offsetof(ValueVector, count)

// TyObject layout:
#define OBJ_OFF_INIT    0    // bool init
#define OBJ_OFF_NSLOT   4    // u32 nslot
#define OBJ_OFF_CLASS   8    // Class *class
#define OBJ_OFF_DYN     16   // struct itable *dynamic
#define OBJ_OFF_SLOTS   24   // Value slots[] (flexible array)

// ============================================================================
// DynASM runtime includes
// ============================================================================

#include "../LuaJIT/dynasm/dasm_proto.h"

#if defined(__aarch64__) || defined(_M_ARM64)
#  include "../LuaJIT/dynasm/dasm_arm64.h"
#  include "jit_arm64.h"
#  define JIT_ARCH_ARM64 1
#  define PARAM_REG_BASE 0
#  define SCRATCH_REG_BASE 8
#  define MAX_SCRATCH_REGS 8
#elif defined(__x86_64__) || defined(_M_X64)
#  include "../LuaJIT/dynasm/dasm_x86.h"
#  include "jit_x64.h"
#  define JIT_ARCH_X64 1
static int const x64_param_regs[] = { 7, 6, 2, 1 };
#  define PARAM_REG(i) x64_param_regs[i]
#  define SCRATCH_REG_BASE 8
#  define MAX_SCRATCH_REGS 4
// x64 C calling convention arg registers
#  define X64_ARG0 7   // rdi
#  define X64_ARG1 6   // rsi
#  define X64_ARG2 2   // rdx
#  define X64_ARG3 1   // rcx
#else
#  define JIT_ARCH_NONE 1
#endif
#ifdef JIT_ARCH_NONE

void jit_init(Ty *ty) { (void)ty; }
void jit_free(Ty *ty) { (void)ty; }
JitInfo *jit_compile(Ty *ty, Value const *func) { (void)ty; (void)func; return NULL; }

#else

// ============================================================================
// Runtime helpers - called from JIT'd code
// ============================================================================

#if JIT_LOG_VERBOSE
#define DBG(fmt, ...) do {                                      \
        jit_emit_mov(asm, 0, BC_TY);                            \
        jit_emit_load_imm(asm, 1, ctx->sp);                     \
        jit_emit_load_imm(asm, 2, ((intptr_t)xfmt(fmt __VA_OPT__(,) __VA_ARGS__)));            \
        jit_emit_load_imm(asm, BC_CALL, (intptr_t)jit_rt_dbg);  \
        jit_emit_call_reg(asm, BC_CALL);                        \
} while (0)
#else
#define DBG(fmt, ...)
#endif

static void
jit_rt_dbg(Ty *ty, i64 sp, char const *msg)
{
        usize fp = vvL(ty->st.frames)->fp;
        usize bp = fp + vvL(ty->st.frames)->f.info[FUN_INFO_BOUND];
        Value const *v = v_(ty->stack, bp + sp - 1);

        char const *repr = (sp == 0) ? "<>" : SHOW(v, BASIC, ABBREV);

        XPRINT_CTX("%sJIT%s [%zu]: %s%s%s: %s", TERM(91), TERM(0), (usize)(bp + sp - 1 - fp), TERM(34), msg, TERM(0), repr);
}

static void
jit_rt_idbg(Ty *ty, i64 sp, char const *op)
{

        int fp = vvL(ty->st.frames)->fp;
        int np = vvL(ty->st.frames)->f.info[FUN_INFO_PARAM_COUNT];
        Value const *f = &vvL(ty->st.frames)->f;

        char *self;
        if (class_of(f) != -1) {
                self = SHOW(&vv(ty->stack)[fp + np], BASIC, ABBREV);
        } else {
                self = "<no self>";
        }

        XPRINT_CTX(
                "(%2d) %sJIT%s: %s%s%s   (self/frame[%d]=%s)",
                (int)sp,
                TERM(94),
                TERM(0),
                TERM(34;1),
                op,
                TERM(0),
                np,
                self
        );
}

static void
jit_rt_add(Ty *ty, Value *result, Value *a, Value *b)
{
        if (a->type == VALUE_INTEGER && b->type == VALUE_INTEGER) {
                *result = INTEGER(a->z + b->z);
                return;
        }
        *result = vm_2op(ty, OP_ADD, a, b);
}

static void
jit_rt_sub(Ty *ty, Value *result, Value *a, Value *b)
{
        if (a->type == VALUE_INTEGER && b->type == VALUE_INTEGER) {
                *result = INTEGER(a->z - b->z);
                return;
        }
        *result = vm_2op(ty, OP_SUB, a, b);
}

static void
jit_rt_mul(Ty *ty, Value *result, Value *a, Value *b)
{
        if (a->type == VALUE_INTEGER && b->type == VALUE_INTEGER) {
                *result = INTEGER(a->z * b->z);
                return;
        }
        *result = vm_2op(ty, OP_MUL, a, b);
}

static void
jit_rt_div(Ty *ty, Value *result, Value *a, Value *b)
{
        if (a->type == VALUE_INTEGER && b->type == VALUE_INTEGER) {
                *result = INTEGER(a->z / b->z);
                return;
        }
        *result = vm_2op(ty, OP_DIV, a, b);
}

static void
jit_rt_mod(Ty *ty, Value *result, Value *a, Value *b)
{
        if (a->type == VALUE_INTEGER && b->type == VALUE_INTEGER) {
                *result = INTEGER(a->z % b->z);
                return;
        }
        *result = vm_2op(ty, OP_MOD, a, b);
}

static void
jit_rt_neg(Ty *ty, Value *result, Value *a)
{
        (void)ty;
        if (a->type == VALUE_INTEGER) {
                *result = INTEGER(-a->z);
                return;
        }
        if (a->type == VALUE_REAL) {
                *result = REAL(-a->real);
                return;
        }
        // TODO: operator overload for negation
        *result = INTEGER(-a->z);
}

static void
jit_rt_not(Ty *ty, Value *result, Value *a)
{
        *result = BOOLEAN(!value_truthy(ty, a));
}

// Comparison helpers
static void
jit_rt_eq(Ty *ty, Value *result, Value *a, Value *b)
{
        if (LIKELY(a->type == VALUE_NIL || b->type == VALUE_NIL)) {
                *result = BOOLEAN(a->type == b->type);
        } else {
                *result = BOOLEAN(value_test_equality(ty, a, b));
        }
}

static void
jit_rt_ne(Ty *ty, Value *result, Value *a, Value *b)
{
        if (LIKELY(a->type == VALUE_NIL || b->type == VALUE_NIL)) {
                *result = BOOLEAN(a->type != b->type);
        } else {
                *result = BOOLEAN(!value_test_equality(ty, a, b));
        }
}

static void
jit_rt_lt(Ty *ty, Value *result, Value *a, Value *b)
{
        if (a->type == VALUE_INTEGER && b->type == VALUE_INTEGER) {
                *result = BOOLEAN(a->z < b->z);
                return;
        }
        *result = BOOLEAN(value_compare(ty, a, b) < 0);
}

static void
jit_rt_le(Ty *ty, Value *result, Value *a, Value *b)
{
        if (a->type == VALUE_INTEGER && b->type == VALUE_INTEGER) {
                *result = BOOLEAN(a->z <= b->z);
                return;
        }
        *result = BOOLEAN(value_compare(ty, a, b) <= 0);
}

static void
jit_rt_gt(Ty *ty, Value *result, Value *a, Value *b)
{
        if (a->type == VALUE_INTEGER && b->type == VALUE_INTEGER) {
                *result = BOOLEAN(a->z > b->z);
                return;
        }
        *result = BOOLEAN(value_compare(ty, a, b) > 0);
}

static void
jit_rt_ge(Ty *ty, Value *result, Value *a, Value *b)
{
        if (a->type == VALUE_INTEGER && b->type == VALUE_INTEGER) {
                *result = BOOLEAN(a->z >= b->z);
                return;
        }
        *result = BOOLEAN(value_compare(ty, a, b) >= 0);
}

// Member access helper
static void
jit_rt_member(Ty *ty, Value *result, Value *obj, int member_id)
{
        // Inline fast path (equivalent to LoadFieldFast for OFF_FIELD case)
        if (0 && obj->type == VALUE_OBJECT) {
                Class *cls = class_get(ty, obj->class);
                if (member_id < vN(cls->offsets_r)) {
                        u16 off = v__(cls->offsets_r, member_id);
                        if (off != OFF_NOT_FOUND) {
                                u8 kind = (off >> OFF_SHIFT);
                                if (kind == OFF_FIELD) {
                                        *result = obj->object->slots[off & OFF_MASK];
#if JIT_DEBUG_CALLS
                                        if (result->type == VALUE_REAL)
                                                fprintf(stderr, "JIT member(fast) %-20s => Float(%g)\n", M_NAME(member_id), result->real);
#endif
                                        return;
                                }
                        }
                }
        }

        // Fall back to GetMember for methods, getters, non-objects, etc.
        // exec=true so getters are called via exec_fn (returning the value,
        // not a METHOD wrapper). This is what MEMBER_ACCESS expects.
        vN(ty->stack) = result - vv(ty->stack);
        Value v = GetMember(ty, *obj, member_id, true, true);
        if (v.type != VALUE_NONE) {
                *result = v;
        } else {
                *result = NIL;
        }
}

// Member write helper
static void
jit_rt_member_set(Ty *ty, Value *obj, int member_id, Value *val)
{
        if (val > obj) {
                vN(ty->stack) = val - vv(ty->stack) + 1;
        } else {
                vN(ty->stack) = obj - vv(ty->stack) + 1;
        }
#if JIT_DEBUG_CALLS
        fprintf(stderr, "JIT member_set: obj type=%d, member=%d, val type=%d",
                obj->type, member_id, val->type);
        if (val->type == VALUE_INTEGER) fprintf(stderr, " val=%jd", val->z);
        else if (val->type == VALUE_REAL) fprintf(stderr, " val=%g", val->real);
        else if (val->type == VALUE_NIL) fprintf(stderr, " val=nil");
        fprintf(stderr, "\n");
#endif
        DoTargetMember(ty, *obj, member_id);
        xvP(ty->stack, *val);
        DoAssignExec(ty);
}

// Call a function with one argument
static void
jit_rt_call1(Ty *ty, Value *result, Value *fn, Value *arg)
{
        vm_push(ty, arg);
        *result = vm_call(ty, fn, 1);
}

// Call a method with no extra arguments (just self)
static void
jit_rt_method_call0(Ty *ty, Value *result, Value *obj, int member_id)
{
        Value method = GetMember(ty, *obj, member_id, true, false);
        if (method.type == VALUE_METHOD) {
                *result = vm_call_method(ty, method.this, method.method, 0);
        } else if (method.type != VALUE_NONE) {
                *result = vm_call(ty, &method, 0);
        } else {
                *result = NIL;
        }
}

// Call a method with N arguments on VM stack
static void
jit_rt_method_call(Ty *ty, Value *result, Value *obj, int member_id, int argc)
{
        Value method = GetMember(ty, *obj, member_id, true, false);
        if (method.type == VALUE_METHOD) {
                *result = vm_call_method(ty, method.this, method.method, argc);
        } else if (method.type != VALUE_NONE) {
                *result = vm_call(ty, &method, argc);
        } else {
                *result = NIL;
        }
}

// Subscript access
static void
jit_rt_subscript(Ty *ty, Value *result, Value *container, Value *index)
{
        switch (container->type) {
        case VALUE_ARRAY:
                *result = ArraySubscript(ty, *container, *index, true);
                break;
        case VALUE_DICT: {
                Value *vp = dict_get_value(ty, container->dict, index);
                *result = (vp == NULL) ? NIL : *vp;
                break;
        }
        case VALUE_STRING:
                vm_push(ty, index);
                *result = string_char(ty, container, 1, NULL);
                vm_pop(ty);
                break;
        case VALUE_BLOB:
                vm_push(ty, index);
                *result = blob_get(ty, container, 1, NULL);
                vm_pop(ty);
                break;
        case VALUE_OBJECT: {
                Value *method = class_lookup_method_i(ty, container->class, NAMES.subscript);
                if (method != NULL) {
                        vm_push(ty, index);
                        *result = vm_call_method(ty, container, method, 1);
                } else {
                        *result = NIL;
                }
                break;
        }
        case VALUE_TUPLE:
                if (index->type == VALUE_INTEGER) {
                        imax i = index->z;
                        if (i < 0) i += container->count;
                        if (i >= 0 && i < container->count)
                                *result = container->items[i];
                        else
                                *result = NIL;
                } else {
                        *result = NIL;
                }
                break;
        default:
                vm_push(ty, index);
                *result = vm_call(ty, container, 1);
                break;
        }
}

// Truthiness check (general case)
static bool
jit_rt_truthy(Ty *ty, Value *v)
{
        return value_truthy(ty, v);
}

// Bitwise ops
static void
jit_rt_bit_and(Ty *ty, Value *result, Value *a, Value *b)
{
        *result = vm_2op(ty, OP_BIT_AND, a, b);
}

static void
jit_rt_bit_or(Ty *ty, Value *result, Value *a, Value *b)
{
        *result = vm_2op(ty, OP_BIT_OR, a, b);
}

static void
jit_rt_bit_xor(Ty *ty, Value *result, Value *a, Value *b)
{
        *result = vm_2op(ty, OP_BIT_XOR, a, b);
}

static void
jit_rt_shl(Ty *ty, Value *result, Value *a, Value *b)
{
        *result = vm_2op(ty, OP_BIT_SHL, a, b);
}

static void
jit_rt_shr(Ty *ty, Value *result, Value *a, Value *b)
{
        *result = vm_2op(ty, OP_BIT_SHR, a, b);
}

// Increment a Value in-place (mirrors static IncValue in vm.c)
static void
jit_rt_inc(Ty *ty, Value *v)
{
        switch (v->type) {
        case VALUE_INTEGER: v->z += 1;    break;
        case VALUE_REAL:    v->real += 1; break;
        default: zP("increment applied to invalid type: %s", VSC(v));
        }
}

// Decrement a Value in-place (mirrors static DecValue in vm.c)
static void
jit_rt_dec(Ty *ty, Value *v)
{
        switch (v->type) {
        case VALUE_INTEGER: v->z -= 1;    break;
        case VALUE_REAL:    v->real -= 1; break;
        default: zP("decrement applied to invalid type: %s", VSC(v));
        }
}

// String literal: mirrors static DoStringLiteral in vm.c
static void
jit_rt_string(Ty *ty, Value *result, i32 i)
{
        InternEntry const *interned = intern_entry(&xD.strings, i);
        *result = STRING_NOGC(interned->name, (uptr)interned->data);
}

// Three-way compare → Value (wraps value_compare into INTEGER)
static void
jit_rt_cmp(Ty *ty, Value *result, Value *a, Value *b)
{
        *result = INTEGER(value_compare(ty, a, b));
}

// Count (#v) → Value
static void
jit_rt_count(Ty *ty, Value *result, Value *v)
{
        vN(ty->stack) = result - vv(ty->stack) + 1;
        DoCount(ty, true);
        *result = *vm_get(ty, 0);
}

static void
jit_rt_global(Ty *ty, Value *result, i64 n, Value *locals)
{
        *result = *vm_global(ty, n);
}

// Stack position management: mirrors VM's SP_STACK operations on the real VM stack
static void
jit_rt_save_stack_pos(Ty *ty)
{
        //xvP(ty->st.sps, vN(ty->stack));
}

static void
jit_rt_pop_stack_pos(Ty *ty)
{
        //ty->stack.count = *vvX(ty->st.sps);
}

static void
jit_rt_pop_stack_pos_pop(Ty *ty, int n)
{
        //ty->stack.count = *vvX(ty->st.sps) - n;
}

// Just pop from SP_STACK without restoring stack count (used by ARRAY)
static void
jit_rt_sp_stack_pop(Ty *ty)
{
        //(void)*vvX(ty->st.sps);
}

// Subscript assign: container[subscript] = value
// Stack layout: value, container, subscript (TOS)
// Pops all 3
static void
jit_rt_assign_subscript(Ty *ty, Value *value, Value *container, Value *subscript)
{
        vN(ty->stack) = value - vv(ty->stack) + 3;
        DoAssignSubscript(ty, true);
}

// Create array from N values on the JIT operand stack
static void
jit_rt_array(Ty *ty, Value *result, Value *elements, int n)
{
        Value v = ARRAY(vAn(n));
        v.array->count = n;
        memcpy(v.array->items, elements, n * sizeof (Value));
        *result = v;
}

// Create empty array
static void
jit_rt_array0(Ty *ty, Value *result)
{
        *result = ARRAY(vA());
}

// ============================================================================
// BYTECODE MODE: Compile bytecode → native
//
// Calling convention:
//   Value fn(Ty *ty, Value *locals, Value **env)
//   - locals points into the VM stack frame (set up by xcall)
//   - env is the closure capture array
//   - Returns a Value
//
// ARM64 callee-saved register assignments:
//   x19 = Ty *ty
//   x20 = Value *locals
//   x21 = Value **env
//   x22 = Value *ops (shadow operand stack, on C stack)
//
// Operand stack model:
//   The VM is stack-based. JIT'd code uses C-stack-allocated Value slots
//   for the operand stack, with a compile-time sp tracker. Locals are
//   accessed in-place from the VM stack frame via locals[n].
// ============================================================================

// Bytecode mode callee-saved register assignments
// void fn(Ty *ty, Value *result, Value *locals, Value **env)
// After gen_prologue: x19=x0(ty), x20=x1(result), x21=x2(locals), x22=x3(env), x23=sp(ops)
#define BC_TY    19  // Ty *ty  (x19, from x0)
#define BC_RES   20  // Value *result (x20, from x1) — return value written here
#define BC_LOC   21  // Value *locals (x21, from x2)
#define BC_ENV   22  // Value **env (x22, from x3)
#define BC_OPS   23  // Value *ops (x23, = sp after stack alloc)

// Scratch registers (caller-saved, trashed by helper calls)
#define BC_S0    8   // x8
#define BC_S1    9   // x9
#define BC_S2   10   // x10
#define BC_S3   11   // x11

#define BC_CALL 16   // x16 - call target / scratch

#define MAX_BC_OPS    64   // Max operand stack depth
#define MAX_BC_LABELS 512  // Max DynASM labels

// Bytecode compilation context
typedef struct {
        dasm_State *asm;
        Ty *ty;
        Value const *func;
        int sp;             // Current operand stack depth (compile-time)
        int max_sp;         // Maximum operand stack depth seen
        int next_label;
        int param_count;
        int bound;
        char const *name;

        // Type information (from expr_of(func)->_type)
        Type *func_type;    // TYPE_FUNCTION with param types and return type
        Class *self_class;  // Non-NULL if this is a method (class of self)
        int self_class_id;  // Class ID for guard checks (-1 if unknown)

        int save_sp_stack[16]; // Stack of saved sp values for SAVE_STACK_POS
        int save_sp_top;       // Top of save_sp stack (-1 = empty)

        // Track which local each operand stack slot came from (-1 = unknown)
        // Used to look up types for CALL_METHOD/MEMBER_ACCESS fast paths
        int op_local[MAX_BC_OPS];

        // Label map: bytecode offset → DynASM label + expected sp
        struct { int offset; int label; int sp; } labels[MAX_BC_LABELS];
        int label_count;
} JitBcCtx;

// Operand stack offset: address of ops[i] relative to BC_OPS
#define OP_OFF(i) ((i) * VALUE_SIZE)

// Get a DynASM label for a bytecode offset, creating one if needed
static int
bc_label_for(JitBcCtx *ctx, int offset)
{
        for (int i = 0; i < ctx->label_count; ++i) {
                if (ctx->labels[i].offset == offset) {
                        return ctx->labels[i].label;
                }
        }
        if (ctx->label_count >= MAX_BC_LABELS) {
                return -1;
        }
        int label = ctx->next_label++;
        ctx->labels[ctx->label_count].offset = offset;
        ctx->labels[ctx->label_count].label = label;
        ctx->labels[ctx->label_count].sp = -1; // unknown until emission
        ctx->label_count++;
        return label;
}

// Look up a label for a bytecode offset (returns -1 if not found)
static int
bc_find_label(JitBcCtx *ctx, int offset)
{
        for (int i = 0; i < ctx->label_count; ++i) {
                if (ctx->labels[i].offset == offset) {
                        return ctx->labels[i].label;
                }
        }
        return -1;
}

// Record the expected sp at a jump target
static void
bc_set_label_sp(JitBcCtx *ctx, int offset, int sp)
{
        for (int i = 0; i < ctx->label_count; ++i) {
                if (ctx->labels[i].offset == offset) {
                        if (ctx->labels[i].sp == -1) {
                                ctx->labels[i].sp = sp;
                        }
                        return;
                }
        }
}

// Get the expected sp at a label (or -1 if unknown)
static int
bc_get_label_sp(JitBcCtx *ctx, int offset)
{
        for (int i = 0; i < ctx->label_count; ++i) {
                if (ctx->labels[i].offset == offset) {
                        return ctx->labels[i].sp;
                }
        }
        return -1;
}

inline static void
idbg(JitBcCtx *ctx, char const *op)
{
        jit_emit_mov(&ctx->asm, 0, BC_TY);
        jit_emit_load_imm(&ctx->asm, 1, ctx->sp);
        jit_emit_load_imm(&ctx->asm, 2, ((intptr_t)op));
        jit_emit_load_imm(&ctx->asm, BC_CALL, (intptr_t)jit_rt_idbg);
        jit_emit_call_reg(&ctx->asm, BC_CALL);
}

// ============================================================================
// ============================================================================
// Bytecode pre-scan: discover jump targets and check supportedness
// ============================================================================

static bool
bc_prescan(JitBcCtx *ctx, char const *code, int code_size)
{
        Ty *ty = ctx->ty;
        (void)ty;

        char const *ip = code;
        char const *end = code + code_size;

#define BC_READ(var)  do { __builtin_memcpy(&var, ip, sizeof var); ip += sizeof var; } while (0)
#define BC_SKIP(type) (ip += sizeof(type))
#define BC_SKIPSTR()  (ip += strlen(ip) + 1)

        while (ip < end) {
                char const *instr_start = ip;
                int instr_off = (int)(ip - code);
                (void)instr_start;
                (void)instr_off;

                u8 op = (u8)*ip++;
                int n;
                imax k;
                double x;
                bool b;
                int nkw;
                int i, j, tag;
                uptr s;

                switch (op) {
                case INSTR_NOP:
                case INSTR_DUP:
                case INSTR_POP:
                case INSTR_POP2:
                case INSTR_SWAP:
                case INSTR_ADD:
                case INSTR_SUB:
                case INSTR_MUL:
                case INSTR_DIV:
                case INSTR_MOD:
                case INSTR_NEG:
                case INSTR_NOT:
                case INSTR_EQ:
                case INSTR_NEQ:
                case INSTR_LT:
                case INSTR_GT:
                case INSTR_LEQ:
                case INSTR_GEQ:
                case INSTR_CMP:
                case INSTR_BIT_AND:
                case INSTR_BIT_OR:
                case INSTR_BIT_XOR:
                case INSTR_SHL:
                case INSTR_SHR:
                case INSTR_CHECK_MATCH:
                case INSTR_RETURN:
                case INSTR_RETURN_PRESERVE_CTX:
                case INSTR_TRUE:
                case INSTR_FALSE:
                case INSTR_NIL:
                case INSTR_SELF:
                case INSTR_ASSIGN:
                case INSTR_MAYBE_ASSIGN:
                case INSTR_SUBSCRIPT:
                case INSTR_QUESTION:
                case INSTR_INC:
                case INSTR_DEC:
                case INSTR_COUNT:
                case INSTR_GET_TAG:
                case INSTR_CLASS_OF:
                case INSTR_MUT_ADD:
                case INSTR_MUT_SUB:
                case INSTR_MUT_MUL:
                case INSTR_MUT_DIV:
                case INSTR_MUT_MOD:
                case INSTR_CHECK_INIT:
                case INSTR_NONE_IF_NIL:
                case INSTR_THROW_IF_NIL:
                        break;

                case INSTR_LOAD_LOCAL:
                case INSTR_LOAD_REF:
                case INSTR_LOAD_CAPTURED:
                        BC_SKIP(i32);
#ifndef TY_NO_LOG
                        BC_SKIPSTR();
#endif
                        break;

                case INSTR_ASSIGN_LOCAL:
                case INSTR_TARGET_LOCAL:
                case INSTR_TARGET_REF:
                        BC_SKIP(i32);
                        break;

                case INSTR_TARGET_CAPTURED:
                        BC_SKIP(i32);
#ifndef TY_NO_LOG
                        BC_SKIPSTR();
#endif
                        break;

                case INSTR_INT8:
                        ip += 1;
                        break;

                case INSTR_INTEGER:
                        BC_SKIP(imax);
                        break;

                case INSTR_REAL:
                        BC_SKIP(double);
                        break;

                case INSTR_STRING:
                        BC_SKIP(i32);
                        break;

                case INSTR_MEMBER_ACCESS:
                case INSTR_SELF_MEMBER_ACCESS:
                        BC_SKIP(i32);
                        break;

                case INSTR_TARGET_MEMBER:
                case INSTR_TARGET_SELF_MEMBER:
                        BC_SKIP(i32);
                        break;

                case INSTR_JUMP: {
                        int off;
                        BC_READ(off);
                        int target = (int)(ip - code) + off;
                        if (bc_label_for(ctx, target) < 0) return false;
                        break;
                }

                case INSTR_JUMP_IF:
                case INSTR_JUMP_IF_NOT:
                case INSTR_JUMP_IF_NIL:
                case INSTR_JUMP_IF_NONE:
                case INSTR_JUMP_AND:
                case INSTR_JUMP_OR: {
                        int off;
                        BC_READ(off);
                        int target = (int)(ip - code) + off;
                        if (bc_label_for(ctx, target) < 0) return false;
                        break;
                }

                case INSTR_JEQ:
                case INSTR_JNE:
                case INSTR_JLT:
                case INSTR_JGT:
                case INSTR_JLE:
                case INSTR_JGE: {
                        int off;
                        BC_READ(off);
                        int target = (int)(ip - code) + off;
                        if (bc_label_for(ctx, target) < 0) return false;
                        break;
                }

                case INSTR_CALL:
                        BC_SKIP(i32);  // n (argc)
                        BC_READ(nkw);
                        for (int q = 0; q < nkw; ++q) BC_SKIPSTR();
                        break;

                case INSTR_CALL_METHOD:
                case INSTR_CALL_SELF_METHOD:
                        BC_SKIP(i32);  // n (argc)
                        BC_SKIP(i32);  // z (member_id)
                        BC_READ(nkw);
                        for (int q = 0; q < nkw; ++q) BC_SKIPSTR();
                        break;

                case INSTR_LOAD_THREAD_LOCAL:
                        return false; // not supported in JIT

                case INSTR_LOAD_GLOBAL:
                        BC_SKIP(i32);
#ifndef TY_NO_LOG
                        BC_SKIPSTR();
#endif
                        break;

                case INSTR_ASSIGN_GLOBAL:
                case INSTR_TARGET_GLOBAL:
                        BC_SKIP(i32);
                        break;

                case INSTR_CALL_GLOBAL:
                        BC_SKIP(i32);  // global idx
                        BC_SKIP(i32);  // n (argc)
                        BC_READ(nkw);
                        for (int q = 0; q < nkw; ++q) BC_SKIPSTR();
                        break;

                case INSTR_VALUE:
                case INSTR_TYPE:
                        BC_SKIP(uptr);
                        break;

                case INSTR_BAD_CALL:
                        BC_SKIPSTR();
                        BC_SKIPSTR();
                        break;

                case INSTR_BAD_MATCH:
                case INSTR_BAD_DISPATCH:
                case INSTR_BAD_ASSIGN:
                        // BAD_ASSIGN has a string; BAD_MATCH/BAD_DISPATCH have none
                        if (op == INSTR_BAD_ASSIGN) BC_SKIPSTR();
                        break;

                case INSTR_SAVE_STACK_POS:
                case INSTR_POP_STACK_POS:
                case INSTR_POP_STACK_POS_POP:
                        break;

                case INSTR_ARRAY:
                case INSTR_ARRAY0:
                        break;

                case INSTR_DUP2_SWAP:
                        break;

                case INSTR_TRY_ASSIGN_NON_NIL: {
                        i32 jump_off;
                        BC_READ(jump_off);
                        int target = (int)(ip - code) + jump_off;
                        if (bc_label_for(ctx, target) < 0) return false;
                        break;
                }

                case INSTR_ASSIGN_SUBSCRIPT:
                        break;

                case INSTR_HALT:
                        break;

                case INSTR_TAG:
                        BC_SKIP(i32);
                        break;

                case INSTR_CONCAT_STRINGS:
                        BC_SKIP(i32);
                        break;

                case INSTR_RANGE:
                case INSTR_INCRANGE:
                        break;

                case INSTR_UNARY_OP:
                case INSTR_BINARY_OP:
                        BC_SKIP(i32);
                        break;

                case INSTR_MATCH_TAG: {
                        ip += 1; // wrapped byte
                        i32 num_entries;
                        BC_READ(num_entries);
                        i32 fail_off;
                        BC_READ(fail_off);
                        int fail_target = (int)(ip - code) + fail_off;
                        if (bc_label_for(ctx, fail_target) < 0) return false;
                        for (i32 q = 0; q < num_entries; ++q) {
                                BC_SKIP(i32); // tag_id
                                i32 jmp_off;
                                BC_READ(jmp_off);
                                int jmp_target = (int)(ip - code) + jmp_off;
                                if (bc_label_for(ctx, jmp_target) < 0) return false;
                        }
                        break;
                }

                // Unsupported — bail out
                default:
                        LOG("JIT[bc]: prescan bail on %s at offset %d",
                            GetInstructionName(op), instr_off);
                        return false;
                }
        }

#undef BC_READ
#undef BC_SKIP
#undef BC_SKIPSTR

        return true;
}

// ============================================================================
// Runtime helpers for bytecode JIT (called from native code)
// ============================================================================

#define JIT_DEBUG_CALLS 0

#if JIT_DEBUG_CALLS
static void
jit_debug_result(Ty *ty, char const *kind, char const *name, Value *result)
{
        if (!name) name = "?";
        if (result->type == VALUE_INTEGER)
                fprintf(stderr, "JIT %-18s %-30s => Int(%jd)\n", kind, name, result->z);
        else if (result->type == VALUE_REAL)
                fprintf(stderr, "JIT %-18s %-30s => Float(%g)\n", kind, name, result->real);
        else if (result->type == VALUE_BOOLEAN)
                fprintf(stderr, "JIT %-18s %-30s => Bool(%s)\n", kind, name, result->boolean ? "true" : "false");
        else if (result->type == VALUE_NIL)
                fprintf(stderr, "JIT %-18s %-30s => nil\n", kind, name);
        else
                fprintf(stderr, "JIT %-18s %-30s => type=%d\n", kind, name, result->type);
}
#endif

// Call a function: args are already on the VM stack
static void
jit_rt_call(Ty *ty, Value *result, Value *fn, int argc)
{
        Value _fn = *fn;
        vN(ty->stack) = (result - vv(ty->stack)) + argc;
        DoCall(ty, &_fn, argc, 0, false, true);
        *result = *vm_get(ty, 0);
}

// Call a method on an object (generic slow path)
static void
jit_rt_call_method(Ty *ty, Value *result, Value *self, int member_id, int argc)
{
        vN(ty->stack) = (result - vv(ty->stack)) + argc;

        if (self == NULL) {
                vm_push_self(ty);
        } else {
                vm_push(ty, self);
        }

        CallMethod(ty, member_id, argc, 0, true, true);

        *result = *vm_pop(ty);
}

// Call a method directly with a baked Value* (fast path when class is known at JIT time)
static void
jit_rt_call_method_direct(Ty *ty, Value *result, Value *self, Value *method, int argc)
{
        *result = vm_call_method(ty, self, method, argc);
}

// Guarded self-method call: check self's class at runtime before using baked method.
// If self is an object of exactly the expected class, use the baked method (fast path).
// Otherwise fall back to runtime dispatch via GetMember.
static void
jit_rt_call_self_method_guarded(Ty *ty, Value *result, Value *self,
                                Value *baked, int class_id, int member_id, int argc)
{
        jit_rt_call_method(ty, result, self, member_id, argc);
        return;
        if (self->type == VALUE_OBJECT && self->class == class_id) {
                jit_rt_call_method_direct(ty, result, self, baked, argc);
                *result = vm_call_method(ty, self, baked, argc);
        } else {
                jit_rt_call_method(ty, result, self, member_id, argc);
        }
}

// Guarded builtin method call: check self's value type at runtime, then call C builtin directly.
// Falls back to runtime dispatch if the type doesn't match.
static void
jit_rt_call_builtin_method(Ty *ty, Value *result, Value *self,
                           BuiltinMethod *bm, int value_type, int member_id, int argc)
{
        if (LIKELY(self->type == value_type)) {
                usize sp0 = (result - vv(ty->stack));
                vN(ty->stack) = sp0 + argc;
                *result = bm(ty, self, argc, NULL);
                vN(ty->stack) = sp0;
        } else {
                jit_rt_call_method(ty, result, self, member_id, argc);
        }
}

// Call a method on an object using fast dispatch (offsets_r table)
// Falls back to generic GetMember if fast dispatch fails
static void
jit_rt_call_method_fast(Ty *ty, Value *result, Value *self, int member_id, int argc)
{
        jit_rt_call_method(ty, result, self, member_id, argc);
        return;

        int sp0 = vN(ty->stack) - argc;
        if (LIKELY(self->type == VALUE_OBJECT)) {
                Class *cls = class_get(ty, self->class);
                if (LIKELY(member_id < (int)vN(cls->offsets_r))) {
                        u16 off = v__(cls->offsets_r, member_id);
                        if (LIKELY(off != OFF_NOT_FOUND)) {
                                u16 kind = off >> OFF_SHIFT;
                                u16 idx = off & OFF_MASK;
                                if (LIKELY(kind == OFF_METHOD)) {
                                        Value *method = v_(cls->methods.values, idx);
                                        *result = vm_call_method(ty, self, method, argc);
                                        ty->stack.count = sp0;
                                        return;
                                }
                        }
                }
        }

        // Full fallback
        jit_rt_call_method(ty, result, self, member_id, argc);
        ty->stack.count = sp0;
}

// CHECK_MATCH: pattern matching check
// pattern is the pattern (Type, Class, Tag, Bool, or nil), value is the thing being matched
// Replaces both with a BOOLEAN result
static void
jit_rt_check_match(Ty *ty, Value *result, Value *value, Value *pattern)
{
        vN(ty->stack) = result - vv(ty->stack) + 2;
        DoCheckMatch(ty, true);
}


// Comparison (returns <0, 0, >0)
static int
jit_rt_compare(Ty *ty, Value *a, Value *b)
{
        return value_compare(ty, a, b);
}

// ============================================================================
// Bytecode emission (Pass 2)
// ============================================================================

// Emit: copy 32-byte Value from src_base+src_off to dst_base+dst_off
// For small offsets, uses ldp/stp with immediate offsets.
// For large offsets, computes effective addresses first.
static void
bc_copy_value(JitBcCtx *ctx, int dst_reg, int dst_off, int src_reg, int src_off)
{
        dasm_State **asm = &ctx->asm;

        // ldp x,x,[base,#imm] requires signed 7-bit scaled offset: range [-512, 504]
        bool src_direct = (src_off >= -512 && src_off + 16 <= 504);
        bool dst_direct = (dst_off >= -512 && dst_off + 16 <= 504);

        int sa = src_reg, so0 = src_off, so1 = src_off + 16;
        int da = dst_reg, do0 = dst_off, do1 = dst_off + 16;

        if (!src_direct) {
                jit_emit_add_imm(asm, BC_S2, src_reg, src_off);
                sa = BC_S2; so0 = 0; so1 = 16;
        }

        if (!dst_direct) {
                jit_emit_add_imm(asm, BC_S3, dst_reg, dst_off);
                da = BC_S3; do0 = 0; do1 = 16;
        }

        jit_emit_ldp64(asm, BC_S0, BC_S1, sa, so0);
        jit_emit_stp64(asm, BC_S0, BC_S1, da, do0);
        jit_emit_ldp64(asm, BC_S0, BC_S1, sa, so1);
        jit_emit_stp64(asm, BC_S0, BC_S1, da, do1);
}

// Emit: push a Value from src_base[src_off] onto the operand stack
static void
bc_push_from(JitBcCtx *ctx, int src_reg, int src_off)
{
        bc_copy_value(ctx, BC_OPS, OP_OFF(ctx->sp), src_reg, src_off);
        ctx->op_local[ctx->sp] = -1; // default: unknown origin
        ctx->sp++;
        if (ctx->sp > ctx->max_sp) ctx->max_sp = ctx->sp;
}

// Emit: pop a Value from the operand stack to dst_base[dst_off]
static void
bc_pop_to(JitBcCtx *ctx, int dst_reg, int dst_off)
{
        ctx->sp--;
        bc_copy_value(ctx, dst_reg, dst_off, BC_OPS, OP_OFF(ctx->sp));
}

// Emit: store an INTEGER Value onto the operand stack
// type=VALUE_INTEGER(2), z=val
static void
bc_push_integer(JitBcCtx *ctx, intmax_t val)
{
        dasm_State **asm = &ctx->asm;
        int off = OP_OFF(ctx->sp);

        // Zero the entire 32-byte slot first (type, tags, src, etc.)
        jit_emit_load_imm(asm, BC_S0, 0);
        jit_emit_stp64(asm, BC_S0, BC_S0, BC_OPS, off);
        jit_emit_stp64(asm, BC_S0, BC_S0, BC_OPS, off + 16);

        // Set type = VALUE_INTEGER
        jit_emit_load_imm(asm, BC_S0, VALUE_INTEGER);
        jit_emit_strb(asm, BC_S0, BC_OPS, off + VAL_OFF_TYPE);

        // Set z = val
        jit_emit_load_imm(asm, BC_S0, val);
        jit_emit_str64(asm, BC_S0, BC_OPS, off + VAL_OFF_Z);

        ctx->sp++;
        if (ctx->sp > ctx->max_sp) ctx->max_sp = ctx->sp;
}

// Emit: store a BOOLEAN Value
static void
bc_push_bool(JitBcCtx *ctx, bool val)
{
        dasm_State **asm = &ctx->asm;
        int off = OP_OFF(ctx->sp);

        jit_emit_load_imm(asm, BC_S0, 0);
        jit_emit_stp64(asm, BC_S0, BC_S0, BC_OPS, off);
        jit_emit_stp64(asm, BC_S0, BC_S0, BC_OPS, off + 16);

        jit_emit_load_imm(asm, BC_S0, VALUE_BOOLEAN);
        jit_emit_strb(asm, BC_S0, BC_OPS, off + VAL_OFF_TYPE);

        jit_emit_load_imm(asm, BC_S0, val ? 1 : 0);
        jit_emit_str64(asm, BC_S0, BC_OPS, off + VAL_OFF_Z);

        ctx->sp++;
        if (ctx->sp > ctx->max_sp) ctx->max_sp = ctx->sp;
}

// Emit: store NIL Value
static void
bc_push_nil(JitBcCtx *ctx)
{
        dasm_State **asm = &ctx->asm;
        int off = OP_OFF(ctx->sp);

        jit_emit_load_imm(asm, BC_S0, 0);
        jit_emit_stp64(asm, BC_S0, BC_S0, BC_OPS, off);
        jit_emit_stp64(asm, BC_S0, BC_S0, BC_OPS, off + 16);

        jit_emit_load_imm(asm, BC_S0, VALUE_NIL);
        jit_emit_strb(asm, BC_S0, BC_OPS, off + VAL_OFF_TYPE);

        ctx->sp++;
        if (ctx->sp > ctx->max_sp) ctx->max_sp = ctx->sp;
}

// Emit: call a C helper with signature void helper(Ty*, Value *result, Value *a, Value *b)
// a = ops[sp-2], b = ops[sp-1], result = ops[sp-2], sp--
static void
bc_emit_binop_helper(JitBcCtx *ctx, void *helper)
{
        dasm_State **asm = &ctx->asm;

        // x0 = ty
        jit_emit_mov(asm, 0, BC_TY);
        // x1 = &ops[sp-2] (result)
        jit_emit_add_imm(asm, 1, BC_OPS, OP_OFF(ctx->sp - 2));
        // x2 = &ops[sp-2] (a)
        jit_emit_mov(asm, 2, 1);
        // x3 = &ops[sp-1] (b)
        jit_emit_add_imm(asm, 3, BC_OPS, OP_OFF(ctx->sp - 1));

        jit_emit_load_imm(asm, BC_CALL, (intptr_t)helper);
        jit_emit_call_reg(asm, BC_CALL);

        ctx->sp--;
}

// Emit: call a C helper for unary op: void helper(Ty*, Value *result, Value *a)
// a = ops[sp-1], result = ops[sp-1]
static void
bc_emit_unop_helper(JitBcCtx *ctx, void *helper)
{
        dasm_State **asm = &ctx->asm;

        jit_emit_mov(asm, 0, BC_TY);
        jit_emit_add_imm(asm, 1, BC_OPS, OP_OFF(ctx->sp - 1));
        jit_emit_mov(asm, 2, 1);

        jit_emit_load_imm(asm, BC_CALL, (intptr_t)helper);
        jit_emit_call_reg(asm, BC_CALL);
}

// Emit: inline integer fast path + helper fallback for binary ops
// Both operands checked for VALUE_INTEGER, fast path does the op inline,
// slow path calls the helper.
static void
bc_emit_arith(JitBcCtx *ctx, void *helper)
{
        dasm_State **asm = &ctx->asm;
        int a_off = OP_OFF(ctx->sp - 2);
        int b_off = OP_OFF(ctx->sp - 1);

        int lbl_slow = ctx->next_label++;
        int lbl_done = ctx->next_label++;

        // Check a->type == VALUE_INTEGER
        jit_emit_ldrb(asm, BC_S0, BC_OPS, a_off + VAL_OFF_TYPE);
        jit_emit_cmp_ri(asm, BC_S0, VALUE_INTEGER);
        jit_emit_branch_ne(asm, lbl_slow);

        // Check b->type == VALUE_INTEGER
        jit_emit_ldrb(asm, BC_S0, BC_OPS, b_off + VAL_OFF_TYPE);
        jit_emit_cmp_ri(asm, BC_S0, VALUE_INTEGER);
        jit_emit_branch_ne(asm, lbl_slow);

        // Fast path: load integers, compute, store result
        jit_emit_ldr64(asm, BC_S0, BC_OPS, a_off + VAL_OFF_Z);
        jit_emit_ldr64(asm, BC_S1, BC_OPS, b_off + VAL_OFF_Z);

        // The specific operation
        if (helper == (void *)jit_rt_add) {
                jit_emit_add(asm, BC_S0, BC_S0, BC_S1);
        } else if (helper == (void *)jit_rt_sub) {
                jit_emit_sub(asm, BC_S0, BC_S0, BC_S1);
        } else if (helper == (void *)jit_rt_mul) {
                jit_emit_mul(asm, BC_S0, BC_S0, BC_S1);
        } else if (helper == (void *)jit_rt_div) {
                jit_emit_sdiv(asm, BC_S0, BC_S0, BC_S1);
        } else if (helper == (void *)jit_rt_mod) {
                jit_emit_mod(asm, BC_S0, BC_S0, BC_S1);
        } else if (helper == (void *)jit_rt_bit_and) {
                jit_emit_and(asm, BC_S0, BC_S0, BC_S1);
        } else if (helper == (void *)jit_rt_bit_or) {
                jit_emit_or(asm, BC_S0, BC_S0, BC_S1);
        } else if (helper == (void *)jit_rt_bit_xor) {
                jit_emit_xor(asm, BC_S0, BC_S0, BC_S1);
        } else if (helper == (void *)jit_rt_shl) {
                jit_emit_shl(asm, BC_S0, BC_S0, BC_S1);
        } else if (helper == (void *)jit_rt_shr) {
                jit_emit_shr(asm, BC_S0, BC_S0, BC_S1);
        }

        // Store result z into ops[sp-2]
        jit_emit_str64(asm, BC_S0, BC_OPS, a_off + VAL_OFF_Z);
        // Type is already VALUE_INTEGER
        jit_emit_jump(asm, lbl_done);

        // Slow path
        jit_emit_label(asm, lbl_slow);
        bc_emit_binop_helper(ctx, helper);
        ctx->sp++; // bc_emit_binop_helper decremented sp, but we want to undo it here
                    // since we decrement once below

        jit_emit_label(asm, lbl_done);
        ctx->sp--;
}

// Helper: write boolean result into ops slot (zeros slot, sets type + z)
static void
bc_write_bool(JitBcCtx *ctx, int off, int val_reg)
{
        dasm_State **asm = &ctx->asm;
        jit_emit_load_imm(asm, BC_S1, 0);
        jit_emit_stp64(asm, BC_S1, BC_S1, BC_OPS, off);
        jit_emit_stp64(asm, BC_S1, BC_S1, BC_OPS, off + 16);
        jit_emit_load_imm(asm, BC_S1, VALUE_BOOLEAN);
        jit_emit_strb(asm, BC_S1, BC_OPS, off + VAL_OFF_TYPE);
        jit_emit_str64(asm, val_reg, BC_OPS, off + VAL_OFF_Z);
}

// Emit: inline fast paths for comparison ops
// 1. Both int → inline cmp
// 2. Either is nil (EQ/NEQ only) → type comparison
// 3. Everything else → helper call
static void
bc_emit_cmp(JitBcCtx *ctx, void *helper)
{
        dasm_State **asm = &ctx->asm;
        int a_off = OP_OFF(ctx->sp - 2);
        int b_off = OP_OFF(ctx->sp - 1);

        int lbl_nil_check = ctx->next_label++;
        int lbl_slow = ctx->next_label++;
        int lbl_done = ctx->next_label++;

        // Load both types
        jit_emit_ldrb(asm, BC_S0, BC_OPS, a_off + VAL_OFF_TYPE); // a.type
        jit_emit_ldrb(asm, BC_S1, BC_OPS, b_off + VAL_OFF_TYPE); // b.type

        // Check a.type == VALUE_INTEGER
        jit_emit_cmp_ri(asm, BC_S0, VALUE_INTEGER);
        jit_emit_branch_ne(asm, lbl_nil_check);

        // Check b.type == VALUE_INTEGER
        jit_emit_cmp_ri(asm, BC_S1, VALUE_INTEGER);
        jit_emit_branch_ne(asm, lbl_slow);

        // === Integer fast path ===
        jit_emit_ldr64(asm, BC_S0, BC_OPS, a_off + VAL_OFF_Z);
        jit_emit_ldr64(asm, BC_S1, BC_OPS, b_off + VAL_OFF_Z);

        if (helper == (void *)jit_rt_eq) {
                jit_emit_cmp_eq(asm, BC_S0, BC_S0, BC_S1);
        } else if (helper == (void *)jit_rt_ne) {
                jit_emit_cmp_ne(asm, BC_S0, BC_S0, BC_S1);
        } else if (helper == (void *)jit_rt_lt) {
                jit_emit_cmp_lt(asm, BC_S0, BC_S0, BC_S1);
        } else if (helper == (void *)jit_rt_gt) {
                jit_emit_cmp_gt(asm, BC_S0, BC_S0, BC_S1);
        } else if (helper == (void *)jit_rt_le) {
                jit_emit_cmp_le(asm, BC_S0, BC_S0, BC_S1);
        } else if (helper == (void *)jit_rt_ge) {
                jit_emit_cmp_ge(asm, BC_S0, BC_S0, BC_S1);
        }

        bc_write_bool(ctx, a_off, BC_S0);
        jit_emit_jump(asm, lbl_done);

        // === Nil fast path (EQ/NEQ only) ===
        jit_emit_label(asm, lbl_nil_check);
        if (helper == (void *)jit_rt_eq || helper == (void *)jit_rt_ne) {
                // BC_S0 = a.type, BC_S1 = b.type (already loaded)
                // If either is nil, result = (a.type == b.type) for EQ, != for NEQ
                jit_emit_cmp_ri(asm, BC_S0, VALUE_NIL);
                int lbl_a_nil = ctx->next_label++;
                jit_emit_branch_eq(asm, lbl_a_nil);
                jit_emit_cmp_ri(asm, BC_S1, VALUE_NIL);
                jit_emit_branch_ne(asm, lbl_slow);
                // b is nil, a is not nil → EQ=false, NEQ=true
                jit_emit_load_imm(asm, BC_S0, (helper == (void *)jit_rt_ne) ? 1 : 0);
                bc_write_bool(ctx, a_off, BC_S0);
                jit_emit_jump(asm, lbl_done);
                // a is nil
                jit_emit_label(asm, lbl_a_nil);
                // result = (b.type == VALUE_NIL) for EQ, (b.type != VALUE_NIL) for NEQ
                if (helper == (void *)jit_rt_eq) {
                        jit_emit_cmp_eq(asm, BC_S0, BC_S1, BC_S0); // BC_S0 has VALUE_NIL from a
                        // Actually BC_S0 = a.type = VALUE_NIL, BC_S1 = b.type
                        // We want: result = (b.type == VALUE_NIL)
                        // BC_S0 still holds VALUE_NIL, BC_S1 holds b.type
                        jit_emit_cmp_eq(asm, BC_S0, BC_S1, BC_S0);
                } else {
                        jit_emit_cmp_ne(asm, BC_S0, BC_S1, BC_S0);
                }
                bc_write_bool(ctx, a_off, BC_S0);
                jit_emit_jump(asm, lbl_done);
        } else {
                jit_emit_jump(asm, lbl_slow);
        }

        // Slow path: call helper
        jit_emit_label(asm, lbl_slow);
        bc_emit_binop_helper(ctx, helper);
        ctx->sp++; // binop_helper decremented sp; undo since we decrement below

        jit_emit_label(asm, lbl_done);
        ctx->sp--;
}

// Emit: truthiness check on ops[sp-1], result in BC_S0 (0 or 1)
// Does NOT modify sp.
// Inline: NIL→0, BOOL→z, INT→(z!=0), other→call helper
static void
bc_emit_truthy(JitBcCtx *ctx)
{
        dasm_State **asm = &ctx->asm;
        int off = OP_OFF(ctx->sp - 1);

        int lbl_nil  = ctx->next_label++;
        int lbl_bool = ctx->next_label++;
        int lbl_int  = ctx->next_label++;
        int lbl_done = ctx->next_label++;

        // Load type byte
        jit_emit_ldrb(asm, BC_S0, BC_OPS, off + VAL_OFF_TYPE);

        // NIL → false (result = 0)
        jit_emit_cmp_ri(asm, BC_S0, VALUE_NIL);
        jit_emit_branch_eq(asm, lbl_nil);

        // BOOL → use z field directly (0 or 1)
        jit_emit_cmp_ri(asm, BC_S0, VALUE_BOOLEAN);
        jit_emit_branch_eq(asm, lbl_bool);

        // INT → z != 0
        jit_emit_cmp_ri(asm, BC_S0, VALUE_INTEGER);
        jit_emit_branch_eq(asm, lbl_int);

        // Everything else: call helper (objects, strings, arrays, etc.)
        jit_emit_mov(asm, 0, BC_TY);
        jit_emit_add_imm(asm, 1, BC_OPS, off);
        jit_emit_load_imm(asm, BC_CALL, (intptr_t)jit_rt_truthy);
        jit_emit_call_reg(asm, BC_CALL);
        jit_emit_mov(asm, BC_S0, 0);
        jit_emit_jump(asm, lbl_done);

        // NIL path: result = 0
        jit_emit_label(asm, lbl_nil);
        jit_emit_load_imm(asm, BC_S0, 0);
        jit_emit_jump(asm, lbl_done);

        // BOOL path: result = z
        jit_emit_label(asm, lbl_bool);
        jit_emit_ldr64(asm, BC_S0, BC_OPS, off + VAL_OFF_Z);
        jit_emit_jump(asm, lbl_done);

        // INT path: result = (z != 0)
        jit_emit_label(asm, lbl_int);
        jit_emit_ldr64(asm, BC_S0, BC_OPS, off + VAL_OFF_Z);
        jit_emit_load_imm(asm, BC_S1, 0);
        jit_emit_cmp_ne(asm, BC_S0, BC_S0, BC_S1);

        jit_emit_label(asm, lbl_done);
}

// Runtime helper: push N values from src to VM stack in one call
static void
jit_rt_push_n(Ty *ty, Value *src, int n)
{
        for (int i = 0; i < n; ++i) {
                vm_push(ty, src + i);
        }
}

// Emit: push N values from ops to VM stack (for function calls)
static void
bc_emit_push_args(JitBcCtx *ctx, int n)
{
        dasm_State **asm = &ctx->asm;

        if (n == 0) { ctx->sp -= n; return; }

        // Single call to push all N values
        jit_emit_mov(asm, 0, BC_TY);
        jit_emit_add_imm(asm, 1, BC_OPS, OP_OFF(ctx->sp - n));
        jit_emit_load_imm(asm, 2, n);
        jit_emit_load_imm(asm, BC_CALL, (intptr_t)jit_rt_push_n);
        jit_emit_call_reg(asm, BC_CALL);
        ctx->sp -= n;
}

// Type-guided fast path: SELF_MEMBER_ACCESS with known class
// Returns true if fast path was emitted, false to fall back to generic code
static bool
bc_emit_self_member_read_fast(JitBcCtx *ctx, int member_id)
{
        if (ctx->self_class == NULL) return false;

        Ty *ty = ctx->ty;
        Class *cls = ctx->self_class;

        if (member_id >= (int)vN(cls->offsets_r)) return false;

        u16 off = v__(cls->offsets_r, member_id);
        if (off == OFF_NOT_FOUND) return false;

        u16 kind = off >> OFF_SHIFT;
        if (kind != OFF_FIELD) return false;

        u16 slot_idx = off & OFF_MASK;
        int class_id = ctx->self_class_id;
        int slot_byte_off = OBJ_OFF_SLOTS + slot_idx * VALUE_SIZE;

        // Check offset fits in ARM64 ldp range (need slot_byte_off + 16 <= 504)
        if (slot_byte_off + 16 > 504) return false;

        dasm_State **asm = &ctx->asm;
        int self_val_off = ctx->param_count * VALUE_SIZE;
        int lbl_slow = ctx->next_label++;
        int lbl_done = ctx->next_label++;

        // Allocate the output slot
        int out_off = OP_OFF(ctx->sp);
        ctx->sp++;
        if (ctx->sp > ctx->max_sp) ctx->max_sp = ctx->sp;

        // Check self.type == VALUE_OBJECT
        jit_emit_ldrb(asm, BC_S0, BC_LOC, self_val_off + VAL_OFF_TYPE);
        jit_emit_cmp_ri(asm, BC_S0, VALUE_OBJECT);
        jit_emit_branch_ne(asm, lbl_slow);

        // Check self.class == expected_class_id
        jit_emit_ldr32(asm, BC_S0, BC_LOC, self_val_off + VAL_OFF_CLASS);
        jit_emit_cmp_ri(asm, BC_S0, class_id);
        jit_emit_branch_ne(asm, lbl_slow);

        // Fast path: load self.object → BC_S2, then copy slot to ops
        jit_emit_ldr64(asm, BC_S2, BC_LOC, self_val_off + VAL_OFF_OBJECT);
        // Copy 32-byte Value from BC_S2+slot_byte_off to BC_OPS+out_off
        // Use BC_S0/BC_S1 as scratch (safe since src is BC_S2)
        jit_emit_ldp64(asm, BC_S0, BC_S1, BC_S2, slot_byte_off);
        jit_emit_stp64(asm, BC_S0, BC_S1, BC_OPS, out_off);
        jit_emit_ldp64(asm, BC_S0, BC_S1, BC_S2, slot_byte_off + 16);
        jit_emit_stp64(asm, BC_S0, BC_S1, BC_OPS, out_off + 16);
        jit_emit_jump(asm, lbl_done);

        // Slow path: copy self to ops, call jit_rt_member
        jit_emit_label(asm, lbl_slow);
        bc_copy_value(ctx, BC_OPS, out_off, BC_LOC, self_val_off);
        jit_emit_mov(asm, 0, BC_TY);
        jit_emit_add_imm(asm, 1, BC_OPS, out_off);
        jit_emit_mov(asm, 2, 1);
        jit_emit_load_imm(asm, 3, member_id);
        jit_emit_load_imm(asm, BC_CALL, (intptr_t)jit_rt_member);
        jit_emit_call_reg(asm, BC_CALL);

        jit_emit_label(asm, lbl_done);
        return true;
}

// Type-guided fast path: TARGET_SELF_MEMBER + ASSIGN with known class
// Returns true if fast path was emitted, false to fall back to generic code
static bool
bc_emit_self_member_write_fast(JitBcCtx *ctx, int member_id)
{
        return false;

        if (ctx->self_class == NULL) return false;

        Ty *ty = ctx->ty;
        Class *cls = ctx->self_class;

        if (member_id >= (int)vN(cls->offsets_w)) return false;

        u16 off = v__(cls->offsets_w, member_id);
        if (off == OFF_NOT_FOUND) return false;

        u16 kind = off >> OFF_SHIFT;
        if (kind != OFF_FIELD) return false;

        u16 slot_idx = off & OFF_MASK;
        int class_id = ctx->self_class_id;
        int slot_byte_off = OBJ_OFF_SLOTS + slot_idx * VALUE_SIZE;

        if (slot_byte_off + 16 > 504) return false;

        dasm_State **asm = &ctx->asm;
        int self_val_off = ctx->param_count * VALUE_SIZE;
        int lbl_slow = ctx->next_label++;
        int lbl_done = ctx->next_label++;
        int val_off = OP_OFF(ctx->sp - 1);

        // Check self.type == VALUE_OBJECT
        jit_emit_ldrb(asm, BC_S0, BC_LOC, self_val_off + VAL_OFF_TYPE);
        jit_emit_cmp_ri(asm, BC_S0, VALUE_OBJECT);
        jit_emit_branch_ne(asm, lbl_slow);

        // Check self.class == expected_class_id
        jit_emit_ldr32(asm, BC_S0, BC_LOC, self_val_off + VAL_OFF_CLASS);
        jit_emit_cmp_ri(asm, BC_S0, class_id);
        jit_emit_branch_ne(asm, lbl_slow);

        // Fast path: load self.object → BC_S2, copy val to slot
        jit_emit_ldr64(asm, BC_S2, BC_LOC, self_val_off + VAL_OFF_OBJECT);
        // Copy 32-byte Value from BC_OPS+val_off to BC_S2+slot_byte_off
        jit_emit_ldp64(asm, BC_S0, BC_S1, BC_OPS, val_off);
        jit_emit_stp64(asm, BC_S0, BC_S1, BC_S2, slot_byte_off);
        jit_emit_ldp64(asm, BC_S0, BC_S1, BC_OPS, val_off + 16);
        jit_emit_stp64(asm, BC_S0, BC_S1, BC_S2, slot_byte_off + 16);
        jit_emit_jump(asm, lbl_done);

        // Slow path: call jit_rt_member_set
        jit_emit_label(asm, lbl_slow);
        jit_emit_mov(asm, 0, BC_TY);
        jit_emit_add_imm(asm, 1, BC_LOC, self_val_off);
        jit_emit_load_imm(asm, 2, member_id);
        jit_emit_add_imm(asm, 3, BC_OPS, val_off);
        jit_emit_load_imm(asm, BC_CALL, (intptr_t)jit_rt_member_set);
        jit_emit_call_reg(asm, BC_CALL);

        jit_emit_label(asm, lbl_done);
        // val stays on stack (ASSIGN peeks, doesn't pop)
        return true;
}

// Get the Class* for a local variable at JIT compile time using type inference.
// Returns NULL if the type is not a known class.
static Class *
bc_class_of_local(JitBcCtx *ctx, int local_idx)
{
        Expr const *expr = expr_of(ctx->func);
        if (expr == NULL || expr->scope == NULL) return NULL;

        Scope *scope = expr->scope;
        if (local_idx >= (int)vN(scope->owned)) return NULL;

        Symbol *sym = v__(scope->owned, local_idx);
        if (sym == NULL) return NULL;

        Type *t = sym->type;
        if (t == NULL) return NULL;

        // Direct TYPE_OBJECT: class is known
        if (TypeType(t) == TYPE_OBJECT) return t->class;

        // TYPE_UNION of T | nil: extract T if it's a class
        if (TypeType(t) == TYPE_UNION) {
                Type *non_nil = NULL;
                int n_non_nil = 0;
                for (int i = 0; i < (int)vN(t->types); ++i) {
                        if (TypeType(v__(t->types, i)) != TYPE_NIL) {
                                non_nil = v__(t->types, i);
                                n_non_nil++;
                        }
                }
                if (n_non_nil == 1 && non_nil != NULL && TypeType(non_nil) == TYPE_OBJECT) {
                        return non_nil->class;
                }
        }

        // TYPE_VARIABLE: check if bound to a useful type
        if (TypeType(t) == TYPE_VARIABLE && t->val != NULL) {
                Type *bound = t->val;
                if (TypeType(bound) == TYPE_OBJECT) return bound->class;
                // Recurse into unions
                if (TypeType(bound) == TYPE_UNION) {
                        Type *non_nil = NULL;
                        int n_non_nil = 0;
                        for (int i = 0; i < (int)vN(bound->types); ++i) {
                                if (TypeType(v__(bound->types, i)) != TYPE_NIL) {
                                        non_nil = v__(bound->types, i);
                                        n_non_nil++;
                                }
                        }
                        if (n_non_nil == 1 && non_nil != NULL && TypeType(non_nil) == TYPE_OBJECT) {
                                return non_nil->class;
                        }
                }
        }

        return NULL;
}

// Resolve a method at JIT compile time given a known class and member_id.
// Returns the baked Value* for the method, or NULL if not resolvable.
static Value *
bc_resolve_method(JitBcCtx *ctx, Class *cls, int member_id)
{
        Ty *ty = ctx->ty;

        // Check offsets_r for this member
        if (member_id >= (int)vN(cls->offsets_r)) return NULL;

        u16 off = v__(cls->offsets_r, member_id);
        if (off == OFF_NOT_FOUND) return NULL;

        u16 kind = off >> OFF_SHIFT;
        // Only handle plain methods (not decorated method slots)
        if (kind != OFF_METHOD) return NULL;

        u16 method_idx = off & OFF_MASK;
        return v_(cls->methods.values, method_idx);
}

// Resolve a builtin C method for a known value type + member_id at JIT compile time.
// Returns the BuiltinMethod* and sets *out_value_type to the VALUE_xxx constant.
static BuiltinMethod *
bc_resolve_builtin_method(Class *cls, int member_id, int *out_value_type)
{
        BuiltinMethod *bm = NULL;
        int vtype = -1;

        switch (cls->i) {
        case CLASS_STRING:
                bm = get_string_method_i(member_id);
                vtype = VALUE_STRING;
                break;
        case CLASS_ARRAY:
                bm = get_array_method_i(member_id);
                vtype = VALUE_ARRAY;
                break;
        case CLASS_DICT:
                bm = get_dict_method_i(member_id);
                vtype = VALUE_DICT;
                break;
        case CLASS_BLOB:
                bm = get_blob_method_i(member_id);
                vtype = VALUE_BLOB;
                break;
        default:
                break;
        }

        if (bm != NULL && out_value_type != NULL) {
                *out_value_type = vtype;
        }
        return bm;
}

#if JIT_LOG_VERBOSE
#define CASE(name)                \
        case INSTR_##name:        \
                idbg(ctx, ">> " #name);
#else
#define CASE(name)                \
        case INSTR_##name:
#endif

// Main bytecode emission pass
static bool
bc_emit(JitBcCtx *ctx, char const *code, int code_size)
{
        Ty *ty = ctx->ty;
        (void)ty;

        dasm_State **asm = &ctx->asm;
        char const *ip = code;
        char const *end = code + code_size;

        Symbol   **locals = vv(expr_of(ctx->func)->scope->owned);
        Symbol **captures = vv(expr_of(ctx->func)->scope->captured);

#define BC_READ(var)  do { __builtin_memcpy(&var, ip, sizeof var); ip += sizeof var; } while (0)
#define BC_SKIP(type) (ip += sizeof(type))
#define BC_SKIPSTR()  (ip += strlen(ip) + 1)

        ctx->sp     = 0;
        ctx->max_sp = 0;

        DBG("=========== BEGIN ============");

        while (ip < end) {
                int off = (int)(ip - code);

                // If this offset is a jump target, emit label and sync sp
                int lbl = bc_find_label(ctx, off);
                if (lbl >= 0) {
                        int target_sp = bc_get_label_sp(ctx, off);
                        if (target_sp >= 0) {
                                ctx->sp = target_sp;
                        }
                        jit_emit_label(asm, lbl);
                }

                jit_emit_reload_stack(asm, ctx->bound);
                jit_emit_sync_stack_count(asm, ctx->bound, ctx->sp);

                u8 op = (u8)*ip++;

                switch (op) {

                CASE(NOP)
                        break;

                CASE(LOAD_LOCAL) {
                        int n;
                        BC_READ(n);
#ifndef TY_NO_LOG
                        BC_SKIPSTR();
#endif
                        // // push(locals[n])
                        bc_push_from(ctx, BC_LOC, n * VALUE_SIZE);
                        // // Track which local this came from (for type-guided fast paths)
                        ctx->op_local[ctx->sp - 1] = n;

                        DBG("LOAD_LOCAL %s%s%s (%d)", TERM(93;1), locals[n]->identifier, TERM(0), n);
                        break;
                }

                CASE(ASSIGN_LOCAL) {
                        int n;
                        BC_READ(n);
                        // locals[n] = pop()
                        DBG("ASSIGN_LOCAL");
                        bc_pop_to(ctx, BC_LOC, n * VALUE_SIZE);
                        break;
                }

                CASE(TARGET_LOCAL) {
                        int n;
                        BC_READ(n);
                        // TARGET_LOCAL + ASSIGN fusion:
                        // peek at next instruction
                        if (ip < end && (u8)*ip == INSTR_ASSIGN) {
                                ip++; // consume ASSIGN
                                // locals[n] = peek() (ASSIGN peeks, doesn't pop)
                                bc_copy_value(ctx, BC_LOC, n * VALUE_SIZE, BC_OPS, OP_OFF(ctx->sp - 1));
                        } else if (ip < end && (u8)*ip == INSTR_TRY_ASSIGN_NON_NIL) {
                                ip++; // consume TRY_ASSIGN_NON_NIL
                                int jump;
                                BC_READ(jump);
                                int target_off = (int)(ip - code);
                                // if TOS is nil, jump; else locals[n] = TOS (peek, no pop)
                                int off = OP_OFF(ctx->sp - 1);
                                jit_emit_ldrb(asm, BC_S0, BC_OPS, off + VAL_OFF_TYPE);
                                jit_emit_cmp_ri(asm, BC_S0, VALUE_NIL);
                                int lbl_nil = bc_label_for(ctx, target_off + jump);
                                jit_emit_branch_eq(asm, lbl_nil);
                                // Not nil: assign TOS to locals[n]
                                bc_copy_value(ctx, BC_LOC, n * VALUE_SIZE, BC_OPS, off);
                        } else {
                                // Not fused — bail
                                LOG("JIT[bc]: TARGET_LOCAL without fusion (next=%d)",
                                        (ip < end) ? (u8)*ip : -1);
                                return false;
                        }
                        break;
                }

                CASE(LOAD_CAPTURED) {
                        int n;
                        BC_READ(n);
#ifndef TY_NO_LOG
                        BC_SKIPSTR();
#endif
                        // push(*env[n])
                        // env is Value**, so env[n] is Value*
                        // Load env[n] pointer into S2 (not S0/S1, which bc_copy_value clobbers)
                        jit_emit_ldr64(asm, BC_S2, BC_ENV, n * 8);
                        // Copy the Value it points to
                        bc_push_from(ctx, BC_S2, 0);
                        DBG("LOAD_LOCAL %s%s%s (%d)", TERM(93;1), captures[n]->identifier, TERM(0), n);
                        break;
                }

                CASE(INT8) {
                        int8_t k = (int8_t)*ip++;
                        bc_push_integer(ctx, k);
                        DBG("INT8");
                        break;
                }

                CASE(INTEGER) {
                        imax k;
                        BC_READ(k);
                        bc_push_integer(ctx, k);
                        break;
                }

                CASE(TRUE)
                        bc_push_bool(ctx, true);
                        break;

                CASE(FALSE)
                        bc_push_bool(ctx, false);
                        break;

                CASE(NIL)
                        bc_push_nil(ctx);
                        break;

                CASE(SELF)
                        // self = locals[param_count]
                        bc_push_from(ctx, BC_LOC, ctx->param_count * VALUE_SIZE);
                        break;

                CASE(POP)
                        ctx->sp--;
                        break;

                CASE(POP2)
                        ctx->sp -= 2;
                        break;

                CASE(DUP)
                        bc_copy_value(ctx, BC_OPS, OP_OFF(ctx->sp), BC_OPS, OP_OFF(ctx->sp - 1));
                        ctx->sp++;
                        if (ctx->sp > ctx->max_sp) ctx->max_sp = ctx->sp;
                        break;

                CASE(SWAP) {
                        // Swap ops[sp-1] and ops[sp-2]
                        int a = OP_OFF(ctx->sp - 1);
                        int b = OP_OFF(ctx->sp - 2);
                        // Load a into S0,S1
                        jit_emit_ldp64(asm, BC_S0, BC_S1, BC_OPS, a);
                        jit_emit_ldp64(asm, BC_S2, BC_S3, BC_OPS, a + 16);
                        // Load b into temp via direct copy
                        // Copy b -> a
                        bc_copy_value(ctx, BC_OPS, a, BC_OPS, b);
                        // Store original a (in regs) to b
                        jit_emit_stp64(asm, BC_S0, BC_S1, BC_OPS, b);
                        jit_emit_stp64(asm, BC_S2, BC_S3, BC_OPS, b + 16);
                        break;
                }

                // --- Arithmetic ---
                CASE(ADD)
                        bc_emit_arith(ctx, (void *)jit_rt_add);
                        break;

                CASE(SUB)
                        bc_emit_arith(ctx, (void *)jit_rt_sub);
                        break;

                CASE(MUL)
                        bc_emit_arith(ctx, (void *)jit_rt_mul);
                        break;

                CASE(DIV)
                        bc_emit_arith(ctx, (void *)jit_rt_div);
                        break;

                CASE(MOD)
                        bc_emit_arith(ctx, (void *)jit_rt_mod);
                        break;

                CASE(NEG) {
                        int off = OP_OFF(ctx->sp - 1);
                        int lbl_slow = ctx->next_label++;
                        int lbl_done = ctx->next_label++;

                        jit_emit_ldrb(asm, BC_S0, BC_OPS, off + VAL_OFF_TYPE);
                        jit_emit_cmp_ri(asm, BC_S0, VALUE_INTEGER);
                        jit_emit_branch_ne(asm, lbl_slow);

                        // Fast: negate in place
                        jit_emit_ldr64(asm, BC_S0, BC_OPS, off + VAL_OFF_Z);
                        jit_emit_neg(asm, BC_S0, BC_S0);
                        jit_emit_str64(asm, BC_S0, BC_OPS, off + VAL_OFF_Z);
                        jit_emit_jump(asm, lbl_done);

                        jit_emit_label(asm, lbl_slow);
                        bc_emit_unop_helper(ctx, (void *)jit_rt_neg);

                        jit_emit_label(asm, lbl_done);
                        break;
                }

                CASE(NOT) {
                        // !value: for booleans, flip; for nil, true; for int, z==0; else call helper
                        int off = OP_OFF(ctx->sp - 1);
                        int lbl_bool = ctx->next_label++;
                        int lbl_nil  = ctx->next_label++;
                        int lbl_slow = ctx->next_label++;
                        int lbl_done = ctx->next_label++;

                        jit_emit_ldrb(asm, BC_S0, BC_OPS, off + VAL_OFF_TYPE);

                        jit_emit_cmp_ri(asm, BC_S0, VALUE_BOOLEAN);
                        jit_emit_branch_eq(asm, lbl_bool);

                        jit_emit_cmp_ri(asm, BC_S0, VALUE_NIL);
                        jit_emit_branch_eq(asm, lbl_nil);

                        // Slow path
                        jit_emit_label(asm, lbl_slow);
                        bc_emit_unop_helper(ctx, (void *)jit_rt_not);
                        jit_emit_jump(asm, lbl_done);

                        // BOOL: flip z (0→1, 1→0), keep type as BOOLEAN
                        jit_emit_label(asm, lbl_bool);
                        jit_emit_ldr64(asm, BC_S0, BC_OPS, off + VAL_OFF_Z);
                        jit_emit_load_imm(asm, BC_S1, 1);
                        jit_emit_xor(asm, BC_S0, BC_S0, BC_S1);
                        jit_emit_str64(asm, BC_S0, BC_OPS, off + VAL_OFF_Z);
                        jit_emit_jump(asm, lbl_done);

                        // NIL: result = true
                        jit_emit_label(asm, lbl_nil);
                        jit_emit_load_imm(asm, BC_S0, 0);
                        jit_emit_stp64(asm, BC_S0, BC_S0, BC_OPS, off);
                        jit_emit_stp64(asm, BC_S0, BC_S0, BC_OPS, off + 16);
                        jit_emit_load_imm(asm, BC_S0, VALUE_BOOLEAN);
                        jit_emit_strb(asm, BC_S0, BC_OPS, off + VAL_OFF_TYPE);
                        jit_emit_load_imm(asm, BC_S0, 1);
                        jit_emit_str64(asm, BC_S0, BC_OPS, off + VAL_OFF_Z);

                        jit_emit_label(asm, lbl_done);
                        break;
                }

                // --- Comparisons ---
                CASE(EQ)
                        bc_emit_cmp(ctx, (void *)jit_rt_eq);
                        break;

                CASE(NEQ)
                        bc_emit_cmp(ctx, (void *)jit_rt_ne);
                        break;

                CASE(LT)
                        bc_emit_cmp(ctx, (void *)jit_rt_lt);
                        break;

                CASE(GT)
                        bc_emit_cmp(ctx, (void *)jit_rt_gt);
                        break;

                CASE(LEQ)
                        bc_emit_cmp(ctx, (void *)jit_rt_le);
                        break;

                CASE(GEQ)
                        bc_emit_cmp(ctx, (void *)jit_rt_ge);
                        break;

                // --- Branches ---
                CASE(JUMP) {
                        int n;
                        BC_READ(n);
                        int target = (int)(ip - code) + n;
                        int lbl = bc_find_label(ctx, target);
                        if (lbl < 0) return false;
                        bc_set_label_sp(ctx, target, ctx->sp);
                        jit_emit_jump(asm, lbl);
                        break;
                }

                CASE(JUMP_IF) {
                        int n;
                        BC_READ(n);
                        int target = (int)(ip - code) + n;
                        int lbl_target = bc_find_label(ctx, target);
                        if (lbl_target < 0) return false;

                        // Check truthiness of TOS, pop
                        bc_emit_truthy(ctx);
                        ctx->sp--;
                        bc_set_label_sp(ctx, target, ctx->sp);

                        // Branch if truthy (BC_S0 != 0)
                        jit_emit_cbnz(asm, BC_S0, lbl_target);
                        break;
                }

                CASE(JUMP_IF_NOT) {
                        int n;
                        BC_READ(n);
                        int target = (int)(ip - code) + n;
                        int lbl_target = bc_find_label(ctx, target);
                        if (lbl_target < 0) return false;

                        bc_emit_truthy(ctx);
                        ctx->sp--;
                        bc_set_label_sp(ctx, target, ctx->sp);

                        // Branch if NOT truthy (BC_S0 == 0)
                        jit_emit_cbz(asm, BC_S0, lbl_target);
                        break;
                }

                CASE(JUMP_IF_NIL) {
                        int n;
                        BC_READ(n);
                        int target = (int)(ip - code) + n;
                        int lbl_target = bc_find_label(ctx, target);
                        if (lbl_target < 0) return false;
                        jit_emit_ldrb(asm, BC_S0, BC_OPS, OP_OFF(ctx->sp - 1) + VAL_OFF_TYPE);
                        jit_emit_cmp_ri(asm, BC_S0, VALUE_NIL);
                        ctx->sp--;
                        bc_set_label_sp(ctx, target, ctx->sp);
                        jit_emit_branch_eq(asm, lbl_target);
                        break;
                }

                CASE(JUMP_IF_NONE) {
                        int n;
                        BC_READ(n);
                        int target = (int)(ip - code) + n;
                        int lbl_target = bc_find_label(ctx, target);
                        if (lbl_target < 0) return false;

                        int tos_off = OP_OFF(ctx->sp - 1);
                        jit_emit_ldrb(asm, BC_S0, BC_OPS, tos_off + VAL_OFF_TYPE);
                        jit_emit_cmp_ri(asm, BC_S0, VALUE_NONE);
                        bc_set_label_sp(ctx, target, ctx->sp);
                        jit_emit_branch_eq(asm, lbl_target);
                        break;
                }

                CASE(JUMP_AND) {
                        int n;
                        BC_READ(n);
                        int target = (int)(ip - code) + n;
                        int lbl_target = bc_find_label(ctx, target);
                        if (lbl_target < 0) return false;

                        // If TOS is falsy, jump (keep TOS)
                        // If truthy, pop and continue
                        bc_emit_truthy(ctx); // result in BC_S0
                        bc_set_label_sp(ctx, target, ctx->sp);
                        jit_emit_cbz(asm, BC_S0, lbl_target);
                        // Truthy: pop
                        ctx->sp--;
                        break;
                }

                CASE(JUMP_OR) {
                        int n;
                        BC_READ(n);
                        int target = (int)(ip - code) + n;
                        int lbl_target = bc_find_label(ctx, target);
                        if (lbl_target < 0) return false;

                        // If TOS is truthy, jump (keep TOS)
                        // If falsy, pop and continue
                        bc_emit_truthy(ctx);
                        bc_set_label_sp(ctx, target, ctx->sp); // TOS kept at branch target
                        // If truthy, jump
                        jit_emit_cbnz(asm, BC_S0, lbl_target);
                        // Falsy: pop
                        ctx->sp--;
                        break;
                }

                // --- Fused compare-and-branch ---
                CASE(JEQ)
                CASE(JNE) {
                        int n;
                        BC_READ(n);
                        int target = (int)(ip - code) + n;
                        int lbl_target = bc_find_label(ctx, target);
                        if (lbl_target < 0) return false;

                        // Equality test: call jit_rt_eq/ne(ty, &result, &a, &b)
                        // result goes into ops[sp-2], overwriting a
                        void *helper = (op == INSTR_JEQ)
                                     ? (void *)jit_rt_eq
                                     : (void *)jit_rt_ne;
                        jit_emit_mov(asm, 0, BC_TY);
                        jit_emit_add_imm(asm, 1, BC_OPS, OP_OFF(ctx->sp - 2)); // result
                        jit_emit_add_imm(asm, 2, BC_OPS, OP_OFF(ctx->sp - 2)); // a
                        jit_emit_add_imm(asm, 3, BC_OPS, OP_OFF(ctx->sp - 1)); // b
                        jit_emit_load_imm(asm, BC_CALL, (intptr_t)helper);
                        jit_emit_call_reg(asm, BC_CALL);

                        ctx->sp -= 2;
                        bc_set_label_sp(ctx, target, ctx->sp);

                        // Result is a BOOLEAN in ops[sp] (before decrement).
                        // Read the boolean byte (ldrb zero-extends to full register)
                        jit_emit_ldrb(asm, BC_S0, BC_OPS, OP_OFF(ctx->sp) + VAL_OFF_BOOL);
                        jit_emit_cbnz(asm, BC_S0, lbl_target);
                        break;
                }

                CASE(JLT)
                CASE(JGT)
                CASE(JLE)
                CASE(JGE) {
                        int n;
                        BC_READ(n);
                        int target = (int)(ip - code) + n;
                        int lbl_target = bc_find_label(ctx, target);
                        if (lbl_target < 0) return false;

                        // Ordering compare: call jit_rt_compare(ty, &a, &b)
                        jit_emit_mov(asm, 0, BC_TY);
                        jit_emit_add_imm(asm, 1, BC_OPS, OP_OFF(ctx->sp - 2));
                        jit_emit_add_imm(asm, 2, BC_OPS, OP_OFF(ctx->sp - 1));
                        jit_emit_load_imm(asm, BC_CALL, (intptr_t)jit_rt_compare);
                        jit_emit_call_reg(asm, BC_CALL);

                        ctx->sp -= 2;
                        bc_set_label_sp(ctx, target, ctx->sp);

                        // Result in w0: <0, 0, >0 (int, 32-bit)
                        jit_emit_cmp_ri32(asm, 0, 0);
                        switch (op) {
                        CASE(JLT) jit_emit_branch_lt(asm, lbl_target); break;
                        CASE(JGT) jit_emit_branch_gt(asm, lbl_target); break;
                        CASE(JLE) jit_emit_branch_le(asm, lbl_target); break;
                        CASE(JGE) jit_emit_branch_ge(asm, lbl_target); break;
                        }
                        break;
                }

                // --- Member access ---
                CASE(MEMBER_ACCESS) {
                        int z;
                        BC_READ(z);

                        // Try type-guided fast path using local type info
                        int obj_local = ctx->op_local[ctx->sp - 1];
                        Class *obj_class = (obj_local >= 0)
                                ? bc_class_of_local(ctx, obj_local)
                                : NULL;

                        bool emitted_fast = false;
                        if (obj_class != NULL) {
                                Ty *ty = ctx->ty;
                                if (z < (int)vN(obj_class->offsets_r)) {
                                        u16 off = v__(obj_class->offsets_r, z);
                                        if (off != OFF_NOT_FOUND && (off >> OFF_SHIFT) == OFF_FIELD) {
                                                u16 slot_idx = off & OFF_MASK;
                                                int class_id = obj_class->i;
                                                int slot_byte_off = OBJ_OFF_SLOTS + slot_idx * VALUE_SIZE;

                                                if (slot_byte_off + 16 <= 504) {
                                                        int obj_off = OP_OFF(ctx->sp - 1);
                                                        int lbl_slow = ctx->next_label++;
                                                        int lbl_done = ctx->next_label++;

                                                        // Check obj.type == VALUE_OBJECT
                                                        jit_emit_ldrb(asm, BC_S0, BC_OPS, obj_off + VAL_OFF_TYPE);
                                                        jit_emit_cmp_ri(asm, BC_S0, VALUE_OBJECT);
                                                        jit_emit_branch_ne(asm, lbl_slow);

                                                        // Check obj.class == expected
                                                        jit_emit_ldr32(asm, BC_S0, BC_OPS, obj_off + VAL_OFF_CLASS);
                                                        jit_emit_cmp_ri(asm, BC_S0, class_id);
                                                        jit_emit_branch_ne(asm, lbl_slow);

                                                        // Fast: load obj.object → BC_S2, copy slot to ops
                                                        jit_emit_ldr64(asm, BC_S2, BC_OPS, obj_off + VAL_OFF_OBJECT);
                                                        jit_emit_ldp64(asm, BC_S0, BC_S1, BC_S2, slot_byte_off);
                                                        jit_emit_stp64(asm, BC_S0, BC_S1, BC_OPS, obj_off);
                                                        jit_emit_ldp64(asm, BC_S0, BC_S1, BC_S2, slot_byte_off + 16);
                                                        jit_emit_stp64(asm, BC_S0, BC_S1, BC_OPS, obj_off + 16);
                                                        jit_emit_jump(asm, lbl_done);

                                                        // Slow: call helper
                                                        jit_emit_label(asm, lbl_slow);
                                                        jit_emit_mov(asm, 0, BC_TY);
                                                        jit_emit_add_imm(asm, 1, BC_OPS, obj_off);
                                                        jit_emit_mov(asm, 2, 1);
                                                        jit_emit_load_imm(asm, 3, z);
                                                        jit_emit_load_imm(asm, BC_CALL, (intptr_t)jit_rt_member);
                                                        jit_emit_call_reg(asm, BC_CALL);

                                                        jit_emit_label(asm, lbl_done);
                                                        emitted_fast = true;
                                                }
                                        }
                                }
                        }

                        if (!emitted_fast) {
                                // Generic path (no type info — not trapped)
                                jit_emit_mov(asm, 0, BC_TY);
                                jit_emit_add_imm(asm, 1, BC_OPS, OP_OFF(ctx->sp - 1));
                                jit_emit_mov(asm, 2, 1);
                                jit_emit_load_imm(asm, 3, z);
                                jit_emit_load_imm(asm, BC_CALL, (intptr_t)jit_rt_member);
                                jit_emit_call_reg(asm, BC_CALL);
                        }
                        // sp unchanged (pop obj, push result → net 0)
                        DBG("MEMBER_ACCESS");
                        break;
                }

                CASE(SELF_MEMBER_ACCESS) {
                        int z;
                        BC_READ(z);

                        // Try type-guided fast path (baked slot offset)
                        //if (bc_emit_self_member_read_fast(ctx, z)) {
                        //        break;
                        //}

                        // Generic path: push self, call helper
                        int self_off = ctx->param_count * VALUE_SIZE;
                        bc_push_from(ctx, BC_LOC, self_off);

                        jit_emit_mov(asm, 0, BC_TY);
                        jit_emit_add_imm(asm, 1, BC_OPS, OP_OFF(ctx->sp - 1));
                        jit_emit_mov(asm, 2, 1);
                        jit_emit_load_imm(asm, 3, z);
                        jit_emit_load_imm(asm, BC_CALL, (intptr_t)jit_rt_member);
                        jit_emit_call_reg(asm, BC_CALL);
                        // sp +1 from push, net +1 (self.member pushed)
                        DBG("SELF_MEMBER_ACCESS");
                        break;
                }

                // --- Target member + Assign fusion ---
                CASE(TARGET_MEMBER) {
                        int z;
                        BC_READ(z);

                        if (ip < end && (u8)*ip == INSTR_ASSIGN) {
                                ip++; // consume ASSIGN
                                // Stack: [... val obj] where obj is on top (sp-1)
                                // val is at sp-2
                                // TARGET_MEMBER pops obj, ASSIGN peeks val (doesn't pop)

                                // Try type-guided fast path
                                int obj_local = ctx->op_local[ctx->sp - 1];
                                Class *obj_class = (obj_local >= 0)
                                        ? bc_class_of_local(ctx, obj_local)
                                        : NULL;

                                bool wrote_fast = false;
                                if (0 && obj_class != NULL) {
                                        Ty *ty = ctx->ty;
                                        if (z < (int)vN(obj_class->offsets_w)) {
                                                u16 off = v__(obj_class->offsets_w, z);
                                                if (off != OFF_NOT_FOUND && (off >> OFF_SHIFT) == OFF_FIELD) {
                                                        u16 slot_idx = off & OFF_MASK;
                                                        int class_id = obj_class->i;
                                                        int slot_byte_off = OBJ_OFF_SLOTS + slot_idx * VALUE_SIZE;

                                                        if (slot_byte_off + 16 <= 504) {
                                                                int obj_off = OP_OFF(ctx->sp - 1);
                                                                int val_off = OP_OFF(ctx->sp - 2);
                                                                int lbl_slow = ctx->next_label++;
                                                                int lbl_done = ctx->next_label++;

                                                                // Check obj.type == VALUE_OBJECT
                                                                jit_emit_ldrb(asm, BC_S0, BC_OPS, obj_off + VAL_OFF_TYPE);
                                                                jit_emit_cmp_ri(asm, BC_S0, VALUE_OBJECT);
                                                                jit_emit_branch_ne(asm, lbl_slow);

                                                                // Check obj.class == expected
                                                                jit_emit_ldr32(asm, BC_S0, BC_OPS, obj_off + VAL_OFF_CLASS);
                                                                jit_emit_cmp_ri(asm, BC_S0, class_id);
                                                                jit_emit_branch_ne(asm, lbl_slow);

                                                                // Fast: load obj.object → BC_S2, copy val to slot
                                                                jit_emit_ldr64(asm, BC_S2, BC_OPS, obj_off + VAL_OFF_OBJECT);
                                                                jit_emit_ldp64(asm, BC_S0, BC_S1, BC_OPS, val_off);
                                                                jit_emit_stp64(asm, BC_S0, BC_S1, BC_S2, slot_byte_off);
                                                                jit_emit_ldp64(asm, BC_S0, BC_S1, BC_OPS, val_off + 16);
                                                                jit_emit_stp64(asm, BC_S0, BC_S1, BC_S2, slot_byte_off + 16);
                                                                jit_emit_jump(asm, lbl_done);

                                                                // Slow: call helper
                                                                jit_emit_label(asm, lbl_slow);
                                                                jit_emit_mov(asm, 0, BC_TY);
                                                                jit_emit_add_imm(asm, 1, BC_OPS, obj_off);
                                                                jit_emit_load_imm(asm, 2, z);
                                                                jit_emit_add_imm(asm, 3, BC_OPS, val_off);
                                                                jit_emit_load_imm(asm, BC_CALL, (intptr_t)jit_rt_member_set);
                                                                jit_emit_call_reg(asm, BC_CALL);

                                                                jit_emit_label(asm, lbl_done);
                                                                wrote_fast = true;
                                                        }
                                                }
                                        }
                                }

                                if (!wrote_fast) {
                                        jit_emit_mov(asm, 0, BC_TY);
                                        jit_emit_add_imm(asm, 1, BC_OPS, OP_OFF(ctx->sp - 1));
                                        jit_emit_load_imm(asm, 2, z);
                                        jit_emit_add_imm(asm, 3, BC_OPS, OP_OFF(ctx->sp - 2));
                                        jit_emit_load_imm(asm, BC_CALL, (intptr_t)jit_rt_member_set);
                                        jit_emit_call_reg(asm, BC_CALL);
                                }
                                ctx->sp -= 1; // only pop obj, val stays
                        } else {
                                LOG("JIT[bc]: TARGET_MEMBER without ASSIGN fusion");
                                return false;
                        }
                        break;
                }

                CASE(TARGET_SELF_MEMBER) {
                        int z;
                        BC_READ(z);

                        if (ip < end && (u8)*ip == INSTR_ASSIGN) {
                                ip++; // consume ASSIGN

                                // Try type-guided fast path
                                if (bc_emit_self_member_write_fast(ctx, z)) {
                                        break;
                                }

                                // Generic path: call helper
                                jit_emit_mov(asm, 0, BC_TY);
                                jit_emit_add_imm(asm, 1, BC_LOC, ctx->param_count * VALUE_SIZE);
                                jit_emit_load_imm(asm, 2, z);
                                jit_emit_add_imm(asm, 3, BC_OPS, OP_OFF(ctx->sp - 1));
                                jit_emit_load_imm(asm, BC_CALL, (intptr_t)jit_rt_member_set);
                                jit_emit_call_reg(asm, BC_CALL);
                                // val stays on stack (ASSIGN peeks, doesn't pop)
                        } else {
                                LOG("JIT[bc]: TARGET_SELF_MEMBER without ASSIGN fusion");
                                return false;
                        }
                        break;
                }

                CASE(ASSIGN)
                        // Standalone ASSIGN (not fused) — bail
                        LOG("JIT[bc]: standalone ASSIGN not supported");
                        return false;

                // --- Function calls ---
                CASE(CALL) {
                        int n, nkw;
                        BC_READ(n);
                        BC_READ(nkw);
                        for (int q = 0; q < nkw; ++q) BC_SKIPSTR();

                        if (nkw > 0) {
                                LOG("JIT[bc]: CALL with kwargs not supported");
                                return false;
                        }

                        if (n == -1) {
                                LOG("JIT[bc]: CALL with spread args not supported");
                                return false;
                        }

                        // VM stack layout: [... arg0 arg1 ... argN-1 fn]
                        // fn is at ops[sp-1] (top), args at ops[sp-1-n..sp-2]
                        //
                        // We need to:
                        // 1. Push args to VM stack (ops[sp-1-n .. sp-2])
                        // 2. Call with fn (ops[sp-1])

                        // Push args (below the function) to VM stack
                        // if (n > 0) {
                        //         jit_emit_mov(asm, 0, BC_TY);
                        //         jit_emit_add_imm(asm, 1, BC_OPS, OP_OFF(ctx->sp - 1 - n));
                        //         jit_emit_load_imm(asm, 2, n);
                        //         jit_emit_load_imm(asm, BC_CALL, (intptr_t)jit_rt_push_n);
                        //         jit_emit_call_reg(asm, BC_CALL);
                        // }

                        DBG("CALL(argc=%d)", n);

                        // fn is still at ops[sp-1]
                        // jit_rt_call(ty, &result, &fn, n)
                        // Result overwrites the fn slot, args+fn all consumed → sp -= (n+1), push result → sp += 1
                        int fn_off = OP_OFF(ctx->sp - 1);
                        int result_off = OP_OFF(ctx->sp - n - 1); // where result goes (replaces args+fn with one value)
                        jit_emit_mov(asm, 0, BC_TY);
                        jit_emit_add_imm(asm, 1, BC_OPS, result_off);  // result
                        jit_emit_add_imm(asm, 2, BC_OPS, fn_off);      // fn
                        jit_emit_load_imm(asm, 3, n);
                        jit_emit_load_imm(asm, BC_CALL, (intptr_t)jit_rt_call);
                        jit_emit_call_reg(asm, BC_CALL);
                        // Pop fn + n args, push result
                        ctx->sp -= n; // was n+1 slots (args+fn), now 1 slot (result)
                        DBG("CALL");
                        break;
                }

                CASE(CALL_METHOD) {
                        int n, z, nkw;
                        BC_READ(n);
                        BC_READ(z);
                        BC_READ(nkw);
                        for (int q = 0; q < nkw; ++q) BC_SKIPSTR();

                        if (nkw > 0 || n == -1) {
                                LOG("JIT[bc]: CALL_METHOD with kwargs/spread not supported");
                                return false;
                        }

                        // VM stack layout: [... arg0 arg1 ... argN-1 self]
                        // self is at ops[sp-1] (top), args at ops[sp-1-n..sp-2]

                        // Try to resolve method at compile time using receiver type info
                        int self_local = ctx->op_local[ctx->sp - 1];
                        Class *receiver_class = (self_local >= 0)
                                ? bc_class_of_local(ctx, self_local)
                                : NULL;

                        // Try builtin type fast path (String, Array, Dict, Blob)
                        int builtin_vtype = -1;
                        BuiltinMethod *builtin_method = (receiver_class != NULL)
                                ? bc_resolve_builtin_method(receiver_class, z, &builtin_vtype)
                                : NULL;

                        // Try object method baking (for user-defined classes)
                        Value *baked_method = (receiver_class != NULL && builtin_method == NULL)
                                ? bc_resolve_method(ctx, receiver_class, z)
                                : NULL;

                        // Push args (below self) to VM stack in one call
                        // if (n > 0) {
                        //         jit_emit_mov(asm, 0, BC_TY);
                        //         jit_emit_add_imm(asm, 1, BC_OPS, OP_OFF(ctx->sp - 1 - n));
                        //         jit_emit_load_imm(asm, 2, n);
                        //         jit_emit_load_imm(asm, BC_CALL, (intptr_t)jit_rt_push_n);
                        //         jit_emit_call_reg(asm, BC_CALL);
                        // }

                        // self is at ops[sp-1], result goes where args+self were
                        int self_off = OP_OFF(ctx->sp - 1);
                        int result_off = OP_OFF(ctx->sp - 1 - n); // replaces args+self with result

                        if (0 && builtin_method != NULL) {
                                // Direct builtin call with type guard
                                jit_emit_mov(asm, 0, BC_TY);
                                jit_emit_add_imm(asm, 1, BC_OPS, result_off);          // result
                                jit_emit_add_imm(asm, 2, BC_OPS, self_off);            // self
                                jit_emit_load_imm(asm, 3, (intptr_t)builtin_method);   // C function
                                jit_emit_load_imm(asm, 4, builtin_vtype);              // value type
                                jit_emit_load_imm(asm, 5, z);                          // member_id
                                jit_emit_load_imm(asm, 6, n);                          // argc
                                jit_emit_load_imm(asm, BC_CALL, (intptr_t)jit_rt_call_builtin_method);
                                jit_emit_call_reg(asm, BC_CALL);
                        } else if (0 && baked_method != NULL) {
                                // Guarded fast path for user-defined classes
                                jit_emit_mov(asm, 0, BC_TY);
                                jit_emit_add_imm(asm, 1, BC_OPS, result_off);  // result
                                jit_emit_add_imm(asm, 2, BC_OPS, self_off);    // self
                                jit_emit_load_imm(asm, 3, (intptr_t)baked_method);
                                jit_emit_load_imm(asm, 4, receiver_class->i);  // class_id
                                jit_emit_load_imm(asm, 5, z);                  // member_id
                                jit_emit_load_imm(asm, 6, n);                  // argc
                                jit_emit_load_imm(asm, BC_CALL, (intptr_t)jit_rt_call_self_method_guarded);
                                jit_emit_call_reg(asm, BC_CALL);
                        } else {
                                // Generic path with fast dispatch
                                jit_emit_mov(asm, 0, BC_TY);
                                jit_emit_add_imm(asm, 1, BC_OPS, result_off);  // result
                                jit_emit_add_imm(asm, 2, BC_OPS, self_off);    // self
                                jit_emit_load_imm(asm, 3, z);
                                jit_emit_load_imm(asm, 4, n);
                                jit_emit_load_imm(asm, BC_CALL, (intptr_t)jit_rt_call_method_fast);
                                jit_emit_call_reg(asm, BC_CALL);
                        }
                        // Pop self + n args, push result
                        ctx->sp -= n; // was n+1 slots (args+self), now 1 slot (result)
                        DBG("CALL_METHOD");
                        break;
                }

                CASE(CALL_SELF_METHOD) {
                        int n, z, nkw;
                        BC_READ(n);
                        BC_READ(z);
                        BC_READ(nkw);
                        for (int q = 0; q < nkw; ++q) BC_SKIPSTR();

                        if (nkw > 0 || n == -1) {
                                LOG("JIT[bc]: CALL_SELF_METHOD with kwargs/spread not supported");
                                return false;
                        }

                        // For CALL_SELF_METHOD, self is implicit (not on operand stack).
                        // Operand stack: [...][arg0][arg1]...[argN-1]
                        // Result replaces args: goes at ops[sp - n]
                        int result_off = OP_OFF(ctx->sp - n);

                        // Generic path: runtime method lookup
                        // self=NULL tells jit_rt_call_method to use vm_push_self
                        jit_emit_mov(asm, 0, BC_TY);
                        jit_emit_add_imm(asm, 1, BC_OPS, result_off);  // result
                        jit_emit_load_imm(asm, 2, 0);                  // self = NULL
                        jit_emit_load_imm(asm, 3, z);                  // member_id
                        jit_emit_load_imm(asm, 4, n);                  // argc
                        jit_emit_load_imm(asm, BC_CALL, (intptr_t)jit_rt_call_method);
                        jit_emit_call_reg(asm, BC_CALL);
                        // n args consumed, 1 result produced
                        ctx->sp -= (n - 1);
                        if (ctx->sp > ctx->max_sp) ctx->max_sp = ctx->sp;
                        break;
                }

                CASE(CALL_GLOBAL) {
                        int gi, n, nkw;
                        BC_READ(gi);
                        BC_READ(n);
                        BC_READ(nkw);
                        for (int q = 0; q < nkw; ++q) BC_SKIPSTR();

                        if (nkw > 0 || n == -1) {
                                LOG("JIT[bc]: CALL_GLOBAL with kwargs/spread not supported");
                                return false;
                        }

                        // Push n args to VM stack
                        bc_emit_push_args(ctx, n);

                        // Load global[gi] address
                        jit_emit_mov(asm, 0, BC_TY);
                        jit_emit_load_imm(asm, 1, gi);
                        jit_emit_load_imm(asm, BC_S0, (intptr_t)vm_global);
                        jit_emit_call_reg(asm, BC_S0);
                        // x0 now has Value* to the global

                        // jit_rt_call(ty, &result, fn_ptr, n)
                        jit_emit_mov(asm, 2, 0);  // fn ptr (was in x0)
                        jit_emit_mov(asm, 0, BC_TY);
                        jit_emit_add_imm(asm, 1, BC_OPS, OP_OFF(ctx->sp)); // result
                        jit_emit_load_imm(asm, 3, n);
                        jit_emit_load_imm(asm, BC_CALL, (intptr_t)jit_rt_call);
                        jit_emit_call_reg(asm, BC_CALL);
                        ctx->sp++;
                        if (ctx->sp > ctx->max_sp) ctx->max_sp = ctx->sp;
                        break;
                }

                // --- Return ---
                CASE(RETURN)
                CASE(RETURN_PRESERVE_CTX) {
                        // Result is ops[sp-1], copy to *BC_RES
                        bc_copy_value(ctx, BC_RES, 0, BC_OPS, OP_OFF(ctx->sp - 1));

                        // Jump to shared epilogue
                        int lbl_ret = bc_label_for(ctx, -1);
                        jit_emit_jump(asm, lbl_ret);
                        break;
                }

                CASE(HALT)
                        break;

                // --- Globals ---
                CASE(LOAD_GLOBAL) {
                        int n;
                        BC_READ(n);
#ifndef TY_NO_LOG
                        BC_SKIPSTR();
#endif
                        // Load global[n]
                        jit_emit_mov(asm, 0, BC_TY);
                        jit_emit_add_imm(asm, 1, BC_OPS, OP_OFF(ctx->sp)); // result
                        jit_emit_load_imm(asm, 2, n);
                        jit_emit_mov(asm, 3, BC_LOC);
                        jit_emit_load_imm(asm, BC_CALL, (intptr_t)jit_rt_global);
                        jit_emit_call_reg(asm, BC_CALL);
                        // x0 = Value*, copy to ops
                        //bc_push_from(ctx, 0, 0);
                        ctx->sp++;
                        DBG("LOAD_GLOBAL %s (%d)", compiler_global_sym(ty, n)->identifier, n);
                        break;
                }

                CASE(LOAD_THREAD_LOCAL) {
                        int n;
                        BC_READ(n);
#ifndef TY_NO_LOG
                        BC_SKIPSTR();
#endif
                        // Same as LOAD_GLOBAL for now
                        jit_emit_mov(asm, 0, BC_TY);
                        jit_emit_load_imm(asm, 1, n);
                        jit_emit_load_imm(asm, BC_CALL, (intptr_t)vm_global);
                        jit_emit_call_reg(asm, BC_CALL);
                        bc_push_from(ctx, 0, 0);
                        break;
                }

                // --- VALUE instruction (load a compile-time constant) ---
                CASE(VALUE) {
                        uptr p;
                        BC_READ(p);
                        // p is a pointer to a Value stored at compile time
                        // Use S2, not S0 (bc_copy_value clobbers S0/S1)
                        jit_emit_load_imm(asm, BC_S2, (intptr_t)p);
                        bc_push_from(ctx, BC_S2, 0);
                        break;
                }

                CASE(TYPE) {
                        uptr p;
                        BC_READ(p);
                        // TYPE pushes a Type* as a value
                        // Build TYPE value on operand stack
                        int off = OP_OFF(ctx->sp);
                        jit_emit_load_imm(asm, BC_S0, 0);
                        jit_emit_stp64(asm, BC_S0, BC_S0, BC_OPS, off);
                        jit_emit_stp64(asm, BC_S0, BC_S0, BC_OPS, off + 16);
                        jit_emit_load_imm(asm, BC_S0, VALUE_TYPE);
                        jit_emit_strb(asm, BC_S0, BC_OPS, off + VAL_OFF_TYPE);
                        jit_emit_load_imm(asm, BC_S0, (intptr_t)p);
                        jit_emit_str64(asm, BC_S0, BC_OPS, off + VAL_OFF_Z);
                        ctx->sp++;
                        if (ctx->sp > ctx->max_sp) ctx->max_sp = ctx->sp;
                        break;
                }

                // --- SAVE_STACK_POS / POP_STACK_POS ---
                CASE(SAVE_STACK_POS)
                        // Push current sp onto compile-time save stack
                        if (ctx->save_sp_top >= 15) return false;
                        ctx->save_sp_stack[++ctx->save_sp_top] = ctx->sp;
                        // Also emit runtime call to save VM stack position
                        jit_emit_mov(asm, 0, BC_TY);
                        jit_emit_load_imm(asm, BC_CALL, (intptr_t)jit_rt_save_stack_pos);
                        jit_emit_call_reg(asm, BC_CALL);
                        break;
                CASE(POP_STACK_POS)
                        // Restore compile-time sp
                        if (ctx->save_sp_top < 0) return false;
                        ctx->sp = ctx->save_sp_stack[ctx->save_sp_top--];
                        // Also emit runtime call to restore VM stack position
                        jit_emit_mov(asm, 0, BC_TY);
                        jit_emit_load_imm(asm, BC_CALL, (intptr_t)jit_rt_pop_stack_pos);
                        jit_emit_call_reg(asm, BC_CALL);
                        break;
                CASE(POP_STACK_POS_POP)
                        // Restore compile-time sp - 1
                        if (ctx->save_sp_top < 0) return false;
                        ctx->sp = ctx->save_sp_stack[ctx->save_sp_top--] - 1;
                        // Also emit runtime call to restore VM stack position - 1
                        jit_emit_mov(asm, 0, BC_TY);
                        jit_emit_load_imm(asm, 1, 1);
                        jit_emit_load_imm(asm, BC_CALL, (intptr_t)jit_rt_pop_stack_pos_pop);
                        jit_emit_call_reg(asm, BC_CALL);
                        break;

                // --- ARRAY literal ---
                CASE(ARRAY) {
                        // Elements are on ops stack from save_sp to sp
                        // Pop from compile-time save_sp stack
                        if (ctx->save_sp_top < 0) return false;
                        int saved = ctx->save_sp_stack[ctx->save_sp_top--];
                        int n = ctx->sp - saved;
                        // Pop from runtime SP_STACK (mirrors VM's *vvX(SP_STACK))
                        jit_emit_mov(asm, 0, BC_TY);
                        jit_emit_load_imm(asm, BC_CALL, (intptr_t)jit_rt_sp_stack_pop);
                        jit_emit_call_reg(asm, BC_CALL);
                        // Call helper: jit_rt_array(ty, &ops[save_sp], n, &ops[save_sp])
                        // Result overwrites first element slot, sp = save_sp + 1
                        int base_off = OP_OFF(saved);
                        jit_emit_mov(asm, 0, BC_TY);
                        jit_emit_add_imm(asm, 1, BC_OPS, base_off); // result
                        jit_emit_mov(asm, 2, 1);                    // elements
                        jit_emit_load_imm(asm, 3, n);               // count
                        jit_emit_load_imm(asm, BC_CALL, (intptr_t)jit_rt_array);
                        jit_emit_call_reg(asm, BC_CALL);
                        ctx->sp = saved + 1;
                        DBG("ARRAY literal");
                        break;
                }

                CASE(ARRAY0) {
                        // Empty array
                        int off = OP_OFF(ctx->sp);
                        jit_emit_mov(asm, 0, BC_TY);
                        jit_emit_add_imm(asm, 1, BC_OPS, off);
                        jit_emit_load_imm(asm, BC_CALL, (intptr_t)jit_rt_array0);
                        jit_emit_call_reg(asm, BC_CALL);
                        ctx->sp++;
                        if (ctx->sp > ctx->max_sp) ctx->max_sp = ctx->sp;
                        break;
                }

                // --- DUP2_SWAP ---
                CASE(DUP2_SWAP) {
                        // Before: ..., A, B (sp=N)
                        // After:  ..., A, B, B, A (sp=N+2)
                        // Copy B (at sp-1) to sp
                        bc_copy_value(ctx, BC_OPS, OP_OFF(ctx->sp), BC_OPS, OP_OFF(ctx->sp - 1));
                        ctx->sp++;
                        // Copy A (now at sp-3) to sp
                        bc_copy_value(ctx, BC_OPS, OP_OFF(ctx->sp), BC_OPS, OP_OFF(ctx->sp - 3));
                        ctx->sp++;
                        if (ctx->sp > ctx->max_sp) ctx->max_sp = ctx->sp;
                        break;
                }

                CASE(LOAD_REF) {
                        int n;
                        BC_READ(n);
#ifndef TY_NO_LOG
                        BC_SKIPSTR();
#endif
                        // Load ref: locals[n] is a VALUE_REF, dereference it
                        // For simplicity, just load it (the deref happens at runtime)
                        bc_push_from(ctx, BC_LOC, n * VALUE_SIZE);
                        break;
                }

                CASE(TARGET_REF) {
                        int n;
                        BC_READ(n);
                        if (ip < end && (u8)*ip == INSTR_ASSIGN) {
                                ip++;
                                // ASSIGN peeks, doesn't pop
                                bc_copy_value(ctx, BC_LOC, n * VALUE_SIZE, BC_OPS, OP_OFF(ctx->sp - 1));
                        } else {
                                return false;
                        }
                        break;
                }

                CASE(MAYBE_ASSIGN)
                        // Conditional assign to target: if TOS is not nil/none, assign
                        // For simplicity, bail
                        LOG("JIT[bc]: MAYBE_ASSIGN not yet supported");
                        return false;

                // --- Misc ops ---
                CASE(CHECK_MATCH) {
                        // Pattern matching: stack has [value, pattern]
                        // Replace both with BOOLEAN result
                        dasm_State **asm = &ctx->asm;
                        int pat_off = OP_OFF(ctx->sp - 1);  // pattern (TOS)
                        int val_off = OP_OFF(ctx->sp - 2);  // value being matched
                        ctx->sp -= 2;
                        int res_off = OP_OFF(ctx->sp);

                        // Call jit_rt_check_match(ty, &result, &value, &pattern)
                        jit_emit_mov(asm, 0, BC_TY);
                        jit_emit_add_imm(asm, 1, BC_OPS, res_off);
                        jit_emit_add_imm(asm, 2, BC_OPS, val_off);
                        jit_emit_add_imm(asm, 3, BC_OPS, pat_off);
                        jit_emit_load_imm(asm, BC_CALL, (intptr_t)jit_rt_check_match);
                        jit_emit_call_reg(asm, BC_CALL);

                        ctx->sp++;
                        if (ctx->sp > ctx->max_sp) ctx->max_sp = ctx->sp;
                        DBG("CHECK_MATCH");
                        break;
                }

                // --- ASSIGN_SUBSCRIPT: container[subscript] = value ---
                CASE(ASSIGN_SUBSCRIPT) {
                        // Stack: ..., value, container, subscript (TOS)
                        // After: ..., value (pops subscript + container, keeps value)
                        int sub_off = OP_OFF(ctx->sp - 1);
                        int con_off = OP_OFF(ctx->sp - 2);
                        int val_off = OP_OFF(ctx->sp - 3);

                        int lbl_slow = ctx->next_label++;
                        int lbl_done = ctx->next_label++;

                        // Fast path: container is array, subscript is non-negative int
                        jit_emit_ldrb(asm, BC_S0, BC_OPS, con_off + VAL_OFF_TYPE);
                        jit_emit_cmp_ri(asm, BC_S0, VALUE_ARRAY);
                        jit_emit_branch_ne(asm, lbl_slow);

                        jit_emit_ldrb(asm, BC_S0, BC_OPS, sub_off + VAL_OFF_TYPE);
                        jit_emit_cmp_ri(asm, BC_S0, VALUE_INTEGER);
                        jit_emit_branch_ne(asm, lbl_slow);

                        // Load index
                        jit_emit_ldr64(asm, BC_S0, BC_OPS, sub_off + VAL_OFF_Z); // idx

                        // Load array pointer
                        jit_emit_ldr64(asm, BC_S1, BC_OPS, con_off + VAL_OFF_Z); // Array*

                        // Bounds check: 0 <= idx < array->count
                        jit_emit_ldr64(asm, BC_S2, BC_S1, 8);  // count (Array+8)

                        // idx < 0 → slow path (handles negative indices)
                        jit_emit_cmp_ri(asm, BC_S0, 0);
                        jit_emit_branch_lt(asm, lbl_slow);

                        // idx >= count → slow path
                        // cmp_lt sets BC_S2 = (idx < count), branch if NOT
                        jit_emit_cmp_lt(asm, BC_S2, BC_S0, BC_S2);
                        jit_emit_cbz(asm, BC_S2, lbl_slow);

                        // Compute item address: items + idx * 32
                        jit_emit_ldr64(asm, BC_S1, BC_S1, 0);  // items pointer
                        // BC_S0 = idx, shift left by 5 (multiply by 32)
                        jit_emit_load_imm(asm, BC_S2, 5);
                        jit_emit_shl(asm, BC_S0, BC_S0, BC_S2);
                        jit_emit_add(asm, BC_S1, BC_S1, BC_S0); // item_addr = items + idx*32

                        // Copy value (32 bytes) from ops[val_off] to item_addr
                        jit_emit_ldp64(asm, BC_S0, BC_S2, BC_OPS, val_off);
                        jit_emit_stp64(asm, BC_S0, BC_S2, BC_S1, 0);
                        jit_emit_ldp64(asm, BC_S0, BC_S2, BC_OPS, val_off + 16);
                        jit_emit_stp64(asm, BC_S0, BC_S2, BC_S1, 16);
                        jit_emit_jump(asm, lbl_done);

                        // Slow path: call helper
                        jit_emit_label(asm, lbl_slow);
                        jit_emit_mov(asm, 0, BC_TY);
                        jit_emit_add_imm(asm, 1, BC_OPS, val_off);
                        jit_emit_add_imm(asm, 2, BC_OPS, con_off);
                        jit_emit_add_imm(asm, 3, BC_OPS, sub_off);
                        jit_emit_load_imm(asm, BC_CALL, (intptr_t)jit_rt_assign_subscript);
                        jit_emit_call_reg(asm, BC_CALL);

                        jit_emit_label(asm, lbl_done);
                        ctx->sp -= 2; // pop subscript + container, keep value
                        break;
                }

                CASE(QUESTION) {
                        // Check if TOS is nil → NONE, otherwise keep
                        // Actually QUESTION is the ? operator: pops, if nil returns NONE, else keeps
                        // For now bail
                        LOG("JIT[bc]: QUESTION not yet supported");
                        return false;
                }

                CASE(TAG) {
                        int tag;
                        BC_READ(tag);
                        // Push the tag value
                        // Tags are stored as VALUE_TAG with integer value
                        dasm_State **asm = &ctx->asm;
                        int off = OP_OFF(ctx->sp);

                        jit_emit_load_imm(asm, BC_S0, 0);
                        jit_emit_stp64(asm, BC_S0, BC_S0, BC_OPS, off);
                        jit_emit_stp64(asm, BC_S0, BC_S0, BC_OPS, off + 16);

                        jit_emit_load_imm(asm, BC_S0, VALUE_TAG);
                        jit_emit_strb(asm, BC_S0, BC_OPS, off + VAL_OFF_TYPE);

                        jit_emit_load_imm(asm, BC_S0, tag);
                        jit_emit_str64(asm, BC_S0, BC_OPS, off + VAL_OFF_Z);

                        ctx->sp++;
                        if (ctx->sp > ctx->max_sp) ctx->max_sp = ctx->sp;
                        break;
                }

                CASE(SUBSCRIPT) {
                        // Stack: ..., container, subscript (TOS) → result
                        int con_off = OP_OFF(ctx->sp - 2);
                        int sub_off = OP_OFF(ctx->sp - 1);
                        int res_off = con_off; // result overwrites container slot

                        int lbl_slow = ctx->next_label++;
                        int lbl_done = ctx->next_label++;

                        // Fast path: array[int]
                        jit_emit_ldrb(asm, BC_S0, BC_OPS, con_off + VAL_OFF_TYPE);
                        jit_emit_cmp_ri(asm, BC_S0, VALUE_ARRAY);
                        jit_emit_branch_ne(asm, lbl_slow);

                        jit_emit_ldrb(asm, BC_S0, BC_OPS, sub_off + VAL_OFF_TYPE);
                        jit_emit_cmp_ri(asm, BC_S0, VALUE_INTEGER);
                        jit_emit_branch_ne(asm, lbl_slow);

                        // Load index and array pointer
                        jit_emit_ldr64(asm, BC_S0, BC_OPS, sub_off + VAL_OFF_Z); // idx
                        jit_emit_ldr64(asm, BC_S1, BC_OPS, con_off + VAL_OFF_Z); // Array*

                        // Bounds check
                        jit_emit_ldr64(asm, BC_S2, BC_S1, 8);  // count
                        jit_emit_cmp_ri(asm, BC_S0, 0);
                        jit_emit_branch_lt(asm, lbl_slow);
                        jit_emit_cmp_lt(asm, BC_S2, BC_S0, BC_S2); // BC_S2 = (idx < count)
                        jit_emit_cbz(asm, BC_S2, lbl_slow);

                        // Compute item address: items + idx * 32
                        jit_emit_ldr64(asm, BC_S1, BC_S1, 0);  // items
                        jit_emit_load_imm(asm, BC_S2, 5);
                        jit_emit_shl(asm, BC_S0, BC_S0, BC_S2);
                        jit_emit_add(asm, BC_S1, BC_S1, BC_S0); // &items[idx]

                        // Copy 32 bytes from items[idx] to ops[res_off]
                        // Can't use bc_copy_value (clobbers BC_S0/S1)
                        jit_emit_ldp64(asm, BC_S0, BC_S2, BC_S1, 0);
                        jit_emit_stp64(asm, BC_S0, BC_S2, BC_OPS, res_off);
                        jit_emit_ldp64(asm, BC_S0, BC_S2, BC_S1, 16);
                        jit_emit_stp64(asm, BC_S0, BC_S2, BC_OPS, res_off + 16);
                        jit_emit_jump(asm, lbl_done);

                        // Slow path
                        jit_emit_label(asm, lbl_slow);
                        jit_emit_mov(asm, 0, BC_TY);
                        jit_emit_add_imm(asm, 1, BC_OPS, res_off);
                        jit_emit_add_imm(asm, 2, BC_OPS, con_off);
                        jit_emit_add_imm(asm, 3, BC_OPS, sub_off);
                        jit_emit_load_imm(asm, BC_CALL, (intptr_t)jit_rt_subscript);
                        jit_emit_call_reg(asm, BC_CALL);

                        jit_emit_label(asm, lbl_done);
                        ctx->sp--;
                        break;
                }

                CASE(NONE_IF_NIL) {
                        // If TOS is nil, replace with NONE
                        int off = OP_OFF(ctx->sp - 1);
                        int lbl_not_nil = ctx->next_label++;
                        jit_emit_ldrb(asm, BC_S0, BC_OPS, off + VAL_OFF_TYPE);
                        jit_emit_cmp_ri(asm, BC_S0, VALUE_NIL);
                        jit_emit_branch_ne(asm, lbl_not_nil);
                        // Is nil: set type to VALUE_NONE
                        jit_emit_load_imm(asm, BC_S0, VALUE_NONE);
                        jit_emit_strb(asm, BC_S0, BC_OPS, off + VAL_OFF_TYPE);
                        jit_emit_label(asm, lbl_not_nil);
                        break;
                }

                CASE(CHECK_INIT)
                        // Runtime check that object is initialized — skip in JIT
                        break;

                CASE(THROW_IF_NIL)
                        zP("asd");
                        // Should throw if TOS is nil — for now, skip
                        break;

                CASE(BAD_CALL)
                        BC_SKIPSTR();
                        BC_SKIPSTR();
                        // This is an error path — should not be reached at runtime
                        break;

                CASE(BAD_MATCH)
                CASE(BAD_DISPATCH)
                        break;

                CASE(BAD_ASSIGN)
                        BC_SKIPSTR();
                        break;

                // --- Bitwise ops ---
                CASE(BIT_AND)
                        bc_emit_arith(ctx, (void *)jit_rt_bit_and);
                        break;

                CASE(BIT_OR)
                        bc_emit_arith(ctx, (void *)jit_rt_bit_or);
                        break;

                CASE(BIT_XOR)
                        bc_emit_arith(ctx, (void *)jit_rt_bit_xor);
                        break;

                CASE(SHL)
                        bc_emit_arith(ctx, (void *)jit_rt_shl);
                        break;

                CASE(SHR)
                        bc_emit_arith(ctx, (void *)jit_rt_shr);
                        break;

                // --- INC/DEC (in-place on TOS) ---
                CASE(INC) {
                        int off = OP_OFF(ctx->sp - 1);
                        int lbl_slow = ctx->next_label++;
                        int lbl_done = ctx->next_label++;

                        // Fast path: if int, add 1 to z
                        jit_emit_ldrb(asm, BC_S0, BC_OPS, off + VAL_OFF_TYPE);
                        jit_emit_cmp_ri(asm, BC_S0, VALUE_INTEGER);
                        jit_emit_branch_ne(asm, lbl_slow);

                        jit_emit_ldr64(asm, BC_S0, BC_OPS, off + VAL_OFF_Z);
                        jit_emit_add_imm(asm, BC_S0, BC_S0, 1);
                        jit_emit_str64(asm, BC_S0, BC_OPS, off + VAL_OFF_Z);
                        jit_emit_jump(asm, lbl_done);

                        // Slow path: call IncValue(ty, &ops[sp-1])
                        jit_emit_label(asm, lbl_slow);
                        jit_emit_mov(asm, 0, BC_TY);
                        jit_emit_add_imm(asm, 1, BC_OPS, off);
                        jit_emit_load_imm(asm, BC_CALL, (intptr_t)jit_rt_inc);
                        jit_emit_call_reg(asm, BC_CALL);

                        jit_emit_label(asm, lbl_done);
                        break;
                }

                CASE(DEC) {
                        int off = OP_OFF(ctx->sp - 1);
                        int lbl_slow = ctx->next_label++;
                        int lbl_done = ctx->next_label++;

                        jit_emit_ldrb(asm, BC_S0, BC_OPS, off + VAL_OFF_TYPE);
                        jit_emit_cmp_ri(asm, BC_S0, VALUE_INTEGER);
                        jit_emit_branch_ne(asm, lbl_slow);

                        jit_emit_ldr64(asm, BC_S0, BC_OPS, off + VAL_OFF_Z);
                        jit_emit_load_imm(asm, BC_S1, 1);
                        jit_emit_sub(asm, BC_S0, BC_S0, BC_S1);
                        jit_emit_str64(asm, BC_S0, BC_OPS, off + VAL_OFF_Z);
                        jit_emit_jump(asm, lbl_done);

                        jit_emit_label(asm, lbl_slow);
                        jit_emit_mov(asm, 0, BC_TY);
                        jit_emit_add_imm(asm, 1, BC_OPS, off);
                        jit_emit_load_imm(asm, BC_CALL, (intptr_t)jit_rt_dec);
                        jit_emit_call_reg(asm, BC_CALL);

                        jit_emit_label(asm, lbl_done);
                        break;
                }

                // --- STRING literal ---
                CASE(STRING) {
                        int n;
                        BC_READ(n);
                        // jit_rt_string(ty, &ops[sp], n)
                        int off = OP_OFF(ctx->sp);
                        jit_emit_mov(asm, 0, BC_TY);
                        jit_emit_add_imm(asm, 1, BC_OPS, off);
                        jit_emit_load_imm(asm, 2, n);
                        jit_emit_load_imm(asm, BC_CALL, (intptr_t)jit_rt_string);
                        jit_emit_call_reg(asm, BC_CALL);
                        ctx->sp++;
                        if (ctx->sp > ctx->max_sp) ctx->max_sp = ctx->sp;
                        DBG("STRING");
                        break;
                }

                // --- REAL literal ---
                CASE(REAL) {
                        double x;
                        BC_READ(x);
                        int off = OP_OFF(ctx->sp);

                        // Zero the slot
                        jit_emit_load_imm(asm, BC_S0, 0);
                        jit_emit_stp64(asm, BC_S0, BC_S0, BC_OPS, off);
                        jit_emit_stp64(asm, BC_S0, BC_S0, BC_OPS, off + 16);

                        // Set type = VALUE_REAL
                        jit_emit_load_imm(asm, BC_S0, VALUE_REAL);
                        jit_emit_strb(asm, BC_S0, BC_OPS, off + VAL_OFF_TYPE);

                        // Set real value (copy double bits into z field)
                        {
                                union { double d; intmax_t z; } u;
                                u.d = x;
                                jit_emit_load_imm(asm, BC_S0, u.z);
                        }
                        jit_emit_str64(asm, BC_S0, BC_OPS, off + VAL_OFF_Z);

                        ctx->sp++;
                        if (ctx->sp > ctx->max_sp) ctx->max_sp = ctx->sp;
                        break;
                }

                // --- CMP (three-way compare) ---
                CASE(CMP)
                        bc_emit_binop_helper(ctx, (void *)jit_rt_cmp);
                        break;

                // --- COUNT (.len) ---
                CASE(COUNT)
                        bc_emit_unop_helper(ctx, (void *)jit_rt_count);
                        break;

                // --- GET_TAG ---
                CASE(GET_TAG) {
                        // Pop value, push its tag (or nil if no tag)
                        // For now, use a helper
                        int off = OP_OFF(ctx->sp - 1);
                        int lbl_has_tag = ctx->next_label++;
                        int lbl_done = ctx->next_label++;

                        // Check tags field
                        jit_emit_ldr32(asm, BC_S0, BC_OPS, off + VAL_OFF_TAGS);
                        jit_emit_cbnz(asm, BC_S0, lbl_has_tag);

                        // No tag: write NIL
                        jit_emit_load_imm(asm, BC_S0, 0);
                        jit_emit_stp64(asm, BC_S0, BC_S0, BC_OPS, off);
                        jit_emit_stp64(asm, BC_S0, BC_S0, BC_OPS, off + 16);
                        jit_emit_load_imm(asm, BC_S0, VALUE_NIL);
                        jit_emit_strb(asm, BC_S0, BC_OPS, off + VAL_OFF_TYPE);
                        jit_emit_jump(asm, lbl_done);

                        // Has tag: call tags_first(ty, tags) and make TAG value
                        jit_emit_label(asm, lbl_has_tag);
                        jit_emit_mov(asm, 0, BC_TY);
                        jit_emit_ldr32(asm, 1, BC_OPS, off + VAL_OFF_TAGS);
                        jit_emit_load_imm(asm, BC_CALL, (intptr_t)tags_first);
                        jit_emit_call_reg(asm, BC_CALL);
                        // Result in w0 (tag id)
                        jit_emit_mov(asm, BC_S1, 0); // save tag id
                        jit_emit_load_imm(asm, BC_S0, 0);
                        jit_emit_stp64(asm, BC_S0, BC_S0, BC_OPS, off);
                        jit_emit_stp64(asm, BC_S0, BC_S0, BC_OPS, off + 16);
                        jit_emit_load_imm(asm, BC_S0, VALUE_TAG);
                        jit_emit_strb(asm, BC_S0, BC_OPS, off + VAL_OFF_TYPE);
                        jit_emit_str64(asm, BC_S1, BC_OPS, off + VAL_OFF_Z);

                        jit_emit_label(asm, lbl_done);
                        break;
                }

                // --- MATCH_TAG: multi-way tag branch ---
                CASE(MATCH_TAG) {
                        u8 wrapped = (u8)*ip++;
                        i32 num_entries;
                        BC_READ(num_entries);
                        i32 fail_off;
                        BC_READ(fail_off);
                        int fail_target = (int)(ip - code) + fail_off;
                        int fail_lbl = bc_label_for(ctx, fail_target);

                        int off = OP_OFF(ctx->sp - 1);

                        if (wrapped) {
                                // Check value has tags (type & VALUE_TAGGED)
                                jit_emit_ldrb(asm, BC_S0, BC_OPS, off + VAL_OFF_TYPE);
                                jit_emit_load_imm(asm, BC_S1, VALUE_TAGGED);
                                jit_emit_and(asm, BC_S0, BC_S0, BC_S1);
                                jit_emit_cbz(asm, BC_S0, fail_lbl);
                                // Get tag id: tags_first(ty, top->tags)
                                jit_emit_mov(asm, 0, BC_TY);
                                jit_emit_ldr32(asm, 1, BC_OPS, off + VAL_OFF_TAGS);
                                jit_emit_load_imm(asm, BC_CALL, (intptr_t)tags_first);
                                jit_emit_call_reg(asm, BC_CALL);
                                // Result tag id in w0
                                jit_emit_mov(asm, BC_S0, 0);
                        } else {
                                // Check type == VALUE_TAG
                                jit_emit_ldrb(asm, BC_S0, BC_OPS, off + VAL_OFF_TYPE);
                                jit_emit_cmp_ri(asm, BC_S0, VALUE_TAG);
                                jit_emit_branch_ne(asm, fail_lbl);
                                // Load tag id from z field
                                jit_emit_ldr64(asm, BC_S0, BC_OPS, off + VAL_OFF_Z);
                        }

                        // Now BC_S0 = subject tag id
                        // Emit comparisons for each entry
                        for (i32 q = 0; q < num_entries; ++q) {
                                i32 entry_id;
                                BC_READ(entry_id);
                                i32 jmp_off;
                                BC_READ(jmp_off);
                                int jmp_target = (int)(ip - code) + jmp_off;
                                int jmp_lbl = bc_label_for(ctx, jmp_target);

                                jit_emit_cmp_ri(asm, BC_S0, entry_id);
                                jit_emit_branch_eq(asm, jmp_lbl);
                        }

                        // No match: fall through to fail
                        jit_emit_jump(asm, fail_lbl);
                        // sp unchanged (MATCH_TAG doesn't pop)
                        break;
                }

                // --- UNARY_OP / BINARY_OP ---
                CASE(UNARY_OP) {
                        int n;
                        BC_READ(n);
                        // Call DoUnaryOp(ty, n, false) — but it operates on VM stack.
                        // For now bail.
                        LOG("JIT[bc]: UNARY_OP not yet implemented");
                        return false;
                }

                CASE(BINARY_OP) {
                        int n;
                        BC_READ(n);
                        LOG("JIT[bc]: BINARY_OP not yet implemented");
                        return false;
                }

                // --- These require more complex handling ---
                CASE(CLASS_OF)
                CASE(MUT_ADD)
                CASE(MUT_SUB)
                CASE(MUT_MUL)
                CASE(MUT_DIV)
                CASE(MUT_MOD)
                CASE(CONCAT_STRINGS)
                CASE(RANGE)
                CASE(INCRANGE)
                CASE(ASSIGN_GLOBAL)
                CASE(TARGET_GLOBAL)
                CASE(TARGET_CAPTURED)
                        LOG("JIT[bc]: emit bail on %s", GetInstructionName(op));
                        return false;

                default:
                        LOG("JIT[bc]: unknown opcode %d", op);
                        return false;
                }
        }

        return true;

#undef BC_READ
#undef BC_SKIP
#undef BC_SKIPSTR
}

// ============================================================================
// Bytecode JIT: main entry point
// ============================================================================

JitInfo *
jit_compile(Ty *ty, Value const *func)
{
        i32 const *info = func->info;
        int code_size  = info[FUN_INFO_CODE_SIZE];
        int bound      = info[FUN_INFO_BOUND];
        int param_count = info[FUN_INFO_PARAM_COUNT];
        char const *bc = (char const *)info + info[FUN_INFO_HEADER_SIZE];

        char const *name = name_of(func);

        Expr const *_e = expr_of(func);
        char const *clsn = (_e && _e->class) ? _e->class->name : "";

        LOG("JIT[bc]: compiling %s%s%s (params=%d, bound=%d, code_size=%d, caps=%d)",
            name, clsn[0] ? " of " : "", clsn,
            param_count, bound, code_size, info[FUN_INFO_CAPTURES]);

        JitBcCtx ctx = {0};
        ctx.ty = ty;
        ctx.func = func;
        ctx.param_count = param_count;
        ctx.bound = bound;
        ctx.name = name;
        ctx.sp = 0;
        ctx.max_sp = 0;
        ctx.next_label = 0;
        ctx.label_count = 0;
        ctx.save_sp_top = -1;
        memset(ctx.op_local, -1, sizeof ctx.op_local);

        // Extract type information for fast paths
        ctx.func_type = NULL;
        ctx.self_class = NULL;
        ctx.self_class_id = -1;

        Expr const *expr = expr_of(func);
        if (expr != NULL) {
                ctx.func_type = expr->_type;
                if (expr->class != NULL) {
                        ctx.self_class = expr->class;
                        ctx.self_class_id = expr->class->i;
                        LOG("JIT[bc]: %s is method of class %s (id=%d)",
                            name, expr->class->name, ctx.self_class_id);
                }
        }

        // Pre-scan: discover jump targets, check support
        if (!bc_prescan(&ctx, bc, code_size)) {
                LOG("JIT[bc]: bail on %s", name);
#if JIT_DEBUG_CALLS
                fprintf(stderr, "JIT BAIL: %s\n", name);
#endif
                return NULL;
        }

        // Allocate a special label for the return epilogue
        bc_label_for(&ctx, -1);

        // Set up DynASM
        dasm_State *asm;
        dasm_init(&asm, DASM_MAXSECTION);
        ctx.asm = asm;

        void *global_labels[JIT_GLOB__MAX];
        dasm_setupglobal(&asm, global_labels, JIT_GLOB__MAX);
        dasm_growpc(&asm, MAX_BC_LABELS);
        dasm_setup(&asm, jit_actions);

        jit_emit_gen_prologue(&asm, bound);

        // Emit bytecode
        ctx.asm = asm; // refresh after prologue might have changed it
        if (!bc_emit(&ctx, bc, code_size)) {
                LOG("JIT[bc]: emission failed for %s", name);
                dasm_free(&asm);
                return NULL;
        }

        // Emit return epilogue at the special label
        int lbl_ret = bc_find_label(&ctx, -1);
        if (lbl_ret >= 0) {
                jit_emit_label(&asm, lbl_ret);
        }

        jit_emit_gen_epilogue(&asm);

        // Link and encode
        size_t final_size;
        int status = dasm_link(&asm, &final_size);
        if (status != DASM_S_OK) {
                LOG("JIT[bc]: dasm_link failed: %d", status);
                dasm_free(&asm);
                return NULL;
        }

        void *code = mmap(
                NULL, final_size,
                PROT_READ | PROT_WRITE,
#ifdef MAP_JIT
                MAP_PRIVATE | MAP_ANONYMOUS | MAP_JIT,
#else
                MAP_PRIVATE | MAP_ANONYMOUS,
#endif
                -1, 0
        );

        if (code == MAP_FAILED) {
                LOG("JIT[bc]: mmap failed");
                dasm_free(&asm);
                return NULL;
        }

        dasm_encode(&asm, code);
        dasm_free(&asm);
        mprotect(code, final_size, PROT_READ | PROT_EXEC);

#ifdef __APPLE__
        sys_icache_invalidate(code, final_size);
#endif

        JitInfo *ji = xmA(sizeof *ji);
        ji->code = code;
        ji->code_size = final_size;
        ji->param_count = param_count;
        ji->bound = bound;
        ji->expr = expr_of(func);
        ji->name = name;
        ji->env = NULL;
        ji->env_count = info[FUN_INFO_CAPTURES];

        LOG("JIT[bc]: compiled %s (%d params, %d bound, %zu bytes native)",
            name, param_count, bound, final_size);
#if JIT_DEBUG_CALLS
        fprintf(stderr, "JIT OK:   %s (params=%d bound=%d)\n", name, param_count, bound);
#endif

        static _Thread_local byte_vector dis;

        //DumpProgram(ty, &dis, "<bytecode>", code_of(func), code_of(func) + code_size_of(func), false);
        //xvP(dis, '\0');
        //LOGX("JIT compiled %s:\n%s", VSC(func), vv(dis));
        //v0(dis);

        return ji;
}

// ============================================================================
// Init / Free
// ============================================================================

void
jit_init(Ty *ty)
{
        (void)ty;
        LOG("JIT: initialized");
}

void
jit_free(Ty *ty)
{
        (void)ty;
        // TODO: munmap all cached JIT code
}

#endif // JIT_ARCH_NONE

/* vim: set sts=8 sw=8 expandtab: */
