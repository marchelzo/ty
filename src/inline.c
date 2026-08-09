#include <string.h>

#include "alloc.h"
#include "class.h"
#include "inline.h"
#include "operators.h"
#include "value.h"

struct TyInlineTarget {
        Class const *left;
        Class const *right;
        int left_id;
        int right_id;
        i32 const *info;
        Value **env;
        int member;
        int offset_kind;
        int op;
        int ref;
};

static bool
read_bytes(char const **ip, char const *end, void *out, usize n)
{
        if ((usize)(end - *ip) < n) {
                return false;
        }
        memcpy(out, *ip, n);
        *ip += n;
        return true;
}

#ifndef TY_NO_LOG
static bool
skip_string(char const **ip, char const *end)
{
        char const *p = memchr(*ip, '\0', end - *ip);
        if (p == NULL) {
                return false;
        }
        *ip = p + 1;
        return true;
}
#endif

static bool
push_insn(TyInlinePlan *plan, TyInlineInsn insn)
{
        if (plan->count >= TY_INLINE_MAX_INSNS) {
                return false;
        }
        plan->insns[plan->count++] = insn;
        return true;
}

bool
ty_inline_analyze(Value const *callee, TyInlineKind kind, int argc, TyInlinePlan *plan)
{
        memset(plan, 0, sizeof *plan);
        plan->self_local = -1;

        if (callee == NULL || callee->type != VALUE_FUNCTION) {
                return false;
        }
        if (argc < 0
            || argc > TY_INLINE_MAX_ARGS
            || argc != param_count_of(callee)) {
                return false;
        }
        if (callee->info[FUN_INFO_CAPTURES] != 0) {
                return false;
        }
        if (rest_idx_of(callee) != -1 || kwargs_idx_of(callee) != -1) {
                return false;
        }
        if (is_starred(callee) || is_decorated(callee)) {
                return false;
        }
        if (kind == TY_INLINE_METHOD && is_overload(callee)) {
                return false;
        }

        int expected_bound = argc + (kind == TY_INLINE_METHOD);
        if (callee->info[FUN_INFO_BOUND] != expected_bound) {
                return false;
        }
        if (kind == TY_INLINE_METHOD) {
                plan->self_local = argc;
        }
        plan->argc = argc;

        int code_size = code_size_of(callee);
        if (code_size <= 0 || code_size > TY_INLINE_MAX_BYTES) {
                return false;
        }

        char const *ip = code_of(callee);
        char const *end = ip + code_size;
        int depth = 0;
        int max_depth = 0;

        while (ip < end) {
                u8 op = (u8)*ip++;
                TyInlineInsn insn = {0};

                switch (op) {
                case INSTR_NOP:
                        break;

                case INSTR_LOAD_LOCAL:
                {
                        i32 local;
                        if (!read_bytes(&ip, end, &local, sizeof local)) {
                                return false;
                        }
#ifndef TY_NO_LOG
                        if (!skip_string(&ip, end)) {
                                return false;
                        }
#endif
                        if (local < 0 || local >= expected_bound) {
                                return false;
                        }
                        insn.op = TY_INLINE_LOCAL;
                        insn.local = local;
                        if (!push_insn(plan, insn)) {
                                return false;
                        }
                        depth++;
                        break;
                }

                case INSTR_SELF_MEMBER_ACCESS:
                {
                        i32 member;
                        if (!read_bytes(&ip, end, &member, sizeof member)
                            || kind != TY_INLINE_METHOD
                            || member < 0) {
                                return false;
                        }
                        insn.op = TY_INLINE_FIELD;
                        insn.local = plan->self_local;
                        insn.member = member;
                        if (!push_insn(plan, insn)) {
                                return false;
                        }
                        depth++;
                        break;
                }

                case INSTR_MEMBER_ACCESS:
                {
                        i32 member;
                        if (!read_bytes(&ip, end, &member, sizeof member)) {
                                return false;
                        }
                        if (depth < 1 || plan->count == 0) {
                                return false;
                        }
                        TyInlineInsn *top = &plan->insns[plan->count - 1];
                        if (top->op != TY_INLINE_LOCAL || member < 0) {
                                return false;
                        }
                        top->op = TY_INLINE_FIELD;
                        top->member = member;
                        break;
                }

                case INSTR_INT8:
                {
                        i8 value;
                        if (!read_bytes(&ip, end, &value, sizeof value)) {
                                return false;
                        }
                        insn.op = TY_INLINE_INTEGER;
                        insn.integer = value;
                        if (!push_insn(plan, insn)) {
                                return false;
                        }
                        depth++;
                        break;
                }

                case INSTR_INTEGER:
                        insn.op = TY_INLINE_INTEGER;
                        if (!read_bytes(&ip, end, &insn.integer, sizeof insn.integer)) {
                                return false;
                        }
                        if (!push_insn(plan, insn)) {
                                return false;
                        }
                        depth++;
                        break;

                case INSTR_ADD:
                case INSTR_SUB:
                case INSTR_MUL:
                        if (depth < 2) {
                                return false;
                        }
                        insn.op = op == INSTR_ADD ? TY_INLINE_ADD
                                : op == INSTR_SUB ? TY_INLINE_SUB
                                                  : TY_INLINE_MUL;
                        if (!push_insn(plan, insn)) {
                                return false;
                        }
                        depth--;
                        break;

                case INSTR_RETURN:
                        if (ip != end || depth != 1 || plan->count == 0) {
                                return false;
                        }
                        plan->max_stack = max_depth > depth ? max_depth : depth;
                        return plan->max_stack <= TY_INLINE_MAX_STACK;

                default:
                        return false;
                }

                if (depth > max_depth) {
                        max_depth = depth;
                }
                if (depth > TY_INLINE_MAX_STACK) {
                        return false;
                }
        }

        return false;
}

static TyInlineTarget *
new_target(Class const *left, Class const *right, int member, int offset_kind,
           int op, int ref, Value const *callee)
{
        TyInlineTarget *target = xmA(sizeof *target);
        *target = (TyInlineTarget) {
                .left = left,
                .right = right,
                .left_id = left != NULL ? left->i : -1,
                .right_id = right != NULL ? right->i : -1,
                .info = callee->info,
                .env = callee->env,
                .member = member,
                .offset_kind = offset_kind,
                .op = op,
                .ref = ref,
        };
        return target;
}

TyInlineTarget *
ty_inline_method_target(Class const *class, int member, Value const *callee)
{
        return new_target(class, NULL, member, OFF_METHOD, -1, -1, callee);
}

TyInlineTarget *
ty_inline_getter_target(Class const *class, int member, Value const *callee)
{
        return new_target(class, NULL, member, OFF_GETTER, -1, -1, callee);
}

TyInlineTarget *
ty_inline_operator_target(Class const *left, Class const *right, int op, int ref,
                          Value const *callee)
{
        return new_target(left, right, -1, -1, op, ref, callee);
}

static bool
same_function(Value const *value, TyInlineTarget const *target)
{
        return value != NULL
            && value->type == VALUE_FUNCTION
            && value->info == target->info
            && value->env == target->env;
}

bool
ty_inline_guard_member(Ty *ty, Value const *receiver, TyInlineTarget const *target)
{
        (void)ty;
        if (receiver->type != VALUE_OBJECT || receiver->object == NULL) {
                return false;
        }
        if (receiver->class != target->left_id
            || receiver->object->class != target->left) {
                return false;
        }
        Class const *class = target->left;
        if (target->member < 0 || target->member >= (int)vN(class->offsets_r)) {
                return false;
        }
        u16 offset = v__(class->offsets_r, target->member);
        if ((offset >> OFF_SHIFT) != target->offset_kind) {
                return false;
        }
        int index = offset & OFF_MASK;
        if (target->offset_kind == OFF_METHOD) {
                if (index >= vN(class->methods.values)) {
                        return false;
                }
                return same_function(v_(class->methods.values, index), target);
        }
        if (target->offset_kind == OFF_GETTER) {
                if (index >= vN(class->getters.values)) {
                        return false;
                }
                return same_function(v_(class->getters.values, index), target);
        }
        return false;
}

bool
ty_inline_guard_operator(Ty *ty, Value const *left, Value const *right,
                         TyInlineTarget const *target)
{
        if (left->type != VALUE_OBJECT || right->type != VALUE_OBJECT) {
                return false;
        }
        if (ClassOf(left) != target->left_id || ClassOf(right) != target->right_id) {
                return false;
        }
        int ref = op_dispatch(ty, target->op, target->left_id, target->right_id);
        if (ref != target->ref || ref < 0 || ref >= vN(Globals)) {
                return false;
        }
        return same_function(v_(Globals, ref), target);
}
