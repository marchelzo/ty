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

static bool
propagate_depth(i16 *depths, int target, int depth, int *queue, int *tail,
                int count)
{
        if (target < 0 || target > count) {
                return false;
        }
        if (depths[target] < 0) {
                depths[target] = depth;
                queue[(*tail)++] = target;
                return true;
        }
        return depths[target] == depth;
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
        if (kind != TY_INLINE_OPERATOR && is_overload(callee)) {
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

        char const *code = code_of(callee);
        char const *ip = code;
        char const *end = code + code_size;
        i16 offsets[TY_INLINE_MAX_INSNS] = {0};
        int return_offset = -1;
        int branch_count = 0;
        int jump_count = 0;
        int branch_index = -1;
        int jump_index = -1;

        while (ip < end) {
                int offset = (int)(ip - code);
                u8 op = (u8)*ip++;
                TyInlineInsn insn = {0};
                int before = plan->count;

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
                        break;
                }

                case INSTR_MEMBER_ACCESS:
                {
                        i32 member;
                        if (!read_bytes(&ip, end, &member, sizeof member)
                            || plan->count == 0) {
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
                        break;
                }

                case INSTR_INTEGER:
                        insn.op = TY_INLINE_INTEGER;
                        if (!read_bytes(&ip, end, &insn.integer, sizeof insn.integer)
                            || !push_insn(plan, insn)) {
                                return false;
                        }
                        break;

                case INSTR_REAL:
                        insn.op = TY_INLINE_REAL;
                        if (!read_bytes(&ip, end, &insn.real, sizeof insn.real)
                            || !push_insn(plan, insn)) {
                                return false;
                        }
                        break;

                case INSTR_ADD:
                case INSTR_SUB:
                case INSTR_MUL:
                case INSTR_EQ:
                case INSTR_NEQ:
                case INSTR_LT:
                case INSTR_GT:
                case INSTR_LEQ:
                case INSTR_GEQ:
                        insn.op = op == INSTR_ADD ? TY_INLINE_ADD
                                : op == INSTR_SUB ? TY_INLINE_SUB
                                : op == INSTR_MUL ? TY_INLINE_MUL
                                : op == INSTR_EQ  ? TY_INLINE_EQ
                                : op == INSTR_NEQ ? TY_INLINE_NE
                                : op == INSTR_LT  ? TY_INLINE_LT
                                : op == INSTR_GT  ? TY_INLINE_GT
                                : op == INSTR_LEQ ? TY_INLINE_LE
                                                  : TY_INLINE_GE;
                        if (!push_insn(plan, insn)) {
                                return false;
                        }
                        break;

                case INSTR_JLT:
                case INSTR_JLE:
                case INSTR_JGT:
                case INSTR_JGE:
                case INSTR_JEQ:
                case INSTR_JNE:
                {
                        i32 relative;
                        if (!read_bytes(&ip, end, &relative, sizeof relative)) {
                                return false;
                        }
                        insn.op = op == INSTR_JLT ? TY_INLINE_LT
                                : op == INSTR_JLE ? TY_INLINE_LE
                                : op == INSTR_JGT ? TY_INLINE_GT
                                : op == INSTR_JGE ? TY_INLINE_GE
                                : op == INSTR_JEQ ? TY_INLINE_EQ
                                                  : TY_INLINE_NE;
                        if (!push_insn(plan, insn)) {
                                return false;
                        }
                        offsets[before] = offset;
                        before = plan->count;
                        insn = (TyInlineInsn) {
                                .op = TY_INLINE_BRANCH_TRUE,
                                .member = (i32)(ip - code) + relative,
                        };
                        if (!push_insn(plan, insn)) {
                                return false;
                        }
                        branch_count++;
                        branch_index = plan->count - 1;
                        break;
                }

                case INSTR_JUMP:
                {
                        i32 relative;
                        if (!read_bytes(&ip, end, &relative, sizeof relative)) {
                                return false;
                        }
                        insn.op = TY_INLINE_JUMP;
                        insn.member = (i32)(ip - code) + relative;
                        if (!push_insn(plan, insn)) {
                                return false;
                        }
                        jump_count++;
                        jump_index = plan->count - 1;
                        break;
                }

                case INSTR_RETURN:
                        if (ip != end) {
                                return false;
                        }
                        return_offset = offset;
                        break;

                default:
                        return false;
                }

                for (int i = before; i < plan->count; ++i) {
                        offsets[i] = offset;
                }
                if (return_offset >= 0) {
                        break;
                }
        }

        if (return_offset < 0 || plan->count == 0) {
                return false;
        }
        if ((branch_count != 0 || jump_count != 0)
            && (branch_count != 1 || jump_count != 1)) {
                return false;
        }

        for (int i = 0; i < plan->count; ++i) {
                TyInlineInsn *insn = &plan->insns[i];
                if (insn->op != TY_INLINE_BRANCH_TRUE
                    && insn->op != TY_INLINE_JUMP) {
                        continue;
                }
                int target = -1;
                if (insn->member == return_offset) {
                        target = plan->count;
                } else {
                        for (int j = 0; j < plan->count; ++j) {
                                if (offsets[j] == insn->member) {
                                        target = j;
                                        break;
                                }
                        }
                }
                if (target <= i || target > plan->count) {
                        return false;
                }
                insn->target = target;
        }

        if (branch_count == 1) {
                TyInlineInsn const *branch = &plan->insns[branch_index];
                TyInlineInsn const *jump = &plan->insns[jump_index];
                if (branch_index <= 0
                    || branch_index >= jump_index
                    || jump_index + 1 != branch->target
                    || jump->target <= branch->target) {
                        return false;
                }
                u8 previous = plan->insns[branch_index - 1].op;
                if (previous != TY_INLINE_EQ
                    && previous != TY_INLINE_NE
                    && previous != TY_INLINE_LT
                    && previous != TY_INLINE_GT
                    && previous != TY_INLINE_LE
                    && previous != TY_INLINE_GE) {
                        return false;
                }
        }

        i16 depths[TY_INLINE_MAX_INSNS + 1];
        for (int i = 0; i <= TY_INLINE_MAX_INSNS; ++i) {
                depths[i] = -1;
        }
        int queue[TY_INLINE_MAX_INSNS + 1];
        int head = 0;
        int tail = 0;
        depths[0] = 0;
        queue[tail++] = 0;
        int max_depth = 0;

        while (head < tail) {
                int i = queue[head++];
                if (i == plan->count) {
                        continue;
                }
                int depth = depths[i];
                TyInlineInsn const *insn = &plan->insns[i];
                int next_depth = depth;
                switch (insn->op) {
                case TY_INLINE_LOCAL:
                case TY_INLINE_FIELD:
                case TY_INLINE_INTEGER:
                case TY_INLINE_REAL:
                        next_depth++;
                        break;
                case TY_INLINE_ADD:
                case TY_INLINE_SUB:
                case TY_INLINE_MUL:
                case TY_INLINE_EQ:
                case TY_INLINE_NE:
                case TY_INLINE_LT:
                case TY_INLINE_GT:
                case TY_INLINE_LE:
                case TY_INLINE_GE:
                        if (depth < 2) {
                                return false;
                        }
                        next_depth--;
                        break;
                case TY_INLINE_BRANCH_TRUE:
                        if (depth < 1) {
                                return false;
                        }
                        next_depth--;
                        break;
                case TY_INLINE_JUMP:
                        break;
                }
                if (next_depth > TY_INLINE_MAX_STACK) {
                        return false;
                }
                if (next_depth > max_depth) {
                        max_depth = next_depth;
                }

                if (insn->op == TY_INLINE_BRANCH_TRUE) {
                        if (!propagate_depth(
                                depths, i + 1, next_depth, queue, &tail, plan->count
                            ) || !propagate_depth(
                                depths, insn->target, next_depth,
                                queue, &tail, plan->count
                            )) {
                                return false;
                        }
                } else if (insn->op == TY_INLINE_JUMP) {
                        if (!propagate_depth(
                                depths, insn->target, next_depth,
                                queue, &tail, plan->count
                            )) {
                                return false;
                        }
                } else if (!propagate_depth(
                        depths, i + 1, next_depth, queue, &tail, plan->count
                )) {
                        return false;
                }
        }

        if (depths[plan->count] != 1) {
                return false;
        }
        if (branch_count == 1
            && depths[branch_index] != depths[branch_index - 1] - 1) {
                return false;
        }
        for (int i = 0; i < plan->count; ++i) {
                if (depths[i] < 0) {
                        return false;
                }
                plan->depths[i] = depths[i];
        }
        plan->depths[plan->count] = depths[plan->count];
        plan->max_stack = max_depth;
        return true;
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

TyInlineTarget *
ty_inline_global_target(int global, Value const *callee)
{
        return new_target(NULL, NULL, -1, -1, -1, global, callee);
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
ty_inline_guard_global(Ty *ty, TyInlineTarget const *target)
{
        (void)ty;
        return target->ref >= 0
            && target->ref < vN(Globals)
            && same_function(v_(Globals, target->ref), target);
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
