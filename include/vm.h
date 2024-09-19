#ifndef VM_H_INCLUDED
#define VM_H_INCLUDED

#include <stdint.h>
#include <stdbool.h>
#include <stdarg.h>
#include <stdnoreturn.h>

#include <signal.h>

#include "ty.h"
#include "value.h"
#include "tthread.h"
#include "log.h"

extern bool CompileOnly;
extern bool PrintResult;
extern _Thread_local int EvalDepth;

#define TY_INSTRUCTIONS \
        X(NOP), \
        X(LOAD_LOCAL), \
        X(LOAD_REF), \
        X(LOAD_CAPTURED), \
        X(LOAD_GLOBAL), \
        X(CHECK_INIT), \
        X(CAPTURE), \
        X(TARGET_LOCAL), \
        X(TARGET_REF), \
        X(TARGET_CAPTURED), \
        X(TARGET_GLOBAL), \
        X(TARGET_MEMBER), \
        X(TARGET_SUBSCRIPT), \
        X(ASSIGN), \
        X(MAYBE_ASSIGN), \
        X(ARRAY_REST), \
        X(TUPLE_REST), \
        X(RECORD_REST), \
        X(INTEGER), \
        X(REAL), \
        X(BOOLEAN), \
        X(STRING), \
        X(REGEX), \
        X(ARRAY), \
        X(DICT), \
        X(TUPLE), \
        X(DICT_DEFAULT), \
        X(NIL), \
        X(SELF), \
        X(TAG), \
        X(CLASS), \
        X(TO_STRING), \
        X(CONCAT_STRINGS), \
        X(RANGE), \
        X(INCRANGE), \
        X(MEMBER_ACCESS), \
        X(TRY_MEMBER_ACCESS), \
        X(SUBSCRIPT), \
        X(SLICE), \
        X(TAIL_CALL), \
        X(CALL), \
        X(CALL_METHOD), \
        X(TRY_CALL_METHOD), \
        X(GET_NEXT), \
        X(PUSH_INDEX), \
        X(READ_INDEX), \
        X(POP), \
        X(UNPOP), \
        X(DUP), \
        X(LEN), \
        X(ARRAY_COMPR), \
        X(DICT_COMPR), \
        X(THROW_IF_NIL), \
        X(PRE_INC), \
        X(POST_INC), \
        X(PRE_DEC), \
        X(POST_DEC), \
        X(FUNCTION), \
        X(JUMP), \
        X(JUMP_IF), \
        X(JUMP_IF_NIL), \
        X(JUMP_IF_NOT), \
        X(JUMP_IF_NONE), \
        X(RETURN), \
        X(RETURN_PRESERVE_CTX), \
        X(EXEC_CODE), \
        X(HALT), \
        X(MULTI_RETURN), \
        X(RETURN_IF_NOT_NONE), \
        X(SENTINEL), \
        X(FIX_TO), \
        X(REVERSE), \
        X(SWAP), \
        X(NONE), \
        X(NONE_IF_NIL), \
        X(CLEAR_RC), \
        X(GET_EXTRA), \
        X(PUSH_NTH), \
        X(PUSH_ARRAY_ELEM), \
        X(PUSH_TUPLE_ELEM), \
        X(PUSH_TUPLE_MEMBER), \
        X(MULTI_ASSIGN), \
        X(MAYBE_MULTI), \
        X(JUMP_IF_SENTINEL), \
        X(CLEAR_EXTRA), \
        X(FIX_EXTRA), \
        X(PUSH_ALL), \
        X(VALUE), \
        X(EVAL), \
        X(SAVE_STACK_POS), \
        X(RESTORE_STACK_POS), \
        X(NEXT), \
        X(YIELD), \
        X(MAKE_GENERATOR), \
        X(THROW), \
        X(RETHROW), \
        X(TRY), \
        X(CATCH), \
        X(POP_TRY), \
        X(RESUME_TRY), \
        X(FINALLY), \
        X(PUSH_DEFER_GROUP), \
        X(DEFER), \
        X(CLEANUP), \
        X(DROP), \
        X(PUSH_DROP), \
        X(PUSH_DROP_GROUP), \
        X(TAG_PUSH), \
        X(DEFINE_TAG), \
        X(DEFINE_CLASS), \
        X(TRY_INDEX), \
        X(TRY_INDEX_TUPLE), \
        X(TRY_TUPLE_MEMBER), \
        X(TRY_TAG_POP), \
        X(TRY_REGEX), \
        X(TRY_ASSIGN_NON_NIL), \
        X(BAD_MATCH), \
        X(BAD_CALL), \
        X(BAD_DISPATCH), \
        X(BAD_ASSIGN), \
        X(UNTAG_OR_DIE), \
        X(STEAL_TAG), \
        X(TRY_STEAL_TAG), \
        X(ENSURE_LEN), \
        X(ENSURE_LEN_TUPLE), \
        X(ENSURE_EQUALS_VAR), \
        X(ENSURE_DICT), \
        X(ENSURE_CONTAINS), \
        X(ENSURE_SAME_KEYS), \
        X(RENDER_TEMPLATE), \
        X(TRAP), \
        X(ADD), \
        X(SUB), \
        X(MUL), \
        X(DIV), \
        X(MOD), \
        X(EQ), \
        X(NEQ), \
        X(LT), \
        X(GT), \
        X(LEQ), \
        X(GEQ), \
        X(CMP), \
        X(CHECK_MATCH), \
        X(MUT_ADD), \
        X(MUT_MUL), \
        X(MUT_DIV), \
        X(MUT_SUB), \
        X(NEG), \
        X(NOT), \
        X(QUESTION), \
        X(COUNT), \
        X(PATCH_ENV), \
        X(GET_TAG)

#define X(i) INSTR_ ## i
enum instruction {
        TY_INSTRUCTIONS
};
#undef X

bool
vm_init(Ty *ty, int ac, char **av);

char const *
vm_error(Ty *ty);

noreturn void
vm_panic(Ty *ty, char const *fmt, ...);

void
vm_mark(Ty *ty);

void
Forget(Ty *ty, struct value *v, AllocList *allocs);

void
DoGC(Ty *ty);

void
NewThread(Ty *ty, Thread *thread, struct value *ctx, struct value *name, bool sigma);

void
vm_set_sigfn(Ty *ty, int, struct value const *);

void
vm_del_sigfn(Ty *ty, int);

struct value
vm_get_sigfn(Ty *ty, int);

#ifndef _WIN32
void
vm_do_signal(Ty *ty, int, siginfo_t *, void *);
#endif

bool
vm_execute(Ty *ty, char const *source, char const *file);

bool
vm_execute_file(Ty *ty, char const *path);

void
vm_push(Ty *ty, struct value const *v);

void
vm_pop(Ty *ty);

struct value *
vm_get(Ty *ty, int i);

_Noreturn void
vm_throw(Ty *ty, struct value const *);

struct value
vm_call(Ty *ty, struct value const *f, int argc);

Value
vm_call_ex(Ty *ty, Value const *f, int argc, Value const *kwargs, bool collect);

uint64_t
MyThreadId(Ty *ty);

struct value
vm_call_method(Ty *ty, struct value const *self, struct value const *f, int argc);

struct value
vm_eval_function(Ty *ty, struct value const *f, ...);

void
vm_load_c_module(Ty *ty, char const *name, void *p);

void
vm_exec(Ty *ty, char *ip);

struct value
vm_try_exec(Ty *ty, char *ip);

FrameStack *
vm_get_frames(Ty *ty);

struct value
GetMember(Ty *ty, struct value v, char const *member, unsigned long h, bool b);

extern _Thread_local TyMutex *MyLock;

void
TakeLock(Ty *ty);

void
ReleaseLock(Ty *ty, bool blocked);

char const *
GetInstructionName(uint8_t i);

#endif

/* vim: set sts=8 sw=8 expandtab: */
