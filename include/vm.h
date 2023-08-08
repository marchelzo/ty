#ifndef VM_H_INCLUDED
#define VM_H_INCLUDED

#include <stdbool.h>
#include <stdarg.h>
#include <stdnoreturn.h>

#include <pthread.h>
#include <signal.h>

#include "value.h"


extern bool CompileOnly;
extern bool PrintResult;
extern pthread_t MainThread;

enum instruction {
        INSTR_NOP,

        INSTR_LOAD_LOCAL,
        INSTR_LOAD_REF,
        INSTR_LOAD_CAPTURED,
        INSTR_LOAD_GLOBAL,
        INSTR_PUSH_VAR,
        INSTR_CHECK_VARS,
        INSTR_POP_VAR,
        INSTR_TARGET_LOCAL,
        INSTR_TARGET_REF,
        INSTR_TARGET_CAPTURED,
        INSTR_TARGET_GLOBAL,
        INSTR_TARGET_MEMBER,
        INSTR_TARGET_SUBSCRIPT,
        INSTR_ASSIGN,
        INSTR_MAYBE_ASSIGN,

        INSTR_ARRAY_REST,
        INSTR_TUPLE_REST,

        INSTR_INTEGER,
        INSTR_REAL,
        INSTR_BOOLEAN,
        INSTR_STRING,
        INSTR_REGEX,
        INSTR_ARRAY,
        INSTR_DICT,
        INSTR_TUPLE,
        INSTR_DICT_DEFAULT,
        INSTR_NIL,
        INSTR_SELF,
        INSTR_TAG,
        INSTR_CLASS,

        INSTR_TO_STRING,
        INSTR_CONCAT_STRINGS,

        INSTR_RANGE,
        INSTR_INCRANGE,

        INSTR_MEMBER_ACCESS,
        INSTR_TRY_MEMBER_ACCESS,
        INSTR_SUBSCRIPT,
        INSTR_TAIL_CALL,
        INSTR_CALL,
        INSTR_CALL_METHOD,
        INSTR_TRY_CALL_METHOD,
        INSTR_GET_NEXT,
        INSTR_PUSH_INDEX,
        INSTR_READ_INDEX,
        INSTR_POP,
        INSTR_UNPOP,
        INSTR_DUP,
        INSTR_LEN,
        INSTR_ARRAY_COMPR,
        INSTR_DICT_COMPR,

        INSTR_THROW_IF_NIL,

        INSTR_PRE_INC,
        INSTR_POST_INC,
        INSTR_PRE_DEC,
        INSTR_POST_DEC,

        INSTR_FUNCTION,
        INSTR_JUMP,
        INSTR_JUMP_IF,
        INSTR_JUMP_IF_NIL,
        INSTR_JUMP_IF_NOT,
        INSTR_JUMP_IF_NONE,
        INSTR_RETURN,
        INSTR_RETURN_PRESERVE_CTX,
        INSTR_EXEC_CODE,
        INSTR_HALT,

        INSTR_MULTI_RETURN,
        INSTR_SENTINEL,
        INSTR_FIX_TO,
        INSTR_REVERSE,
        INSTR_SWAP,
        INSTR_NONE,
        INSTR_NONE_IF_NIL,
        INSTR_CLEAR_RC,
        INSTR_GET_EXTRA,
        INSTR_PUSH_NTH,
        INSTR_PUSH_ARRAY_ELEM,
        INSTR_PUSH_TUPLE_ELEM,
        INSTR_PUSH_TUPLE_MEMBER,
        INSTR_MULTI_ASSIGN,
        INSTR_MAYBE_MULTI,
        INSTR_JUMP_IF_SENTINEL,
        INSTR_CLEAR_EXTRA,
        INSTR_FIX_EXTRA,
        INSTR_PUSH_ALL,

        INSTR_FUCK,
        INSTR_FUCK2,
        INSTR_FUCK3,

        INSTR_VALUE,

        INSTR_SAVE_STACK_POS,
        INSTR_RESTORE_STACK_POS,

        INSTR_NEXT,
        INSTR_YIELD,
        INSTR_MAKE_GENERATOR,

        INSTR_THROW,
        INSTR_RETHROW,
        INSTR_TRY,
        INSTR_POP_TRY,
        INSTR_POP_THROW,
        INSTR_FINALLY,

        INSTR_PUSH_DEFER_GROUP,
        INSTR_DEFER,
        INSTR_CLEANUP,
        INSTR_DROP,

        INSTR_TAG_PUSH,
        INSTR_DEFINE_TAG,
        INSTR_DEFINE_CLASS,
        INSTR_TRY_INDEX,
        INSTR_TRY_INDEX_TUPLE,
        INSTR_TRY_TUPLE_MEMBER,
        INSTR_TRY_TAG_POP,
        INSTR_TRY_REGEX,
        INSTR_TRY_ASSIGN_NON_NIL,
        INSTR_BAD_MATCH,
        INSTR_BAD_CALL,
        INSTR_BAD_ASSIGN,
        INSTR_UNTAG_OR_DIE,
        INSTR_ENSURE_LEN,
        INSTR_ENSURE_LEN_TUPLE,
        INSTR_ENSURE_EQUALS_VAR,
        INSTR_ENSURE_DICT,
        INSTR_ENSURE_CONTAINS,
        INSTR_ENSURE_SAME_KEYS,

        // binary operators
        INSTR_ADD,
        INSTR_SUB,
        INSTR_MUL,
        INSTR_DIV,
        INSTR_MOD,
        INSTR_EQ,
        INSTR_NEQ,
        INSTR_LT,
        INSTR_GT,
        INSTR_LEQ,
        INSTR_GEQ,
        INSTR_CMP,
        INSTR_CHECK_MATCH,

        INSTR_MUT_ADD,
        INSTR_MUT_MUL,
        INSTR_MUT_DIV,
        INSTR_MUT_SUB,

        // unary operators
        INSTR_NEG,
        INSTR_NOT,
        INSTR_QUESTION,
        INSTR_COUNT,
        INSTR_GET_TAG,
};

bool
vm_init(int ac, char **av);

char const *
vm_error(void);

noreturn void
vm_panic(char const *fmt, ...);

void
vm_mark(void);

void
DoGC(void);

void *
vm_run_thread(void *);

void
NewThread(pthread_t *thread, struct value *ctx, struct value *name);

void
vm_set_sigfn(int, struct value const *);

void
vm_del_sigfn(int);

struct value
vm_get_sigfn(int);

void
vm_do_signal(int, siginfo_t *, void *);

bool
vm_execute(char const *source);

bool
vm_execute_file(char const *path);

void
vm_push(struct value const *v);

void
vm_pop(void);

struct value *
vm_get(int i);

struct value
vm_call(struct value const *f, int argc);

struct value
vm_eval_function(struct value const *f, ...);

void
vm_load_c_module(char const *name, void *p);

void
vm_exec(char *ip);

extern _Thread_local pthread_mutex_t *MyLock;

void
TakeLock(void);

void
ReleaseLock(bool blocked);

#endif
