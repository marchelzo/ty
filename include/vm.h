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
vm_do_signal(int, siginfo_t *, void *);
#endif

bool
vm_execute(Ty *ty, char const *source, char const *file);

bool
vm_load_program(Ty *ty, char const *source, char const *file);

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
vm_2op(Ty *ty, int op, Value const *a, Value const *b);

Value
vm_try_2op(Ty *ty, int op, Value const *a, Value const *b);

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

Value
vm_try_exec(Ty *ty, char *ip);

FrameStack *
vm_get_frames(Ty *ty);

Value
GetMember(Ty *ty, Value v, int i, bool b);

extern _Thread_local TyMutex *MyLock;

void
TakeLock(Ty *ty);

void
ReleaseLock(Ty *ty, bool blocked);

bool
MaybeTakeLock(Ty *ty);

char const *
GetInstructionName(uint8_t i);

void
DebugAddBreak(Ty *ty, Value const *f);

#endif

/* vim: set sts=8 sw=8 expandtab: */
