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

extern bool PrintResult;

bool
vm_init(Ty *ty, int ac, char **av);

noreturn void
vm_panic_ex(Ty *ty, ThrowCtx const *ctx, char const *fmt, ...);

noreturn void
vm_panic(Ty *ty, char const *fmt, ...);

void
vm_mark(Ty *ty);

void
Forget(Ty *ty, Value *v, AllocList *allocs);

void
DoGC(Ty *ty);

void
NewThread(Ty *ty, Thread *thread, Value *ctx, Value *name, bool sigma);

void
vm_set_sigfn(Ty *ty, int, Value const *);

void
vm_del_sigfn(Ty *ty, int);

Value
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
vm_push(Ty *ty, Value const *v);

Value *
vm_pop(Ty *ty);

Value *
vm_get(Ty *ty, int i);

noreturn void
vm_throw(Ty *ty, Value const *);

Value
vm_call(Ty *ty, Value const *f, int argc);

Value
vm_2op(Ty *ty, int op, Value const *a, Value const *b);

Value
vm_try_2op(Ty *ty, int op, Value const *a, Value const *b);

Value
vm_call_ex(Ty *ty, Value const *f, int argc, Value *kwargs, bool collect);

u64
MyThreadId(Ty *ty);

Value
vm_call_method(Ty *ty, Value const *self, Value const *f, int argc);

Value
vm_eval_function(Ty *ty, Value const *f, ...);

void
vm_load_c_module(Ty *ty, char const *name, void *p);

void
vm_exec(Ty *ty, char *ip);

Value
vm_try_exec(Ty *ty, char *ip);

FrameStack *
vm_get_frames(Ty *ty);

Value *
vm_local(Ty *ty, int i);

Value *
vm_global(Ty *ty, int i);

Value
GetMember(Ty *ty, Value v, int i, bool try_missing, bool exec);

Value
CompleteCurrentFunction(Ty *ty);

extern _Thread_local TySpinLock *MyLock;

void
TakeLock(Ty *ty);

void
ReleaseLock(Ty *ty, bool blocked);

bool
MaybeTakeLock(Ty *ty);

char const *
GetInstructionName(uint8_t i);

char *
StepInstruction(char const *ip);

void
DebugAddBreak(Ty *ty, Value const *f);

bool
TyReloadModule(Ty *ty, char const *module);

char *
FormatTrace(Ty *ty, ThrowCtx const *ctx, byte_vector *out);

void
CaptureContext(Ty *ty, ThrowCtx *ctx);

void
CaptureContextEx(Ty *ty, ThrowCtx *ctx);

noreturn void
ZeroDividePanic(Ty *ty);

struct try *
vm_push_try(Ty *ty);

void
vm_catch(Ty *ty);

void
vm_finally(Ty *ty);

#define VM_TRY() (setjmp(vm_push_try(ty)->jb) == 0)

#endif

/* vim: set sts=8 sw=8 expandtab: */
