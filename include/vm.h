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
extern volatile sig_atomic_t JitInterruptFlag;

bool
vm_init(Ty *ty, int ac, char **av);

noreturn void
vm_panic_ex(Ty *ty, char const *fmt, ...);

noreturn void
vm_panic(Ty *ty, char const *fmt, ...);

void
vm_mark(Ty *ty);

void
Forget(Ty *ty, Value *v, AllocList *allocs);

void
DoGC(Ty *ty);

void
DoTargetMember(Ty *ty, Value v, i32 z);

void
DoAssign(Ty *ty);

void
DoAssignExec(Ty *ty);

void
DoAssignSubscript(Ty *ty, bool exec);

bool
DoCall(Ty *ty, Value const *f, int n, int nkw, bool auto_this, bool exec);

bool
CallMethod(Ty *ty, int m_id, int n, int nkw, bool b, bool exec);

void
DoYield(Ty *ty);

void
DoTargetSubscript(Ty *ty);

void
DoCount(Ty *ty, bool exec);

void
DoCheckMatch(Ty *ty, bool exec);

void
NewThread(Ty *ty, Thread *thread, Value *ctx, Value *name, bool sigma);

void
vm_set_sigfn(Ty *ty, int sig, Value const *f);

void
vm_del_sigfn(Ty *ty, int sig);

Value
vm_get_sigfn(Ty *ty, int sig);

void
vm_invoke_sigfn(Ty *ty, int sig);

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

int
RunTests(Ty *ty);

void
vm_push(Ty *ty, Value const *v);

Value *
vm_pop(Ty *ty);

Value *
vm_get(Ty *ty, int i);

noreturn void
vm_throw(Ty *ty, Value const *);

noreturn void
vm_throw_ty(Ty *ty);

Value
ArraySubscript(Ty *ty, Value container, Value subscript, bool strict);

Value
vm_call(Ty *ty, Value const *f, int argc);

Value
vm_2op(Ty *ty, int op, Value const *a, Value const *b);

Value
vm_try_2op(Ty *ty, int op, Value const *a, Value const *b);

Value
vm_call_ex(Ty *ty, Value const *f, int argc, Value *kwargs, bool collect);

u64
TyThreadId(Ty *ty);

u64
RealThreadId(void);

Ty *
GetMyTy(void);

Value
vm_call_method(Ty *ty, Value const *self, Value const *f, int argc);

Value
vm_call1(Ty *ty, Value const *f, Value const *x);

Value
vm_call_method_fast(Ty *ty, Value const *self, Value const *f, int argc);

void
vm_push_self(Ty *ty);

Value *
vm_get_self(Ty *ty);

Value
vm_eval_function(Ty *ty, Value const *f, ...);

void
vm_load_c_module(Ty *ty, char const *name, void *p);

void
vm_exec(Ty *ty, char *ip);

void
vm_xcall(Ty *ty, Value const *f, Value const *pSelf, int argc, Value const *pKwargs);

bool
vm_try_exec(Ty *ty, char *ip, Value *ret);

FrameStack *
vm_get_frames(Ty *ty);

Value *
vm_local(Ty *ty, int i);

Value *
vm_global(Ty *ty, int i);

void
vm_to_string(Ty *ty, Value *v);

Value
vm_make_range(Ty *ty, Value const *a, Value const *b, bool inclusive);

Value
GetMember(Ty *ty, int i, bool try_missing, bool exec);

Value
CompleteCurrentFunction(Ty *ty);

void
TakeLock(Ty *ty);

void
ReleaseLock(Ty *ty, bool blocked);

bool
HoldingLock(Ty *ty);

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

inline static Value const *
FrameFun(Ty *ty, Frame const *frame)
{
        return &frame->f;
}

inline static Value const *
ActiveFun(Ty *ty)
{
        return FrameFun(ty, vvL(ty->st.frames));
}

Value
TyActiveGenerator(Ty *ty);

void
TyPostFork(Ty *ty);

void
TySyncThreadState(Ty *ty);

noreturn void
ZeroDividePanic(Ty *ty);

struct try *
vm_push_try(Ty *ty);

Value
vm_catch(Ty *ty);

void
vm_finally(Ty *ty);

noreturn void
vm_rethrow(Ty *ty);

void
xprint_stack(Ty *ty, int n);

void
vm_jit_handle_interrupt(Ty *ty, Value *top);

void
vm_check_flags(Ty *ty);

// JIT helpers (implemented in vm.c, called from jit.c)
void
vm_jit_push_target(Ty *ty, Value *v);

Value *
vm_jit_pop_target(Ty *ty);

Value
vm_jit_bind_method(Ty *ty, Value *f, Value *v);

void
vm_jit_loop_iter(Ty *ty);

bool
vm_jit_loop_check(Ty *ty, int z);

void
vm_jit_fail(Ty *ty, Value *top, char *ip);

#if !defined(TY_NO_JIT)
JitContStack *
GetFreeJitContStack(Ty *ty);
#endif

char *
DoFunction(Ty *ty, char const *ip);

char *
DoGenerator(Ty *ty, char const *ip);

void
DoDictLiteral(Ty *ty, i32 n, Value const *dflt);

void
DoSubscript(Ty *ty, bool exec);

void
DoMutAdd(Ty *ty, bool exec);

void
DoMutSub(Ty *ty, bool exec);

void
DoMutMul(Ty *ty, bool exec);

void
DoMutDiv(Ty *ty, bool exec);

void
DoMutMod(Ty *ty, bool exec);

void
DoMutAnd(Ty *ty, bool exec);

void
DoMutOr(Ty *ty, bool exec);

void
DoMutXor(Ty *ty, bool exec);

void
DoMutShl(Ty *ty, bool exec);

void
DoMutShr(Ty *ty, bool exec);

void
DoBinaryOp(Ty *ty, int op, bool exec);

void
IncValue(Ty *ty, Value *v);

void
DecValue(Ty *ty, Value *v);

void
DoCmp(Ty *ty);

void
DoLt(Ty *ty);

void
DoGt(Ty *ty);

void
DoLeq(Ty *ty);

void
DoGeq(Ty *ty);

char *
co_colored(Ty *ty);

#define VM_TRY() (setjmp(vm_push_try(ty)->jb) == 0)

#ifdef TY_PROFILER
void
jit_profiler_tick(Ty *ty, char const *ip);

extern u64 ProfileSampleInterval;
#endif

#endif

/* vim: set sts=8 sw=8 expandtab: */
