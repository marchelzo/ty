#ifndef VM_H_INCLUDED
#define VM_H_INCLUDED

#include <stdint.h>
#include <stdbool.h>
#include <stdarg.h>
#include <stdnoreturn.h>

#include <signal.h>

#include "ty.h"
#include "value.h"
#include "ty/thread.h"
#include "log.h"
#include "jit/jit.h"

extern bool PrintResult;
extern volatile sig_atomic_t JitInterruptFlag;

extern Value LOTS_OF_NILS[2048];

inline static void
NilStackRange(Ty *ty, usize i, usize n)
{
        memcpy(v_(STACK, i), LOTS_OF_NILS, n * sizeof (Value));
}

bool
vm_init(Ty *ty, int ac, char **av);

Ty *
vm_new_debug_ty(void);

void
vm_free_debug_ty(Ty *ty);

void
vm_take_lock_raw(Ty *ty);

bool
vm_reset(Ty *ty);

void
vm_global_added(Ty *ty, Symbol const *sym);

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
DoAssignSubscript(Ty *ty, int n, bool exec);

bool
DoCallEx(Ty *ty, Value const *f, int n, Value const *kwargs, bool exec);

Value
BuildKwargsDict(Ty *ty, char **ip, int nkw);

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
RunTestsNative(Ty *ty);

int
RunTestHarness(Ty *ty, char **args, int n);

void
vm_push(Ty *ty, Value const *v);

Value *
vm_pop(Ty *ty);

Value *
vm_get(Ty *ty, int i);

noreturn void
vm_throw(Ty *ty, Value const *);


typedef enum {
        INDEX_OPTIONAL,
        INDEX_STRICT,
        INDEX_SAFE
} IndexMode;

Value
ArraySubscript(Ty *ty, Value container, Value subscript, IndexMode mode);

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

char const *
vm_builtin_type(char const *module, char const *name);

char const *
vm_builtin_source(Value const *f, char const **file, int *line);

char const *
vm_builtin_method_source(int class, char const *name, char const **file, int *line);

void
vm_exec(Ty *ty, char *ip);

void
vm_xcall(Ty *ty, Value const *f, Value const *pSelf, int argc, Value const *pKwargs);

void
vm_trampoline(Ty *ty);

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

void
vm_concat_strings(Ty *ty, int n);

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

[[gnu::always_inline]]
inline static void
EnsureThreadLocal(Ty *ty, usize i)
{
        if (UNLIKELY(vN(ty->tls) <= i)) {
                usize n = max(i + 1, vN(xD.tls0));
                xvR(ty->tls, n);
                while (vN(ty->tls) < n) {
                        xvP(ty->tls, NONE);
                }
        }

        if (UNLIKELY(IsNone(v__(ty->tls, i)))) {
                v_(ty->tls, i)->type = VALUE_NIL;
                vm_exec(ty, v__(xD.tls0, i));
        }
}

inline static Value const *
FrameFun(Ty *ty, Frame const *frame)
{
        return &frame->f;
}

inline static Value const *
ActiveFun(Ty *ty)
{
        return FrameFun(ty, vvL(ty->st->frames));
}

Value
TyActiveGenerator(Ty *ty);

void
TyPostFork(Ty *ty);

void
TySyncThreadState(Ty *ty);

noreturn void
ZeroDividePanic(Ty *ty);

inline static imax
IntDiv(imax a, imax b)
{
        return (b == -1) ? (imax)(0 - (umax)a) : a / b;
}

inline static imax
IntMod(imax a, imax b)
{
        return (b == -1) ? 0 : a % b;
}

inline static imax
IntShl(imax a, imax b)
{
        return (imax)((umax)a << (b & 63));
}

inline static imax
IntShr(imax a, imax b)
{
        return a >> (b & 63);
}

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

int
vm_jit_handle_interrupt(Ty *ty, Value *top, JitDeopt const *info);

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
vm_iter_begin(Ty *ty, Value xs);

bool
vm_iter_next(Ty *ty, Value *x);

void
vm_jit_loop_iter(Ty *ty);

bool
vm_jit_loop_check(Ty *ty, int z);

bool
vm_jit_spread_check(Ty *ty, bool inject_nil);

void
vm_jit_tuple_literal(Ty *ty, char *ip);

void
vm_jit_fail(Ty *ty, Value *top, char *ip);

// JIT try/catch helpers
void *
vm_jit_push_try(Ty *ty, char *catch_addr, char *finally_addr, char *end_addr);

noreturn void
vm_jit_end_try_rethrow(Ty *ty);

// JIT pattern-matching helpers
bool
vm_jit_array_rest(Ty *ty, Value *tos, Value *target, i32 start, i32 suffix);

bool
vm_jit_tuple_rest(Ty *ty, Value *tos, Value *target, i32 start);

bool
vm_jit_record_rest(Ty *ty, Value *tos, Value *target, i32 const *excluded_ids);

char *
DoFunction(Ty *ty, char const *ip);

char *
DoGenerator(Ty *ty, char const *ip);

void
DoDictLiteral(Ty *ty, i32 n, Value const *dflt);

void
DoSetLiteral(Ty *ty, i32 n);

void
DoSetCompr(Ty *ty, i32 skip, i32 n);

void
DoSubscript(Ty *ty, bool exec);

void
DoSafeSubscript(Ty *ty, bool exec);

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

void
vm_jit_neg(Ty *ty);

void
vm_trampoline_linked(Ty *ty, JitFn *func, Value **env);

void
vm_trampoline_resume(Ty *ty, i32 rc);

void
vm_jit_get_member(Ty *ty);

void
vm_jit_dyn_member_assign(Ty *ty);

void
vm_jit_target_member(Ty *ty, Value *v, i32 z);

Value
vm_jit_member_access(Ty *ty, int z);

void
vm_jit_try_member_access(Ty *ty, int z);

bool
vm_jit_try_match_member(Ty *ty, int z);

bool
vm_jit_unapply(Ty *ty, bool maybe);

void
vm_jit_scope(Ty *ty, int op);

void
vm_jit_mutation(Ty *ty, int op);

void
vm_jit_target(Ty *ty, int op, int n, int z);

void
vm_jit_binding(Ty *ty, int op, int n, int z, void *info);

Value *
vm_jit_state_slot(Ty *ty, int n, bool tls);

bool
vm_jit_check_init(Ty *ty);

void
vm_jit_misc(Ty *ty, int op, int n, void *data);

bool
vm_jit_extra_branch(Ty *ty, int op);

void
vm_jit_declaration(Ty *ty, char *ip);

void
vm_jit_failure(Ty *ty, int op, char *ip);

bool
vm_jit_yield_from(Ty *ty);

void
vm_jit_try_get_member(Ty *ty);

char *
co_colored(Ty *ty);

#define VM_TRY() (setjmp(vm_push_try(ty)->jb) == 0)

extern bool DyingOfError;

extern u64 ProfileSampleInterval;

#endif
/* vim: set sts=8 sw=8 expandtab: */
