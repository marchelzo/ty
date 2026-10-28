#ifndef PROF_H_INCLUDED
#define PROF_H_INCLUDED

#include "ty.h"

#if defined(__linux__) || defined(__APPLE__)
 #define TY_HAVE_SAMPLER 1
#endif

#if defined(TY_USDT) && defined(__linux__) && __has_include(<sys/sdt.h>)
 #define _SDT_HAS_SEMAPHORES 1
 #define SDT_USE_VARIADIC 1
 #include <sys/sdt.h>
 #define TY_USDT_SEM(name) ty_ ## name ## _semaphore
 #define TY_USDT_DECLARE(name) \
         extern unsigned short volatile TY_USDT_SEM(name)
 #define TY_USDT_DEFINE(name) \
         __extension__ unsigned short volatile TY_USDT_SEM(name) \
         __attribute__((section(".probes"), used)) = 0
 #define TY_PROBING(name) UNLIKELY(TY_USDT_SEM(name) != 0)
 #define TY_PROBE(name, ...) STAP_PROBEV(ty, name, ##__VA_ARGS__)
 #define TY_HAVE_USDT 1
#else
 #define TY_USDT_DECLARE(name) extern int ty_usdt_unused_
 #define TY_USDT_DEFINE(name) extern int ty_usdt_unused_
 #define TY_PROBING(name) 0
 #define TY_PROBE(name, ...) ((void)0)
#endif

#define TY_USDT_PROBES        \
        X(function__entry)    \
        X(function__return)   \
        X(gc__start)          \
        X(gc__done)           \
        X(alloc)              \
        X(throw)              \
        X(jit__compile)       \
        X(jit__decline)       \
        X(jit__deopt)         \
        X(import__start)      \
        X(import__done)       \
        X(thread__start)      \
        X(thread__stop)       \
        X(sample)

#define X(name) TY_USDT_DECLARE(name);
TY_USDT_PROBES
#undef X

#define TY_PROBE_IF(name, ...) do {               \
        if (TY_PROBING(name)) {                   \
                TY_PROBE(name, ##__VA_ARGS__);    \
        }                                         \
} while (0)

enum {
        PS_RUN,
        PS_GC,
        PS_GC_WAIT,
        PS_COMPILE,
        PS_JIT_COMPILE,
        PS_BLOCKED,
        PS_COUNT
};

enum {
        PK_CPU,
        PK_WALL,
        PK_EVENT,
        PK_OPS,
        PK_ALLOC,
        PK_THROW,
        PK_COUNT
};

extern _Thread_local u8 volatile ProfState;
extern _Thread_local i64 ProfAllocLeft;
extern _Thread_local i64 ProfOpsLeft;
extern bool ProfCountOps;
extern _Thread_local u64 ProfPending;
extern _Atomic u64 ProfLiveN;

void
prof_start(Ty *ty);

void
prof_thread_start(Ty *ty);

void
prof_thread_stop(Ty *ty);

void
prof_alloc_slow(Ty *ty, usize n, int type);

void
prof_ops_slow(Ty *ty, char const *ip);

void
prof_report(Ty *ty);

void
prof_poll(Ty *ty);

void
prof_set_target(char const *path);

int
prof_diff_main(int argc, char **argv);

int
prof_module_begin(char const *name, char const *path, char const *source);

void
prof_module_compiled(int id);

void
prof_module_done(int id);

void
prof_gc_done(u64 before, u64 after, u64 ns);

void
prof_alloc_bind(Ty *ty, Alloc *a);

void
prof_gc_swept(Ty *ty, bool minor);

void
prof_free(Alloc *a);

void
color_sequence(float p, char *out);

extern _Atomic bool ProfWantReport;

int
prof_option(char const *arg);

void
prof_setup(void);

void
prof_usage(FILE *out);

void
prof_usdt_usage(FILE *out);

void
prof_jit_decline(Value const *f, char const *why, i32 off);

void
prof_jit_deopt(Ty *ty, Frame const *frame, i32 off);

void
prof_jit_despecialize(Value const *f, u32 deopts);

char const *
prof_jit_ip(Ty *ty, void const *ra);

char const *
prof_symbolize(uptr addr);

void
prof_throw(Ty *ty, char const *ip);

void
prof_attach_init(Ty *ty);

void
prof_attach_toggle(Ty *ty);

int
prof_attach_main(int argc, char **argv);

void
prof_attach_exit(Ty *ty);

#ifdef TY_HAVE_SAMPLER

#define PROF_ALLOC(ty, n, t) do {                                    \
        if (UNLIKELY((ProfAllocLeft -= (i64)(n)) < 0)) {             \
                prof_alloc_slow((ty), (n), (t));                     \
        }                                                            \
} while (0)

#define PROF_BIND(ty, a) do {                                        \
        if (UNLIKELY(ProfPending != 0)) {                            \
                prof_alloc_bind((ty), (a));                          \
        }                                                            \
} while (0)

#define PROF_FREE(a) do {                                            \
        if (UNLIKELY(atomic_load_explicit(&ProfLiveN, memory_order_relaxed) != 0)) { \
                prof_free((a));                                      \
        }                                                            \
} while (0)

#define PROF_OP(ty, ip) do {                                         \
        if (UNLIKELY(--ProfOpsLeft < 0)) {                           \
                prof_ops_slow((ty), (ip));                           \
        }                                                            \
} while (0)

#define PROF_POLL(ty) do {                                           \
        if (UNLIKELY(atomic_load_explicit(&ProfWantReport, memory_order_relaxed))) { \
                prof_poll(ty);                                       \
        }                                                            \
} while (0)

#define PROF_ENTER(s) u8 const prof_saved_state_ = ProfState; ProfState = (s)
#define PROF_LEAVE() (ProfState = prof_saved_state_)

#else

#define PROF_ALLOC(ty, n, t) ((void)0)
#define PROF_BIND(ty, a)     ((void)0)
#define PROF_FREE(a)         ((void)0)
#define PROF_OP(ty, ip)      ((void)0)
#define PROF_POLL(ty)        ((void)0)
#define PROF_ENTER(s)        ((void)0)
#define PROF_LEAVE()         ((void)0)

#endif

#endif

/* vim: set sts=8 sw=8 expandtab: */
