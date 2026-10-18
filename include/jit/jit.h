#ifndef JIT_H_INCLUDED
#define JIT_H_INCLUDED

#include <stdio.h>
#include <signal.h>
#include <stdatomic.h>

#include "ty.h"
#include "value.h"

extern volatile sig_atomic_t DebugJitOff;

#define JIT_RT_DEBUG 0
#define JIT_RT_TRACE 0
#define JIT_SCAN_LOG 0
#define JIT_DUMP_DIS 0

extern char JIT;

char const *
jit_frame_ip(Frame const *frame, char const *ip);

enum {
        JIT_RETURN,
        JIT_CALL,
        JIT_YIELD,
        JIT_YIELD_SOME,
        JIT_YIELD_NONE,
        JIT_DEOPT,
        JIT_OSR
};

typedef struct {
        i32 sp;
        i32 nsave;
        i32 save[16];
} JitDeopt;

// Pack/unpack JIT return values: low 4 bits = reason, upper bits = resume index
#define JIT_PACK(reason, idx)  (((i32)(idx) << 4) | (reason))
#define JIT_REASON(packed)     ((packed) & 0xF)
#define JIT_RESUME(packed)     ((packed) >> 4)

typedef i32 (JitFn)(Ty *, i32 resume_idx, Value *args, Value **env, uptr const **pc);

// Initialize the JIT subsystem
void
jit_init(Ty *ty);

// Compile a function's bytecode to native code.
// Returns the compiled entry point on success, or NULL on failure.
JitFn *
jit_compile(Ty *ty, Value const *func);

// Free JIT resources
void
jit_free(Ty *ty);

// Print JIT stats report (compilation info, fast/slow paths, top slow sites)
void
jit_stats_report(Ty *ty, FILE *out);

enum {
        JIT_UNSEEN    = 0xFA57,
        JIT_BUDGET    = 1000,
        JIT_CALL_COST = 1,
        JIT_PENDING   = JIT_UNSEEN + 0x100000,
        JIT_TIER_BUDGET = 5000,
        JIT_PINNED_BUDGET = 32
};

bool
jit_hot_on_entry(Value const *f);

int
jit_eager(void);

bool
jit_pinned_loop(Value const *f);

int
jit_tier(void);

JitFn *
jit_promote(Ty *ty, Value const *f);

JitFn *
jit_despecialize(Ty *ty, Value const *f);

enum { JIT_DEOPT_LIMIT = 16 };

enum {
        JIT_WHY_UNKNOWN,
        JIT_WHY_LOOP_ENTRY,
        JIT_WHY_LOOP_TYPE,
        JIT_WHY_NUMERIC,
        JIT_WHY_POLL,
        JIT_WHY_TRAP
};


inline static uptr
jit_budget(Value const *f)
{
        if (jit_eager() == 2) {
                return 2;
        }
        if (jit_pinned_loop(f)) {
                return JIT_PINNED_BUDGET;
        }
        uptr budget = JIT_BUDGET + (uptr)code_size_of(f) / 2;
        return budget < JIT_PENDING - JIT_UNSEEN - 1 ? budget : JIT_PENDING - JIT_UNSEEN - 1;
}

inline static bool
jit_pending(void const *jit)
{
        return (uptr)jit >= JIT_UNSEEN && (uptr)jit < JIT_PENDING;
}

inline static JitFn *
try_jit_ex(Ty *ty, Value const *f, bool now)
{
        if (UNLIKELY(DebugJitOff)) {
                return NULL;
        }

        void *jit = jit_of(f);

        if (LIKELY(!jit_pending(jit))) {
                return jit;
        }

        uptr state = (uptr)jit;

        if (!now && state == JIT_UNSEEN) {
                if (jit_hot_on_entry(f)) {
                        now = true;
                } else {
                        state = JIT_UNSEEN + jit_budget(f);
                }
        }

        if (!now && state > JIT_UNSEEN + JIT_CALL_COST) {
                set_jit_of(f, (void *)(state - JIT_CALL_COST));
                return NULL;
        }

        _Atomic i16 *flags = (void *)flags_of(f);
        i16 flags0 = atomic_load_explicit(flags, memory_order_relaxed);

        if (UNLIKELY(flags0 & FF_JIT_FIRST)) {
                return NULL;
        }

        bool miss = !atomic_compare_exchange_strong_explicit(
                flags,
                &flags0,
                flags0 | FF_JIT_FIRST,
                memory_order_acq_rel,
                memory_order_relaxed

        );

        if (UNLIKELY(miss)) {
                return NULL;
        }

        JitFn *compiled = jit_compile(ty, f);
        if (LIKELY(compiled != NULL)) {
                jit = compiled;
        } else {
                jit = NULL;
        }

        set_jit_of(f, jit);

        return jit;
}

inline static JitFn *
try_jit(Ty *ty, Value const *f)
{
        return try_jit_ex(ty, f, false);
}

inline static JitFn *
try_jit_now(Ty *ty, Value const *f)
{
        return try_jit_ex(ty, f, true);
}

#endif

/* vim: set sts=8 sw=8 expandtab: */
