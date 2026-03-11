#ifndef JIT_H_INCLUDED
#define JIT_H_INCLUDED

#include <stdio.h>
#include <stdatomic.h>

#include "ty.h"
#include "value.h"
#include "ast.h"

#define JIT_RT_DEBUG 0
#define JIT_RT_TRACE 0
#define JIT_SCAN_LOG 0
#define JIT_DUMP_DIS 0

extern char JIT;

enum {
        JIT_RETURN,
        JIT_CALL,
        JIT_YIELD,
        JIT_YIELD_SOME,
        JIT_YIELD_NONE
};

typedef struct jit_info {
        void *code;       // Pointer to JIT'd machine code
        size_t code_size; // Size of the machine code buffer
        int param_count;  // Number of parameters
        int bound;        // Total local slots (params + locals) from FUN_INFO_BOUND
        Expr const *expr; // Source expression for debugging
        char const *name; // Function name
        Value **env;      // Closure environment (same layout as function env)
        int env_count;    // Number of captured values
} JitInfo;

typedef void (JitFn)(Ty *, Value *, Value *, Value **);

// Initialize the JIT subsystem
void
jit_init(Ty *ty);

// Compile a function's bytecode to native code.
// Returns a JitInfo* on success, or NULL on failure.
JitInfo *
jit_compile(Ty *ty, Value const *func);

// Free JIT resources
void
jit_free(Ty *ty);

#ifdef TY_PROFILER
// Print JIT stats report (compilation info, fast/slow paths, top slow sites)
void
jit_stats_report(Ty *ty, FILE *out);
#endif

inline static JitFn *
try_jit(Ty *ty, Value const *f)
{
#if !defined(TY_NO_JIT)
        void *jit = jit_of(f);

        if (LIKELY(jit != (void *)0xFA57)) {
                return jit;
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

        JitInfo *info = jit_compile(ty, f);
        if (LIKELY(info != NULL)) {
                jit = info->code;
        } else {
                jit = NULL;
        }

        set_jit_of(f, jit);

        return jit;
#else
        return NULL;
#endif
}

#endif

/* vim: set sts=8 sw=8 expandtab: */
