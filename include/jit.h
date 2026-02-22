#ifndef JIT_H_INCLUDED
#define JIT_H_INCLUDED

#include "ty.h"
#include "value.h"
#include "ast.h"

#define JIT_LOG_VERBOSE 1

// JIT compilation modes
#define JIT_MODE_BYTECODE 2   // Bytecode-to-native compilation

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

typedef void (*JitFn)(Ty *, Value *, Value *, Value **);

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

#endif

/* vim: set sts=8 sw=8 expandtab: */
